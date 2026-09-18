# JevHammer

A Lean finishing tactic with **pluggable premise selection**, **configurable
proof steps**, and **Jev-guided proof-state search**. Supply a premise selector;
JevHammer explores Lean-checked proof steps, uses Jev to choose promising
continuations, and checks the final
proof in Lean's kernel.

The only package dependency is the [JevPilot client](https://github.com/adamtopaz/jevpilot).
**Mathlib, Aesop, LeanHammer, and neural premise services are optional.** The
default toolchain is Lean 4.34.0; Lean 4.33.0 is also supported.

## Install

Add to your `lakefile.toml`:

```toml
[[require]]
name = "jevhammer"
git = "https://github.com/adamtopaz/jevhammer"
rev = "main"
```

Run `lake update` and commit `lake-manifest.json` to pin the resolved versions.
If your project uses Lean 4.33.0, use `lake --keep-toolchain update`.

## Use a premise selector

Lean already provides the standard interface:

```lean
Lean.LibrarySuggestions.Selector
-- MVarId → LibrarySuggestions.Config → MetaM (Array Suggestion)
```

Use Lean's built-in Sine Qua Non / current-file selector by importing its default
registration:

```lean
import JevHammer
import Lean.LibrarySuggestions.Default

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  jev_hammer
```

Alternatively, register your own selector with `set_library_suggestions`, or
pass one to a single invocation:

```lean
import JevHammer

open Lean Meta LibrarySuggestions

def mySelector : Selector := fun _ config => do
  -- Replace this fixed example with your own retrieval implementation.
  return #[{ name := ``Nat.add_comm, score := 1.0 }].take config.maxSuggestions

set_library_suggestions mySelector

example (a b : Nat) : a + b = b + a := by
  jev_hammer

example (a b : Nat) : a + b = b + a := by
  jev_hammer using mySelector
```

The `using` form accepts a closed Lean expression of type `Selector`, including
a lambda or a composition of selectors. It does not change global registration.
JevHammer does not install or override a registered selector. If retrieval is
needed and no selector is configured, Lean reports that explicitly.

Selectors receive the actual goal and local context, `maxSuggestions`, the caller
name `"jev_hammer"`, and an availability filter. Their array order is preserved.
Duplicate and unavailable declarations are removed, and the premise limit is
enforced. Scores and optional tactic flags are currently not interpreted by the
proof engine. Selection is isolated from changes to the metavariable state and
environment; external IO performed by the selector cannot be rolled back.

This allows an existing neural selector, a deterministic selector, or a future
Jev dependency-traversal selector to be implemented independently of JevHammer.

## Configure the tactic collection

`jev_hammer` uses `JevHammer.defaultTactics` unless a `with` expression supplies
a replacement `JevHammer.TacticSet`. This is independent of the `using` premise
selector. Both expressions accept closed Lean terms.

For example, in a downstream project with Mathlib:

```lean
import JevHammer
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open JevHammer

def mathlibTactics : TacticSet := {
  defaultTactics with
  close := defaultTactics.close.append (.fixed #["ring", "linarith", "norm_num"])
  steps := .interleave #[defaultTactics.steps, .fixed #["ring_nf at *"]] }

example (x y : Int) : (x + y)^2 = x^2 + 2*x*y + y^2 := by
  jev_hammer with mathlibTactics

-- With an explicit premise selector:
-- jev_hammer (guidePremises := true) with mathlibTactics using mySelector
-- jev_hammer_pass "my/entry" with mathlibTactics using mySelector
```

The collection controls **every proof attempt**, including preparation and
cleanup. Each field is a `TacticGenerator`:

| Field | When it runs | Treatment of generated tactics |
|---|---|---|
| `close` | Before root retrieval and at selected search states | Try alternatives until one closes the goal |
| `prepare` | After root closing fails, before retrieval | Apply sequentially to every remaining goal; may split or close goals |
| `finish` | After premise retrieval/reranking, including a refresh | Try alternatives until one closes the goal |
| `steps` | When expanding a search state | Build alternative successors for Jev to rank |
| `cleanup` | On successor subgoals, before ranking | Try closing alternatives; retain unclosed goals |

`TacticGenerator.fixed` supplies an ordered array of tactic strings. `append`
concatenates two generators; `interleave` alternates between generators and
deduplicates their results. Interleaving helps new action families get considered
before the successor limit is reached. Order matters under bounded search.

A custom generator has type `TacticContext → MetaM (Array String)`. It receives
the actual `goal`, selected `premises`, and search `config`, with the goal's local
context active. Premises are empty before retrieval. For example:

```lean
import JevHammer
open Lean Meta JevHammer

def applySelected : TacticGenerator := fun ctx => do
  ctx.premises.mapM fun name => do
    return s!"apply {(← unresolveNameGlobal name)}"

def applicationSearch : TacticSet := {
  defaultTactics with steps := applySelected }
```

The individual default generators are public under `JevHammer.DefaultTactics`,
including premise application/rewriting/simplification, local hypothesis
application/rewriting/case splitting, and unfolding. They can be composed without
copying the defaults' implementation. Downstream projects can define a wrapper
tactic using their chosen collection; importing a collection does not silently
change the default.

All fields of a fresh `TacticSet` are empty. For a restricted collection, start
with `{ close := .fixed #["assumption"] }`; `{}` permits no proof steps at all.
Neither implicitly adds introductions, simplification, or trivial-goal cleanup.
Premise retrieval can still run; set `maxPremises := 0` to disable it. Starting
from `{ defaultTactics with ... }` instead retains all fields you do not replace.

Generators run as state-isolated, heartbeat-bounded queries. Returned code is
parsed in the caller's environment and executed speculatively; unavailable
syntax, failed tactics, and admissions are rejected. A failed preparation tactic
leaves that goal unchanged. Generator exceptions fail the entire invocation
atomically. External IO cannot be rolled back. This controls which tactics the
engine dispatches; a supplied tactic may itself call other tactics or use its
registered simp/grind/Aesop rules.

The default collection retains the original action families and their order,
with `intros` now an explicit, budgeted preparation step. Additional tactics or
different ordering are new configurations and do not inherit the old benchmark
scores. The [Mathlib example](examples/Mathlib.lean) is intended for a downstream
Mathlib project and is not part of the core package's dependency graph.

## Jev guidance and proof suggestions

`jev_hammer` loads `TYPESAFE_API_KEY` only when a nontrivial model decision is
needed. To use a password store, write:

```lean
-- jev_hammer_pass "your/password-store/entry" using mySelector
```

Cheap goals can finish without premise retrieval or any model call. When search
needs guidance, the goal context and candidate continuations are sent to Jev.
One client is reused within each tactic invocation, with retries disabled.

By default, Jev ranks **proof states**, preserving the premise selector's order.
Optional Jev premise reranking is available with:

```lean
-- jev_hammer (guidePremises := true) using mySelector
```

This keeps proof-state guidance enabled. Premise and state requests share the
same `maxCalls` budget. Exhausted call budgets, malformed responses, and API
failures preserve the structural candidate order. Enable `set_option
trace.JevHammer true` to see ranking failures and successful-run statistics.

For a single goal, JevHammer tries to produce a checked, clickable `Try this:`
suggestion. Direct successes first try a short closing tactic; other proofs
get an `exact ...` term, which may be long. Each replacement is replayed in the
original state before being offered. Applying it removes the need for Jev and
premise retrieval on later compilations. If an exact term cannot be rendered
back into elaboratable Lean, the proof still succeeds and Lean reports the
reconstruction failure. Multiple goals are solved atomically, but do not
currently receive a combined replacement suggestion.

## Search and limits

The engine first tries inexpensive closing tactics, then retrieves premises and
tries premise-assisted automation. If needed, it explores a bounded beam of
checked applications, rewrites, simplifications, introductions, case splits,
and selective unfolding. Jev sees the actual remaining goals, local context,
and action history for each continuation. The selector can be called once more
on a changed subgoal.

In the default collection, core Lean supplies `simp_all`, `omega`, `grind`, and
the basic proof steps. When the calling file imports Aesop or the relevant
Mathlib tactics, JevHammer also tries `aesop`, `ext1`, `contrapose!`, and `push_neg`. Unsupported tactic syntax
is skipped through the ordinary speculative-failure path. Import the tools your
project wants to use; they do not become dependencies of JevHammer.

Defaults are 6 seconds, depth 3, 12 expanded nodes, beam width 4, 24 successor
candidates per expansion, 100 retrieved premises, and 3 Jev calls. Each
speculative tactic has a 15,000-heartbeat limit. Model requests time out after
5 seconds and use the pinned `jev-1.13.0` model by default.

```lean
-- jev_hammer (maxMillis := 20000) (maxDepth := 5)
--   (maxNodes := 64) (maxCalls := 8) using mySelector
-- jev_hammer (model := "jev-latest") (timeoutSeconds := 3)
```

Wall time is a soft budget checked between operations. An in-flight selector,
tactic, network request, or final proof check can finish after it. The selector
must implement its own network timeouts. Search is incomplete: bounded beams and
candidate limits can discard useful steps.

## Programmatic API

```lean
-- JevHammer.solve goals selector ranker stats config (tactics := myTactics) : MetaM Unit
-- JevHammer.Scoring.jevRanker client model : JevHammer.Ranker
-- JevHammer.lazyJevRanker config : IO JevHammer.Ranker
```

`solve` takes a standard `Selector`, a required `Ranker`, and an `IO.Ref Stats`.
Its optional `tactics` argument defaults to `defaultTactics`; existing callers
need no changes. The search configuration and the tactic collection are separate.
Use a Jev ranker for normal operation, or inject a mock/recorded ranker for tests.
A ranker returns a permutation of program-generated candidates; it cannot
return executable tactic text. The whole goal list succeeds with kernel-checked
proofs or restores its original state on failure. Successful proofs are checked
again after inlining newly generated auxiliaries into the original environment.

Statistics include premise/state ranking calls, failures, successfully returned
token usage, nodes, trials, branches, retrieval time, and elapsed time. These
token counters are not a complete billing ledger for failed requests or for a
selector's own service calls.

## Develop

```sh
lake build
lake test
lake -d tests/consumer build
```

The tests require no API key. They exercise both selector entry points, actual
proof-state ranking with a mock client, malformed ranking fallback, shared call
budgets, read-only selection, multi-goal rollback, kernel checks, and replayable
suggestions. They also exercise every configurable phase, empty/restricted sets,
custom state ranking, generator isolation, and downstream-defined tactics.
CI checks Lean 4.33.0 and 4.34.0.

See [the extraction notes](docs/extraction.md) for provenance and differences
from the research tactic. Earlier benchmark coverage is not a measurement of
every possible selector or of this core-only import configuration.
