# JevHammer

A Lean finishing tactic with **pluggable premise selection** and **Jev-guided
proof-state search**. Supply a premise selector; JevHammer explores Lean-checked
proof steps, uses Jev to choose promising continuations, and checks the final
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
suggestion. Direct portfolio successes get a short closing tactic; other proofs
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

Core Lean supplies `simp_all`, `omega`, `grind`, and the basic proof steps.
When the calling file imports Aesop or the relevant Mathlib tactics, JevHammer
also tries `aesop`, `ext1`, `contrapose!`, and `push_neg`. Unsupported tactic syntax
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
-- JevHammer.solve goals selector ranker stats config : MetaM Unit
-- JevHammer.Scoring.jevRanker client model : JevHammer.Ranker
-- JevHammer.lazyJevRanker config : IO JevHammer.Ranker
```

`solve` takes a standard `Selector`, a required `Ranker`, and an `IO.Ref Stats`.
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
suggestions. CI checks Lean 4.33.0 and 4.34.0.

See [the extraction notes](docs/extraction.md) for provenance and differences
from the research tactic. Earlier benchmark coverage is not a measurement of
every possible selector or of this core-only import configuration.
