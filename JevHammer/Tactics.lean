module

public meta import JevHammer.Types

public meta section
namespace JevHammer
open Lean Meta

/-- Input to a tactic generator. The goal's local context is active. Premises
are empty before retrieval; otherwise they have the current selected order. -/
structure TacticContext where
  goal : MVarId
  premises : Array Name
  config : Config

/-- Generate tactic code from the actual goal and selected premises. Generators
are read-only queries: the engine restores their Lean state before executing
the returned code. External IO cannot be rolled back. -/
abbrev TacticGenerator := TacticContext → MetaM (Array String)

/-- Round-robin selection prevents one action family from filling the cap. -/
def interleaveUnique (routes : Array (Array String)) (limit : Nat) : Array String := Id.run do
  let mut result := #[]
  let depth := routes.foldl (fun n r => max n r.size) 0
  for i in [:depth] do
    for route in routes do
      if result.size >= limit then return result
      if let some item := route[i]? then
        unless result.contains item do result := result.push item
  return result

namespace TacticGenerator

/-- A fixed ordered collection, parsed in the calling file's environment. -/
def fixed (codes : Array String) : TacticGenerator := fun _ => pure codes

/-- Try the first collection before the second collection. -/
def append (first second : TacticGenerator) : TacticGenerator := fun ctx => do
  return (← first ctx) ++ (← second ctx)

/-- Interleave action families, preserving order within each and removing
duplicate code. Useful when a successor limit could starve appended families. -/
def interleave (generators : Array TacticGenerator) : TacticGenerator := fun ctx => do
  let routes ← generators.mapM (· ctx)
  return interleaveUnique routes (routes.foldl (fun n r => n + r.size) 0)

end TacticGenerator

/-- All proof attempts made by the engine come from these five generators.
Every field defaults to empty: `{}` performs no proof steps. The normal tactic
uses `defaultTactics`, which explicitly supplies the standard collection.

Each returned string is one tactic (possibly a composed tactic script).
Unsupported syntax and failed attempts are skipped with state restored.
Generator exceptions abort the invocation, restoring its initial Lean state.
The supplied tactics may themselves invoke other tactics and registered rules;
this interface controls engine dispatch, not their transitive implementation. -/
structure TacticSet where
  /-- Alternatives that must close a goal. Used before retrieval at each root
  and at selected search states, with available premises supplied. -/
  close : TacticGenerator := .fixed #[]
  /-- Generated once after root closing fails, before retrieval. Run sequentially
  on every remaining goal. A failed attempt leaves that goal unchanged; successful
  attempts may close it or create several subgoals. No implicit intros are added. -/
  prepare : TacticGenerator := .fixed #[]
  /-- Closing alternatives after retrieval/reranking, including a premise refresh. -/
  finish : TacticGenerator := .fixed #[]
  /-- Alternative transformations from which the beam's successors are built. -/
  steps : TacticGenerator := .fixed #[]
  /-- Closing alternatives on each successor subgoal before Jev sees it.
  There is no implicit assumption/rfl/trivial fallback. -/
  cleanup : TacticGenerator := .fixed #[]

end JevHammer
