module

public meta import JevPilot
public meta import Lean.LibrarySuggestions.Basic

public meta section
namespace JevHammer
open Lean Meta
open JevPilot

/-- Search budgets are shared across the supplied goal list. Wall time is soft:
individual tactics, selectors, requests, and final checks can exceed the deadline. -/
structure Config where
  maxMillis : Nat := 6000
  maxNodes : Nat := 12
  maxDepth : Nat := 3
  maxCalls : Nat := 3
  maxCandidates : Nat := 24
  maxPremises : Nat := 100
  premiseCount : Nat := 8
  beamWidth : Nat := 4
  tacticHeartbeats : Nat := 15000
  /-- Preserve the selector's order by default. Jev always guides proof states. -/
  guidePremises : Bool := false
  /-- Retrieve once more after a checked transformation changes a subgoal. -/
  refreshPremises : Bool := true
  /-- Used by the public tactic's lazy Jev client. -/
  model : String := "jev-1.13.0"
  timeoutSeconds : Nat := 5
  deriving Repr

structure Ranking where
  order : Array Nat
  usage : TypeSafe.Usage := {}
  model : String := ""

/-- A heuristic can only reorder Lean-generated candidates. It cannot return
proof text or new tactics. Injection supports offline testing and recorded replay. -/
abbrev Ranker := Json → Array Json → IO Ranking

/-- Rank selector-generated mathematical choices using the search's existing
clock, call limit, client and statistics. The question is program-supplied;
the result is a checked permutation, with candidate-order fallback. -/
abbrev SelectorRanker := String → MVarId → Array Json → MetaM (Array Nat)

/-- Decorate a standard selector with access to budgeted Jev decisions. This
function type can also be written in a selector library without importing
JevHammer. Applying the factory itself performs no monadic work. -/
abbrev SelectorFactory := SelectorRanker → LibrarySuggestions.Selector → LibrarySuggestions.Selector

def isPermutation (order : Array Nat) (size : Nat) : Bool :=
  order.size == size && (List.range size).all (order.contains ·)

structure Stats where
  nodes : Nat := 0
  trials : Nat := 0
  rankCalls : Nat := 0
  premiseRankCalls : Nat := 0
  /-- A subset of premiseRankCalls, made through an injected selector callback. -/
  selectorRankCalls : Nat := 0
  stateRankCalls : Nat := 0
  rankFailures : Nat := 0
  inputTokens : Nat := 0
  outputTokens : Nat := 0
  elapsedMs : Nat := 0
  exhausted : Bool := false
  model : String := ""
  premises : Nat := 0
  branches : Nat := 0
  winner : String := ""
  retrievalMs : Nat := 0
  refreshes : Nat := 0
  deriving Repr, ToJson
end JevHammer
