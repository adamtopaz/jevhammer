module

public meta import JevHammer.Types

public meta section
namespace JevHammer.Scoring
open Lean JevPilot

/-- Compact an inherited local context only when it is exactly the same prefix.
Changed or non-extension contexts are kept in full, including let values. -/
def compact (state : Json) (choices : Array Json) : Array Json := Id.run do
  let root := state.getObjValD "goal"
  let ctx := root.getObjValD "context"
  let base := if let .arr xs := ctx then xs else
    let goals := (root.getObjValD "remaining").getArr?.toOption.getD #[]
    ((goals[0]?.getD Json.null).getObjValD "context").getArr?.toOption.getD #[]
  return choices.map fun choice =>
    match (choice.getObjValD "remaining").getArr? with
    | .error _ => choice
    | .ok goals =>
      let gs := goals.map fun g =>
        let ctx := (g.getObjValD "context").getArr?.toOption.getD #[]
        if ctx.size >= base.size && ctx.extract 0 base.size == base then
          Json.mkObj [("target", g.getObjValD "target"), ("inherits_root_context", .bool true),
            ("additional_context", .arr (ctx.extract base.size ctx.size))]
        else g
      Json.mkObj [("actions", choice.getObjValD "actions"), ("remaining", .arr gs)]

/-- Independent questions permit multiple jointly useful premises to score highly.
Question IDs are labels only: each instruction contains its candidate explicitly. -/
def request (state : Json) (choices : Array Json) (model : String) : TypeSafe.Request :=
  let premise := state.getObjValD "task" == .str "premises" ||
    state.getObjValD "task" == .str "premise_refresh"
  let independent := state.getObjValD "independent_scores" == .bool true
  let candidates := compact state choices
  let instruction := if premise then
    "Will this mathematical lemma be useful in a short proof of the Lean goal, by rewriting, forward reasoning, or backward application, possibly together with other lemmas? Judge the complete statement against the target and local hypotheses."
    else
      "Can ALL remaining goals in this checked Lean continuation likely be closed by short standard proofs? Judge actual progress, available hypotheses, and unresolved witnesses. A circular restatement or arbitrary underconstrained witness is unlikely to help. Goals marked inherits_root_context inherit the original root context plus additional_context."
  let questions := if independent then candidates.mapIdx fun i candidate =>
      (toString i, TypeSafe.Question.noul (Json.mkObj [
        ("question", .str instruction), ("candidate", candidate)]))
    else #[("rank", TypeSafe.Question.choice (.str (instruction ++ " Select the most promising candidate."))
      (candidates.mapIdx fun i c => (toString i, c)))]
  { model, state, questions }

def ranking (response : TypeSafe.Response) (size : Nat) (independent : Bool) : IO Ranking := do
  let scores ← if independent then (List.range size).toArray.mapM fun i => do
      return (← IO.ofExcept (response.noul? (toString i))).noul
    else do
      let a ← IO.ofExcept (response.choice? "rank")
      pure <| (List.range size).toArray.map fun i =>
        (a.probabilities.find? (fun (k, _) => k == toString i)).map Prod.snd |>.getD 0
  let order := (List.range size).toArray.qsort fun i j =>
    if scores[i]! == scores[j]! then i < j else scores[i]! > scores[j]!
  return { order, usage := response.usage, model := response.model }

/-- The same client can serve many state-ranking calls. -/
def jevRanker (client : TypeSafe.Client) (model : String := "jev-1.13.0") : Ranker :=
  fun state choices => do
    ranking (← client.systemOneIO (request state choices model)) choices.size
      (state.getObjValD "independent_scores" == .bool true)

end JevHammer.Scoring
