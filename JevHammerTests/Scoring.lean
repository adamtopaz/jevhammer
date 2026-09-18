import JevHammer

open Lean JevHammer JevPilot

run_cmd do
  let state := Json.mkObj [
    ("task", .str "continuations"),
    ("goal", Json.mkObj [("remaining", .arr #[Json.mkObj [
      ("target", .str "p ∨ q"), ("context", .arr #[.str "p : Prop"])]] )])]
  let choices := #[
    Json.mkObj [("actions", .arr #[.str "constructor"]),
      ("remaining", .arr #[Json.mkObj [("target", .str "p"),
        ("context", .arr #[.str "p : Prop", .str "q : Prop"])]] )],
    Json.mkObj [("actions", .arr #[.str "symm"]),
      ("remaining", .arr #[Json.mkObj [("target", .str "q ∨ p"),
        ("context", .arr #[.str "different context"])]] )]]
  let compact := Scoring.compact state choices
  let first := ((compact[0]!.getObjValD "remaining").getArr?.toOption.getD #[])[0]!
  unless first.getObjValD "inherits_root_context" == .bool true &&
      first.getObjValD "additional_context" == .arr #[.str "q : Prop"] do
    throwError "equal-prefix context compaction failed"
  unless compact[1]! == choices[1]! do throwError "changed context was compacted incorrectly"
  let request := Scoring.request state choices "test-model"
  IO.ofExcept request.validate
  let some (_, TypeSafe.Question.choice _ candidates) := request.questions[0]?
    | throwError "states did not use Choice"
  unless candidates.size == 2 do throwError "state candidates were lost"
  let mock : TypeSafe.Transport := fun _ => pure { status := 200, body :=
    r#"{"model":"mock-jev","answers":{"rank":{"type":"choice","choice":"1","probabilities":{"0":0.1,"1":0.9},"confidence":0.8}},"usage":{"input_tokens":10,"output_tokens":2}}"# }
  let client ← IO.ofExcept <| (TypeSafe.Client.create "test-key" { maxRetries := 0 } mock).mapError toString
  let ranked ← Scoring.jevRanker client "test-model" state choices
  unless ranked.order == #[1, 0] && ranked.model == "mock-jev" &&
      ranked.usage.inputTokens == some 10 do
    throwError "Jev client adapter lost ranking or usage information"
