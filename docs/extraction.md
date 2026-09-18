# Extraction notes

JevHammer packages the adaptive proof-search engine used by the earlier
`jev_neural_live` tactic, independently of any premise-selection implementation.
The source research revision is
`9a07e7452246662a919c19407ae7def19f3ebfa4`; the source repository and all benchmark
evidence remain in the local `jevpilot-experiments` repository and its worktrees.

The core came from `benchmarks/JevFinish/Advanced.lean`. Checked speculative
tactic execution and auxiliary inlining came from `benchmarks/JevFinish.lean`;
kernel closure checks and heartbeat scoping came from `JevPilot/Search.lean`;
decision prompts came from `benchmarks/JevFinish/Scoring.lean`.

Changes made for the standalone package:

- Use the published JevPilot client at a pinned Git revision.
- Accept Lean's existing `LibrarySuggestions.Selector` directly, with the usual
  registry and an optional per-invocation `using` expression.
- Remove the research-specific retrieval implementations and ablation switches.
- Preserve selector order by default. Optional Jev premise reranking is explicit;
  all public tactic variants keep the Jev proof-state heuristic enabled.
- Require a ranker in the low-level API; tests can supply a mock.
- Restore goal/environment state after selecting premises and filter all names
  against the original environment.
- Resolve private premise names through Lean's name-resolution machinery.
- Preserve existing private theorem names in exact suggestions, while inlining
  only newly generated auxiliary declarations.
- Check proofs in the original environment after auxiliary inlining.
- Replay short closing tactics for direct portfolio successes, avoiding large
  rendered omega certificates; validate exact suggestions for other proofs.
- Require explicit password-store entries and load credentials lazily.
- Depend only on Lean and JevPilot. Extra tactics are available when imported by
  the calling project, so the core does not require Mathlib or Aesop.

The search still uses the adaptive engine's diverse action ordering, bounded
beam, cycle suppression, premise-assisted solvers, and one changed-goal premise
refresh. This extraction is validated by offline regression tests, not a new
Mathlib performance comparison. The former experiment's benchmark results used
specific selectors and imports and should not be attributed to every configuration.
