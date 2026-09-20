# Budgeted selector guidance

The optional `SelectorFactory` lets a premise selector make Jev decisions using
the same ranking client, wall clock, call allowance, and statistics as proof-state
search. A selector library can express its type with Lean alone. No Mathlib or
selector-specific dependency is added to JevHammer.

The callback receives a mathematical question, current goal, and JSON choices.
JevHammer constructs independent selector questions and checks the returned
permutation. Empty/single choices need no request; exhausted call budgets and
ranking failures preserve input order. The model cannot return new tactics or
premise names through this interface. `selectorRankCalls` is a subset of
`premiseRankCalls`, preserving the total premise/state accounting identity.

Programmatic clients pass `selectorFactory := some factory` to `solve`. Tactic
clients use `jev_hammer using selector guiding factory`, optionally with a
configured tactic set or the password-store variant. The factory is pure;
query work remains lazy, so the cheap closing prefix needs no selector call.

Native build, complete regression tests, and downstream consumer builds passed
on Lean 4.34 and on identical sources in an isolated Lean 4.33 project. Tests
exercise shared selector/state call budgets, time exhaustion, invalid rankings,
transport failure, request schemas, base selection, rollback, and public syntax.
All tests use offline mocks and no credentials. Both validation scopes stayed
below 16 GB with no swap or memory events; see the
[machine-readable evidence](selector-guidance-validation.json).

This is research infrastructure. It makes no claim of improved proof coverage;
guided selectors still need matched benchmarks that include their calls and
latency in the search budget.
