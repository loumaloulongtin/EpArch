# Feasibility and Forced Primitives

The forcing theorems are vacuous unless the constraint bundles are actually
satisfiable. This file describes the concrete witness family that closes the
existence side and shows how it composes with the world layer to yield a
zero-hypothesis form of the main convergence theorem.

Existence is *not* the same as forcing. The forcing claim is that any system
satisfying the operational and bridge properties contains the bank
primitives; existence says that at least one such system can be exhibited
concretely, so the universally-quantified forcing theorem has non-empty
domain.

---

## Concrete witness family

The witness family lives in `EpArch/Concrete/`, split into focused modules:

| File | What it carries |
|---|---|
| `Concrete/Types.lean` | concrete base types: `CProp`, `CDeposit`, `CBubble`, `CACL`, `CTrustBridge`, `CExportRequest`, `CAuditChannel`; ACL permission helpers; cost and freshness predicates |
| `Concrete/Commitments.lean` | C1–C8 commitment witnesses; `all_commitments_satisfiable` |
| `Concrete/WorkingSystem.lean` | `ConcreteWorkingSystem`, behavioral equivalence, grounding |
| `Concrete/DeficientSystems.lean` | the eight deficient-system bridge-impossibility witnesses |
| `Concrete/Realizer.lean` | `Realizer` (8-commitment conjunction) and `SuccessfulSystem` |
| `Concrete/VerificationDepth.lean` | `DepthClaim` constructive witness; `bounded_verify` |
| `Concrete/NonVacuity.lean` | trace, legibility, and convergence witnesses |
| `Concrete/WorkedTraces.lean` | worked traces used by theorem transport |
| `WorldWitness.lean` | `WitnessCtx` — concrete `WorldCtx` satisfying all three W_* bundles |

`WitnessCtx` discharges `holds_W_lies_possible`,
`holds_W_bounded_verification`, and `holds_W_partial_observability`. These
are the three ingredients that turn a `WorldCtx`-quantified obligation into a
closed statement.

---

## Headline existence theorems

### `existence_under_constraints_structural` (`Feasibility.lean`)

```
∃ W : WorkingSystem,
  StructurallyForced W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W
```

There exists a working system that satisfies all operational properties and
contains the bank primitives, with the forcing side witnessed by
`StructurallyForced`. The witness is `ConcreteWorkingSystem`; the three
conjuncts are `concrete_structurally_forced`, `concrete_satisfies_all_properties`,
and `concrete_structural_convergence` (for `containsBankPrimitives`).

### `existence_under_constraints_embedding` (`Feasibility.lean`)

```
∃ W : WorkingSystem,
  ForcingEmbedding W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W
```

The strongest non-vacuity form. All design judgment is localised in
`concrete_forcing_embedding`, which witnesses only the `ForcingEmbedding W`
conjunct. The `containsBankPrimitives` conjunct is the same
`concrete_structural_convergence` = `convergence_structural _ concrete_structurally_forced
concrete_satisfies_all_properties` used in the structural version.

### `kernel_world_forces_bank_primitives` (`WorldBridges.lean`)

```
containsBankPrimitives EpArch.ConcreteInstance.ConcreteWorkingSystem
```

Zero free hypotheses. The proof discharges the three W_* antecedents with
`WitnessCtx` and routes through `structurally_forced_is_world_aware` and
`world_assumptions_force_bank_primitives`. This is the closed-form citation
when the question is "is there a system the convergence theorem actually
applies to?"

---

## World-bundle satisfiability

Three non-vacuity facts close the world-layer satisfiability question:

| Theorem | What it says |
|---|---|
| `world_bundles_feasible` | `∃ C : WorldCtx, Nonempty C.W_lies_possible ∧ Nonempty C.W_bounded_verification ∧ Nonempty C.W_partial_observability` |
| `commitments_feasible` | the 8 architectural commitments are simultaneously satisfiable |
| `realizer_exists` | `Nonempty EpArch.Realizer` |

The world-bundle witness is `WitnessCtx`; the commitments witness lifts the
per-commitment witnesses from `Concrete/Commitments.lean`; the realizer
witness is `ConcreteRealizer`.

---

## World-to-structural bridge

The bridge from W_* bundles to the structural forcing apparatus consists of
three per-dimension lemmas (in `WorldBridges.lean`):

| Bundle | Bridge theorem | Forces |
|---|---|---|
| `W_lies_possible` | `w_lies_forces_revocation_need` | revocation primitives via `monotonic_no_exit` |
| `W_bounded_verification` | `w_bounded_forces_incompleteness` | trust-bridge primitives via `verification_only_import_incomplete` |
| `W_partial_observability` | `w_partial_obs_forces_redeemability` | redeemability primitives via the obs-stable closed-endorsement gap |

`structurally_forced_is_world_aware` then routes these into
`world_assumptions_force_bank_primitives` by weakening: every
`StructurallyForced` system satisfies `WorldAwareSystem` because the eight
unconditional implications strictly imply the three guarded ones.

The recall direction of bounded verification is a Minimality-layer
consequence of the same bound: `RecallBudget` parallels
`BoundedVerification`; `recallBudget_to_bounded` embeds the recall
impossibility into the bounded-verification one. This is not a ninth
pressure — it is the same trust/audit dimension viewed at withdrawal time.

---

## What this file does not claim

This file is about **non-vacuity and forced-primitives** — that the
constraint bundles are inhabited and that any inhabitant carries the bank
primitives. It does not argue uniqueness of the witness, optimality of any
particular realization, or empirical correspondence between
`ConcreteWorkingSystem` and a deployed system. The witness-scope rationale
(why these particular concrete types and not others) is centralized in
[reference/WITNESS-SCOPE.md](../reference/WITNESS-SCOPE.md).

---

## Go next

- [PROOF-STRUCTURE.md](../PROOF-STRUCTURE.md) — per-dimension forcing chains
  these existence theorems make non-vacuous.
- [reference/WITNESS-SCOPE.md](../reference/WITNESS-SCOPE.md) — what the
  concrete witness family is and is not intended to model.
