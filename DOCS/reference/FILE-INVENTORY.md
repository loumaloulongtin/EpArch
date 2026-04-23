# File Inventory

Complete inventory of every `.lean` file under `lean-formalization/`, with a
role label and a route status. This is the file-role map; for the reading
order see [START-HERE.md](../START-HERE.md), and for the proof route see
[PROOF-STRUCTURE.md](../PROOF-STRUCTURE.md).

---

## Taxonomy

Role labels:

- **kernel** — load-bearing primitives: types, substrate, operational
  semantics, the eight commitments, the headline convergence/impossibility
  machinery. Removing or weakening these breaks the central claims.
- **derived** — theorems built on the kernel: case studies, dissolutions,
  pathology diagnoses, corner theorems, agent-imposition results.
  Each is replaceable in principle; collectively they exercise the kernel.
- **witness** — concrete instantiations / non-vacuity proofs. Discharge
  satisfiability obligations: "such-and-such structure has at least one
  inhabitant".
- **meta** — theorems about the theory itself: modularity, transport,
  falsifiability, configurable certification. They reason over EpArch
  rather than inside it.
- **pedagogy** — concrete patterns and worked examples whose primary
  purpose is human reading, not load-bearing proof content.
- **bookkeeping / docs-adjacent** — build wiring and cluster registries
  (`lakefile.lean`, `Main.lean`, `Meta/ClusterRegistry.lean`).
- **optional / stretch** — explicitly cuttable content. Includes the
  Lean-kernel worked example (which carries the project's one named
  axiom) and the `theory_core` token construction.

Route status (orthogonal axis — where the file sits relative to the
headline forcing chain):

- **substrate** — kernel files providing primitives the core route
  builds on top of.
- **core-route** — kernel files *on* the headline forcing chain. In
  practice: `WorldBridges`, `Convergence`, `Minimality`, `Scenarios`,
  `GroundedEvidence`. Removing any breaks the headline directly.
- **supporting** — derived theorems, concrete witnesses,
  modularity/transport meta-results, and bookkeeping. Orbits the kernel.
- **optional** — explicitly cuttable without touching the architectural
  narrative.

Every core-route file is kernel, but not every kernel file is on the route.

Counts: 67 `.lean` files (66 modules + `lakefile.lean`).

---

## Build wiring

| File | Role | Route |
|---|---|---|
| [lakefile.lean](../../lakefile.lean) | bookkeeping / docs-adjacent | supporting |
| [Main.lean](../../Main.lean) | bookkeeping / docs-adjacent | supporting |

## `EpArch/` (top level)

| File | Role | Route |
|---|---|---|
| [EpArch/Basic.lean](../../EpArch/Basic.lean) | kernel | substrate |
| [EpArch/Header.lean](../../EpArch/Header.lean) | kernel | substrate |
| [EpArch/Bank.lean](../../EpArch/Bank.lean) | kernel | substrate |
| [EpArch/WorldCtx.lean](../../EpArch/WorldCtx.lean) | kernel | substrate |
| [EpArch/WorldWitness.lean](../../EpArch/WorldWitness.lean) | witness | supporting |
| [EpArch/WorldBridges.lean](../../EpArch/WorldBridges.lean) | kernel | core-route |
| [EpArch/Commitments.lean](../../EpArch/Commitments.lean) | kernel | substrate |
| [EpArch/SystemSpec.lean](../../EpArch/SystemSpec.lean) | kernel | substrate |
| [EpArch/Invariants.lean](../../EpArch/Invariants.lean) | kernel | substrate |
| [EpArch/Minimality.lean](../../EpArch/Minimality.lean) | kernel | core-route |
| [EpArch/Convergence.lean](../../EpArch/Convergence.lean) | kernel | core-route |
| [EpArch/Scenarios.lean](../../EpArch/Scenarios.lean) | kernel | core-route |
| [EpArch/Mechanisms.lean](../../EpArch/Mechanisms.lean) | kernel | substrate |
| [EpArch/Feasibility.lean](../../EpArch/Feasibility.lean) | witness | supporting |
| [EpArch/GroundedEvidence.lean](../../EpArch/GroundedEvidence.lean) | kernel | core-route |
| [EpArch/Health.lean](../../EpArch/Health.lean) | derived | supporting |
| [EpArch/ConditionalPredictions.lean](../../EpArch/ConditionalPredictions.lean) | derived | supporting |
| [EpArch/ResidualRiskMitigation.lean](../../EpArch/ResidualRiskMitigation.lean) | derived | supporting |

## `EpArch/Semantics/`

| File | Role | Route |
|---|---|---|
| [EpArch/Semantics/LTS.lean](../../EpArch/Semantics/LTS.lean) | kernel | substrate |
| [EpArch/Semantics/StepSemantics.lean](../../EpArch/Semantics/StepSemantics.lean) | kernel | substrate |
| [EpArch/Semantics/RevisionSafety.lean](../../EpArch/Semantics/RevisionSafety.lean) | kernel | substrate |
| [EpArch/Semantics/ScopeIrrelevance.lean](../../EpArch/Semantics/ScopeIrrelevance.lean) | derived | supporting |

## `EpArch/Theorems/`

| File | Role | Route |
|---|---|---|
| [EpArch/Theorems/Withdrawal.lean](../../EpArch/Theorems/Withdrawal.lean) | derived | supporting |
| [EpArch/Theorems/Headers.lean](../../EpArch/Theorems/Headers.lean) | derived | supporting |
| [EpArch/Theorems/Modal.lean](../../EpArch/Theorems/Modal.lean) | derived | supporting |
| [EpArch/Theorems/Dissolutions.lean](../../EpArch/Theorems/Dissolutions.lean) | derived | supporting |
| [EpArch/Theorems/Pathologies.lean](../../EpArch/Theorems/Pathologies.lean) | derived | supporting |
| [EpArch/Theorems/Strip.lean](../../EpArch/Theorems/Strip.lean) | derived | supporting |
| [EpArch/Theorems/Corners.lean](../../EpArch/Theorems/Corners.lean) | derived | supporting |
| [EpArch/Theorems/Diagnosability.lean](../../EpArch/Theorems/Diagnosability.lean) | derived | supporting |
| [EpArch/Theorems/BehavioralEquivalence.lean](../../EpArch/Theorems/BehavioralEquivalence.lean) | derived | supporting |
| [EpArch/Theorems/NotationBridge.lean](../../EpArch/Theorems/NotationBridge.lean) | derived | supporting |

## `EpArch/Theorems/Cases/`

| File | Role | Route |
|---|---|---|
| [EpArch/Theorems/Cases/Gettier.lean](../../EpArch/Theorems/Cases/Gettier.lean) | derived | supporting |
| [EpArch/Theorems/Cases/FakeBarn.lean](../../EpArch/Theorems/Cases/FakeBarn.lean) | derived | supporting |
| [EpArch/Theorems/Cases/Standard.lean](../../EpArch/Theorems/Cases/Standard.lean) | derived | supporting |
| [EpArch/Theorems/Cases/VacuousStandard.lean](../../EpArch/Theorems/Cases/VacuousStandard.lean) | derived | supporting |
| [EpArch/Theorems/Cases/TypeErrors.lean](../../EpArch/Theorems/Cases/TypeErrors.lean) | derived | supporting |

## `EpArch/Concrete/`

| File | Role | Route |
|---|---|---|
| [EpArch/Concrete/Types.lean](../../EpArch/Concrete/Types.lean) | witness | supporting |
| [EpArch/Concrete/Commitments.lean](../../EpArch/Concrete/Commitments.lean) | witness | supporting |
| [EpArch/Concrete/WorkingSystem.lean](../../EpArch/Concrete/WorkingSystem.lean) | witness | supporting |
| [EpArch/Concrete/DeficientSystems.lean](../../EpArch/Concrete/DeficientSystems.lean) | witness | supporting |
| [EpArch/Concrete/NonVacuity.lean](../../EpArch/Concrete/NonVacuity.lean) | witness | supporting |
| [EpArch/Concrete/Realizer.lean](../../EpArch/Concrete/Realizer.lean) | witness | supporting |
| [EpArch/Concrete/VerificationDepth.lean](../../EpArch/Concrete/VerificationDepth.lean) | witness | supporting |

## `EpArch/Agent/`

| File | Role | Route |
|---|---|---|
| [EpArch/Agent/Constraints.lean](../../EpArch/Agent/Constraints.lean) | kernel | substrate |
| [EpArch/Agent/Imposition.lean](../../EpArch/Agent/Imposition.lean) | derived | supporting |
| [EpArch/Agent/Resilience.lean](../../EpArch/Agent/Resilience.lean) | derived | supporting |
| [EpArch/Agent/Corroboration.lean](../../EpArch/Agent/Corroboration.lean) | derived | supporting |
| [EpArch/Agent/PatternExamples.lean](../../EpArch/Agent/PatternExamples.lean) | pedagogy | optional |

## `EpArch/Adversarial/`

| File | Role | Route |
|---|---|---|
| [EpArch/Adversarial/Base.lean](../../EpArch/Adversarial/Base.lean) | kernel | substrate |
| [EpArch/Adversarial/Concrete.lean](../../EpArch/Adversarial/Concrete.lean) | witness | supporting |
| [EpArch/Adversarial/Obligations.lean](../../EpArch/Adversarial/Obligations.lean) | derived | supporting |

## `EpArch/Meta/`

| File | Role | Route |
|---|---|---|
| [EpArch/Meta/Modular.lean](../../EpArch/Meta/Modular.lean) | meta | supporting |
| [EpArch/Meta/TheoremTransport.lean](../../EpArch/Meta/TheoremTransport.lean) | meta | supporting |
| [EpArch/Meta/Tier4Transport.lean](../../EpArch/Meta/Tier4Transport.lean) | meta | supporting |
| [EpArch/Meta/Reconfiguration.lean](../../EpArch/Meta/Reconfiguration.lean) | meta | supporting |
| [EpArch/Meta/Config.lean](../../EpArch/Meta/Config.lean) | meta | supporting |
| [EpArch/Meta/ClusterRegistry.lean](../../EpArch/Meta/ClusterRegistry.lean) | bookkeeping / docs-adjacent | supporting |
| [EpArch/Meta/FalsifiableNotAuthorizable.lean](../../EpArch/Meta/FalsifiableNotAuthorizable.lean) | meta | supporting |
| [EpArch/Meta/TheoryCoreClaim.lean](../../EpArch/Meta/TheoryCoreClaim.lean) | optional / stretch | optional |

## `EpArch/Meta/LeanKernel/`

The Lean-kernel worked example: a self-referential domain instantiation
showing Lean itself as an EpArch instance. Explicitly outside the core
architectural claim; this is where the project's one named axiom
(`lean_kernel_verification_path`) lives.

| File | Role | Route |
|---|---|---|
| [EpArch/Meta/LeanKernel/OdometerModel.lean](../../EpArch/Meta/LeanKernel/OdometerModel.lean) | optional / stretch | optional |
| [EpArch/Meta/LeanKernel/World.lean](../../EpArch/Meta/LeanKernel/World.lean) | optional / stretch | optional |
| [EpArch/Meta/LeanKernel/SFailure.lean](../../EpArch/Meta/LeanKernel/SFailure.lean) | optional / stretch | optional |
| [EpArch/Meta/LeanKernel/RepairLoop.lean](../../EpArch/Meta/LeanKernel/RepairLoop.lean) | optional / stretch | optional |
| [EpArch/Meta/LeanKernel/VerificationPath.lean](../../EpArch/Meta/LeanKernel/VerificationPath.lean) | optional / stretch | optional |

---

## Roll-up by role

| Label | Count |
|---|---:|
| kernel | 18 |
| derived | 23 |
| witness | 10 |
| meta | 6 |
| pedagogy | 1 |
| bookkeeping / docs-adjacent | 3 |
| optional / stretch | 6 |
| **total** | **67** |

## Roll-up by route

| Route | Count |
|---|---:|
| substrate | 13 |
| core-route | 5 |
| supporting | 42 |
| optional | 7 |
| **total** | **67** |

The five core-route files are
[WorldBridges](../../EpArch/WorldBridges.lean),
[Convergence](../../EpArch/Convergence.lean),
[Minimality](../../EpArch/Minimality.lean),
[Scenarios](../../EpArch/Scenarios.lean), and
[GroundedEvidence](../../EpArch/GroundedEvidence.lean). The headline
forcing chain runs through these; see
[PROOF-STRUCTURE.md](../PROOF-STRUCTURE.md).

---

## Notes on non-obvious classifications

- **Kernel vs derived for `Theorems/`.** Everything under
  `EpArch/Theorems/` is *derived*: each file applies the kernel substrate
  (`Bank`, `Header`, `StepSemantics`, `Minimality`) to a specific case
  family. None of these defines new substrate; all could in principle be
  cut without invalidating the headline convergence theorem.
- **Kernel vs witness for `Concrete/`.** All `Concrete/*` files are
  *witness*: their job is to discharge non-vacuity obligations for the
  commitments and the deficient-system impossibility witnesses.
- **`WorldBridges` is kernel; `WorldWitness` is witness.** WorldBridges
  carries the W_* → structural forcing direction (load-bearing for
  convergence); WorldWitness is the concrete inhabitation showing the
  bundles are jointly satisfiable.
- **`Adversarial/Base` is kernel; the other two are not.** Base provides
  the type-level vocabulary (attack primitives, attack-success predicate)
  reused by `Concrete` and `Obligations`.
- **`Mechanisms` and `Agent/Constraints` are kernel.** They are the
  interface targets of the design-imposition theorems in
  `Agent/Imposition`.
- **`Scenarios` is kernel, not bookkeeping.** It defines the eight
  `Represents*` structures and the `SystemOperationalBundle` /
  `WorldBridgeBundle` packages, which appear as typed hypotheses in the
  headline forcing theorems in `WorldBridges`. Remove `Scenarios` and
  `WorldBridges` does not build.
- **`GroundedEvidence` is kernel.** Imported directly by `Minimality`;
  its eight `GroundedXStrict` types are the fields of
  `Minimality.GroundedBehavior`, the typed-evidence interface the
  impossibility theorems consume.
- **`Meta/ClusterRegistry` is bookkeeping.** Routing/display tables for
  cluster tags; consumed by `Meta/Config` but not itself a meta-theorem.
- **`PatternExamples` is the only pure pedagogy file.** The case studies
  under `Theorems/Cases/` are *derived* rather than *pedagogy* because
  they prove typed structural theorems about each failure mode, not just
  illustrate it.
- **All `Meta/LeanKernel/*` files are optional/stretch.** This subtree
  is the self-referential worked example, explicitly flagged as outside
  the core architectural claim, and is where the project's one named
  axiom resides.

---

## Go next

- [START-HERE.md](../START-HERE.md) — recommended reading order over these files.
- [PROOF-STRUCTURE.md](../PROOF-STRUCTURE.md) — how the five core-route files compose into the headline chain.
- [AXIOMS.md](AXIOMS.md) — the trusted-base statement these files build against.
