# EpArch — Machine-Checked Epistemic Architecture

> **Work in progress.** This formalization has not undergone peer review. Proofs and documentation are subject to change.

Standalone Lean 4 framework for reasoning about bounded epistemic systems under adversarial pressure.

> **Scope note.** EpArch is a framework for determining which architectural mechanisms are *required* under recognizable constraint and goal profiles — the kinds of real-world operational regimes we actually build epistemic systems for. It is not a claim that every conceivable world or system must instantiate the same mechanisms.
>
> The forcing argument has two parts: *world bundle witnesses* (`W_*` in `WorldCtx.lean`) establish that certain pressures exist in the operating environment; *scenario bridge witnesses* (`WorldBridgeBundle` in `Scenarios.lean`) establish that those pressures constructively bind to the specific system under analysis. The bridge witnesses are not extra assumptions that narrow the claim; they are the formal witness that existential world pressures are instantiated in this system's lifecycle, verification surface, and endorsement structure. For systems genuinely operating under these conditions, this is the proof layer that shows the conditions apply here, not merely in the abstract.

[![CI](https://github.com/loumaloulongtin/EpArch/actions/workflows/ci.yml/badge.svg)](https://github.com/loumaloulongtin/EpArch/actions/workflows/ci.yml)

**0 axiom declarations in the core formalization. 0 sorries.** One named axiom (`lean_kernel_verification_path`) exists in `EpArch/Meta/LeanKernel/VerificationPath.lean` — a worked domain-instantiation example not imported in `Main.lean` and outside the core claim. See [DOCS/AXIOMS.md](DOCS/AXIOMS.md).

> **Reading guide.** Much of the theorem surface is structural bookkeeping (transport lemmas, `Has*` witnesses, definitional unfolding). For the substantive results — the impossibility proofs that show *why* alternative architectures fail — start with `StructurallyForced` in `Convergence.lean` and the impossibility witnesses in `GroundedXStrict`, not the `Has*` predicates in `Minimality.lean`.

```bash
lake build   # Lean 4.3.0, no Mathlib
```

**Start here depending on what you want:**

| I want to… | Go to |
|---|---|
| Build and run it | `lake build` above, then [What EpArch Does](#what-eparch-does) |
| Certify a system configuration | [Quick Example](#quick-example) |
| Find a specific theorem | [DOCS/THEOREMS.md](DOCS/THEOREMS.md) |
| Understand what the framework is for | [The EpArch Framework](#the-eparch-framework) |
| Extend or contribute | [DOCS/MODULARITY.md](DOCS/MODULARITY.md) |

---

## What EpArch Does

| Goal | Entry point |
|---|---|
| **Certify a system configuration** — proof-carrying record for the applicable theorem clusters | `EpArch.Meta.Config.certify myConfig` |
| **Inspect which theorems apply** — human-readable routing report per constraint/goal/world | `#eval EpArch.Meta.Config.showConfig myConfig` |
| **See why primitives are structurally forced** — constraint-to-feature necessity proofs | `EpArch/Minimality.lean`, `EpArch/Convergence.lean`, `EpArch/Agent/Imposition.lean`, `EpArch/WorldBridges.lean` (`bundled_structure_forces_bank_primitives` — world-assumption-free; `world_assumptions_force_bank_primitives` — W_* bundle path) |
| **Transport theorems through compatible extensions** — Tier 3–4 closure | `EpArch/Meta/TheoremTransport.lean`, `EpArch/Meta/Tier4Transport.lean` |
| **Extend or adapt the framework** — 30-cluster registry + contributor recipes | [`DOCS/MODULARITY.md`](DOCS/MODULARITY.md) |
| **Verify a constructive witness** — zero-axiom trace from initial state to revoked | `EpArch/Concrete/NonVacuity.lean` |
| **Localize an epistemic puzzle** (Gettier, Lottery, Fake Barn, confabulation) | `EpArch/Theorems/Cases/` — `gettier_is_V_failure` (Gettier.lean), `confabulation_is_type_error` (TypeErrors.lean); `EpArch/Theorems/Corners.lean` — `lottery_paradox_dissolved_architecturally` |

---

## Quick Example

```lean
def myConfig : EpArchConfig := {
  constraints := [.distributed_agents, .truth_pressure, .adversarial_pressure]
  goals       := [.safeWithdrawal, .corrigibleLedger]
  worlds      := [.lies_possible, .partial_observability]
}

-- Which of the 30 clusters are active for this configuration:
#eval EpArch.Meta.Config.showConfig myConfig

-- Proof-carrying record: one machine-checked witness per cluster family:
#check EpArch.Meta.Config.certify myConfig

-- Typed proof content for a specific cluster:
-- (certify myConfig).goalWitnesses .goal_safeWithdrawal   -- GoalWitness
-- (certify myConfig).tier4Witnesses .tier4_commitments    -- Tier4Witness
```

---

## The EpArch Framework

EpArch is a machine-checked framework for reasoning about bounded epistemic systems under adversarial pressure. Starting from minimal operational constraints on agents and the world, it derives a cluster of structurally forced primitives: scoped authorization zones (**Bubbles**), a shared deposit ledger (**Bank**) with lifecycle gates, structured validation headers (**S/E/V**), and temporal validity (**τ**). These are not design choices — they are machine-proved forced features. The domain scoping is what makes the results strong: declaring a constraint/goal profile is a precondition, not a limitation — within any declared profile the derivations are machine-checked necessities, not conditional recommendations.

The framework has three layers:
- **Formal architecture** — core types, lifecycle semantics, commitments, forcing results, adversarial obligations, revision safety.
- **Configurable certification surface** — `EpArchConfig` selects active constraints, goals, and world bundles; `certify` returns a `CertifiedProjection` for exactly the applicable theorem clusters.
- **Modular extension substrate** — 30-cluster registry with explicit routing, proof-carrier layers, and contributor-facing extension recipes.

---

## Exploring the Formalization

| What you want | Where to look |
|---|---|
| Core types (`Deposit`, `Bubble`, `Header`, `DepositStatus`) | `EpArch/Basic.lean`, `EpArch/Header.lean` |
| Lifecycle gate theorems (withdrawal, export, challenge) | `EpArch/Theorems/Withdrawal.lean`, `EpArch/Theorems/Corners.lean` |
| Type-separation: traction ≠ authorization | `EpArch/Theorems/Corners.lean` — `authorization_implies_traction`; `EpArch/Commitments.lean` — `innovation_allows_traction_without_authorization` |
| Gettier → V-field failure | `EpArch/Theorems/Cases/Gettier.lean` — `gettier_is_V_failure` |
| Lottery → type error (diagnosis) | `EpArch/Theorems/Cases/TypeErrors.lean` — `LotteryIsTypeError` |
| Lottery → dissolved operationally | `EpArch/Theorems/Corners.lean` — `lottery_paradox_dissolved_architecturally` |
| Header stripping has no left inverse | `EpArch/Theorems/Strip.lean` — `no_strip_left_inverse` |
| Non-vacuity witnesses (all constraints satisfiable) | `EpArch/WorldWitness.lean`, `EpArch/Concrete/` |
| Adversarial obligation theorems | `EpArch/Adversarial/Obligations.lean` |
| Revision safety (extensions can't break existing results) | `EpArch/Semantics/RevisionSafety.lean` |

**Notable derived interpretations:** The notation-invariance theorems (`notation_invariance_of_redeemability`, `math_practice_is_bubble_distinct`) show that mathematical practice is itself a bubble in the architecture's terms, with Lean's kernel as the constraint surface — and these claims are discharged by that same kernel.

---

## Core Claims Formalized

| Claim | Key Theorem | File |
|---|---|---|
| Self-correction requires revision capability | `no_revision_no_correction` | Semantics/StepSemantics.lean |
| Authorization implies traction (one direction) | `authorization_implies_traction` | Theorems/Corners.lean |
| Traction without authorization (other direction) | `innovation_allows_traction_without_authorization` | Commitments.lean |
| Header stripping has no left inverse | `no_strip_left_inverse` | Theorems/Strip.lean |
| Stripping reduces diagnosability | `strip_reduces_diagnosability` | Theorems/Diagnosability.lean |
| Lottery paradox is a type error | `lottery_paradox_dissolved_architecturally` | Theorems/Corners.lean |
| Staleness blocks withdrawal | `stale_blocks_withdrawal` | Theorems/Corners.lean |
| All world constraint bundles are satisfiable (non-vacuity) | `holds_W_lies_possible`, `holds_W_bounded_verification`, `holds_W_partial_observability` | WorldWitness.lean |
| Each W_* bundle independently forces its architectural primitive | `w_lies_forces_revocation_need`, `w_bounded_forces_incompleteness`, `w_partial_obs_forces_redeemability` | WorldBridges.lean |
| In any world satisfying all three bundles, Bank primitives are necessary | `world_assumptions_force_bank_primitives` | WorldBridges.lean |
| Bank primitives necessary — no free assumptions (W_* discharged by WitnessCtx) | `kernel_world_forces_bank_primitives` | WorldBridges.lean |
| Concrete model satisfies all commitments | `all_commitments_satisfiable` | Concrete/Commitments.lean |

---

## Module Structure

### Foundation

| Module | Purpose |
|---|---|
| `Basic.lean` | Core types: `Agent`, `Claim`, `Bubble`, `Deposit`, `DepositStatus`, `LadderStage` |
| `Header.lean` | S/E/V header structure and factorization |
| `Bank.lean` | Bank substrate, lifecycle operators, and bubble hygiene |
| `Bank/Dynamics.lean` | Runtime behavioral profiling: `DepositDynamics`, reliance/blast-radius theorems |
| `Semantics/LTS.lean` | Generic labeled transition systems |
| `Semantics/StepSemantics.lean` | Concrete step semantics for all lifecycle operators |

### World and Agent Layers

| Module | Purpose |
|---|---|
| `WorldCtx.lean` | Semantic signature for obligation theorems |
| `WorldWitness.lean` | Non-vacuity proofs: concrete worlds satisfying each bundle |
| `Agent/Constraints.lean` | Agent constraint predicates (PRP, bounded audit, fallibility) |
| `Agent/Imposition.lean` | Mechanism necessity: forcing arguments |
| `Agent/Resilience.lean` | Fault containment and trace invariants |

### Theorem Modules

| Module | Purpose |
|---|---|
| `Theorems/` | Primary theorem library — 11 focused sub-modules: `Withdrawal`, `Cases`, `Headers`, `Modal`, `Strip`, `Corners`, `Dissolutions`, `Pathologies`, `Diagnosability`, `BehavioralEquivalence`, `NotationBridge` |
| `Theorems/Diagnosability.lean` | Observability-based diagnosability ordering |
| `Adversarial/Base.lean` | Adversarial type definitions |
| `Adversarial/Obligations.lean` | Attack/defense obligation theorems under world bundles |
| `Agent/Corroboration.lean` | k-of-n corroboration guarantees and independence conditions |
| `Commitments.lean` | The 8 structural commitments; all proved as standalone theorems; `commitments_pack` bundles the unconditional ones (C3/C4b/C7b/C8) |
| `Minimality.lean` | Structural impossibility models + alternative-architecture dismissals; `Pressure` inductive as canonical dimension index |
| `Scenarios.lean` | Seven `Represents*` scenario enrichments + `SystemOperationalBundle`/`WorldBridgeBundle` packaging |
| `GroundedEvidence.lean` | `GroundedX` evidence structures; `GroundedSystemSpec`/`PartialGroundedSpec` compliance API |
| `Convergence.lean` | `StructurallyForced`, `ForcingEmbedding`, `convergence_structural`, bridge predicates; seven per-dimension `*_forces_*` theorems |
| `Concrete/VerificationDepth.lean` | Kernel-grounded verification depth: `DepthClaim` constructive witness; `bounded_verify` budget decision procedure; `DepthWorldCtx` instantiates `W_bounded_verification` by construction |
| `Theorems/BehavioralEquivalence.lean` | Observation-boundary equivalence; `working_systems_equivalent` — any two `GroundedBehavior` certificates are behaviorally equivalent (unconditional; no `SatisfiesAllProperties` premise); step-bridge section grounds withdraw/challenge/tick via `ReadyState` witnesses |
| `Feasibility.lean` | Existence/non-vacuity witnesses: `world_bundles_feasible`, `commitments_feasible`, `existence_under_constraints_structural`, `existence_under_constraints_embedding` |
| `WorldBridges.lean` | World-to-structural bridge theorems: `w_bounded_forces_incompleteness`, `w_lies_forces_revocation_need`, `w_partial_obs_forces_redeemability`; `WorldAwareSystem` def; `world_assumptions_force_bank_primitives` (W_* bundle path); `bundled_structure_forces_bank_primitives` (headline: `SystemOperationalBundle` + `WorldBridgeBundle` → `containsBankPrimitives`); `kernel_world_forces_bank_primitives` (zero-assumption corollary) |
| `Health.lean` | Health goal predicates and necessity theorems |
| `Invariants.lean` | System invariants (grounded operational theorems, 0 axiom declarations) |
| `Meta/TheoremTransport.lean` | Health-goal transport schema: all 5 health goals are transport-safe under Compatible extensions (Tier 3 closure) |
| `Meta/Tier4Transport.lean` | Main theorem library transport: standalone commitments, structural, and ConcreteBankModel clusters (Tier 4 closure) |
| `Meta/Modular.lean` | Constraint-subset modularity: `PartialWellFormed`, `modular` (∀ S ⊆ constraints, biconditional fragment → forcing projection), `allConstraints`/`noConstraints` |
| `Meta/ClusterRegistry.lean` | 30-cluster tag registry: `ClusterTag`, `EnabledXxxCluster` inductives, per-family canonical lists, `clusterEnabled` routing |
| `Meta/Config.lean` | Configurable certification engine: `CertifiedProjection`, `certify`, named proof witnesses for all 30 clusters |
| `Meta/LeanKernel/World.lean` | Lean kernel self-application — world layer (`LeanKernelCtx`, bundle witnesses, Gettier), architecture layer (`LeanWorkingSystem`, HasX proofs, convergence chain), and OleanStaleness deposit witness |
| `Meta/LeanKernel/SFailure.lean` | Lean kernel S-field failure taxonomy: `LeanAxiomLevel`, `ElabMode`, `LeanStandardCase`, `LeanVacuousStandard`, relational vs. absolute S-failure theorems |
| `Meta/LeanKernel/OdometerModel.lean` | Concrete minimal sub-bundle: single-bubble append-only system, graceful degradation witness |
| `Bank/Dynamics.lean` | Behavioral profiling: `success_driven_bypass`, `blast_radius_scales_with_reliance` |

### Safety and Scope

| Module | Purpose |
|---|---|
| `Semantics/RevisionSafety.lean` | Compatible extension preserves all existing implications |
| `Semantics/ScopeIrrelevance.lean` | Extra substrate state is irrelevant to core properties |
| `Meta/FalsifiableNotAuthorizable.lean` | Falsifiability ≠ authorizability |
| `Meta/TheoryCoreClaim.lean` | Core theory claim formalization |

### Entry Points and Witnesses

| Module | Purpose |
|---|---|
| `Main.lean` | Full build entry point |
| `EpArch/Concrete/` | Zero-axiom constructive witness (8 modules: Types, Commitments, WorkingSystem, DeficientSystems, NonVacuity, Realizer, VerificationDepth, WorkedTraces) |

---

## Axiom Declarations

The core formalization (the `Main.lean` import surface) contains **zero `axiom` declarations**. All 8 structural commitments are proved standalone theorems; `commitments_pack` bundles the unconditional ones (C3/C4b/C7b/C8). Operational invariants are grounded in `StepSemantics`. Opaque domain primitives are declared with `opaque`, not `axiom`. One named axiom (`lean_kernel_verification_path`) exists in `EpArch/Meta/LeanKernel/VerificationPath.lean` — a worked domain-instantiation example not imported in `Main.lean` and outside the core architectural claim.

> **Note:** “zero global axioms” does not mean “zero assumptions in an absolute sense.”
> EpArch works with explicit base commitments and context-bundled conditions where appropriate;
> those boundaries are made explicit rather than hidden.
> That is intentional: the framework does not claim terminal epistemic closure,
> and PRP rules out eliminating every assumption boundary altogether.
> See [DOCS/AXIOMS.md](DOCS/AXIOMS.md) and [DOCS/WORLD.md](DOCS/WORLD.md).

See [DOCS/AXIOMS.md](DOCS/AXIOMS.md) for the full account.

---

## Kernel Boundary

EpArch identifies and formalizes the **minimal mechanisms** required for heterogeneous agents to coordinate together — that is, the architectural layer every coordination participant must share regardless of its internal epistemology, cognition model, or constraint bundle. The kernel boundary follows from this goal: anything specific to one class of agent's internals is, by definition, not part of the shared coordination substrate and belongs in a downstream overlay. This includes minimal agents such as an odometer-like system that tracks position without facing the full human-style constraint bundle; such agents are first-class coordination participants, and the kernel must scale down to accommodate them without losing its guarantees. The mechanisms this kernel identifies are precisely what `Minimality.lean`'s forcing theorems derive as necessary under recognizable profiles — the boundary is not a design choice but a proof obligation.

### Out of scope for the kernel

These are not missing features. They are excluded to preserve agent-agnostic applicability:

| Concept | Reason |
|---|---|
| Full Ladder dynamics (belief update rules, graded modulation) | Requires an agent-internal belief model; including it would break agent agnosticism |
| Rich access/consultation semantics beyond the typed interface | Agent-specific; the kernel formalizes the interface surface only |
| Agent phenomenology, consciousness, or omniscience-adjacent claims | Not coordination-relevant unless they change theorem-level coordination requirements |
| Empirical implementation correspondence | Deliberately not claimed — architectural spec, not deployment protocol |

### Possible downstream extensions

| Concept | Notes |
|---|---|
| Multi-bubble conflict routing | Attachment points exist; implementable as an agent-specific overlay |
| Domain-level correlated adversaries (graded independence) | Binary independent/common-mode is formalized; graded refinement belongs to an overlay |
| Richer deposit recovery transitions | Application-layer state tracking; not a kernel requirement |

### Domain instantiation

The kernel boundary is also an **instantiation surface**. `GroundedBehavior` carries abstract type parameters — `Entry`, `Claim`, `Clause`, etc. — that a domain fills in with its own types. Any instantiation that satisfies the mechanism signatures immediately inherits `working_systems_equivalent` (proved in `Theorems/BehavioralEquivalence.lean`): any two implementations holding the certificate agree at the observation boundary, without knowing anything about each other's internals.

The kernel enforces the observation boundary contract and the mechanism signatures. It does not enforce whether a domain's design is good — that judgment belongs to the instantiator. The `let _ :=` lines in the ready-state builders are the explicit extension hooks: at the kernel layer they confirm certificate field presence only; a domain taking correctness seriously replaces them with substantive obligations over its own types. This is the upgrade path from "typechecks against EpArch's signatures" to "mechanically grounded in domain evidence," taken per domain rather than in the abstract kernel.

`Meta/LeanKernel/World.lean` (`LeanGroundedBehavior`) is the reference instantiation: the Lean type-checker itself modeled as an EpArch coordination participant.

---

## Documentation

| Document | Description |
|---|---|
| [DOCS/AXIOMS.md](DOCS/AXIOMS.md) | Full axiom inventory with categories and justifications |
| [DOCS/THEOREMS.md](DOCS/THEOREMS.md) | Theorem inventory organized by architectural role |
| [DOCS/SEMANTICS.md](DOCS/SEMANTICS.md) | Operational proxy definitions and formal interpretations |
| [DOCS/WORLD.md](DOCS/WORLD.md) | World layer: parametric semantic interface and W_* obligation theorems |
| [DOCS/TRUST-BRIDGE-DESIGN.md](DOCS/TRUST-BRIDGE-DESIGN.md) | Trust bridge design: two auth modes (byAgent/byToken), multi-hop chains, gate invariants |
| [DOCS/CORROBORATION.md](DOCS/CORROBORATION.md) | Corroboration module design notes |
| [DOCS/FEASIBILITY.md](DOCS/FEASIBILITY.md) | Feasibility witness strategy |
| [DOCS/WITNESS-SCOPE.md](DOCS/WITNESS-SCOPE.md) | What `EpArch/Concrete/` witnesses, what is proved elsewhere, and what is out of scope |
| [DOCS/MODULARITY.md](DOCS/MODULARITY.md) | Modularity tiers: what survives disabling a constraint, health goal, or world bundle, and by what mechanism |

---

## References

> Longtin, L.-M. (2026). *Epistemic Architecture: A Constraints-and-Objectives Framework for Bounded Agents Under Adversarial Pressure.* PhilArchive: <https://philarchive.org/rec/LONEAA-7>

---

## Building and Verifying

```bash
# Build (requires Lean 4.3.0, no Mathlib)
lake build

# Verify zero sorries
Select-String -Path "EpArch\*.lean", "EpArch\**\*.lean" -Pattern "^\s*sorry\b"
# Expected: no output

# Verify axiom declarations (expect 1: lean_kernel_verification_path in Meta/LeanKernel/VerificationPath.lean;
# that file is a worked domain-instantiation example outside the core claim, not imported in Main.lean)
(Select-String -Path "EpArch\*.lean", "EpArch\**\*.lean" -Pattern "^axiom\s" | Measure-Object).Count
# Expected: 1

# Verify Concrete/ modules have no axioms
Get-ChildItem -Path "EpArch\Concrete\" -Filter "*.lean" | ForEach-Object {
    Select-String -Path $_.FullName -Pattern "^axiom\s"
}
# Expected: no output
```
