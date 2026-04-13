# EpArch — Machine-Checked Epistemic Architecture

Standalone Lean 4 framework for reasoning about bounded epistemic systems under adversarial pressure.

> **Scope note.** EpArch is a framework for determining which architectural mechanisms are *required* under recognizable constraint and goal profiles — the kinds of real-world operational regimes we actually build epistemic systems for. It is not a claim that every conceivable world or system must instantiate the same mechanisms.

[![CI](https://github.com/loumaloulongtin/EpArch/actions/workflows/ci.yml/badge.svg)](https://github.com/loumaloulongtin/EpArch/actions/workflows/ci.yml)

**0 axiom declarations. 0 sorries.**

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
| **See why primitives are structurally forced** — constraint-to-feature necessity proofs | `EpArch/Minimality.lean`, `EpArch/Convergence.lean`, `EpArch/Agent/Imposition.lean`, `EpArch/Feasibility.lean` (`bundled_structure_forces_bank_primitives` — world-assumption-free; `world_assumptions_force_bank_primitives` — W_* bundle path) |
| **Transport theorems through compatible extensions** — Tier 3–4 closure | `EpArch/Meta/TheoremTransport.lean`, `EpArch/Meta/Tier4Transport.lean` |
| **Extend or adapt the framework** — 29-cluster registry + contributor recipes | [`DOCS/MODULARITY.md`](DOCS/MODULARITY.md) |
| **Verify a constructive witness** — zero-axiom trace from initial state to revoked | `EpArch/ConcreteLedgerModel.lean` |
| **Localize an epistemic puzzle** (Gettier, Lottery, Fake Barn, confabulation) | `EpArch/Theorems/Cases.lean` — `gettier_is_V_failure`, `confabulation_is_type_error`; `EpArch/Theorems/Corners.lean` — `lottery_paradox_dissolved_architecturally` |

---

## Quick Example

```lean
def myConfig : EpArchConfig := {
  constraints := [.distributed_agents, .truth_pressure, .adversarial_pressure]
  goals       := [.safeWithdrawal, .corrigibleLedger]
  worlds      := [.lies_possible, .partial_observability]
}

-- Which of the 29 clusters are active for this configuration:
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
- **Modular extension substrate** — 29-cluster registry with explicit routing, proof-carrier layers, and contributor-facing extension recipes.

---

## Exploring the Formalization

| What you want | Where to look |
|---|---|
| Core types (`Deposit`, `Bubble`, `Header`, `DepositStatus`) | `EpArch/Basic.lean`, `EpArch/Header.lean` |
| Lifecycle gate theorems (withdrawal, export, challenge) | `EpArch/Theorems/Withdrawal.lean`, `EpArch/Theorems/Corners.lean` |
| Type-separation: traction ≠ authorization | `EpArch/Theorems/Corners.lean` — `traction_broader_than_authorization` |
| Gettier → V-field failure | `EpArch/Theorems/Cases.lean` — `gettier_is_V_failure` |
| Lottery → type error | `EpArch/Theorems/Corners.lean` — `lottery_paradox_dissolved_architecturally` |
| Header stripping has no left inverse | `EpArch/Theorems/Strip.lean` — `no_strip_left_inverse` |
| Non-vacuity witnesses (all constraints satisfiable) | `EpArch/WorldWitness.lean`, `EpArch/ConcreteLedgerModel.lean` |
| Adversarial obligation theorems | `EpArch/AdversarialObligations.lean` |
| Revision safety (extensions can't break existing results) | `EpArch/RevisionSafety.lean` |

**Notable derived interpretations:** The notation-invariance theorems (`notation_invariance_of_redeemability`, `math_practice_is_bubble_distinct`) show that mathematical practice is itself a bubble in the architecture's terms, with Lean's kernel as the constraint surface — and these claims are discharged by that same kernel.

---

## Core Claims Formalized

| Claim | Key Theorem | File |
|---|---|---|
| Self-correction requires revision capability | `no_revision_no_correction` | StepSemantics.lean |
| Traction is broader than authorization | `traction_broader_than_authorization` | Theorems/Corners.lean |
| Header stripping has no left inverse | `no_strip_left_inverse` | Theorems/Strip.lean |
| Stripping reduces diagnosability | `strip_reduces_diagnosability` | Diagnosability.lean |
| Lottery paradox is a type error | `lottery_paradox_dissolved_architecturally` | Theorems/Corners.lean |
| Staleness blocks withdrawal | `stale_blocks_withdrawal` | Theorems/Corners.lean |
| All world constraint bundles are satisfiable (non-vacuity) | `holds_W_lies_possible`, `holds_W_bounded_verification`, `holds_W_partial_observability` | WorldWitness.lean |
| Each W_* bundle independently forces its architectural primitive | `w_lies_forces_revocation_need`, `w_bounded_forces_incompleteness`, `w_partial_obs_forces_redeemability` | Feasibility.lean |
| In any world satisfying all three bundles, Bank primitives are necessary | `world_assumptions_force_bank_primitives` | Feasibility.lean |
| Bank primitives necessary — no free assumptions (W_* discharged by WitnessCtx) | `kernel_world_forces_bank_primitives` | Feasibility.lean |
| Concrete model satisfies all commitments | `all_commitments_satisfiable` | ConcreteLedgerModel.lean |

---

## Module Structure

### Foundation

| Module | Purpose |
|---|---|
| `Basic.lean` | Core types: `Agent`, `Claim`, `Bubble`, `Deposit`, `DepositStatus`, `LadderStage` |
| `Header.lean` | S/E/V header structure and factorization |
| `Bank.lean` | Bank substrate and lifecycle operators |
| `LTS.lean` | Generic labeled transition systems |
| `StepSemantics.lean` | Concrete step semantics for all lifecycle operators |

### World and Agent Layers

| Module | Purpose |
|---|---|
| `World.lean` | World-bundle predicates (`W_lies_possible`, etc.) |
| `WorldCtx.lean` | Semantic signature for obligation theorems |
| `WorldWitness.lean` | Non-vacuity proofs: concrete worlds satisfying each bundle |
| `Agent/Constraints.lean` | Agent constraint predicates (PRP, bounded audit, fallibility) |
| `Agent/Imposition.lean` | Mechanism necessity: forcing arguments |
| `Agent/Resilience.lean` | Fault containment and trace invariants |

### Theorem Modules

| Module | Purpose |
|---|---|
| `Theorems/` | Primary theorem library — 8 focused sub-modules: `Withdrawal`, `Cases`, `Headers`, `Modal`, `Strip`, `Corners`, `Dissolutions`, `Pathologies` |
| `Diagnosability.lean` | Observability-based diagnosability ordering |
| `AdversarialBase.lean` | Adversarial type definitions |
| `AdversarialObligations.lean` | Attack/defense obligation theorems under world bundles |
| `Agent/Corroboration.lean` | k-of-n corroboration guarantees and independence conditions |
| `Commitments.lean` | The 8 structural commitments; all proved as standalone theorems; `commitments_pack` bundles the unconditional ones (C3/C4b/C7b/C8) |
| `Minimality.lean` | Structural impossibility models + alternative-architecture dismissals; `Pressure` inductive as canonical dimension index |
| `Convergence.lean` | `StructurallyForced`, `ForcingEmbedding`, `convergence_structural`, bridge predicates; six per-dimension `*_forces_*` theorems; `SystemOperationalBundle`, `WorldBridgeBundle` |
| `VerificationDepth.lean` | Kernel-grounded verification depth: `DepthClaim` constructive witness; `bounded_verify` budget decision procedure; `DepthWorldCtx` instantiates `W_bounded_verification` by construction |
| `BehavioralEquivalence.lean` | Observation-boundary equivalence; `working_systems_equivalent` — any two `GroundedBehavior` certificates are behaviorally equivalent (unconditional; no `SatisfiesAllProperties` premise); step-bridge section grounds withdraw/challenge/tick via `ReadyState` witnesses |
| `Feasibility.lean` | Feasibility witnesses; structural and world-to-structural bridge theorems; `bundled_structure_forces_bank_primitives` (headline: `SystemOperationalBundle` + `WorldBridgeBundle` → `containsBankPrimitives`); `world_assumptions_force_bank_primitives` (W_* bundle path); `kernel_world_forces_bank_primitives` (zero-assumption corollary) |
| `Health.lean` | Health goal predicates and necessity theorems |
| `Invariants.lean` | System invariants (grounded operational theorems, 0 axiom declarations) |
| `Modularity.lean` | Lattice-stability: graceful scale-down and sub-level RevisionSafety (9 theorems) |
| `Meta/TheoremTransport.lean` | Health-goal transport schema: all 5 health goals are transport-safe under Compatible extensions (Tier 3 closure) |
| `Meta/Tier4Transport.lean` | Main theorem library transport: standalone commitments, structural, and ConcreteBankModel clusters (Tier 4 closure) |
| `Meta/Modular.lean` | Constraint-subset modularity: `PartialWellFormed`, `modular` (∀ S ⊆ constraints, biconditional fragment → forcing projection), `allConstraints`/`noConstraints` |
| `Meta/ClusterRegistry.lean` | 29-cluster tag registry: `ClusterTag`, `EnabledXxxCluster` inductives, per-family canonical lists, `clusterEnabled`/`clusterDescription` routing |
| `Meta/Config.lean` | Configurable certification engine: `CertifiedProjection`, `certify`, named proof witnesses for all 29 clusters |
| `Meta/LeanKernelModel.lean` | Lean kernel self-application: `LeanKernelCtx` (world layer), `LeanWorkingSystem` (architecture layer), 30 theorems proving the Lean kernel is EpArch-compliant; the convergence chain closes with `lean_structural_convergence` (direct route: `lean_implements_bank_primitives`) |

### Safety and Scope

| Module | Purpose |
|---|---|
| `RevisionSafety.lean` | Compatible extension preserves all existing implications |
| `ScopeIrrelevance.lean` | Extra substrate state is irrelevant to core properties |
| `Meta/FalsifiableNotAuthorizable.lean` | Falsifiability ≠ authorizability |
| `Meta/TheoryCoreClaim.lean` | Core theory claim formalization |

### Entry Points and Witnesses

| Module | Purpose |
|---|---|
| `Main.lean` | Full build entry point |
| `ConcreteLedgerModel.lean` | Zero-axiom constructive witness: explicit trace from initial state to revoked |

---

## Axiom Declarations

The formalization contains **zero `axiom` declarations**. All 8 structural commitments are proved standalone theorems; `commitments_pack` bundles the unconditional ones (C3/C4b/C7b/C8). Operational invariants are grounded in `StepSemantics`. Opaque domain primitives are declared with `opaque`, not `axiom`.

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

---

## Documentation

| Document | Description |
|---|---|
| [DOCS/AXIOMS.md](DOCS/AXIOMS.md) | Full axiom inventory with categories and justifications |
| [DOCS/THEOREMS.md](DOCS/THEOREMS.md) | Theorem inventory organized by architectural role |
| [DOCS/SEMANTICS.md](DOCS/SEMANTICS.md) | Operational proxy definitions and formal interpretations |
| [DOCS/WORLD.md](DOCS/WORLD.md) | World layer: parametric semantic interface and W_* obligation theorems |
| [DOCS/CORROBORATION.md](DOCS/CORROBORATION.md) | Corroboration module design notes |
| [DOCS/FEASIBILITY.md](DOCS/FEASIBILITY.md) | Feasibility witness strategy |
| [DOCS/WITNESS-SCOPE.md](DOCS/WITNESS-SCOPE.md) | What ConcreteLedgerModel.lean witnesses, what is proved elsewhere, and what is out of scope |
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

# Verify axiom declarations (expect 0)
(Select-String -Path "EpArch\*.lean", "EpArch\**\*.lean" -Pattern "^axiom\s" | Measure-Object).Count
# Expected: 0

# Verify ConcreteLedgerModel has no axioms
Select-String -Path "EpArch\ConcreteLedgerModel.lean" -Pattern "^axiom\s"
# Expected: no output
```
