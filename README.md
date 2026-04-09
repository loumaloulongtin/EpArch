# EpArch — Machine-Checked Epistemic Architecture

Standalone Lean 4 framework for reasoning about bounded epistemic systems under adversarial pressure.

> **Scope note.** EpArch is a framework for determining which architectural mechanisms are *required* under recognizable constraint and goal profiles — the kinds of real-world operational regimes we actually build epistemic systems for. It is not a claim that every conceivable world or system must instantiate the same mechanisms.

[![CI](https://github.com/loumaloulongtin/EpArch/actions/workflows/ci.yml/badge.svg)](https://github.com/loumaloulongtin/EpArch/actions/workflows/ci.yml)

**539 theorems. 0 axiom declarations. 0 sorries.**

```bash
lake build   # Lean 4.3.0, no Mathlib
```

---

## What EpArch Does

| Goal | Entry point |
|---|---|
| **Certify a system configuration** — proof-carrying record for the applicable theorem clusters | `EpArch.Meta.Config.certify myConfig` |
| **Inspect which theorems apply** — human-readable routing report per constraint/goal/world | `#eval EpArch.Meta.Config.showConfig myConfig` |
| **See why primitives are structurally forced** — constraint-to-feature necessity proofs | `EpArch/Minimality.lean`, `EpArch/Agent/Imposition.lean` |
| **Transport theorems through compatible extensions** — Tier 3–4 closure | `EpArch/Meta/TheoremTransport.lean`, `EpArch/Meta/Tier4Transport.lean` |
| **Extend or adapt the framework** — 30-cluster registry + contributor recipes | [`DOCS/MODULARITY.md`](DOCS/MODULARITY.md) |
| **Verify a constructive witness** — zero-axiom trace from initial state to revoked | `EpArch/ConcreteLedgerModel.lean` |
| **Localize an epistemic puzzle** (Gettier, Lottery, Fake Barn, confabulation) | `EpArch/Theorems.lean` — `gettier_is_V_failure`, `lottery_paradox_dissolved_architecturally`, `confabulation_is_type_error` |

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
| Lifecycle gate theorems (withdrawal, export, challenge) | `EpArch/Theorems.lean` |
| Type-separation: traction ≠ authorization | `EpArch/Theorems.lean` — `traction_broader_than_authorization` |
| Gettier → V-field failure | `EpArch/Theorems.lean` — `gettier_is_V_failure` |
| Lottery → type error | `EpArch/Theorems.lean` — `lottery_paradox_dissolved_architecturally` |
| Header stripping has no left inverse | `EpArch/Theorems.lean` — `no_strip_left_inverse` |
| Non-vacuity witnesses (all constraints satisfiable) | `EpArch/WorldWitness.lean`, `EpArch/ConcreteLedgerModel.lean` |
| Adversarial obligation theorems | `EpArch/AdversarialObligations.lean` |
| Revision safety (extensions can't break existing results) | `EpArch/RevisionSafety.lean` |

**Notable derived interpretations:** The notation-invariance theorems (`notation_invariance_of_redeemability`, `math_practice_is_bubble_distinct`) show that mathematical practice is itself a bubble in the architecture's terms, with Lean's kernel as the constraint surface — and these claims are discharged by that same kernel.

---

## Core Claims Formalized

| Claim | Key Theorem | File |
|---|---|---|
| Self-correction requires revision capability | `no_revision_no_correction` | StepSemantics.lean |
| Traction is broader than authorization | `traction_broader_than_authorization` | Theorems.lean |
| Header stripping has no left inverse | `no_strip_left_inverse` | Theorems.lean |
| Stripping reduces diagnosability | `strip_reduces_diagnosability` | Diagnosability.lean |
| Lottery paradox is a type error | `lottery_paradox_dissolved_architecturally` | Theorems.lean |
| Staleness blocks withdrawal | `stale_blocks_withdrawal` | Theorems.lean |
| All world constraints are simultaneously satisfiable | `W_lies_possible`, `W_bounded_verification`, `W_partial_observability` | WorldWitness.lean |
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
| `Theorems.lean` | Main theorem library (109 theorems) — lifecycle gates, case bindings, epistemic puzzle localizations |
| `Diagnosability.lean` | Observability-based diagnosability ordering |
| `AdversarialBase.lean` | Adversarial type definitions |
| `AdversarialObligations.lean` | Attack/defense obligation theorems under world bundles |
| `Agent/Corroboration.lean` | k-of-n corroboration guarantees and independence conditions |
| `Commitments.lean` | The paper's 8 structural commitments; all proved as standalone theorems; `commitments_pack` bundles the unconditional ones (C3/C4b/C7b/C8) |
| `Minimality.lean` | Minimality and forcing results |
| `Feasibility.lean` | Feasibility witnesses |
| `Health.lean` | Health goal predicates and necessity theorems |
| `Invariants.lean` | System invariants (grounded operational theorems, 0 axiom declarations) |
| `Modularity.lean` | Lattice-stability: graceful scale-down and sub-level RevisionSafety (9 theorems) |
| `Meta/TheoremTransport.lean` | Health-goal transport schema: all 5 health goals are transport-safe under Compatible extensions (Tier 3 closure) |
| `Meta/Tier4Transport.lean` | Main theorem library transport: standalone commitments, structural, and ConcreteBankModel clusters (Tier 4 closure) |
| `Meta/Modular.lean` | Constraint-subset modularity: `PartialWellFormed`, `modular` (∀ S ⊆ constraints, WellFormed-fragment → forcing results), `wellformed_is_modular` |
| `Meta/ClusterRegistry.lean` | 30-cluster tag registry: `ClusterTag`, `EnabledXxxCluster` inductives, per-family canonical lists, `clusterEnabled`/`clusterDescription` routing |
| `Meta/Config.lean` | Configurable certification engine: `CertifiedProjection`, `certify`, named proof witnesses for all 30 clusters |

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
| `MainPaper.lean` | Paper-facing entry point — imports only paper-cited theorems |
| `Main.lean` | Full build entry point |
| `PaperFacing.lean` | Re-exports of canonical paper-facing theorems |
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

EpArch identifies and formalizes the **minimal mechanisms** required for heterogeneous agents to coordinate together — that is, the architectural layer every coordination participant must share regardless of its internal epistemology, cognition model, or constraint bundle. The kernel boundary follows from this goal: anything specific to one class of agent's internals is, by definition, not part of the shared coordination substrate and belongs in a downstream overlay. This includes minimal agents such as an odometer-like system that tracks position without facing the full human-style constraint bundle; such agents are first-class coordination participants, and the kernel must scale down to accommodate them without losing its guarantees.

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
| [DOCS/THEOREMS.md](DOCS/THEOREMS.md) | Theorem inventory organized by paper role |
| [DOCS/SEMANTICS.md](DOCS/SEMANTICS.md) | Operational proxy definitions and their paper counterparts |
| [DOCS/WORLD.md](DOCS/WORLD.md) | World layer: parametric semantic interface and W_* obligation theorems |
| [DOCS/CORROBORATION.md](DOCS/CORROBORATION.md) | Corroboration module design notes |
| [DOCS/FEASIBILITY.md](DOCS/FEASIBILITY.md) | Feasibility witness strategy |
| [DOCS/WITNESS-SCOPE.md](DOCS/WITNESS-SCOPE.md) | What ConcreteLedgerModel.lean witnesses, what is proved elsewhere, and what is out of scope |
| [DOCS/MODULARITY.md](DOCS/MODULARITY.md) | Modularity tiers: what survives disabling a constraint, health goal, or world bundle, and by what mechanism |
| [DOCS/PAPER-MAP.md](DOCS/PAPER-MAP.md) | Paper-section–to–Lean-artifact mapping with tier labels, file:line references, and certification-engine inventory |

---

## Relationship to the Paper

> Longtin, L.-M. (2026). *Epistemic Architecture: A Constraints-and-Objectives Framework for Bounded Agents Under Adversarial Pressure.* PhilArchive: <https://philarchive.org/rec/LONEAA-7>

The paper gives the narrative motivation, the philosophical argument, and the design rationale.
This repo is the standalone executable artifact: the paper's claims are machine-checked here, not just asserted.

Three specific functions:

1. **Consistency** — the architecture is non-vacuously satisfiable (zero sorries, concrete witnesses)
2. **Conditional necessity** — rival architectures must address specific theorem-level challenges to compete
3. **Operational grounding** — abstract paper commitments have concrete LTS semantics that can be inspected

The type definitions function as completeness claims: two deposits agreeing on all named fields (P, S, E, V, τ, ACL, redeemability, bubble, status) are provably identical — there are no hidden degrees of freedom (`observational_completeness_full` in `EpArch/Header.lean`). Combined with the revision safety results (`RevisionSafety.lean`), any proposed extension either refines an existing field (compatible, safe) or is operationally inert. The only productive attack surface is the constraint enumeration: finding a new constraint that forces a primitive none of the existing fields can express. The burden of proof lies with the proposer, who must produce a Lean formalization where the new constraint provably forces the new primitive.

The repo stands without reading the paper first. [`DOCS/PAPER-MAP.md`](DOCS/PAPER-MAP.md) maps paper sections to Lean artifacts for readers working in the other direction.

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
