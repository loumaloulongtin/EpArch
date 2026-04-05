# Epistemic Architecture — Lean Formalization

Machine-checked companion to **"Epistemic Architecture: A Constraints-and-Objectives Framework for Bounded Agents Under Adversarial Pressure"**

[![CI](https://github.com/loumaloulongtin/EpArch/actions/workflows/ci.yml/badge.svg)](https://github.com/loumaloulongtin/EpArch/actions/workflows/ci.yml)

> **Paper:** Longtin, L.-M. (2026). *Epistemic Architecture: A Constraints-and-Objectives Framework for Bounded Agents Under Adversarial Pressure.* Pre-print forthcoming.

---

## What This Is

This repository contains the Lean 4 formalization of EpArch — a constraints-and-objectives architecture for bounded epistemic agents under adversarial pressure. Starting from minimal operational constraints on agents and the world, the paper derives a cluster of required primitives: scoped authorization zones (Bubbles), a shared deposit ledger (Bank) with lifecycle gates, structured validation headers (S/E/V), and temporal validity (τ). This formalization machine-checks the key conditional necessity results, provides non-vacuity witnesses, and verifies revision safety.

**435 theorems. 35 axioms. 0 sorries.**

```bash
lake build   # requires Lean 4.3.0, no Mathlib
```

---

## Quick Start for Lean Readers

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

**A notable result:** The notation-invariance theorems (`notation_invariance_of_redeemability`, `math_practice_is_bubble_distinct`) show that mathematical practice is itself a bubble in the architecture's terms, with Lean's kernel as the constraint surface — and these claims are discharged by that same kernel.

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
| `Bank.lean` | Bank substrate and lifecycle operators (18 axioms — API contracts) |
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
| `Commitments.lean` | The paper's 8 structural commitments (12 axioms — definitional) |
| `Minimality.lean` | Minimality and forcing results |
| `Feasibility.lean` | Feasibility witnesses |
| `Health.lean` | Health goal predicates and necessity theorems |
| `Invariants.lean` | System invariants (5 axioms — protocol requirements) |

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

## Axiom Inventory

The formalization uses 35 axioms, all design-constraint declarations:

| Category | Count | Role |
|---|---|---|
| Bank operators | 18 | System API contracts — specify what operators do, not how |
| Commitments | 12 | The paper's 8 structural forcing constraints (some split into components) |
| Invariants | 5 | Protocol requirements — properties that must hold across all states |

`ConcreteLedgerModel.lean` contains **zero axioms** — all witnesses are fully constructive.

See [DOCS/AXIOMS.md](DOCS/AXIOMS.md) for the complete inventory with justifications.

---

## What Is Not Formalized

Some paper concepts are explicitly out of scope for this formalization:

| Concept | Reason |
|---|---|
| Full Ladder dynamics (belief update rules) | Requires an agent belief model beyond the scope of this spec |
| Multi-bubble conflict routing | High formal cost; attachment points exist for future extension |
| Domain-level correlated adversaries (graded independence) | Current model handles binary independent/common-mode; graded spectrum is future work |
| Empirical implementation correspondence | Deliberately not claimed — architectural spec, not deployment protocol |

---

## Documentation

| Document | Description |
|---|---|
| [DOCS/AXIOMS.md](DOCS/AXIOMS.md) | Full axiom inventory with categories and justifications |
| [DOCS/THEOREMS.md](DOCS/THEOREMS.md) | Theorem inventory organized by paper role |
| [DOCS/SEMANTICS.md](DOCS/SEMANTICS.md) | Operational proxy definitions and their paper counterparts |
| [DOCS/WORLD.md](DOCS/WORLD.md) | World-bundle structure and satisfiability |
| [DOCS/CORROBORATION.md](DOCS/CORROBORATION.md) | Corroboration module design notes |
| [DOCS/FEASIBILITY.md](DOCS/FEASIBILITY.md) | Feasibility witness strategy |
| [DOCS/WITNESS-SCOPE.md](DOCS/WITNESS-SCOPE.md) | Scope of non-vacuity witnesses |

---

## Relationship to the Paper

The formalization serves three purposes:

1. **Consistency** — the architecture is non-vacuously satisfiable (zero sorries, concrete witnesses)
2. **Conditional necessity** — rival architectures must address specific theorem-level challenges to compete
3. **Operational grounding** — abstract paper commitments have concrete LTS semantics that can be inspected

Together these three results support a stronger combined claim: the architecture is **mandatory up to compatible extension and notation-preserving redescription**. You can add extra state (`ScopeIrrelevance`), safely extend the system (`RevisionSafety`), or change the vocabulary (`notation_invariance_of_redeemability`) — but if the extension is genuinely compatible, the core structure is preserved. If you change the core semantics, you have a different system, not a harmless rewording.

This is an architectural specification that makes the paper's claims checkable, not a full mechanization of epistemology.

---

## Building and Verifying

```bash
# Build (requires Lean 4.3.0, no Mathlib)
lake build

# Verify zero sorries
Select-String -Path "EpArch\*.lean", "EpArch\**\*.lean" -Pattern "^\s*sorry\b"
# Expected: no output

# Verify axiom count
(Select-String -Path "EpArch\*.lean", "EpArch\**\*.lean" -Pattern "^axiom\s" | Measure-Object).Count
# Expected: 35

# Verify ConcreteLedgerModel has no axioms
Select-String -Path "EpArch\ConcreteLedgerModel.lean" -Pattern "^axiom\s"
# Expected: no output
```
