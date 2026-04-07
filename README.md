# Epistemic Architecture — Lean Formalization

Machine-checked companion to **"Epistemic Architecture: A Constraints-and-Objectives Framework for Bounded Agents Under Adversarial Pressure"**

[![CI](https://github.com/loumaloulongtin/EpArch/actions/workflows/ci.yml/badge.svg)](https://github.com/loumaloulongtin/EpArch/actions/workflows/ci.yml)

> **Paper:** Longtin, L.-M. (2026). *Epistemic Architecture: A Constraints-and-Objectives Framework for Bounded Agents Under Adversarial Pressure.* PhilArchive: <https://philarchive.org/rec/LONEAA-7>

---

## Where to Start

| If you are... | Start here |
|---|---|
| A **Lean / formal methods reader** | [Quick Start for Lean Readers](#quick-start-for-lean-readers) below — core types, theorem names, direct file links |
| A **philosopher or epistemologist** | `EpArch/Theorems.lean` — `gettier_is_V_failure`, `fake_barn_is_E_failure`, `LotteryIsTypeError`; `EpArch/Header.lean` — `observational_completeness_full` for the no-hidden-degrees-of-freedom result; then [Relationship to the Paper](#relationship-to-the-paper) for the combined completeness argument |
| An **AI safety / LLM evaluation reader** | `EpArch/Theorems.lean` — `confabulation_is_type_error` (hallucination is the lottery problem instantiated in generative systems: high fluency-traction, no Bank grounding); `EpArch/AdversarialObligations.lean` for V-spoof and trust-bridge obligations |
| Interested in **why these primitives are forced** | `EpArch/Agent/Imposition.lean` (mechanism necessity proofs), `EpArch/Minimality.lean` (forcing results), `EpArch/WorldWitness.lean` (non-vacuity witnesses) |
| A **skeptic** wanting non-vacuity first | `EpArch/ConcreteLedgerModel.lean` — zero axioms, fully constructive trace from initial state to revoked |

---

## What This Is

This repository contains the Lean 4 formalization of EpArch — a constraints-and-objectives architecture for bounded epistemic agents under adversarial pressure. Starting from minimal operational constraints on agents and the world, the paper derives a cluster of required primitives: scoped authorization zones (Bubbles), a shared deposit ledger (Bank) with lifecycle gates, structured validation headers (S/E/V), and temporal validity (τ). This formalization machine-checks the key conditional necessity results, provides non-vacuity witnesses, and verifies revision safety.

**505 theorems. 0 axiom declarations. 0 sorries.**

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
| `Commitments.lean` | The paper's 8 structural commitments; 4 structural ones bundled in `CommitmentsCtx` |
| `Minimality.lean` | Minimality and forcing results |
| `Feasibility.lean` | Feasibility witnesses |
| `Health.lean` | Health goal predicates and necessity theorems |
| `Invariants.lean` | System invariants (grounded operational theorems, 0 axiom declarations) |
| `Modularity.lean` | Lattice-stability: graceful scale-down and sub-level RevisionSafety (9 theorems) |
| `Meta/TheoremTransport.lean` | Health-goal transport schema: all 5 health goals are transport-safe under Compatible extensions (Tier 3 closure) |
| `Meta/Tier4Transport.lean` | Main theorem library transport: CommitmentsCtx, structural, and ConcreteBankModel clusters (Tier 4 closure) |

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

The formalization contains **zero `axiom` declarations**. The four structural
commitments are bundled in `CommitmentsCtx` (a hypothesis structure); forward theorems
are conditioned on `(C : CommitmentsCtx ...)`. Operational invariants are grounded in
`StepSemantics`. Opaque domain primitives are declared with `opaque`,
not `axiom`.

> **Note:** “zero global axioms” does not mean “zero assumptions in an absolute sense.”
> EpArch works with explicit base commitments and context-bundled conditions where appropriate;
> those boundaries are made explicit rather than hidden.
> That is intentional: the framework does not claim terminal epistemic closure,
> and PRP rules out eliminating every assumption boundary altogether.
> See [DOCS/AXIOMS.md](DOCS/AXIOMS.md) and [DOCS/WORLD.md](DOCS/WORLD.md).

See [DOCS/AXIOMS.md](DOCS/AXIOMS.md) for the full account.

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
| [DOCS/WORLD.md](DOCS/WORLD.md) | World layer: parametric semantic interface and W_* obligation theorems |
| [DOCS/CORROBORATION.md](DOCS/CORROBORATION.md) | Corroboration module design notes |
| [DOCS/FEASIBILITY.md](DOCS/FEASIBILITY.md) | Feasibility witness strategy |
| [DOCS/WITNESS-SCOPE.md](DOCS/WITNESS-SCOPE.md) | What ConcreteLedgerModel.lean witnesses, what is proved elsewhere, and what is out of scope |

---

## Relationship to the Paper

The formalization serves three purposes:

1. **Consistency** — the architecture is non-vacuously satisfiable (zero sorries, concrete witnesses)
2. **Conditional necessity** — rival architectures must address specific theorem-level challenges to compete
3. **Operational grounding** — abstract paper commitments have concrete LTS semantics that can be inspected

Together these three results support a stronger combined claim. The type definitions function as completeness claims: two deposits agreeing on all named fields (P, S, E, V, τ, ACL, redeemability, bubble, status) are provably identical — there are no hidden degrees of freedom (`observational_completeness_full` in `EpArch/Header.lean`). Combined with the revision safety results (`RevisionSafety.lean`), this means: any proposed extension either refines an existing field (compatible, safe) or is operationally inert (does not affect any transition). The only productive attack surface is the constraint *enumeration* — finding a new constraint that forces a primitive none of the existing fields can express. The burden of proof lies with the proposer, who must produce a Lean formalization where the new constraint provably forces the new primitive.

This is an architectural specification that makes the paper's claims checkable, not a full mechanization of epistemology.

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
