# Axiom Inventory

This document is the single authoritative list of intentionally postulated design and interface axioms in the formalization. Total: **35 axioms** across three files.

---

## How to Read This File

These are not gaps or failures of the formalization. They are **intentionally postulated** at the specification and interface level.

The three axiom classes each have a different conceptual role:

- **Bank operators** are API postcondition contracts — they say what each operation produces, not how it works internally.
- **Commitments** are the paper's architectural requirements — the design decisions being formalized.
- **Invariants** are protocol constraints that must hold across all system states.

The repo's theorem burden is to derive consequences from these axioms and minimize them where possible. When an axiom becomes definitional or derivable, it is removed from this inventory.

---

## Bank Operators — 18 axioms

**File:** `EpArch/Bank.lean`

These are operator postcondition contracts. They specify what each Bank operation produces — the required outcome of each action. They are not implementation details; they are the interface the rest of the formalization reasons against.

| Axiom | Statement |
|-------|-----------|
| `KnowledgeIffDeposited` | Knowledge ↔ deposit relation |
| `repair` | Repair action specification |
| `Validate_B` | Validation produces a validated deposit |
| `Accept_B` | Acceptance produces a deposited deposit |
| `Challenge_B` | Challenge produces a quarantined deposit |
| `Repair_B` | Repair produces a repaired deposit |
| `Revoke_B` | Revoke produces a revoked deposit |
| `Restore_B` | Restore produces a restored deposit |
| `Export_B_C` | Export produces an export record |
| `Import_C` | Import produces an imported deposit |
| `validate_produces_validated` | Validate → Validated status |
| `accept_produces_deposited` | Accept → Deposited status |
| `challenge_produces_quarantined` | Challenge → Quarantined status |
| `revoke_produces_revoked` | Revoke → Revoked status |
| `τ_refresh` | τ refresh updates timestamp |
| `deprecate` | Deprecate marks deposit stale |
| `success_driven_bypass` | Success-driven verification bypass |
| `blast_radius_scales_with_reliance` | Blast radius scales with reliance |

---

## Commitments — 12 axioms

**File:** `EpArch/Commitments.lean`

These are the paper's architectural commitments — the design requirements being formally stated. They encode the structural choices that distinguish this architecture from alternatives. They are postulated because the repo is specifying a system class, not deriving it from first principles.

| Axiom | Commitment |
|-------|------------|
| `TractionAuthorizationSplit` | C1: Type separation — certainty_L ⊥ knowledge_B |
| `NoGlobalLedgerTradeoff` | C2: No global ledger |
| `redeemable_implies_path` | C3: Redeemability → path |
| `RedeemabilityExternal` | C4: Redeemability is external |
| `by_consensus_creates_redeemability` | C4a: Consensus pattern |
| `ConsensusNotSufficient` | C4b: Consensus ≠ redeemability |
| `reliable_implies_export` | C5: Reliable → exportable |
| `reliable_unreliable_exclusive` | C5b: Exclusivity |
| `RepairLoopExists` | C6: Repair loop exists |
| `NoSelfCorrectionWithoutRevision` | C6b: Self-correction → revision |
| `HeaderPreservationAsymmetry` | C7: Strip is asymmetric |
| `TemporalValidity` | C8: τ creates pressure |

---

## Invariants — 5 axioms

**File:** `EpArch/Invariants.lean`

These are protocol-level constraints. They do not describe what operations do — they constrain what system states are permissible. They must hold across all reachable states.

| Axiom | Statement |
|-------|-----------|
| `no_deposit_without_redeemability` | All deposits have redeemability |
| `no_withdrawal_without_acl` | Withdrawal requires ACL |
| `no_export_without_gate` | Export requires gate |
| `deposit_kind` | Deposits have kinds |
| `worldstate_requires_finite_τ` | World state has finite τ |

---

## Axiom-Free Modules

These modules are theorem-bearing or definitional surfaces only; they introduce no new axioms. All results in them are derived from the 35 axioms above.

| Module | Description |
|--------|-------------|
| `Basic.lean` | Core types (Bubble, Agent, Claim, etc.) |
| `Header.lean` | S/E/V header structure |
| `Health.lean` | Health goal definitions and necessity theorems |
| `StepSemantics.lean` | LTS operational semantics |
| `Theorems.lean` | Derived theorems |
| `Diagnosability.lean` | Observability predicates |
| `World.lean` | World layer for obligation theorems |
| `WorldCtx.lean` | WorldCtx signature with proved transport |
| `AdversarialBase.lean` | Adversarial types and structures |
| `AdversarialObligations.lean` | Obligation theorems |
| `LTS.lean` | Generic LTS for revision safety |
| `RevisionSafety.lean` | Revision safety meta-theorems |
| `ScopeIrrelevance.lean` | Scope irrelevance theorems |
| `Minimality.lean` | Minimality and convergence theorems |
| `Feasibility.lean` | Existence and feasibility theorems |
| `PaperFacing.lean` | Re-exports only |
| `ConcreteLedgerModel.lean` | Constructive concrete model |
| `Agent/Constraints.lean` | PRP constraint theorems |
| `Agent/Imposition.lean` | Design-forcing theorems |
| `Agent/Resilience.lean` | Containment invariants |
| `Agent/Corroboration.lean` | Corroboration theorems |
