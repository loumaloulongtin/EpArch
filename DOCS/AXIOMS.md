# Axiom Inventory

This document catalogs all axioms in the formalization.

## Summary

| Category | Count | File |
|----------|-------|------|
| Bank Operators | 18 | Bank.lean |
| Commitments | 12 | Commitments.lean |
| Invariants | 5 | Invariants.lean |
| **Total** | **35** | — |

All axioms are specification-level (Tier C — design requirements, intentionally postulated): operator postconditions, paper commitments, and protocol invariants. There are no empirical axioms.

> **Note:** `SEVFactorization` (formerly listed as Commitment 3 axiom) is now a `theorem` because its statement `∃ s e v, d.h.S=s ∧ d.h.E=e ∧ d.h.V=v` is trivially provable by reflexivity. It does not require a design-commitment axiom.

---

## Category 1: Bank Operators (18 axioms)

**File:** `EpArch/Bank.lean`

| Axiom | Statement | Category |
|-------|-----------|----------|
| `KnowledgeIffDeposited` | Knowledge ↔ deposit relation | Semantic bridge |
| `repair` | Repair action specification | Operator spec |
| `Validate_B` | Validation produces validated deposit | Operator spec |
| `Accept_B` | Acceptance produces deposited deposit | Operator spec |
| `Challenge_B` | Challenge produces quarantined deposit | Operator spec |
| `Repair_B` | Repair produces repaired deposit | Operator spec |
| `Revoke_B` | Revoke produces revoked deposit | Operator spec |
| `Restore_B` | Restore produces restored deposit | Operator spec |
| `Export_B_C` | Export produces export record | Operator spec |
| `Import_C` | Import produces imported deposit | Operator spec |
| `validate_produces_validated` | Validate → Validated status | Post-condition |
| `accept_produces_deposited` | Accept → Deposited status | Post-condition |
| `challenge_produces_quarantined` | Challenge → Quarantined status | Post-condition |
| `revoke_produces_revoked` | Revoke → Revoked status | Post-condition |
| `τ_refresh` | τ refresh updates timestamp | Operator spec |
| `deprecate` | Deprecate marks deposit stale | Operator spec |
| `success_driven_bypass` | Success-driven verification bypass | Operator spec |
| `blast_radius_scales_with_reliance` | Blast radius scaling | Operator spec |

---

## Category 2: Commitments (12 axioms)

**File:** `EpArch/Commitments.lean`

| Axiom | Commitment | Paper Section |
|-------|------------|---------------|
| `TractionAuthorizationSplit` | C1: Type separation — certainty_L ⊥ knowledge_B (genuine content: certainty_L is opaque, both independence directions are non-trivial) | §2 |
| `NoGlobalLedgerTradeoff` | C2: No global ledger | §2 |
| ~~`SEVFactorization`~~ | *(not counted — moved to theorem)* | §3 |
| `redeemable_implies_path` | Redeemability → path | §4 |
| `RedeemabilityExternal` | C4: Redeemability is external | §4 |
| `by_consensus_creates_redeemability` | C4a: Consensus pattern | §4 |
| `ConsensusNotSufficient` | C4b: Consensus ≠ redeemability | §4 |
| `reliable_implies_export` | C5: Reliable → exportable | §5 |
| `reliable_unreliable_exclusive` | C5b: Exclusivity | §5 |
| `RepairLoopExists` | C6: Repair loop exists | §6 |
| `NoSelfCorrectionWithoutRevision` | C6b: Self-correction → revision | §6 |
| `HeaderPreservationAsymmetry` | C7: Strip is asymmetric | §7 |
| `TemporalValidity` | C8: τ creates pressure | §8 |

---

## Category 3: Health Goals (Definitional)

**File:** `EpArch/Health.lean`

Health goals are predicates over `CoreModel`/`CoreOps`:

| Definition | Signature | Description |
|------------|-----------|-------------|
| `SafeWithdrawalGoal` | `CoreModel → Prop` | Authorized submissions only |
| `ReliableExportGoal` | `CoreModel → Prop` | No contamination propagation |
| `CorrigibleLedgerGoal` | `CoreModel → Prop` | Existence + soundness conjunction: `(∃ B, hasRevision B) ∧ (revise → truth)` |
| `SoundDepositsGoal` | `CoreModel → Prop` | Verifiable within effectiveTime |
| `SelfCorrectionGoal` | `CoreModel → Prop` | `selfCorrects B → hasRevision B` (conditional goal) |
| `SelfCorrectingSystem` | `CoreModel → Prop` | `SelfCorrectionGoal M ∧ ∃ B, selfCorrects B` (active self-correction) |

### Necessity Theorems (PROVED)

| Theorem | Statement | Proof |
|---------|-----------|-------|
| `corrigible_needs_revision` | `CorrigibleLedgerGoal → HasRevisionCapability` | Extracts `.1` from the existence-soundness conjunction |
| `self_correction_needs_revision` | `SelfCorrectingSystem → HasRevisionCapability` | Via modus ponens on bundled witness |
| `sound_deposits_needs_verification` | SoundDepositsGoal + ∃truth → HasVerificationCapability | Uses verifyWithin definition |

---

## Category 4: Invariants (5 axioms)

**File:** `EpArch/Invariants.lean`

| Axiom | Statement | Type |
|-------|-----------|------|
| `no_deposit_without_redeemability` | All deposits have redeemability | Protocol invariant |
| `no_withdrawal_without_acl` | Withdrawal requires ACL | Protocol invariant |
| `no_export_without_gate` | Export requires gate | Protocol invariant |
| `deposit_kind` | Deposits have kinds | Type property |
| `worldstate_requires_finite_τ` | World state has finite τ | Protocol invariant |

---

## Category 5: Agent Layer (THEOREMS, NOT AXIOMS)

**Files:** `EpArch/Agent/Constraints.lean`, `EpArch/Agent/Imposition.lean`, `EpArch/Agent/Resilience.lean`

### PRP Theorems (proved)

| Theorem | Statement | File |
|---------|-----------|------|
| `no_global_closure_of_PRP` | PRP prevents finite verification closure | Constraints.lean |
| `needs_revision_of_PRP` | PRP implies ongoing challenges | Constraints.lean |
| `needs_scoping_of_PRP` | PRP implies must prioritize verification | Constraints.lean |
| `needs_revalidation_of_PRP` | Stable deposit sets impossible under PRP | Constraints.lean |
| `prp_incompatible_with_global_redeemability` | PRP blocks universal redemption | Constraints.lean |

### Design-Forcing Theorems (proved, were axioms)

These state that certain combinations (goal + constraints + no mechanism) are
architecturally impossible. Proved via concrete state models in Imposition.lean.

| Theorem | Statement | Pattern |
|---------|-----------|---------|
| `safe_withdrawal_needs_reversibility` | τ-bounded agents need reversibility | Constraints → Mechanism |
| `sound_deposits_need_cheap_validator` | Limited audit + PRP needs validator | Constraints → Mechanism |
| `reliable_export_needs_gate` | Fallible observation needs gate | Constraints → Mechanism |

### Concrete Pattern Models (proved)

| Theorem | What It Shows |
|---------|---------------|
| `irreversibility_violates_safety` | Irreversible + mistake → unsafe |
| `safe_withdrawal_implies_reversibility` | Safe outcomes require correction ability |
| `no_validator_blocks_expensive_claims` | No validator → expensive claims unverifiable |
| `no_gate_allows_error_propagation` | No gate → errors propagate |

### Containment Invariants (proved by trace induction)

| Theorem | Invariant |
|---------|-----------|
| `truth_invariant_preserved` | Agent actions cannot flip truth |
| `gate_invariant_preserved` | Agent actions cannot disable export gate |
| `truth_preserved_along_trace` | Truth stable across all traces |
| `gate_preserved_along_trace` | Gate status stable across all traces |
| `agent_containment` | Combined: agent faults don't crash system |

---

## Category 6: WorldCtx Transport (THEOREM, NOT AXIOM)

**File:** `EpArch/WorldCtx.lean`

| Theorem | Statement | Note |
|---------|-----------|------|
| `transport_lies_possible` | Compatible extensions preserve W_lies_possible | Was axiom, now proved |

---

## Axiom-Free Modules

The following modules contain **zero axioms**:

| Module | Description |
|--------|-------------|
| `Basic.lean` | Core types (Bubble, Agent, Claim, etc.) |
| `Header.lean` | S/E/V header structure |
| `StepSemantics.lean` | LTS operational semantics |
| `Theorems.lean` | Derived theorems |
| `Diagnosability.lean` | Observability predicates |
| `World.lean` | World layer for obligation theorems |
| `WorldCtx.lean` | WorldCtx extension with proved transport |
| `AdversarialBase.lean` | Adversarial types/structures |
| `AdversarialObligations.lean` | Obligation theorems (no axioms) |
| `LTS.lean` | Generic LTS for revision safety |
| `RevisionSafety.lean` | Revision safety meta-theorems |
| `ScopeIrrelevance.lean` | Scope irrelevance theorems |
| `PaperFacing.lean` | Re-exports only |
| `ConcreteLedgerModel.lean` | Constructive concrete model |
| `Agent/*.lean` | Agent constraint theorems |

---

## Tier Mapping

| Category | Tier | Rationale |
|----------|------|-----------|
| Bank Operators | C | Specification axioms (API contracts) |
| Commitments | C | Paper's design requirements |
| Invariants | C | Protocol requirements |

Tier C = design requirements / interface axioms, intentionally postulated (not derived).
