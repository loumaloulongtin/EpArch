# Operational Semantics Documentation

This document describes the canonical operational semantics for the EpArch formalization. Every deposit lifecycle step — submission, withdrawal, export, challenge, repair, revocation — is modeled as a typed transition with explicit preconditions. Safety properties follow by induction over `Trace` sequences using the `generic_invariant_preservation` template; invariants are maintained by construction, not checked ex-post.

**Design choice:** Preconditions are encoded directly into the `Step` constructors rather than checked at runtime. This means the type system enforces the three-gate withdrawal model (`ACL ∧ Deposited ∧ τ-valid`) and export header-preservation statically — a violation is a type error, not a runtime failure.

## StepSemantics as Canonical LTS

**File:** `EpArch/StepSemantics.lean`

StepSemantics defines the canonical labeled transition system (LTS) for the epistemic architecture.

### Core Components

#### State Type

```lean
structure SystemState (PropLike Standard ErrorModel Provenance : Type u) where
  ledger      : List (Deposit PropLike Standard ErrorModel Provenance)
  bubbles     : List Bubble
  clock       : Time
  acl_table   : List ACLEntry
  trust_bridges : List (Bubble × Bubble)
```

#### Action Type

```lean
inductive Action (PropLike Standard ErrorModel Provenance Reason Evidence : Type u) where
  | Submit (d : Deposit PropLike Standard ErrorModel Provenance)
  | Withdraw (a : Agent) (B : Bubble) (d_idx : Nat)
  | Export (B1 B2 : Bubble) (d_idx : Nat)
  | Challenge (c : EpArch.Challenge PropLike Reason Evidence)
  | Tick
  | Repair (d_idx : Nat) (f : Field)
  | Revoke (d_idx : Nat)
```

#### Step Relation

```lean
inductive Step : SystemState → Action → SystemState → Prop where
  | submit : (s : SystemState) → (d : Deposit) → Step s (.Submit d) s'
  | withdraw : (s : SystemState) → (a : Agent) → (B : Bubble) → (d_idx : Nat) →
      hasACLPermission s a B d_idx → isCurrentDeposit s d_idx → isDeposited s d_idx →
      Step s (.Withdraw a B d_idx) s
  | export_with_bridge : (s : SystemState) → (B1 B2 : Bubble) → (d_idx : Nat) →
      isDeposited s d_idx → depositHasHeader s d_idx → hasTrustBridge s B1 B2 →
      Step s (.Export B1 B2 d_idx) s'
  | export_revalidate : (s : SystemState) → (B1 B2 : Bubble) → (d_idx : Nat) →
      isDeposited s d_idx → depositHasHeader s d_idx → ¬hasTrustBridge s B1 B2 →
      Step s (.Export B1 B2 d_idx) s'
  | challenge : (s : SystemState) → (c : Challenge) → (d_idx : Nat) →
      isDeposited s d_idx → Step s (.Challenge c) s'
  | tick : (s : SystemState) → (t' : Time) → Step s .Tick s'
  | repair : (s : SystemState) → (d_idx : Nat) → (f : Field) →
      isQuarantined s d_idx → Step s (.Repair d_idx f) s'
  | revoke : (s : SystemState) → (d_idx : Nat) →
      isQuarantined s d_idx → Step s (.Revoke d_idx) s'
```

### Trace Type (Multi-Step Reachability)

```lean
inductive Trace : SystemState → SystemState → Type where
  | nil : (s : SystemState) → Trace s s
  | cons : Step s a s' → Trace s' s'' → Trace s s''
```

---

## Generic Invariant Preservation

The canonical pattern for safety proofs:

```lean
theorem generic_invariant_preservation
    (Inv : SystemState → Prop)
    (h_step : ∀ s s' a, Step s a s' → Inv s → Inv s')
    (s s' : SystemState)
    (trace : Trace s s')
    (h_init : Inv s) :
    Inv s'
```

**Proof pattern:**
1. Define invariant `Inv : SystemState → Prop`
2. Prove `step_preserves_Inv : ∀ s s' a, Step s a s' → Inv s → Inv s'`
3. Apply `generic_invariant_preservation` to get trace-level preservation

---

## Precondition Structure

Key insight: Most safety properties are **encoded as preconditions** on Step constructors.

| Action | Key Preconditions |
|--------|-------------------|
| `Withdraw` | `hasACLPermission`, `isDeposited`, `isCurrentDeposit` |
| `Export` | `hasTrustBridge` OR revalidation, `depositHasHeader` |
| `Challenge` | `isDeposited` |
| `Repair` | `isQuarantined` |
| `Revoke` | `isQuarantined` |

This structural encoding means invariants are **maintained by construction**.

---

## Paper-LTS Correspondence

| Paper Concept | LTS Implementation |
|---------------|-------------------|
| Deposit lifecycle | Step constructors |
| Withdrawal gate | `Step.withdraw` preconditions |
| Export gate | `Step.export_*` preconditions |
| Challenge/Revision | `Step.challenge`, `Step.repair`, `Step.revoke` |
| Trace semantics | `Trace` inductive type |
| Self-correction | `Trace.demonstratesSelfCorrection` |
| Revision-prohibiting | `prohibits_revision` predicate |

---

## Relationship to AgentLTS

**AgentLTS** (in `Agent/Resilience.lean`) is a **simplified abstraction** of StepSemantics.

- **StepSemantics**: Canonical operational semantics with full detail
- **AgentLTS**: Over-approximation for containment proofs

The relationship: `StepSemantics ⊆ AgentLTS` (simulation).

Containment theorems proved in AgentLTS also hold for StepSemantics (via simulation).
