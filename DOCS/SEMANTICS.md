# Operational Semantics Documentation

This document describes the canonical operational semantics for the EpArch formalization. Every deposit lifecycle step — submission, withdrawal, challenge, repair, revocation, promotion, forgetting, and direct update — is modeled as a typed transition with explicit preconditions. Safety properties follow by induction over `Trace` sequences using the `generic_invariant_preservation` template; invariants are maintained by construction, not checked ex-post.

**Design choice:** Preconditions are encoded directly into the `Step` constructors rather than checked at runtime. This means the type system enforces structural status gates (`isDeposited`, `isQuarantined`, `isCandidate`) and clock monotonicity statically — a violation is a type error, not a runtime failure. Authorization is an agent-level concern: the bank records deposit events; agents carry credentials to the interaction.

**Export is not a bank primitive.** Inter-bubble transfer is an agent-level workflow: the agent Withdraws from B_src, carries the deposit (recording provenance in `d.h.V`), and submits or registers it in B_tgt depending on import policy. `Action.Submit` / `Step.submit` enters the deposit as Candidate (subject to bank promotion); `Action.Register` / `Step.register` enters it as Deposited immediately — the agent's choice of action is itself the assertion that the deposit is already sufficiently grounded. A trust bridge is one reason an agent uses the Register path, but it is not a bank-side precondition.

## StepSemantics as Canonical LTS

**File:** `EpArch/Semantics/StepSemantics.lean`

StepSemantics defines the canonical labeled transition system (LTS) for the epistemic architecture.

### Core Components

#### State Type

```lean
structure SystemState (PropLike Standard ErrorModel Provenance : Type u) where
  ledger      : List (Deposit PropLike Standard ErrorModel Provenance)
  bubbles     : List Bubble
  clock       : Time
  ladder_map  : Agent → PropLike → LadderStage := fun _ _ => LadderStage.Ignorance
```

Trust relationships and ACL tables are **not** SystemState fields. Trust is per-deposit (`d.h.acl`) and per-agent, not a systemic bank-layer list. The bank records what the agent presents; the agent decides what to present.

#### Action Type

```lean
inductive Action (PropLike Standard ErrorModel Provenance Reason Evidence : Type u) where
  | Submit   (a : Agent) (d : Deposit PropLike Standard ErrorModel Provenance)
  | Register (a : Agent) (d : Deposit PropLike Standard ErrorModel Provenance)
  | Withdraw (a : Agent) (B : Bubble) (d_idx : Nat)
  | Challenge (a : Agent) (B : Bubble) (c : EpArch.Challenge PropLike Reason Evidence)
  | Tick
  | Repair   (a : Agent) (B : Bubble) (d_idx : Nat) (f : Field)
  | Revoke   (a : Agent) (B : Bubble) (d_idx : Nat)
  | Promote  (a : Agent) (B : Bubble) (d_idx : Nat)
  | Forget   (a : Agent) (B : Bubble) (d_idx : Nat)
  | Update   (a : Agent) (B : Bubble) (d_idx : Nat) (d_new : Deposit)
```

Every agent-initiated action carries `(a : Agent) (B : Bubble)` so that traces are fully attributed. `Tick` is the sole environment action (clock advance); it carries a monotonicity witness `h_mono : s.clock ≤ t'` but no agent identity.

#### Step Relation

```lean
inductive Step : SystemState → Action → SystemState → Prop where
  | submit : (s : SystemState) → (a : Agent) → (d : Deposit) →
      Step s (.Submit a d) { s with ledger := s.ledger ++ [{ d with status := .Candidate }] }

  | register : (s : SystemState) → (a : Agent) → (d : Deposit) →
      Step s (.Register a d) { s with ledger := s.ledger ++ [{ d with status := .Deposited }] }

  | withdraw : (s : SystemState) → (a : Agent) → (B : Bubble) → (d_idx : Nat) →
      isDeposited s d_idx →
      Step s (.Withdraw a B d_idx) s  -- state unchanged: withdrawal is a read, not a consume

  | challenge : (s : SystemState) → (a : Agent) → (B : Bubble) →
                (c : Challenge) → (d_idx : Nat) →
      isDeposited s d_idx →
      Step s (.Challenge a B c) { s with ledger := updateDepositStatus s.ledger d_idx .Quarantined }

  | tick : (s : SystemState) → (t' : Time) → (h_mono : s.clock ≤ t') →
      Step s .Tick { s with clock := t' }

  | revoke : (s : SystemState) → (a : Agent) → (B : Bubble) → (d_idx : Nat) →
      isQuarantined s d_idx →
      Step s (.Revoke a B d_idx) { s with ledger := updateDepositStatus s.ledger d_idx .Revoked }

  | repair : (s : SystemState) → (a : Agent) → (B : Bubble) → (d_idx : Nat) → (f : Field) →
      isQuarantined s d_idx →
      Step s (.Repair a B d_idx f) { s with ledger := updateDepositStatus s.ledger d_idx .Candidate }

  | promote : (s : SystemState) → (a : Agent) → (B : Bubble) → (d_idx : Nat) →
      isCandidate s d_idx →
      Step s (.Promote a B d_idx) { s with ledger := updateDepositStatus s.ledger d_idx .Deposited }

  | forget : (s : SystemState) → (a : Agent) → (B : Bubble) → (d_idx : Nat) →
      (d_old : Deposit) → s.ledger.get? d_idx = some d_old → d_old.status ≠ .Forgotten →
      Step s (.Forget a B d_idx) { s with ledger := updateDepositStatus s.ledger d_idx .Forgotten }

  | update : (s : SystemState) → (a : Agent) → (B : Bubble) → (d_idx : Nat) →
      (d_new d_old : Deposit) → s.ledger.get? d_idx = some d_old → d_old.status ≠ .Forgotten →
      Step s (.Update a B d_idx d_new) { s with ledger := modifyAt s.ledger d_idx (fun _ => d_new) }
```

Ten constructors total. `Step.submit` fires on `Action.Submit` (→ Candidate); `Step.register` fires on `Action.Register` (→ Deposited). The remaining eight constructors are one-to-one with their Action variant. All agent-initiated constructors carry a named agent and bubble for attribution; `tick` carries only the monotonicity witness. Preconditions are purely structural ledger reads — no ACL tables, bank-authority lists, or trust-bridge registries in the bank's LTS.

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

| Action | Step constructor(s) | Key Preconditions |
|--------|---------------------|-------------------|
| `Submit`    | `submit`   | *(none — open submission; enters as Candidate)* |
| `Register`  | `register` | *(none — agent registers directly; enters as Deposited)* |
| `Withdraw` | `withdraw` | `isDeposited` |
| `Challenge` | `challenge` | `isDeposited` |
| `Repair` | `repair` | `isQuarantined` |
| `Revoke` | `revoke` | `isQuarantined` |
| `Promote` | `promote` | `isCandidate` |
| `Forget` | `forget` | existing slot, `d_old.status ≠ .Forgotten` |
| `Update` | `update` | existing slot, `d_old.status ≠ .Forgotten` |
| `Tick` | `tick` | `s.clock ≤ t'` (monotonicity) |

All preconditions are pure structural ledger reads. There are no ACL tables, bank-authority registries, or trust-bridge lists in the bank's LTS layer. Authorization is an agent-level concern; the bank records what status a deposit is in and whether a transition is structurally legal.

This structural encoding means invariants are **maintained by construction**.

---

## Immediate Semantic Consequences

Because preconditions are structural rather than checked post-hoc, the encoding directly forces:

| Operation | What the type forces |
|-----------|----------------------|
| `Withdraw` | Cannot exist unless the deposit is in `Deposited` status |
| `Submit` (`submit`) | No structural precondition; deposit enters as `Candidate` |
| `Register` (`register`) | No structural precondition; agent registers directly; deposit enters as `Deposited` |
| `Promote` | Cannot exist unless the deposit is in `Candidate` status |
| `Challenge` | Cannot fire unless the deposit is in `Deposited` status |
| `Repair` / `Revoke` | Cannot fire unless the deposit is already in `Quarantined` status |
| `Forget` | Cannot fire if the slot is already `Forgotten`; marks it as `Forgotten` tombstone |
| `Update` | Cannot fire if the slot is already `Forgotten`; wholesale replaces the slot with `d_new`; counts as revision (`isRevision = true`) |
| `Tick` | Clock cannot go backwards; `s.clock ≤ t'` is structurally enforced |

**Safety is induction-friendly by construction:** once step-level preservation is proved for a given invariant, trace-level preservation follows generically via `generic_invariant_preservation`. There is no need to re-examine multi-step cases individually.

---

## Relationship to AgentLTS

**AgentLTS** (in `Agent/Resilience.lean`) is a **proof-oriented abstraction** of StepSemantics, not an alternative semantics.

- **StepSemantics**: Canonical operational semantics with full structural preconditions
- **AgentLTS**: A deliberately coarser over-approximation, designed for containment proofs
- **Why it exists**: Containment arguments — showing that no agent behavior escapes a given class — are easier to prove against the coarser abstraction
- **Results transfer back**: Because StepSemantics is simulated by AgentLTS (`StepSemantics ⊆ AgentLTS`), containment results proved in AgentLTS also hold for StepSemantics

---

## Reading This File

This file specifies the canonical operational semantics: transition structure, precondition encoding, and the trace-level safety pattern. It is about structural preconditions and preservation, not runtime implementation details or empirical systems. Core proofs live in `Semantics/StepSemantics.lean`; containment arguments live in `Agent/Resilience.lean` and transport back via simulation.


