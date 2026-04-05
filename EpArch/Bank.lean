/-
EpArch — Bank (Shared Ledger Substrate)

Defines the Bank substrate: the shared ledger of authorized deposits.
Contains the core predicates (knowledge_B, deposited, hasDeposit), the
withdrawal and export operators, the full lifecycle operator suite
(Validate, Accept, Challenge, Repair, Revoke, Restore, Export, Import),
status-transition axioms, and bubble hygiene structures.

## Why Axioms?

The operators in this file are stated as axioms (e.g., `Validate_B`,
`Accept_B`, `Challenge_B`, etc.). This is a DESIGN CHOICE for the
specification layer: these axioms define WHAT the operators must satisfy,
not HOW they work. They serve as the interface contract.

The constructive implementations that ground these axioms live in two places:
- **StepSemantics.lean**: An operational LTS (labeled transition system) with
  a concrete `Step` inductive that implements Submit, Withdraw, Export,
  Challenge, Repair, Revoke as state transitions with explicit preconditions.
  The linking axioms are proved there as theorems from Step preconditions.
- **ConcreteLedgerModel.lean**: A fully constructive concrete model with
  zero axioms that witnesses the satisfiability of all commitments.

The axioms here are 18 of the project's 36 total axioms. They define the
Bank's interface; the other modules use this interface to prove theorems.

## Relationship to Other Files

- **Basic.lean** provides the types (Deposit, Bubble, Agent, etc.)
- **Header.lean** provides Header and the S/E/V structure
- **StepSemantics.lean** provides the operational semantics that ground
  these specification axioms
- **Commitments.lean** uses Bank axioms to define architectural commitments
- **Minimality.lean** uses Bank features to prove convergence/impossibility
-/

import EpArch.Basic
import EpArch.Header

namespace EpArch

universe u

variable {PropLike Standard ErrorModel Provenance : Type u}

/-! ## Bank Structure -/

/-- Bank: the ledger-like substrate that stores deposits, scoped by bubble.

    Key properties:
    - `has`: predicate for deposit membership
    - `Accept`: bubble-indexed acceptance function (consumes header)
    - `Supersedes`: versioning relation (d' supersedes d)

    Note: Accept is bank governance (substrate), not agent policy.
    The agent decides WHETHER to consult the bank;
    the bank decides WHETHER to accept the deposit. -/
structure Bank where
  has : Deposit PropLike Standard ErrorModel Provenance → Prop
  Accept : Bubble → (PropLike → Header Standard ErrorModel Provenance → Prop)
  Supersedes : Deposit PropLike Standard ErrorModel Provenance →
               Deposit PropLike Standard ErrorModel Provenance → Prop


/-! ## Core Bank Predicates -/

/-- Bank-side knowledge: P is deposited (authorized) in bubble B.
    This is the EXTERNAL axis — what the community has validated. -/
opaque knowledge_B : Bubble → PropLike → Prop

/-- Deposited: the deposit is active in bubble B. -/
opaque deposited : Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop

/-- HasDeposit: there exists some deposit for claim P in bubble B. -/
opaque hasDeposit : Bubble → PropLike → Prop

/-- Knowledge is equivalent to having a deposit. -/
axiom KnowledgeIffDeposited (B : Bubble) (P : PropLike) :
  knowledge_B B P ↔ hasDeposit B P


/-! ## Withdrawal -/

/-- Withdrawal context: an agent relying on a deposit. -/
structure WithdrawalCtx where
  agent : Agent
  deposit : Deposit PropLike Standard ErrorModel Provenance

/-- Withdraw: agent relies on deposit in bubble.
    Requires ACL, τ (currentness), and choice to consult bank. -/
opaque withdraw : Agent → Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop


/-! ## Export/Import -/

/-- Export: deposit crosses from bubble B1 to bubble B2.
    This is testimony / transfer across trust boundaries. -/
opaque exportDep : Bubble → Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop

/-- TrustBridge: B1 and B2 have an established trust relationship.
    Export can proceed without full revalidation. -/
opaque TrustBridge : Bubble → Bubble → Prop

/-- Revalidate: B2 re-runs its acceptance protocol on deposit from B1. -/
opaque Revalidate : Bubble → Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop


/-! ## Repair Actions -/

/-- RepairAction: an action that modifies a specific field of a deposit. -/
opaque RepairAction : Type u

/-- Repair: apply a repair action to a deposit, targeting a specific field.
    Returns the repaired deposit (which must re-enter as Candidate). -/
axiom repair (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance)
    (f : Field) (r : RepairAction) : Deposit PropLike Standard ErrorModel Provenance


/-! ## Consensus (for anti-relativism axioms) -/

/-- Consensus: bubble B has reached agreement on claim P.
    Note: consensus is NOT sufficient for redeemability (Commitment 4). -/
opaque consensus : Bubble → PropLike → Prop


/-! ## Lifecycle Operators -/

-- These are the state-transition functions a bubble applies to deposits.
-- Each operator has explicit preconditions (as comments) and a status-transition
-- axiom below.

/-- Validate_B: Candidate → Validated(S,E,V)
    Precondition: evidence bundle exists; error model chosen; provenance traceable
    Postcondition: header attached; last_validated timestamp set
    Note: The acceptance step is split into Validate_B (evidence → header)
    and Accept_B (header → ledger entry) for finer-grained lifecycle control. -/
axiom Validate_B (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) :
    Deposit PropLike Standard ErrorModel Provenance

/-- Accept_B: Validated → Deposited(meta)
    Precondition: bubble acceptance function satisfied
    Postcondition: ledger entry created; ACL instantiated; export class assigned -/
axiom Accept_B (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) :
    Deposit PropLike Standard ErrorModel Provenance

/-- Challenge_B: Deposited → Quarantined(field)
    Precondition: contestation channel open; challenger specifies field
    Postcondition: withdrawal/export permissions tightened; repair clock starts -/
axiom Challenge_B (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) (f : Field) :
    Deposit PropLike Standard ErrorModel Provenance

/-- Repair_B: Quarantined → Candidate(S',E',V')
    Precondition: new evidence addresses challenged field
    Postcondition: updated header; returns to Candidate for revalidation -/
axiom Repair_B (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) :
    Deposit PropLike Standard ErrorModel Provenance

/-- Revoke_B: Quarantined or Deposited → Revoked
    Precondition: repair failed OR challenge upheld OR constraint-surface disconfirmation
    Postcondition: revocation propagation; marked non-withdrawable
    Note: Permits Revoke from both Quarantined and Deposited, allowing
    direct revocation without requiring a prior challenge step. -/
axiom Revoke_B (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) :
    Deposit PropLike Standard ErrorModel Provenance

/-- Restore_B: Revoked → Candidate
    Precondition: new evidence reopens case
    Postcondition: starts fresh validation cycle
    Note: Extension operator for post-revocation re-entry into the lifecycle. -/
axiom Restore_B (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) :
    Deposit PropLike Standard ErrorModel Provenance

/-- Export_B_C: DepositState_B → ImportState_C
    Precondition: revalidation under C's standards OR TrustBridge(B,C)
    Postcondition: header may mutate (V lengthens, E adds proxy-trust risk) -/
axiom Export_B_C (B C : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) :
    Deposit PropLike Standard ErrorModel Provenance

/-- Import_C: External → Candidate or Deposited
    Outcome depends on trust-bridge strength and header preservation -/
axiom Import_C (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) :
    Deposit PropLike Standard ErrorModel Provenance


/-! ## Operator Status Transitions -/

/-- Status after validation. -/
axiom validate_produces_validated (B : Bubble)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    d.status = .Candidate → (Validate_B B d).status = .Validated

/-- Status after acceptance. -/
axiom accept_produces_deposited (B : Bubble)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    d.status = .Validated → (Accept_B B d).status = .Deposited

/-- Status after challenge. -/
axiom challenge_produces_quarantined (B : Bubble)
    (d : Deposit PropLike Standard ErrorModel Provenance) (f : Field) :
    d.status = .Deposited → (Challenge_B B d f).status = .Quarantined

/-- Status after revocation. -/
axiom revoke_produces_revoked (B : Bubble)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    d.status = .Quarantined ∨ d.status = .Deposited →
    (Revoke_B B d).status = .Revoked


/-! ## Bubble Hygiene -/

-- Operations for maintaining deposit freshness: τ refresh, deprecation, auditing.

/-- τ refresh: update the currentness marker on a deposit. -/
axiom τ_refresh (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) (t : Time) :
    Deposit PropLike Standard ErrorModel Provenance

/-- Deprecation: mark deposit as stale (past TTL). -/
axiom deprecate (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance) :
    Deposit PropLike Standard ErrorModel Provenance

/-- Audit policy: bubble's rules for hygiene frequency. -/
structure AuditPolicy where
  refresh_interval : Time
  deprecation_threshold : Time
  challenge_response_window : Time

/-- Bubble hygiene state. -/
structure HygieneState where
  last_audit : Time
  stale_count : Nat
  pending_challenges : Nat


/-! ## Success-Driven Bypass -/

/-- High-reliance deposits accumulate trust and receive less challenge scrutiny,
    increasing blast radius on failure. High-uptime systems reduce their own
    audit frequency the more they are relied upon — a structural vulnerability
    independent of any adversarial intent. -/
opaque reliance_level : Deposit PropLike Standard ErrorModel Provenance → Nat

/-- Challenge frequency inversely correlates with reliance. -/
opaque challenge_frequency : Deposit PropLike Standard ErrorModel Provenance → Nat

/-- Success-driven bypass: high reliance → low challenge frequency. -/
axiom success_driven_bypass (d : Deposit PropLike Standard ErrorModel Provenance) :
    reliance_level d > 100 → challenge_frequency d < 10

/-- Blast radius scales with reliance. -/
opaque blast_radius : Deposit PropLike Standard ErrorModel Provenance → Nat

axiom blast_radius_scales_with_reliance (d : Deposit PropLike Standard ErrorModel Provenance) :
    blast_radius d ≥ reliance_level d

end EpArch
