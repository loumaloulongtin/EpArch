/-
Core Invariants

Protocol requirements for robust system functioning — what must hold
for the system to remain healthy. Violations predict degradation.

STATUS: These axioms are DESIGN REQUIREMENTS, not derivable facts.
They specify what the system SHOULD do, not what it mathematically MUST do.
As such, they are acceptable as permanent axioms (like Bank governance laws).

Exception: `challenge_requires_field_localization` was discharged — see theorem.

## Axiom Count: 5 (of 16 remaining)

1. `no_deposit_without_redeemability` — deposits must have constraint-surface contact
2. `no_withdrawal_without_acl` — withdrawals require valid ACL membership
3. `no_export_without_gate` — cross-bubble transfers require revalidation or trust-bridge
4. `deposit_kind` — every deposit classifies as world-state or analytic
5. `worldstate_requires_finite_τ` — world-state deposits must have finite TTL

Plus one DISCHARGED former axiom (now a theorem):
- `challenge_requires_field_localization` — challenges must target specific header fields
  (PROVED: see `challenge_requires_field_localization` below)

## Constructive Groundings

- **StepSemantics.lean** provides operational semantics that ground invariants 1–3
  as consequences of the deposit lifecycle.
- **ConcreteLedgerModel.lean** provides a zero-axiom model satisfying all invariants.
- **Health.lean** uses invariants for health-goal necessity proofs.
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank
import EpArch.StepSemantics

namespace EpArch

universe u

variable {PropLike Standard ErrorModel Provenance : Type u}

/-! ## Invariant 1: No deposit without RedeemabilityRef -/

/-- Every deposit must have a non-null redeemability reference.

    Violation consequence: Relativism leak — deposits float free of
    constraint-surface contact; consensus becomes self-validating. -/
axiom no_deposit_without_redeemability
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (empty_cs : ConstraintSurface) :
    d.status = .Deposited → d.h.redeem.cs ≠ empty_cs


/-! ## Invariant 2: No withdrawal without valid ACL -/

/-- Withdrawals require ACL permission.

    Violation consequence: Access control breach — anyone can rely on
    any deposit regardless of authorization. -/
opaque acl_permits : ACL → Agent → Prop

axiom no_withdrawal_without_acl (a : Agent)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    withdraw a d.bubble d → acl_permits d.h.acl a

/-- Grounded version of Invariant 2: Step.withdraw enforces ACL.

    Every Step.withdraw transition requires hasACLPermission in its precondition.
    This is a proved theorem (not an axiom) derived from the Step constructor.

    Note: This lives over StepSemantics.SystemState + deposit index, which is
    the concrete operational layer. The abstract `no_withdrawal_without_acl`
    above lives over the abstract `withdraw` predicate in Bank.lean.
    Route B: the grounded theorem documents the operational grounding without
    requiring a signature refactor of the abstract Bank-facing axiom. -/
theorem grounded_no_withdrawal_without_acl
    {Reason Evidence : Type u}
    (s s' : StepSemantics.SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat)
    (h_step : StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
        s (.Withdraw a B d_idx) s') :
    StepSemantics.hasACLPermission s a B d_idx :=
  (StepSemantics.withdrawal_requires_three_gates s s' a B d_idx h_step).1


/-! ## Invariant 3: No export without revalidation OR trust-bridge -/

/-- Export requires either revalidation or established trust.

    Violation consequence: Contamination propagates — bad deposits
    spread across bubble boundaries without checking. -/
axiom no_export_without_gate (B1 B2 : Bubble)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    exportDep B1 B2 d → (Revalidate B1 B2 d ∨ TrustBridge B1 B2)

/-- Grounded version of Invariant 3: Step.export enforces header preservation.

    Every Step.export transition requires depositHasHeader (header not stripped),
    which is the operational correlate of export gating: exports that lose headers
    cannot carry the S/E/V evidence needed for downstream revalidation.

    This is a proved theorem from StepSemantics.export_requires_header.
    Route B: documents the operational grounding for the abstract axiom above. -/
theorem grounded_no_export_without_gate
    {Reason Evidence : Type u}
    (s s' : StepSemantics.SystemState PropLike Standard ErrorModel Provenance)
    (B1 B2 : Bubble) (d_idx : Nat)
    (h_step : StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
        s (.Export B1 B2 d_idx) s') :
    StepSemantics.depositHasHeader s d_idx :=
  StepSemantics.export_requires_header s s' B1 B2 d_idx h_step


/-! ## Invariant 4: Challenge must specify suspected field -/

/-- Challenges must localize to a specific field.

    Violation consequence: Repair loop fails — without knowing
    which field broke, targeted repair is impossible. -/
structure WellFormedChallenge where
  target : Deposit PropLike Standard ErrorModel Provenance
  suspected_field : Field
  evidence : PropLike

/-- A challenge is well-formed iff it specifies a field. -/
def challenge_well_formed (c : WellFormedChallenge (PropLike := PropLike)
    (Standard := Standard) (ErrorModel := ErrorModel) (Provenance := Provenance)) : Prop :=
  c.suspected_field ∈ [.S, .E, .V, .τ, .redeemability, .acl]

/-- All challenges are well-formed by construction.

    This holds because the Field enum has exactly 6 cases, and WellFormedChallenge
    requires suspected_field : Field. By exhaustion, it must be one of them.

    This was previously an axiom; now it's a theorem. -/
theorem challenge_requires_field_localization
    (c : WellFormedChallenge (PropLike := PropLike)
        (Standard := Standard) (ErrorModel := ErrorModel) (Provenance := Provenance)) :
    challenge_well_formed c := by
  unfold challenge_well_formed
  cases c.suspected_field <;> decide


/-! ## Invariant 5: τ (TTL) finite for world-state deposits -/

/-- World-state deposits must have finite TTL.

    Violation consequence: Staleness invisible — deposits about
    changing facts persist past their validity window. -/
opaque τ_is_finite : Time → Prop

axiom deposit_kind (d : Deposit PropLike Standard ErrorModel Provenance) : DepositKind

axiom worldstate_requires_finite_τ
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    deposit_kind d = .WorldState → τ_is_finite d.h.τ


/-! ## Invariant Reading Note

These invariants are protocol requirements, not behavioral universals.

Real systems violate them — and that's exactly why:
- Export without trust-bridge → contamination propagates
- Headerless challenges → repair fails, disputes persist
- Infinite τ on world-state → stale claims cause failures

The invariants specify what must hold for health; violations
predict degradation, not impossibility. -/


/-! ## Violation Consequence Summary -/

/-- Summary of what breaks when each invariant is violated. -/
structure InvariantViolation where
  invariant : String
  consequence : String

def invariant_violation_table : List InvariantViolation := [
  ⟨"No deposit without RedeemabilityRef", "Relativism leak"⟩,
  ⟨"No withdrawal without ACL", "Access control breach"⟩,
  ⟨"No export without gate", "Contamination propagates"⟩,
  ⟨"Challenge must specify field", "Repair loop fails"⟩,
  ⟨"τ finite for world-state", "Staleness invisible"⟩
]


/-! ## Load-Bearing Status

For what breaks if any invariant is dropped, see the AttackSurface
structure below. -/

/-- Attack surface: ways to falsify the architecture. -/
structure AttackSurface where
  surface : String
  what_to_show : String

def architecture_attack_surfaces : List AttackSurface := [
  ⟨"Bubbles are optional", "Global ledger permits innovation + coordination"⟩,
  ⟨"Binary validation suffices", "Stable repair without field localization"⟩,
  ⟨"Export needs no gating", "Reliable transfer without revalidation or trust"⟩,
  ⟨"Consensus = redeemability", "Distinguish knowledge from shared belief by agreement alone"⟩,
  ⟨"Certainty substitutes for authorization", "Private traction reliably coordinates"⟩,
  ⟨"Headers don't matter for disputes", "Headerless disputes resolve equally"⟩,
  ⟨"Propaganda targets belief, not bandwidth", "Per-claim persuasiveness > volume"⟩
]

end EpArch
