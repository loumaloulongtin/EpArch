/-
EpArch.Invariants — Core Invariants

Protocol requirements for robust system functioning — what must hold
for the system to remain healthy. Violations predict degradation.

Grounded operational invariants proved from the constructive step semantics:
- grounded_no_withdrawal_without_acl (from Step.withdraw)
- grounded_no_export_without_gate (from Step.export)
- challenge_requires_field_localization (Field enum exhaustion)
- worldstate_requires_finite_τ (definitional from deposit_kind)

No axiom declarations are present.
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank
import EpArch.Semantics.StepSemantics

namespace EpArch

universe u

variable {PropLike Standard ErrorModel Provenance : Type u}

/-! ## Invariant 1: Withdrawal ACL Enforcement (Grounded) -/

/-- Every Step.withdraw transition requires ACL permission.

    Proved: Step.withdraw constructor requires hasACLPermission as a precondition;
    the result follows directly from withdrawal_requires_three_gates. -/
theorem grounded_no_withdrawal_without_acl
    {Reason Evidence : Type u}
    (s s' : StepSemantics.SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat)
    (h_step : StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
        s (.Withdraw a B d_idx) s') :
    StepSemantics.hasACLPermission s a B d_idx :=
  (StepSemantics.withdrawal_requires_three_gates s s' a B d_idx h_step).1


/-! ## Invariant 2: Export Gating (Grounded) -/

/-- Every Step.export transition requires depositHasHeader (header not stripped).

    Proved: Step.export constructors require depositHasHeader as a precondition;
    exports that lose headers cannot carry S/E/V evidence for downstream revalidation.
    Proved from StepSemantics.export_requires_header. -/
theorem grounded_no_export_without_gate
    {Reason Evidence : Type u}
    (s s' : StepSemantics.SystemState PropLike Standard ErrorModel Provenance)
    (B1 B2 : Bubble) (d_idx : Nat)
    (h_step : StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
        s (.Export B1 B2 d_idx) s') :
    StepSemantics.depositHasHeader s d_idx :=
  StepSemantics.export_requires_header s s' B1 B2 d_idx h_step


/-! ## Invariant 3: Challenge must specify suspected field -/

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

    The Field enum has exactly 6 cases, and WellFormedChallenge requires
    suspected_field : Field; by exhaustion it must be one of them. -/
theorem challenge_requires_field_localization
    (c : WellFormedChallenge (PropLike := PropLike)
        (Standard := Standard) (ErrorModel := ErrorModel) (Provenance := Provenance)) :
    challenge_well_formed c := by
  unfold challenge_well_formed
  cases c.suspected_field <;> decide


/-! ## Invariant 4: τ (TTL) finite for world-state deposits -/

/-- Maximum TTL for world-state (empirical / schedule / position) deposits.
    365 time units corresponds to one year; empirical facts not refreshed
    within this window are considered stale for banking purposes. -/
def maxWorldStateTTL : Time := 365

/-- τ_is_finite: a TTL value is within the world-state refresh bound.
    Replaces the previous opaque declaration with a concrete upper-bound definition:
    a TTL is "finite" (in the world-state sense) iff it is at most maxWorldStateTTL.
    Structural deposits (proofs, definitions) have τ > 365 and are excluded. -/
def τ_is_finite (t : Time) : Prop := t ≤ maxWorldStateTTL

/-- deposit_kind: classify a deposit by its TTL characteristic.
    Deposits with τ ≤ maxWorldStateTTL are WorldState (empirical facts, schedules,
    positions — require periodic refresh); deposits with τ > maxWorldStateTTL are
    Structural (proofs, definitions — near-infinite shelf life).
    This restores the WorldState/Structural distinction erased by an unconditional
    .Structural assignment, grounding it in the actual τ value. -/
def deposit_kind (d : Deposit PropLike Standard ErrorModel Provenance) : DepositKind :=
  if d.h.τ ≤ maxWorldStateTTL then .WorldState else .Structural

/-- World-state deposits have finite TTL (within the refresh bound).
    Discharged: deposit_kind d = .WorldState iff d.h.τ ≤ maxWorldStateTTL (by if_pos);
    that is exactly τ_is_finite d.h.τ. The .Structural branch is handled by contradiction. -/
theorem worldstate_requires_finite_τ
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    deposit_kind d = .WorldState → τ_is_finite d.h.τ := by
  intro h
  unfold deposit_kind at h
  unfold τ_is_finite
  cases Classical.em (d.h.τ ≤ maxWorldStateTTL) with
  | inl h_le => rw [if_pos h_le] at h; exact h_le
  | inr h_gt => rw [if_neg h_gt] at h; exact absurd h (by decide)


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
