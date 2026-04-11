/-
EpArch/BehavioralEquivalence.lean — Observation-Boundary Equivalence

Defines the abstract input/observation interface for WorkingSystems and
proves that any two systems both satisfying all operational properties
produce identical observations on all inputs.

## Definitions

- `Input`               — abstract input events (withdraw, export, challenge, time-advance)
- `Observation`         — observable outcomes
- `Behavior`            — observation function, indexed by WorkingSystem primitive flags
- `BehaviorallyEquivalent` — identical observations on all inputs

## Theorems

- `working_systems_equivalent` — SatisfiesAllProperties on both → behaviorally equivalent

## Dependencies

- **Minimality.lean:** WorkingSystem, SatisfiesAllProperties
-/

import EpArch.Minimality

namespace EpArch

/-! ## Behavioral Equivalence -/

/-! ### Input Events -/

/-- Abstract input events a WorkingSystem can receive.
    Analogues of CInputEvent in ConcreteLedgerModel.lean. -/
inductive Input where
  /-- Request to withdraw/rely on a deposit. -/
  | WithdrawRequest (agent_id : Nat) (bubble_id : Nat) (claim_id : Nat)
  /-- Request to export deposit across boundary. -/
  | ExportRequest (source_bubble : Nat) (target_bubble : Nat) (claim_id : Nat)
  /-- Challenge a deposit's validity. -/
  | ChallengeRequest (claim_id : Nat) (field : String)
  /-- Time advance. -/
  | TimeAdvance (ticks : Nat)
  deriving Repr, DecidableEq

/-! ### Observable Outcomes -/

/-- Observable outcomes from processing inputs.
    Analogues of COutcome in ConcreteLedgerModel.lean. -/
inductive Observation where
  /-- Withdrawal succeeded. -/
  | WithdrawSuccess (claim_id : Nat)
  /-- Withdrawal denied with reason. -/
  | WithdrawDenied (reason : String)
  /-- Export succeeded. -/
  | ExportSuccess (claim_id : Nat) (target_bubble : Nat)
  /-- Export denied with reason. -/
  | ExportDenied (reason : String)
  /-- Challenge processed. -/
  | ChallengeProcessed (result : String)
  /-- Time advanced. -/
  | TimeAdvanced
  deriving Repr, DecidableEq

/-! ### Behavior Function -/

/-- The observation produced by a WorkingSystem on a given input.
    Depends only on the proof-carrying fields: `bank_ev`, `bridges_ev`,
    `revocation_ev`.  Two systems with identical `isSome` values produce
    identical output. -/
def Behavior (W : WorkingSystem) (i : Input) : Observation :=
  match i with
  | .WithdrawRequest _ _ claim_id =>
    if W.bank_ev.isSome && W.bridges_ev.isSome then
      .WithdrawSuccess claim_id
    else
      .WithdrawDenied "missing primitives"
  | .ExportRequest _ target claim_id =>
    if W.bank_ev.isSome && W.bridges_ev.isSome then
      .ExportSuccess claim_id target
    else
      .ExportDenied "missing primitives"
  | .ChallengeRequest _ field =>
    if W.revocation_ev.isSome then
      .ChallengeProcessed s!"challenged field {field}"
    else
      .ChallengeProcessed "no correction support"
  | .TimeAdvance _ =>
    .TimeAdvanced

/-! ### Behavioral Equivalence -/

/-- Two systems are behaviorally equivalent if they produce identical
    observations on every input. -/
def BehaviorallyEquivalent (W1 W2 : WorkingSystem) : Prop :=
  ∀ i : Input, Behavior W1 i = Behavior W2 i

/-! ### Theorems -/

/-- Behavioral equivalence is reflexive. -/
theorem behavioral_equiv_refl (W : WorkingSystem) : BehaviorallyEquivalent W W := by
  intro i
  rfl

/-- Behavioral equivalence is symmetric. -/
theorem behavioral_equiv_symm (W1 W2 : WorkingSystem) :
    BehaviorallyEquivalent W1 W2 → BehaviorallyEquivalent W2 W1 := by
  intro h i
  exact (h i).symm

/-- Behavioral equivalence is transitive. -/
theorem behavioral_equiv_trans (W1 W2 W3 : WorkingSystem) :
    BehaviorallyEquivalent W1 W2 → BehaviorallyEquivalent W2 W3 →
    BehaviorallyEquivalent W1 W3 := by
  intro h12 h23 i
  exact (h12 i).trans (h23 i)

/-- Systems with identical proof-carrying field presence produce identical observations.
    `Behavior` inspects `bank_ev.isSome`, `bridges_ev.isSome`, and `revocation_ev.isSome`. -/
theorem same_flags_same_behavior (W1 W2 : WorkingSystem)
    (h_bank    : W1.bank_ev.isSome    = W2.bank_ev.isSome)
    (h_bridges : W1.bridges_ev.isSome = W2.bridges_ev.isSome)
    (h_revoc   : W1.revocation_ev.isSome = W2.revocation_ev.isSome) :
    BehaviorallyEquivalent W1 W2 := by
  intro i
  simp [Behavior]
  cases i with
  | WithdrawRequest agent_id bubble_id claim_id =>
    simp [h_bank, h_bridges]
  | ExportRequest source target claim_id =>
    simp [h_bank, h_bridges]
  | ChallengeRequest claim_id field =>
    simp [h_revoc]
  | TimeAdvance ticks =>
    rfl

/-- `SatisfiesAllProperties` determines the presence of all six proof-carrying fields. -/
theorem satisfies_all_fixes_flags (W : WorkingSystem) (h : SatisfiesAllProperties W) :
    W.bubbles_ev.isSome       = true ∧
    W.bridges_ev.isSome       = true ∧
    W.headers_ev.isSome       = true ∧
    W.revocation_ev.isSome    = true ∧
    W.bank_ev.isSome          = true ∧
    W.redeemability_ev.isSome = true :=
  ⟨h .scope, h .trust, h .headers, h .revocation, h .bank, h .redeemability⟩

/-- Any two systems satisfying all properties are behaviorally equivalent. -/
theorem working_systems_equivalent (W1 W2 : WorkingSystem) :
    SatisfiesAllProperties W1 → SatisfiesAllProperties W2 → BehaviorallyEquivalent W1 W2 := by
  intro h_sat1 h_sat2
  have ⟨_, h1_bridges, _, h1_revoc, h1_bank, _⟩ := satisfies_all_fixes_flags W1 h_sat1
  have ⟨_, h2_bridges, _, h2_revoc, h2_bank, _⟩ := satisfies_all_fixes_flags W2 h_sat2
  exact same_flags_same_behavior W1 W2
    (h1_bank.trans h2_bank.symm)
    (h1_bridges.trans h2_bridges.symm)
    (h1_revoc.trans h2_revoc.symm)

end EpArch
