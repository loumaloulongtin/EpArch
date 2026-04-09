/-
Behavioral Equivalence

Sharp observation-boundary equivalence for WorkingSystems.
Two systems with identical Bank primitives produce identical observations
on all inputs in the abstract coordination interface.

## Key Definitions

- `Input`                    — abstract input events (withdraw, export, challenge, time-advance)
- `Observation`              — observable outcomes
- `Behavior`                 — observation function indexed by WorkingSystem primitive flags
- `BehaviorallyEquivalent`   — identical observations on all inputs

## Key Theorems

- `working_systems_equivalent`        — SatisfiesAllProperties on both → behaviorally equivalent
- `bank_primitives_determine_behavior` — WellFormed + containsBankPrimitives → equivalent

## Dependencies

- **Minimality.lean:** WorkingSystem, WellFormed, SatisfiesAllProperties,
  containsBankPrimitives, Has*, handles_*
-/

import EpArch.Minimality

namespace EpArch

/-! ## Sharp Behavioral Equivalence

Systems with Bank primitives are "behaviorally equivalent" for coordination
purposes. Define the observation boundary explicitly, then show that
systems with identical primitives produce identical observations. -/

/-! ### Input Events -/

/-- Input events that a WorkingSystem can receive.
    These are the abstract analogues of CInputEvent in ConcreteLedgerModel.lean. -/
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
    These are the abstract analogues of COutcome in ConcreteLedgerModel.lean. -/
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

/-- The behavior of a WorkingSystem on an input.

    This is the KEY INSIGHT: behavior depends ONLY on the primitives.
    Two systems with the same primitives produce the same observations.

    The function is defined by cases on what primitives the system has.
    This makes the link between primitives and behavior DEFINITIONAL. -/
def Behavior (W : WorkingSystem) (i : Input) : Observation :=
  match i with
  | .WithdrawRequest _ _ claim_id =>
    -- Withdrawal requires: shared records + reliance
    if W.has_shared_records ∧ W.enables_reliance then
      .WithdrawSuccess claim_id
    else
      .WithdrawDenied "missing primitives"
  | .ExportRequest _ target claim_id =>
    -- Export requires: shared records + reliance
    if W.has_shared_records ∧ W.enables_reliance then
      .ExportSuccess claim_id target
    else
      .ExportDenied "missing primitives"
  | .ChallengeRequest _ field =>
    -- Challenge requires: correction support
    if W.supports_correction then
      .ChallengeProcessed s!"challenged field {field}"
    else
      .ChallengeProcessed "no correction support"
  | .TimeAdvance _ =>
    .TimeAdvanced

/-! ### Sharp Behavioral Equivalence -/

/-- Two systems are behaviorally equivalent iff they produce
    the same observations on ALL inputs.

    This is the SHARP definition: not "similar enough" but
    "identical on the observation boundary". -/
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

/-- Core lemma: systems with identical primitive flags behave identically.

    This is the computational content: Behavior only inspects
    has_shared_records, enables_reliance, and supports_correction.
    The resists_adversaries flag is included for completeness but not used by Behavior. -/
theorem same_flags_same_behavior (W1 W2 : WorkingSystem)
    (h_records : W1.has_shared_records = W2.has_shared_records)
    (h_reliance : W1.enables_reliance = W2.enables_reliance)
    (h_correction : W1.supports_correction = W2.supports_correction)
    (_h_adversaries : W1.resists_adversaries = W2.resists_adversaries) :
    BehaviorallyEquivalent W1 W2 := by
  intro i
  simp [Behavior]
  cases i with
  | WithdrawRequest agent_id bubble_id claim_id =>
    simp [h_records, h_reliance]
  | ExportRequest source target claim_id =>
    simp [h_records, h_reliance]
  | ChallengeRequest claim_id field =>
    simp [h_correction]
  | TimeAdvance ticks =>
    rfl

/-- Helper lemma: SatisfiesAllProperties fixes all behavioral flags.

    This is the key computational insight: if a system satisfies all properties,
    we know exactly what its flags must be. -/
theorem satisfies_all_fixes_flags (W : WorkingSystem) (h : SatisfiesAllProperties W) :
    W.has_shared_records = true ∧
    W.enables_reliance = true ∧
    W.supports_correction = true ∧
    W.resists_adversaries = true := by
  have ⟨h1, h2, _h3, h4, _h5, _h6⟩ := h
  -- h1: handles_distributed_agents W = (W.has_shared_records = true)
  -- h2: handles_bounded_audit W = (W.enables_reliance = true)
  -- h4: handles_adversarial W = (W.supports_correction = true ∧ W.resists_adversaries = true)
  unfold handles_distributed_agents at h1
  unfold handles_bounded_audit at h2
  unfold handles_adversarial at h4
  exact ⟨h1, h2, h4.1, h4.2⟩

/-- Main behavioral equivalence theorem: systems satisfying all properties behave identically.
    Proof: SatisfiesAllProperties fixes all flags, same flags = same behavior. -/
theorem working_systems_equivalent (W1 W2 : WorkingSystem) :
    SatisfiesAllProperties W1 → SatisfiesAllProperties W2 → BehaviorallyEquivalent W1 W2 := by
  intro h_sat1 h_sat2
  have ⟨h1_rec, h1_rel, h1_cor, h1_adv⟩ := satisfies_all_fixes_flags W1 h_sat1
  have ⟨h2_rec, h2_rel, h2_cor, h2_adv⟩ := satisfies_all_fixes_flags W2 h_sat2
  exact same_flags_same_behavior W1 W2
    (h1_rec.trans h2_rec.symm)
    (h1_rel.trans h2_rel.symm)
    (h1_cor.trans h2_cor.symm)
    (h1_adv.trans h2_adv.symm)

/-- Systems with Bank primitives are behaviorally equivalent for coordination.

    containsBankPrimitives implies the SystemSpec has all features, which
    (for well-formed systems) implies the behavioral flags are set correctly.

    Note: This requires bidirectional well-formedness to connect spec features
    to behavioral flags. The `mpr` direction of WellFormed gives us:
    spec feature = true → behavioral flag = true. -/
theorem bank_primitives_determine_behavior (W1 W2 : WorkingSystem)
    (h_wf1 : WellFormed W1) (h_wf2 : WellFormed W2) :
    containsBankPrimitives W1 → containsBankPrimitives W2 →
    BehaviorallyEquivalent W1 W2 := by
  intro h1 h2
  -- containsBankPrimitives unfolds to Has* conjunctions
  unfold containsBankPrimitives at h1 h2
  have ⟨hB1, hT1, _hH1, hR1, _hK1, hD1⟩ := h1
  have ⟨hB2, hT2, _hH2, hR2, _hK2, hD2⟩ := h2
  -- Has* are definitional: HasBubbles W = W.spec.has_bubble_separation = true
  unfold HasBubbles HasTrustBridges HasHeaders HasRevocation HasBank HasRedeemability at *
  -- Use bidirectional WellFormed to derive flag values from spec features
  -- WellFormed.1.mpr: spec.has_bubble_separation = true → has_shared_records = true
  have h1_rec : W1.has_shared_records = true := h_wf1.1.mpr hB1
  have h1_rel : W1.enables_reliance = true := h_wf1.2.1.mpr hT1
  have h1_cor : W1.supports_correction = true := h_wf1.2.2.2.2.2.mpr hD1
  -- For resists_adversaries, we need to extract from the revocation ↔
  -- WellFormed says: (supports_correction ∧ resists_adversaries) ↔ has_revocation
  have h1_adv_pair : W1.supports_correction = true ∧ W1.resists_adversaries = true :=
    h_wf1.2.2.2.1.mpr hR1
  have h1_adv : W1.resists_adversaries = true := h1_adv_pair.2
  -- Same for W2
  have h2_rec : W2.has_shared_records = true := h_wf2.1.mpr hB2
  have h2_rel : W2.enables_reliance = true := h_wf2.2.1.mpr hT2
  have h2_cor : W2.supports_correction = true := h_wf2.2.2.2.2.2.mpr hD2
  have h2_adv_pair : W2.supports_correction = true ∧ W2.resists_adversaries = true :=
    h_wf2.2.2.2.1.mpr hR2
  have h2_adv : W2.resists_adversaries = true := h2_adv_pair.2
  -- Now apply same_flags_same_behavior
  exact same_flags_same_behavior W1 W2
    (h1_rec.trans h2_rec.symm)
    (h1_rel.trans h2_rel.symm)
    (h1_cor.trans h2_cor.symm)
    (h1_adv.trans h2_adv.symm)

end EpArch
