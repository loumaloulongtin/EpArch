/-
EpArch.Agent.PatternExamples — Pedagogical Pattern Annex

Concrete instantiations of the design-imposition results from
EpArch.Agent.Imposition, restated over Bool/Nat-valued state structures.

This file is a pedagogical annex, not part of the EpArch kernel; it is
never imported by any kernel module.

The kernel theorems in Imposition.lean work over abstract Prop-valued
predicates (AgentConstraints, ScenarioGoal, ¬Mechanism → False).  The
theorems here restate the same patterns with concrete field-level states
that can be read without knowing the full architecture.  Each item's
doc-comment names the kernel theorem it instantiates; follow those links
to reach the load-bearing architectural claim.

- irreversibility_violates_safety    (→ safe_withdrawal_needs_reversibility)
- safe_withdrawal_implies_reversibility (→ safe_withdrawal_needs_reversibility)
- no_validator_blocks_expensive_claims (→ sound_deposits_need_cheap_validator)
- no_gate_allows_error_propagation   (→ reliable_export_needs_gate)
-/

namespace EpArch.Agent.PatternExamples

/-! ## Withdrawal Pattern -/

/-- Concrete withdrawal state: tracks whether a mistake can be corrected.

    Carrier for the withdrawal-safety pattern instantiated by
    `irreversibility_violates_safety` and `safe_withdrawal_implies_reversibility`. -/
structure WithdrawalState where
  /-- Has a withdrawal been executed? -/
  withdrawn : Bool
  /-- Was the withdrawal based on a mistake? -/
  wasMistake : Bool
  /-- Can the mistake be corrected? (requires reversibility) -/
  canCorrect : Bool

/-- A withdrawal is "safe" if mistakes can be corrected. -/
def SafeWithdrawalOutcome (s : WithdrawalState) : Prop :=
  s.withdrawn ∧ s.wasMistake → s.canCorrect

/-- Without reversibility, mistakes cannot be corrected. -/
def IrreversibleWithdrawal (s : WithdrawalState) : Prop :=
  s.withdrawn → ¬s.canCorrect

/-- Instantiates `safe_withdrawal_needs_reversibility` (EpArch.Agent.Imposition)
    over a concrete WithdrawalState — contrapositive direction.

    **Theorem shape:** IrreversibleWithdrawal + withdrawn + wasMistake → ¬SafeWithdrawalOutcome.
    **Proof strategy:** Assume SafeWithdrawalOutcome; extract canCorrect from the pair;
    contradict IrreversibleWithdrawal which denies canCorrect when withdrawn. -/
theorem irreversibility_violates_safety
    (s : WithdrawalState)
    (h_irrev : IrreversibleWithdrawal s)
    (h_withdrawn : s.withdrawn)
    (h_mistake : s.wasMistake) :
    ¬ SafeWithdrawalOutcome s := by
  intro h_safe
  have h_can := h_safe ⟨h_withdrawn, h_mistake⟩
  exact h_irrev h_withdrawn h_can

/-- Instantiates `safe_withdrawal_needs_reversibility` (EpArch.Agent.Imposition)
    over a concrete WithdrawalState — forward extraction direction.

    **Theorem shape:** withdrawn + wasMistake + SafeWithdrawalOutcome → canCorrect.
    **Proof strategy:** Direct application of the SafeWithdrawalOutcome definition. -/
theorem safe_withdrawal_implies_reversibility
    (s : WithdrawalState)
    (h_withdrawn : s.withdrawn)
    (h_mistake : s.wasMistake)
    (h_safe : SafeWithdrawalOutcome s) :
    s.canCorrect :=
  h_safe ⟨h_withdrawn, h_mistake⟩

/-! ## Verification Pattern -/

/-- Concrete deposit verification state.

    Carrier for the cheap-validator pattern instantiated by
    `no_validator_blocks_expensive_claims`. -/
structure VerificationState where
  /-- Cost to verify -/
  verifyCost : Nat
  /-- Available budget -/
  budget : Nat
  /-- Is there a cheap validator? -/
  hasCheapValidator : Bool
  /-- Validator cost (if exists) -/
  validatorCost : Nat

/-- A deposit is "sound" if it can be verified within budget. -/
def CanVerify (s : VerificationState) : Prop :=
  s.verifyCost ≤ s.budget ∨ (s.hasCheapValidator ∧ s.validatorCost ≤ s.budget)

/-- Instantiates `sound_deposits_need_cheap_validator` (EpArch.Agent.Imposition)
    over a concrete VerificationState.

    **Theorem shape:** expensive claim + no cheap validator → ¬CanVerify.
    **Proof strategy:** Case-split on CanVerify; direct branch contradicts the
    budget bound; cheap-validator branch contradicts h_no_validator. -/
theorem no_validator_blocks_expensive_claims
    (s : VerificationState)
    (h_expensive : s.verifyCost > s.budget)
    (h_no_validator : ¬s.hasCheapValidator) :
    ¬ CanVerify s := by
  intro h_can
  cases h_can with
  | inl h_direct => exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_expensive h_direct)
  | inr h_cheap => exact h_no_validator h_cheap.1

/-! ## Export Pattern -/

/-- Concrete export state.

    Carrier for the export-gate pattern instantiated by
    `no_gate_allows_error_propagation`. -/
structure ExportState where
  /-- Is the observation correct? -/
  correctObservation : Bool
  /-- Is there a gate check? -/
  hasGate : Bool
  /-- Does the gate catch errors? -/
  gateCatchesErrors : Bool

/-- An export is "reliable" if errors don't propagate. -/
def ReliableExport (s : ExportState) : Prop :=
  ¬s.correctObservation → (s.hasGate ∧ s.gateCatchesErrors)

/-- Instantiates `reliable_export_needs_gate` (EpArch.Agent.Imposition)
    over a concrete ExportState.

    **Theorem shape:** incorrect observation + no gate → ¬ReliableExport.
    **Proof strategy:** Apply ReliableExport with h_incorrect to obtain the gate pair;
    extract hasGate and contradict h_no_gate. -/
theorem no_gate_allows_error_propagation
    (s : ExportState)
    (h_incorrect : ¬s.correctObservation)
    (h_no_gate : ¬s.hasGate) :
    ¬ ReliableExport s := by
  intro h_reliable
  have ⟨h_gate, _⟩ := h_reliable h_incorrect
  exact h_no_gate h_gate

end EpArch.Agent.PatternExamples
