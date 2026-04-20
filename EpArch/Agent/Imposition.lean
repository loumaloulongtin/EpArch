/-
EpArch.Agent.Imposition — Design-Imposition Theorems

This module captures design-necessity results: architectural forcing constraints
that state certain combinations (goal + constraints + no mechanism) are impossible.

## Pattern

  Scenario (embedding constraints) + SystemHealth goal + ¬Mechanism → contradiction

## Approach

1. Define Health Goals as PURE OUTCOME predicates (not mechanism-dependent)
2. Define what mechanisms provide (capability predicates)
3. Construct counterexample showing: constraints + no mechanism → goal violation

## Contents

- Mechanism and health goal structures
- Counterexample constructions
- PROVED necessity theorems (not axioms)

-/

import EpArch.Agent.Constraints
import EpArch.Health

namespace EpArch.Agent

universe u

/-! ## Abstract Mechanism Capabilities -/

/-- What reversibility provides: ability to undo actions. -/
structure ReversibilityCapability (State : Type u) where
  /-- Undo function exists -/
  undo : State → State
  /-- Undo is an involution: applying it twice returns the original state.      This is genuine proof content — the caller must supply an `undo` function      that satisfies this property, not just any function. -/
  undo_restores : ∀ s, undo (undo s) = s

/-- What cheap validators provide: verification within bounded cost. -/
structure ValidatorCapability (Claim : Type u) where
  /-- Validator cost for a claim -/
  validatorCost : Claim → Nat
  /-- Upper bound on validator cost -/
  costBound : Nat
  /-- Validator is cheap -/
  is_cheap : ∀ c, validatorCost c ≤ costBound

/-- What export gates provide: error interception. -/
structure GateCapability (Claim : Type u) where
  /-- Gate check function -/
  check : Claim → Bool
  /-- Gate catches errors (non-trivial) -/
  catches_some : ∃ c, check c = false


/-! ## Health Goals as PURE OUTCOME Predicates

Key insight: Goals must be defined WITHOUT referencing mechanisms.
Otherwise "Goal → Mechanism" is circular.
-/

/-- Safe withdrawal: mistakes don't cause permanent harm.

    Defined in terms of OUTCOMES, not mechanisms:
    - If a withdrawal was mistaken, the harm is bounded/recoverable. -/
def SafeWithdrawalGoal (mistakeOccurred : Prop) (harmIsPermanent : Prop) : Prop :=
  mistakeOccurred → ¬harmIsPermanent

/-- Sound deposits: only verified claims become trusted.

    Defined as: high-cost claims don't exceed verification capacity. -/
def SoundDepositsGoal (claimCost : Nat) (verificationBudget : Nat) : Prop :=
  claimCost ≤ verificationBudget

/-- Reliable export: errors don't propagate silently.

    Defined as: if observation incorrect, export blocked or flagged. -/
def ReliableExportGoal (observationCorrect : Prop) (exportBlocked : Prop) : Prop :=
  ¬observationCorrect → exportBlocked


/-! ## Counterexample Construction: Reversibility Necessity

Theorem: If agents make mistakes (boundedVerification implies finite τ),
         and there's no reversibility,
         then safe withdrawal goal is violated.
-/

/-- A withdrawal scenario: models the situation for counterexample. -/
structure WithdrawalScenario where
  /-- A mistake was made -/
  mistakeOccurred : Bool
  /-- Without reversibility, harm is permanent -/
  harmIsPermanent : Bool
  /-- Is reversibility available? -/
  hasReversibility : Prop
  /-- Invariant: without reversibility, mistakes cause permanent harm -/
  no_rev_permanent : ¬hasReversibility → mistakeOccurred = true → harmIsPermanent = true

/-- Counterexample: withdrawal scenario where no reversibility → goal fails. -/
def withdrawal_counterexample : WithdrawalScenario where
  mistakeOccurred := true
  harmIsPermanent := true
  hasReversibility := False
  no_rev_permanent := fun _ _ => rfl

/-- THEOREM (was axiom): Safe withdrawal needs reversibility.

    Proof by counterexample:
    1. Construct scenario where mistake occurred, no reversibility
    2. By no_rev_permanent, harm is permanent
    3. SafeWithdrawalGoal requires: mistake → ¬permanent harm
    4. We have: mistake ∧ permanent harm → contradiction -/
theorem safe_withdrawal_needs_reversibility
    (scenario : WithdrawalScenario)
    (h_mistake : scenario.mistakeOccurred = true)
    (h_no_rev : ¬scenario.hasReversibility)
    (h_goal : SafeWithdrawalGoal (scenario.mistakeOccurred = true) (scenario.harmIsPermanent = true)) :
    False := by
  -- By the scenario invariant: no reversibility + mistake → permanent harm
  have h_permanent := scenario.no_rev_permanent h_no_rev h_mistake
  -- Goal says: mistake → ¬permanent
  have h_not_permanent := h_goal h_mistake
  -- But h_permanent says it IS permanent
  exact h_not_permanent h_permanent


/-! ## Counterexample Construction: Validator Necessity

Theorem: If PRP generates high-cost claims exceeding budget,
         and there's no cheap validator,
         then sound deposits goal is violated.
-/

/-- A deposit scenario: models verification situation. -/
structure DepositScenario where
  /-- Cost of the claim -/
  claimCost : Nat
  /-- Verification budget -/
  budget : Nat
  /-- Validator cost (if exists) -/
  validatorCost : Nat
  /-- Is cheap validator available? -/
  hasValidator : Prop
  /-- PRP guarantees: some claims exceed budget -/
  prp_pressure : claimCost > budget
  /-- Without validator, must pay full claim cost -/
  no_validator_full_cost : ¬hasValidator → validatorCost = claimCost

/-- Counterexample: deposit scenario where no validator → goal fails. -/
def deposit_counterexample (budget : Nat) : DepositScenario where
  claimCost := budget + 1
  budget := budget
  validatorCost := budget + 1
  hasValidator := False
  prp_pressure := Nat.lt_succ_self budget
  no_validator_full_cost := fun _ => rfl

/-- THEOREM: Sound deposits need cheap validator.

    **Theorem shape:** ¬hasValidator → SoundDepositsGoal validatorCost budget → False.
    **Proof strategy:** `h_no_validator` feeds `no_validator_full_cost`, which gives
    `validatorCost = claimCost`. Rewriting the goal yields `claimCost ≤ budget`,
    which contradicts `prp_pressure : claimCost > budget`.

    The goal is stated over `validatorCost` (the effective verification cost), not
    `claimCost`. Without a validator the two are equal (by `no_validator_full_cost`),
    so `h_no_validator` is load-bearing: it is the hypothesis that makes the
    effective cost equal the raw claim cost, and therefore exceed budget. -/
theorem sound_deposits_need_cheap_validator
    (scenario : DepositScenario)
    (h_no_validator : ¬scenario.hasValidator)
    (h_goal : SoundDepositsGoal scenario.validatorCost scenario.budget) :
    False := by
  -- Without a validator, the effective cost equals the raw claim cost
  have h_eq := scenario.no_validator_full_cost h_no_validator
  -- Rewrite the goal: SoundDepositsGoal validatorCost budget → claimCost ≤ budget
  rw [h_eq] at h_goal
  -- prp_pressure : claimCost > budget contradicts h_goal : claimCost ≤ budget
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le scenario.prp_pressure h_goal)


/-! ## Counterexample Construction: Export Gate Necessity

Theorem: If agents are fallible (can misobserve),
         and there's no export gate,
         then reliable export goal is violated.

Note: this is an agent-level abstract scenario theorem. It is not a CoreModel primitive.
CoreModel reliable export is handled by `Health.ReliableExportGoal` using truth plus
revision capability at the receiving bubble — see `Mechanisms.lean`,
`core_false_positive_violates_reliable_export`.
-/

/-- An export scenario: models error propagation. -/
structure ExportScenario where
  /-- Is observation correct? -/
  observationCorrect : Bool
  /-- Is export blocked? -/
  exportBlocked : Bool
  /-- Is gate available? -/
  hasGate : Prop
  /-- Fallibility: some observations are incorrect -/
  fallible : observationCorrect = false
  /-- Without gate, incorrect observations are exported (not blocked) -/
  no_gate_exports : ¬hasGate → exportBlocked = false

/-- Counterexample: export scenario where no gate → goal fails. -/
def export_counterexample : ExportScenario where
  observationCorrect := false
  exportBlocked := false
  hasGate := False
  fallible := rfl
  no_gate_exports := fun _ => rfl

/-- THEOREM (was axiom): Reliable export needs gate.

    Proof by counterexample:
    1. Fallibility means some observation is incorrect
    2. Without gate, export is not blocked
    3. ReliableExportGoal requires: ¬correct → blocked
    4. We have: ¬correct ∧ ¬blocked → contradiction -/
theorem reliable_export_needs_gate
    (scenario : ExportScenario)
    (h_no_gate : ¬scenario.hasGate)
    (h_goal : ReliableExportGoal (scenario.observationCorrect = true) (scenario.exportBlocked = true)) :
    False := by
  -- Fallibility: observation is incorrect
  have h_incorrect : scenario.observationCorrect = false := scenario.fallible
  have h_not_correct : ¬(scenario.observationCorrect = true) := by simp [h_incorrect]
  -- Without gate, export is not blocked
  have h_not_blocked : scenario.exportBlocked = false := scenario.no_gate_exports h_no_gate
  -- Goal says: ¬correct → blocked
  have h_should_block := h_goal h_not_correct
  -- But export is not blocked
  simp [h_not_blocked] at h_should_block


/-! ## Capability Predicates

These predicates capture "the system has capability X" without reference to
boolean flags. They can later be linked to concrete Bank operators.
-/

/-- Capability: System can reverse withdrawals.
    This is what reversibility PROVIDES as a system capability. -/
def ReversibleWithdrawal (canUndo : Prop) : Prop := canUndo

/-- Capability: System has cheap validator for claims.
    This is what cheap validators PROVIDE as a system capability. -/
def CheapValidatorAvailable (canVerifyCheaply : Prop) : Prop := canVerifyCheaply

/-- Capability: System has export gate that catches errors.
    This is what export gates PROVIDE as a system capability. -/
def ExportGateEnforced (gateBlocks : Prop) : Prop := gateBlocks

/-! ## Capability-Goal Implications

Forward implications: if goal holds, capability must exist.
These follow from the contrapositive theorems above.
-/

/-- Forward implication: Reliable export goal → Export gate capability.
    (When observations can be incorrect, gate is needed.) -/
theorem ReliableExportGoal_implies_ExportGateEnforced
    (observationCorrect exportBlocked : Prop)
    (h_incorrect : ¬observationCorrect)
    (h_goal : ReliableExportGoal observationCorrect exportBlocked) :
    ExportGateEnforced exportBlocked := by
  exact h_goal h_incorrect


/-! ## Legacy Structures (for backward compatibility) -/

/-- Abstract mechanism predicates for design-imposition. -/
structure Mechanisms where
  /-- System has reversibility mechanism -/
  hasReversibility : Prop
  /-- System has cheap validator mechanism -/
  hasCheapValidator : Prop
  /-- System has export gate mechanism -/
  hasExportGate : Prop
  /-- System has revision hooks -/
  hasRevisionHooks : Prop
  /-- System has scoped audit surfaces -/
  hasScopedAudit : Prop

/-! ## Canonical Health Goals Integration

**Design decision:**
- Scenario-based goals (SafeWithdrawalGoal, SoundDepositsGoal, ReliableExportGoal above)
  are for COUNTEREXAMPLE CONSTRUCTION — they take raw Prop parameters.
- EpArch.Health defines CANONICAL system health goals over CoreModel.
- The HealthGoals structure below is a PROP BUNDLE for agent-layer reasoning,
  while EpArch.FullSystemHealth is the model-level specification.

**Relationship:**
- This module proves: AgentConstraints + scenario-goal → mechanism needed
- EpArch.Health proves: CoreModel + definitional-goal → capability exists
- Both are valid; scenario proofs are more direct, model proofs are more general.
-/

/-- Abstract health goals (pure outcomes, not implementation).

    This is the Prop-level bundle for agent reasoning.
    For the canonical CoreModel-level definition, see EpArch.FullSystemHealth. -/
structure HealthGoals where
  /-- Withdrawals are safe (no unilateral extraction) -/
  safeWithdrawal : Prop
  /-- Deposits are sound (verified claims) -/
  soundDeposits : Prop
  /-- Exports are reliable (no silent corruption) -/
  reliableExport : Prop

/-- Bridge: Convert scenario-level goals to a HealthGoals bundle. -/
def toHealthGoals (h_sw : Prop) (h_sd : Prop) (h_re : Prop) : HealthGoals :=
  ⟨h_sw, h_sd, h_re⟩


/-! ## Concrete State Pattern Theorems

These show the pattern in concrete terms, complementing the
counterexample proofs above.
-/

/-- Withdrawal state: tracks whether a mistake can be corrected. -/
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

/-- Pattern theorem: Irreversibility + mistake → unsafe outcome. -/
theorem irreversibility_violates_safety
    (s : WithdrawalState)
    (h_irrev : IrreversibleWithdrawal s)
    (h_withdrawn : s.withdrawn)
    (h_mistake : s.wasMistake) :
    ¬ SafeWithdrawalOutcome s := by
  intro h_safe
  have h_can := h_safe ⟨h_withdrawn, h_mistake⟩
  exact h_irrev h_withdrawn h_can

/-- Pattern theorem: Safe withdrawal requires reversibility. -/
theorem safe_withdrawal_implies_reversibility
    (s : WithdrawalState)
    (h_withdrawn : s.withdrawn)
    (h_mistake : s.wasMistake)
    (h_safe : SafeWithdrawalOutcome s) :
    s.canCorrect :=
  h_safe ⟨h_withdrawn, h_mistake⟩

/-- Deposit verification state. -/
structure VerificationState where
  /-- Cost to verify -/
  verifyCost : Nat
  /-- Available budget -/
  budget : Nat
  /-- Is there a cheap validator? -/
  hasCheapValidator : Bool
  /-- Validator cost (if exists) -/
  validatorCost : Nat

/-- A deposit is "sound" if it's verified within budget. -/
def CanVerify (s : VerificationState) : Prop :=
  s.verifyCost ≤ s.budget ∨ (s.hasCheapValidator ∧ s.validatorCost ≤ s.budget)

/-- Pattern theorem: Without cheap validator, expensive claims can't be verified. -/
theorem no_validator_blocks_expensive_claims
    (s : VerificationState)
    (h_expensive : s.verifyCost > s.budget)
    (h_no_validator : ¬s.hasCheapValidator) :
    ¬ CanVerify s := by
  intro h_can
  cases h_can with
  | inl h_direct => exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_expensive h_direct)
  | inr h_cheap => exact h_no_validator h_cheap.1

/-- Export state. -/
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

/-- Pattern theorem: Without gate, incorrect observations propagate. -/
theorem no_gate_allows_error_propagation
    (s : ExportState)
    (h_incorrect : ¬s.correctObservation)
    (h_no_gate : ¬s.hasGate) :
    ¬ ReliableExport s := by
  intro h_reliable
  have ⟨h_gate, _⟩ := h_reliable h_incorrect
  exact h_no_gate h_gate


end EpArch.Agent
