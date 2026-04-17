/-
EpArch.Concrete.NonVacuity — Advanced Non-Vacuity Proofs

Concrete witnesses and proofs for competition gates, legibility,
repair paths, convergence metrics, step-preserved invariants,
and modal links.

Part of the EpArch.Concrete module family.
-/

import EpArch.Concrete.WorkingSystem
import EpArch.Semantics.StepSemantics
import EpArch.Theorems.Strip

namespace EpArch.ConcreteInstance

open EpArch

/-! ## Advanced Non-Vacuity Proofs

These sections demonstrate non-vacuity for the StepSemantics module by
constructing concrete traces and showing revision is genuinely possible.

Since EpArch.Basic now uses concrete inductives (Nat-indexed) rather than
opaque types, we can provide actual witness values without axioms. -/

open EpArch.StepSemantics
open ConcreteModel

/-! ## Concrete Witnesses for Base Types

These definitions provide canonical inhabitants for the base types.
No axioms needed because Bubble/Agent/ACL/ConstraintSurface are now
concrete inductives in EpArch.Basic. -/

/-- Witness bubble for concrete model. -/
def concreteBubble : Bubble := Bubble.mk 0

/-- Witness agent for concrete model. -/
def concreteAgent : Agent := Agent.mk 0

/-- A second bubble for export examples. -/
def concreteBubble2 : Bubble := Bubble.mk 1

/-- Bubbles are distinct (for meaningful export). -/
theorem bubbles_distinct : concreteBubble ≠ concreteBubble2 := by decide

/-- Witness ACL. -/
def concreteACL : ACL := ACL.mk 0

/-- Witness ConstraintSurface. -/
def concreteCS : ConstraintSurface := ConstraintSurface.mk 0

/-! ## Concrete Header Construction -/

/-- A concrete header using our concrete types.
    No longer noncomputable since all witnesses are concrete. -/
def concreteHeader : Header CStandard String String := {
  S := (90 : Nat)
  E := "possible measurement error"
  V := "peer reviewed source"
  τ := 1000
  acl := concreteACL
  redeem := concreteCS
}

/-! ## Concrete Deposit (Abstract Type) -/

/-- A concrete deposit using the abstract Deposit type from EpArch.Header.
    Bridges the concrete model to the abstract StepSemantics. CProp = String. -/
def witness_deposit : Deposit String CStandard String String := {
  P := "test_claim"
  h := concreteHeader
  bubble := concreteBubble
  status := .Deposited
}

/-! ## Conversion Functions -/

/-- Convert a CDeposit to the abstract Deposit type. -/
def toConcreteDep (cd : CDeposit) : Deposit String CStandard String String := {
  P := cd.claim
  h := {
    S := cd.S
    E := cd.E.head?.getD ""
    V := cd.V.head?.getD ""
    τ := cd.τ
    acl := concreteACL
    redeem := concreteCS
  }
  bubble := concreteBubble
  status := .Deposited
}

/-! ## Non-Vacuity for Competition Gate Theorem -/

/-- A concrete system state with one deposited entry. -/
def initialConcreteState7 : SystemState String CStandard String String := {
  ledger := [witness_deposit]
  bubbles := [concreteBubble]
  clock := 50
  acl_table := [{ agent := concreteAgent, bubble := concreteBubble, deposit_id := 0 }]
  trust_bridges := []
}

/-- A concrete challenge targeting the first deposit. -/
def concreteChallenge7 : EpArch.Challenge String String String := {
  P := "test_claim"
  reason := "provenance unverified"
  evidence := "no independent confirmation"
  suspected := .V
}

/-- The initial state has a deposited entry at index 0. -/
theorem initial_has_deposited7 : isDeposited initialConcreteState7 0 := by
  unfold isDeposited initialConcreteState7
  refine ⟨witness_deposit, rfl, rfl⟩

/-- After challenge, the deposit is quarantined. -/
def stateAfterChallenge7 : SystemState String CStandard String String := {
  ledger := [{ witness_deposit with status := .Quarantined }]
  bubbles := [concreteBubble]
  clock := 50
  acl_table := [{ agent := concreteAgent, bubble := concreteBubble, deposit_id := 0 }]
  trust_bridges := []
}

/-- The quarantined state has quarantine at index 0. -/
theorem challenge_produces_quarantine7 : isQuarantined stateAfterChallenge7 0 := by
  unfold isQuarantined stateAfterChallenge7
  exact ⟨{ witness_deposit with status := .Quarantined }, rfl, rfl⟩

/-- After revoke, the deposit is revoked. -/
def stateAfterRevoke7 : SystemState String CStandard String String := {
  ledger := [{ witness_deposit with status := .Revoked }]
  bubbles := [concreteBubble]
  clock := 50
  acl_table := [{ agent := concreteAgent, bubble := concreteBubble, deposit_id := 0 }]
  trust_bridges := []
}

/-- A Challenge action is a revision action. -/
theorem challenge_is_revision7 :
    (Action.Challenge (PropLike := String) (Standard := CStandard)
      (ErrorModel := String) (Provenance := String)
      (Reason := String) (Evidence := String) concreteChallenge7).isRevision = true := rfl

/-- A Revoke action is a revision action. -/
theorem revoke_is_revision7 :
    (Action.Revoke (PropLike := String) (Standard := CStandard)
      (ErrorModel := String) (Provenance := String)
      (Reason := String) (Evidence := String) 0).isRevision = true := rfl

/-! ### Explicit Trace Construction

We construct the trace explicitly using Step constructors, removing the need
for trace proofs. The key is proving that state transformations match. -/

/-- The intermediate state after challenge matches stateAfterChallenge7. -/
theorem challenge_step_state_eq :
    { initialConcreteState7 with
      ledger := updateDepositStatus initialConcreteState7.ledger 0 .Quarantined } =
    stateAfterChallenge7 := by
  simp only [initialConcreteState7, stateAfterChallenge7, updateDepositStatus, modifyAt]
  rfl

/-- The final state after revoke matches stateAfterRevoke7. -/
theorem revoke_step_state_eq :
    { stateAfterChallenge7 with
      ledger := updateDepositStatus stateAfterChallenge7.ledger 0 .Revoked } =
    stateAfterRevoke7 := by
  simp only [stateAfterChallenge7, stateAfterRevoke7, updateDepositStatus, modifyAt]
  rfl

/-- The challenge step from initial to quarantined state. -/
def challenge_step7 : Step (Reason := String) (Evidence := String)
    initialConcreteState7
    (.Challenge concreteChallenge7)
    { initialConcreteState7 with ledger := updateDepositStatus initialConcreteState7.ledger 0 .Quarantined } :=
  Step.challenge initialConcreteState7 concreteChallenge7 0 initial_has_deposited7

/-- The revoke step from quarantined to revoked state. -/
def revoke_step7 : Step (Reason := String) (Evidence := String)
    stateAfterChallenge7
    (.Revoke 0)
    { stateAfterChallenge7 with ledger := updateDepositStatus stateAfterChallenge7.ledger 0 .Revoked } :=
  Step.revoke stateAfterChallenge7 0 challenge_produces_quarantine7

/-- Explicit trace from initial to revoked state (Challenge then Revoke).
    This replaces the axiom concrete_resolution_trace9. -/
def concrete_trace : Trace (Reason := String) (Evidence := String)
    initialConcreteState7 stateAfterRevoke7 :=
  -- Challenge step: initial → quarantined
  Trace.cons (.Challenge concreteChallenge7)
    (challenge_step_state_eq ▸ challenge_step7)
    -- Revoke step: quarantined → revoked
    (Trace.cons (.Revoke 0)
      (revoke_step_state_eq ▸ revoke_step7)
      -- End of trace
      (Trace.nil stateAfterRevoke7))

/-- The concrete trace has revision actions. -/
theorem concrete_trace_hasRevision : concrete_trace.hasRevision = true := by
  unfold concrete_trace Trace.hasRevision Action.isRevision
  rfl

/-- Non-`axiom` version: A concrete trace exists from initial to revoked state. -/
theorem concrete_revision_trace_exists' :
    ∃ (t : Trace (Reason := String) (Evidence := String)
        initialConcreteState7 stateAfterRevoke7),
      t.hasRevision = true :=
  ⟨concrete_trace, concrete_trace_hasRevision⟩

/-- The concrete model ALLOWS revision: we can construct a trace with revision actions.

    This is the NON-VACUITY proof for the competition gate theorem. -/
theorem concrete_model_allows_revision7 :
    ∃ (s s' : SystemState String CStandard String String)
      (t : Trace (Reason := String) (Evidence := String) s s'),
      t.hasRevision = true :=
  ⟨initialConcreteState7, stateAfterRevoke7, concrete_trace, concrete_trace_hasRevision⟩

/-- The concrete model supports self-correction: Deposited → Quarantined path exists. -/
theorem concrete_model_supports_self_correction7 :
    ∃ (d_idx : Nat),
      isDeposited initialConcreteState7 d_idx ∧
      isQuarantined stateAfterChallenge7 d_idx :=
  ⟨0, initial_has_deposited7, challenge_produces_quarantine7⟩


/-! ## Non-Vacuity: Legibility -/

/-- All concrete deposits have S/E/V factorization by construction. -/
theorem concrete_has_factorization8 (d : CDeposit) :
    has_SEV_factorization (PropLike := String) (Standard := CStandard)
      (ErrorModel := String) (Provenance := String) (toConcreteDep d) := by
  unfold has_SEV_factorization
  trivial

/-- Concrete model has repair paths: deposited claims can be challenged. -/
theorem concrete_has_repair_path8 :
    HasRepairPath initialConcreteState7 0 .V := by
  unfold HasRepairPath
  constructor
  · exact initial_has_deposited7
  · -- V is in the Field list
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- Concrete model demonstrates legibility: broken fields are identifiable. -/
theorem concrete_legibility_witness8 :
    ∃ (BrokenField : Deposit String CStandard String String → Field → Prop),
      Legible initialConcreteState7 0 BrokenField := by
  -- Use a BrokenField predicate that says V (provenance) is broken
  refine ⟨fun _ f => f = .V, ?_⟩
  unfold Legible
  -- ∃ f : Field, (∃ d, get? 0 = some d ∧ BrokenField d f) ∧ HasRepairPath
  refine ⟨.V, ?_, concrete_has_repair_path8⟩
  -- ∃ d, ledger.get? 0 = some d ∧ BrokenField d .V
  -- BrokenField d .V = (fun _ f => f = .V) d .V = (.V = .V)
  unfold initialConcreteState7
  -- Get the deposit at index 0
  refine ⟨witness_deposit, ?_, ?_⟩
  · -- ledger.get? 0 = some witness_deposit
    rfl
  · -- BrokenField witness_deposit .V
    rfl


/-! ## Non-Vacuity: Convergence Metrics -/

/-- The state after challenge equals updateDepositStatus applied to initial state. -/
theorem stateAfterChallenge_eq :
    stateAfterChallenge7 = { initialConcreteState7 with
      ledger := updateDepositStatus initialConcreteState7.ledger 0 .Quarantined } := by
  unfold stateAfterChallenge7 initialConcreteState7 updateDepositStatus modifyAt
  simp only [List.get?, witness_deposit]
  rfl

/-- The state after revoke equals updateDepositStatus applied to quarantined state. -/
theorem stateAfterRevoke_eq :
    stateAfterRevoke7 = { stateAfterChallenge7 with
      ledger := updateDepositStatus stateAfterChallenge7.ledger 0 .Revoked } := by
  unfold stateAfterRevoke7 stateAfterChallenge7 updateDepositStatus modifyAt
  simp only [List.get?, witness_deposit]
  rfl

/-- After revoke, the deposit at index 0 is resolved (has Revoked status). -/
theorem revoke_produces_resolved7 : isResolved stateAfterRevoke7 0 := by
  unfold isResolved stateAfterRevoke7
  exact ⟨{ witness_deposit with status := .Revoked }, rfl, rfl⟩

/-- A concrete trace of length 2: Challenge then Revoke.
    Defined explicitly using concrete_trace (no Lean axiom). -/
def concrete_resolution_trace9 :
    Trace (Reason := String) (Evidence := String)
      initialConcreteState7 stateAfterRevoke7 :=
  concrete_trace

/-- The trace has length 2 (Challenge then Revoke). -/
theorem concrete_trace_length_fact : concrete_resolution_trace9.length = 2 := by
  unfold concrete_resolution_trace9 concrete_trace Trace.length
  rfl

/-- The concrete resolution trace has length 2. -/
theorem concrete_trace_length9 :
    concrete_resolution_trace9.length = 2 := concrete_trace_length_fact

/-- The concrete model demonstrates convergence: deposits can reach resolution. -/
theorem concrete_converges9 :
    converges (Reason := String) (Evidence := String) initialConcreteState7 0 :=
  ⟨stateAfterRevoke7, concrete_resolution_trace9, initial_has_deposited7, revoke_produces_resolved7⟩

/-- The concrete challenge is field-specific (targets V). -/
theorem concrete_challenge_field_specific9 :
    challenge_is_field_specific concreteChallenge7 := by
  unfold challenge_is_field_specific concreteChallenge7
  decide

/-- A convergence witness for the concrete model with time = 2.
    Computable since concrete_resolution_trace9 is explicit. -/
def concrete_convergence_witness9 :
    ConvergenceWitness (Reason := String) (Evidence := String) initialConcreteState7 0 :=
  { final_state := stateAfterRevoke7
    trace := concrete_resolution_trace9
    resolves := ⟨initial_has_deposited7, revoke_produces_resolved7⟩ }

/-- The concrete convergence witness has time = 2. -/
theorem concrete_convergence_time9 :
    concrete_convergence_witness9.time = 2 := concrete_trace_length_fact


/-! ## Non-Vacuity Proofs for Step-Preserved Invariants -/

/-- The initial concrete state satisfies inv_valid_status. -/
theorem initial_satisfies_valid_status10 :
    inv_valid_status initialConcreteState7 := by
  unfold inv_valid_status initialConcreteState7
  intro d hd
  -- d is in [witness_deposit], so d = witness_deposit
  cases hd with
  | head => simp only [witness_deposit]; exact List.Mem.head _
  | tail _ h => cases h

/-- The initial concrete state satisfies inv_acl_indices_valid. -/
theorem initial_satisfies_acl_indices10 :
    inv_acl_indices_valid initialConcreteState7 := by
  unfold inv_acl_indices_valid initialConcreteState7
  intro entry hentry
  -- entry is the single ACL entry with deposit_id = 0
  -- ledger has length 1, so 0 < 1
  cases hentry with
  | head =>
    -- The entry has deposit_id = 0, and ledger.length = 1
    simp only [List.length]
    decide
  | tail _ h => cases h

/-- The initial concrete state satisfies inv_bubbles_exist. -/
theorem initial_satisfies_bubbles_exist10 :
    inv_bubbles_exist initialConcreteState7 := by
  unfold inv_bubbles_exist initialConcreteState7
  intro d hd
  -- d = witness_deposit whose bubble = concreteBubble
  -- initialConcreteState7.bubbles = [concreteBubble]
  cases hd with
  | head =>
    -- d = witness_deposit, d.bubble = concreteBubble
    simp only [witness_deposit]
    exact List.Mem.head _
  | tail _ h => cases h

/-- The initial concrete state is well-formed. -/
theorem initial_is_well_formed10 :
    WellFormedState initialConcreteState7 := by
  unfold WellFormedState
  exact ⟨initial_satisfies_valid_status10,
         initial_satisfies_acl_indices10,
         initial_satisfies_bubbles_exist10⟩

/-- Non-vacuity: WellFormedState has concrete instances. -/
noncomputable example : ∃ s : SystemState String CStandard String String, WellFormedState s :=
  ⟨initialConcreteState7, initial_is_well_formed10⟩

/-- Non-vacuity: Step preservation is meaningful (trace exists that exercises it). -/
theorem concrete_step_preservation_example10 : ∃ (s s' : SystemState String CStandard String String),
    ∃ t : Trace (Reason := String) (Evidence := String) s s',
    inv_valid_status s ∧ t.length > 0 :=
  ⟨initialConcreteState7, stateAfterRevoke7, concrete_resolution_trace9,
   initial_satisfies_valid_status10,
   by rw [concrete_trace_length_fact]; decide⟩


/-! ## Competition Gate Non-Vacuity Summary

    This section demonstrates that all competition gate theorems
    apply NON-VACUOUSLY to the concrete model.

    **Key insight:** The concrete model is a satisfiability witness.
    It shows that:
    1. The axioms are consistent (have at least one model)
    2. The competition gate theorems have non-trivial instantiations
    3. The formalization describes a realizable system, not just a story -/

/-- COMPETITION GATE NON-VACUITY 1: Self-correction exists in the concrete model.

    The concrete model demonstrates a path from Deposited → Revoked,
    which is what `Trace.demonstratesSelfCorrection` requires.

    This shows `self_correction_requires_revision` has non-trivial instances. -/
theorem competition_gate_non_vacuity_self_correction :
    ∃ (s s' : SystemState String CStandard String String)
      (_t : Trace (Reason := String) (Evidence := String) s s')
      (d_idx : Nat),
      isDeposited s d_idx ∧
      (∃ d, s'.ledger.get? d_idx = some d ∧ d.status = .Revoked) := by
  -- Use the concrete states and axiomatized trace
  refine ⟨initialConcreteState7, stateAfterRevoke7, concrete_resolution_trace9, 0, ?_⟩
  constructor
  · -- Initial state has deposit at index 0
    exact initial_has_deposited7
  · -- Final state has Revoked at index 0
    unfold stateAfterRevoke7
    exact ⟨{ witness_deposit with status := .Revoked }, rfl, rfl⟩

/-- COMPETITION GATE NON-VACUITY 2: Revision exists in the concrete model.

    The concrete model permits revision (has traces with Challenge/Revoke).
    This shows `no_revision_no_correction` has a non-trivial contrapositive:
    some domains DO permit revision and CAN self-correct. -/
theorem competition_gate_non_vacuity_revision :
    ∃ (s : SystemState String CStandard String String),
      ¬StepSemantics.prohibits_revision (Reason := String) (Evidence := String) s := by
  refine ⟨initialConcreteState7, ?_⟩
  -- By self_correcting_domain_permits_revision, we need a self-correcting trace
  -- We have concrete_model_allows_revision7 which gives us t.hasRevision = true
  intro h_prohibits
  have h_false : concrete_trace.hasRevision = false := h_prohibits stateAfterRevoke7 concrete_trace
  rw [concrete_trace_hasRevision] at h_false
  exact Bool.noConfusion h_false

/-- COMPETITION GATE NON-VACUITY 3: Stripping is non-injective.

    Two deposits with different headers but identical P/bubble/status
    have the same stripped form — information is genuinely lost on export.
    Witnessed by `witness_deposit` (S=90) vs a variant with S=80. -/
theorem competition_gate_non_vacuity_stripping :
    ∃ (d1 d2 : Deposit String CStandard String String),
      d1 ≠ d2 ∧ strip d1 = strip d2 := by
  let d1 : Deposit String CStandard String String := witness_deposit
  let d2 : Deposit String CStandard String String :=
    { witness_deposit with h := { concreteHeader with S := 80 } }
  have h_diff_header : d1.h ≠ d2.h := by
    intro hh
    have h_S := congrArg Header.S hh
    simp only [d1, d2, concreteHeader] at h_S
    exact absurd h_S (by decide)
  have h_ineq_strip := different_headers_same_strip d1 d2 rfl rfl rfl h_diff_header
  exact ⟨d1, d2, h_ineq_strip.1, h_ineq_strip.2⟩

/-! ## Summary: The competition gate is not vacuously true.

    We have shown:
    1. Self-correction exists (concrete trace from Deposited to Revoked)
    2. Revision exists (concrete trace with hasRevision = true)
    3. Non-prohibiting states exist (initialConcreteState7)
    4. Stripping is non-injective: two distinct deposits have the same stripped
       form, so header information is genuinely lost on export (S=90 vs S=80)

    Therefore when we prove "prohibits_revision → no self-correction",
    the antecedent is not trivially false — there ARE states that
    don't prohibit revision, and they CAN self-correct.

    This separates revision-prohibiting from revision-permitting domains. -/


end EpArch.ConcreteInstance
