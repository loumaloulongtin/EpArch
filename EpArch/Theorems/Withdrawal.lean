/-
EpArch.Theorems.Withdrawal — Withdrawal and Repair Theorems

Derived theorems for the operational withdrawal lifecycle:
- Withdrawal gates: ACL + currentness + bank consultation
- Repair enforces revalidation (Candidate status after repair)
-/
import EpArch.Basic
import EpArch.Semantics.StepSemantics
import EpArch.Minimality

namespace EpArch

open StepSemantics

universe u

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}


/-! ## Withdrawal Theorems

The withdrawal gates are defined in terms of the operational LTS
predicates from StepSemantics.  Three gates must all be satisfied:
1. ACL permission
2. Deposit currency (τ not exceeded)
3. Bank consulted (not just remembered)

This is what distinguishes knowledge (Bank) from certainty (Ladder). -/

/-- ACL gate: agent has permission for this deposit in this bubble.
    Definitionally equal to `hasACLPermission`. -/
def ACL_OK_At (s : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat) : Prop :=
  hasACLPermission s a B d_idx

/-- Currentness at a specific state: deposit at index has valid τ.
    Definitionally equal to `isCurrentDeposit`. -/
def Current_At (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) : Prop :=
  isCurrentDeposit s d_idx

/-- Bank consultation gate: deposit is actually in the bank (Deposited status).
    This is the operational meaning of "consulting the bank" — you're not just
    relying on your ladder-side memory, you're checking the shared ledger.
    Definitionally equal to `isDeposited`. -/
def ConsultedBank_At (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) : Prop :=
  isDeposited s d_idx

/-- WITHDRAWAL GATES THEOREM (derived from LTS, no axiom!)

    If Step.withdraw fires, then all three gates must hold.
    This is now a theorem, not an axiom, derived from Step.withdraw's
    constructor preconditions.

    Proof: The Step.withdraw constructor requires hasACLPermission,
    isCurrentDeposit, and isDeposited as explicit hypotheses.
    We just extract them. -/
theorem withdrawal_gates
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (B : Bubble) (a : Agent) (d_idx : Nat)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s') :
    ACL_OK_At s a B d_idx ∧ Current_At s d_idx ∧ ConsultedBank_At s d_idx := by
  -- Directly use the operational theorem from StepSemantics
  exact withdrawal_requires_three_gates s s' a B d_idx h_step


/-! ## Repair Theorems

The repair loop is operational in StepSemantics:
- Step.repair requires Quarantined status (repair_requires_quarantine)
- Step.repair produces Candidate status (repair_produces_candidate)
- This enforces revalidation for any repaired deposit

When a deposit is superseded or repaired, the replacement must go through
acceptance — claims cannot be patched without revalidation. -/

/-- Repair enforces revalidation: after Step.repair, deposit is Candidate.

    This is the operational grounding for supersession_requires_validation.
    The proof follows from repair_produces_candidate in StepSemantics. -/
theorem repair_enforces_revalidation
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) (f : Field)
    (h_step : Step (Reason := Reason) (Evidence := Evidence)
      s (.Repair d_idx f) s') :
    s'.ledger = updateDepositStatus s.ledger d_idx .Candidate :=
  repair_produces_candidate s s' d_idx f h_step

/-- Submit enforces revalidation: new deposits enter as Candidate.

    The Step.submit constructor explicitly sets status := .Candidate. -/
theorem submit_enforces_revalidation
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_step : Step (Reason := Reason) (Evidence := Evidence)
      s (.Submit a d) s') :
    ∃ d', d' ∈ s'.ledger ∧ d'.status = .Candidate := by
  cases h_step
  -- s'.ledger = s.ledger ++ [{ d with status := .Candidate }]
  refine ⟨{ d with status := .Candidate }, ?_, rfl⟩
  -- The appended element is in the appended list
  have h := mem_append_iff { d with status := DepositStatus.Candidate } s.ledger [{ d with status := DepositStatus.Candidate }]
  rw [h]
  exact Or.inr (List.Mem.head _)

/-- The full repair loop requires quarantine first.

    You can't repair something that hasn't been challenged.
    This enforces the Challenge → Quarantine → Repair sequence. -/
theorem repair_requires_prior_challenge
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) (f : Field)
    (h_step : Step (Reason := Reason) (Evidence := Evidence)
      s (.Repair d_idx f) s') :
    isQuarantined s d_idx :=
  repair_requires_quarantine s s' d_idx f h_step

/-! ### Diagnosis Infrastructure

    Made concrete by adding explicit `broken_fields` to deposits.
    This allows `DiagnoseField` to be a computable function rather than axiom. -/

/-- A deposit paired with its diagnosed broken fields.
    Used by `BrokenField` and `DiagnoseField` to enable computable diagnosis. -/
structure DiagnosableDeposit where
  deposit : Deposit PropLike Standard ErrorModel Provenance
  /-- Which fields have been identified as potentially broken. -/
  broken_fields : List Field

def BrokenField (dd : DiagnosableDeposit (PropLike := PropLike)
    (Standard := Standard) (ErrorModel := ErrorModel) (Provenance := Provenance))
    (f : Field) : Prop :=
  f ∈ dd.broken_fields

/-- Diagnosis function: given a diagnosable deposit, return the first broken field.
    Computable via list inspection.
    Returns S as default if no broken fields recorded. -/
def DiagnoseField (_B : Bubble) (dd : DiagnosableDeposit (PropLike := PropLike)
    (Standard := Standard) (ErrorModel := ErrorModel) (Provenance := Provenance)) : Field :=
  dd.broken_fields.head?.getD Field.S

/-- Theorem: DiagnoseField returns a broken field when one exists. -/
theorem diagnose_finds_broken (B : Bubble)
    (dd : DiagnosableDeposit (PropLike := PropLike)
      (Standard := Standard) (ErrorModel := ErrorModel) (Provenance := Provenance))
    (h : dd.broken_fields ≠ []) :
    BrokenField dd (DiagnoseField B dd) := by
  unfold DiagnoseField BrokenField
  cases hlist : dd.broken_fields with
  | nil => exact absurd hlist h
  | cons hd tl =>
    simp only [List.head?, Option.getD]
    exact List.Mem.head tl



end EpArch
