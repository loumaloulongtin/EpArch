/-
EpArch.Theorems.Withdrawal — Withdrawal and Repair Theorems

Derived theorems for the operational withdrawal lifecycle:
- Withdrawal gate: bank consultation (Deposited status)
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

The withdrawal gate is defined in terms of the operational LTS
predicates from StepSemantics. One gate must be satisfied:
1. Bank consulted (deposit in Deposited status)

This is what distinguishes knowledge (Bank) from certainty (Ladder).
Authorization is an agent-level concern; the bank enforces deposit-state structure only. -/

/-- Bank consultation gate: deposit is actually in the bank (Deposited status).
    This is the operational meaning of "consulting the bank" — you're not just
    relying on your ladder-side memory, you're checking the shared ledger.
    Definitionally equal to `isDeposited`. -/
def ConsultedBank_At (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) : Prop :=
  isDeposited s d_idx

/-- WITHDRAWAL GATE THEOREM (derived from LTS, no axiom!)

    If Step.withdraw fires, then the bank consultation gate must hold.
    This is now a theorem, not an axiom, derived from Step.withdraw's
    constructor preconditions.

    Proof: The Step.withdraw constructor requires isDeposited as an explicit
    hypothesis. We just extract it.
    Authorization is an agent-level concern; not a bank gate. -/
theorem withdrawal_gates
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (B : Bubble) (a : Agent) (d_idx : Nat)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s') :
    ConsultedBank_At s d_idx :=
  withdrawal_requires_deposited s s' a B d_idx h_step


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
    (a : Agent) (B : Bubble) (d_idx : Nat) (f : Field)
    (h_step : Step (Reason := Reason) (Evidence := Evidence)
      s (.Repair a B d_idx f) s') :
    s'.ledger = updateDepositStatus s.ledger d_idx .Candidate :=
  repair_produces_candidate s s' a B d_idx f h_step

/-- Submit enforces Candidate entry: ordinary submissions enter as Candidate.

    `Step.submit` explicitly sets status := .Candidate.
    `Action.Register` / `Step.register` is a separate action that enters Deposited
    directly — see `register_enters_deposited` below. -/
theorem submit_enforces_revalidation
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_step : Step (Reason := Reason) (Evidence := Evidence)
      s (.Submit a d) s') :
    ∃ d', d' ∈ s'.ledger ∧ d'.status = .Candidate := by
  cases h_step with
  | submit =>
    refine ⟨{ d with status := .Candidate }, ?_, rfl⟩
    have h := mem_append_iff { d with status := DepositStatus.Candidate } s.ledger [{ d with status := DepositStatus.Candidate }]
    rw [h]
    exact Or.inr (List.Mem.head _)

/-- Register enters Deposited: direct-registration submissions bypass the Candidate queue.

    `Step.register` (firing on `Action.Register`) explicitly sets status := .Deposited.
    No bank-side precondition applies; the agent's choice to present `Action.Register`
    is the sole gate. -/
theorem register_enters_deposited
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_step : Step (Reason := Reason) (Evidence := Evidence)
      s (.Register a d) s') :
    ∃ d', d' ∈ s'.ledger ∧ d'.status = .Deposited := by
  cases h_step with
  | register =>
    refine ⟨{ d with status := .Deposited }, ?_, rfl⟩
    have h := mem_append_iff { d with status := DepositStatus.Deposited } s.ledger [{ d with status := DepositStatus.Deposited }]
    rw [h]
    exact Or.inr (List.Mem.head _)

/-- The full repair loop requires quarantine first.

    You can't repair something that hasn't been challenged.
    This enforces the Challenge → Quarantine → Repair sequence. -/
theorem repair_requires_prior_challenge
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat) (f : Field)
    (h_step : Step (Reason := Reason) (Evidence := Evidence)
      s (.Repair a B d_idx f) s') :
    isQuarantined s d_idx :=
  repair_requires_quarantine s s' a B d_idx f h_step

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
