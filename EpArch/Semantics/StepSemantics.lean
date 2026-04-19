/-
EpArch.Semantics.StepSemantics — Step Semantics (Labeled Transition System)

Constructive operational semantics of the epistemic architecture.
Defines a concrete LTS over SystemState with eight bank-primitive actions
(Submit, Withdraw, Challenge, Tick, Repair, Revoke, Promote,
and Submit-with-source-attribution via submit_bridged) and proves conditional
linking results from operational preconditions rather than asserting them as axioms.

Export is not a bank primitive. Inter-bubble transfer is an agent-level workflow:
Withdraw from source bubble, agent carries deposit, Submit (via submit_bridged)
to target bubble. The agent vouches for the source; d.h.V records provenance.

Bank defines WHAT the operators must satisfy (specification axioms).
This module defines HOW they work: the Step relation's preconditions
FORCE certain architectural features.

Key exports:
- SystemState, Step (inductive LTS relation, 8 constructors)
- no_revision_no_correction (competition gate impossibility)
- generic_invariant_preservation (step-preserved invariants)
- Companion: EpArch.Semantics.LinkingAxioms (operational groundings)
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank

namespace EpArch.StepSemantics

universe u

/-! ## System State -/

/-- SystemState: the global configuration of the epistemic system.

    This is the operational state that the LTS evolves.
    - ledger: all deposits (across all bubbles)
    - bubbles: active bubbles in the system
    - clock: global time (for τ/TTL checks)

    Trust relationships are not recorded here. Whether an agent trusts a source
    is per-deposit (d.h.acl) and per-agent, not a systemic bank-layer list. -/
structure SystemState (PropLike Standard ErrorModel Provenance : Type u) where
  ledger      : List (Deposit PropLike Standard ErrorModel Provenance)
  bubbles     : List Bubble
  clock       : Time
  /-- Per-agent, per-claim Ladder state.  Pass-through on every Step (no Step ever
      modifies it — proved by `step_preserves_ladder_map`).  Default: Ignorance. -/
  ladder_map  : Agent → PropLike → LadderStage := fun _ _ => LadderStage.Ignorance

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}

/-! ## Actions -/

/-- Action: the inputs that drive state transitions.

    These correspond to the deposit lifecycle operators:
    - Submit: deposit enters system (as Candidate, or as Deposited when agent carries bridge)
    - Withdraw: agent relies on deposit
    - Challenge: deposit is contested
    - Tick: time advances (for TTL expiry)
    - Repair: address challenged field
    - Revoke: remove deposit from circulation

    Export is NOT a primitive bank action. Inter-bubble transfer is an agent-level
    workflow: Withdraw from source bubble, agent carries the deposit, Submit to
    target bubble. The agent vouches for the source (d.h.V records provenance);
    the bank records the deposit — it does not verify the claimed source. -/
inductive Action (PropLike Standard ErrorModel Provenance Reason Evidence : Type u) where
  | Submit (a : Agent) (d : Deposit PropLike Standard ErrorModel Provenance)
  | Withdraw (a : Agent) (B : Bubble) (d_idx : Nat)
  | Challenge (a : Agent) (B : Bubble) (c : EpArch.Challenge PropLike Reason Evidence)
  | Tick
  | Repair (a : Agent) (B : Bubble) (d_idx : Nat) (f : Field)
  | Revoke (a : Agent) (B : Bubble) (d_idx : Nat)
  | Promote (a : Agent) (B : Bubble) (d_idx : Nat)

/-! ## Preconditions -/

/-- Check if deposit at index is in Deposited status.
    Deposit exists at index with status = .Deposited. -/
def isDeposited (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) : Prop :=
  ∃ d, s.ledger.get? d_idx = some d ∧ d.status = .Deposited

/-- Check if deposit at index is in Quarantined status. -/
def isQuarantined (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) : Prop :=
  ∃ d, s.ledger.get? d_idx = some d ∧ d.status = .Quarantined

/-- Check if deposit at index is in Candidate status. -/
def isCandidate (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) : Prop :=
  ∃ d, s.ledger.get? d_idx = some d ∧ d.status = .Candidate


/-- Check if deposit has preserved header provenance.
    Used by diagnosability and field-checkability predicates in Headers.lean
    and Pathologies.lean. Not a Step gate (export is not a bank primitive). -/
def depositHasHeader (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) : Prop :=
  ∃ d, s.ledger.get? d_idx = some d ∧ header_preserved d

/-! ## State Update Functions -/

/-! ### List Helper Lemmas

NOTE: Lean 4.3.0 without Mathlib does not provide named lemmas for
`List.get?_append_left`, `List.get?_set_eq`, `List.mem_append`, etc.
The lemmas below are proven from scratch. They can be replaced with
Mathlib equivalents if the project ever adopts Mathlib. -/

/-- List append membership: a ∈ l₁ ++ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂ -/
theorem mem_append_iff {α : Type _} (a : α) (l₁ l₂ : List α) :
    a ∈ l₁ ++ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂ := by
  induction l₁ with
  | nil =>
    constructor
    · intro h; exact Or.inr h
    · intro h; cases h with
      | inl h => cases h
      | inr h => exact h
  | cons x xs ih =>
    constructor
    · intro h
      cases h with
      | head => exact Or.inl (List.Mem.head _)
      | tail _ htail =>
        have := ih.mp htail
        cases this with
        | inl hxs => exact Or.inl (List.Mem.tail _ hxs)
        | inr hl₂ => exact Or.inr hl₂
    · intro h
      cases h with
      | inl hl₁ =>
        cases hl₁ with
        | head => exact List.Mem.head _
        | tail _ htail => exact List.Mem.tail _ (ih.mpr (Or.inl htail))
      | inr hl₂ => exact List.Mem.tail _ (ih.mpr (Or.inr hl₂))

/-- Membership in singleton list -/
theorem mem_singleton {α : Type _} (a b : α) : a ∈ [b] ↔ a = b := by
  constructor
  · intro h
    cases h with
    | head => rfl
    | tail _ htail => cases htail
  · intro h
    rw [h]
    exact List.Mem.head _

/-- Membership implies existence of index -/
theorem mem_implies_get? {α : Type _} (l : List α) (a : α) (h : a ∈ l) :
    ∃ i, l.get? i = some a := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    cases h with
    | head => exact ⟨0, rfl⟩
    | tail _ htail =>
      let ⟨i, hi⟩ := ih htail
      exact ⟨i + 1, by simp [List.get?, hi]⟩

/-- get? some implies membership -/
theorem get?_implies_mem {α : Type _} (l : List α) (i : Nat) (a : α)
    (h : l.get? i = some a) : a ∈ l := by
  induction l generalizing i with
  | nil => simp [List.get?] at h
  | cons x xs ih =>
    cases i with
    | zero =>
      simp [List.get?] at h
      rw [h]
      exact List.Mem.head _
    | succ j =>
      simp [List.get?] at h
      exact List.Mem.tail _ (ih j h)

/-- If l.get? i = some x, then i < l.length -/
theorem get?_implies_lt {α : Type _} (l : List α) (i : Nat) (x : α)
    (h : l.get? i = some x) : i < l.length := by
  induction l generalizing i with
  | nil => simp [List.get?] at h
  | cons a as ih =>
    cases i with
    | zero => simp [List.length]; exact Nat.zero_lt_succ _
    | succ j =>
      simp [List.length, List.get?] at h ⊢
      exact Nat.succ_lt_succ (ih j h)

/-- If l.length ≤ i, then l.get? i = none -/
theorem get?_eq_none' {α : Type _} (l : List α) (i : Nat) (h : l.length ≤ i) :
    l.get? i = none := by
  induction l generalizing i with
  | nil => simp [List.get?]
  | cons a as ih =>
    cases i with
    | zero =>
      have : as.length + 1 ≤ 0 := h
      exact absurd this (Nat.not_succ_le_zero as.length)
    | succ j =>
      simp [List.get?]
      apply ih
      simp [List.length] at h
      exact Nat.le_of_succ_le_succ h

/-- (l.set i v).get? i = some v when i < l.length -/
theorem get?_set_eq {α : Type _} (l : List α) (i : Nat) (v : α) (hi : i < l.length) :
    (l.set i v).get? i = some v := by
  induction l generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero i)
  | cons a as ih =>
    cases i with
    | zero => simp [List.set, List.get?]
    | succ j =>
      simp [List.set, List.get?, List.length] at hi ⊢
      exact ih j (Nat.lt_of_succ_lt_succ hi)

/-- (l.set j v).get? i = l.get? i when i ≠ j -/
theorem get?_set_ne {α : Type _} (l : List α) (i j : Nat) (v : α) (hne : i ≠ j) :
    (l.set j v).get? i = l.get? i := by
  induction l generalizing i j with
  | nil => simp [List.set]
  | cons a as ih =>
    cases j with
    | zero =>
      cases i with
      | zero => exact absurd rfl hne
      | succ i' => simp [List.set, List.get?]
    | succ j' =>
      cases i with
      | zero => simp [List.set, List.get?]
      | succ i' =>
        simp only [List.set, List.get?]
        exact ih i' j' (fun h => hne (congrArg Nat.succ h))

/-- get? on appended list: left side unchanged for valid indices -/
theorem get?_append_left {α : Type _} (l₁ l₂ : List α) (i : Nat) (h : i < l₁.length) :
    (l₁ ++ l₂).get? i = l₁.get? i := by
  induction l₁ generalizing i with
  | nil => exact absurd h (Nat.not_lt_zero i)
  | cons x xs ih =>
    cases i with
    | zero => simp [List.get?]
    | succ j =>
      simp only [List.get?, List.cons_append]
      apply ih
      simp [List.length] at h
      exact Nat.lt_of_succ_lt_succ h

/-- Membership in set list: y ∈ l.set i v ↔ (y = v ∧ i < l.length) ∨ ∃ j ≠ i, l.get? j = some y -/
theorem mem_set {α : Type _} (l : List α) (i : Nat) (v : α) (y : α) :
    y ∈ l.set i v →
    (y = v ∧ i < l.length) ∨ (∃ j, j ≠ i ∧ l.get? j = some y) := by
  intro hy
  -- Use get?_implies_mem inverse: find index j where (l.set i v).get? j = some y
  have ⟨j, hj⟩ := mem_implies_get? (l.set i v) y hy
  match Nat.decEq j i with
  | isTrue heq =>
    -- j = i: y was the set value
    rw [heq] at hj
    have hi : i < l.length := by
      have hlen : (l.set i v).length = l.length := List.length_set l i v
      have hj_lt : i < (l.set i v).length := get?_implies_lt _ _ _ hj
      rw [hlen] at hj_lt
      exact hj_lt
    have hset := get?_set_eq l i v hi
    rw [hset] at hj
    injection hj with heq_y
    exact Or.inl ⟨heq_y.symm, hi⟩
  | isFalse hne =>
    -- j ≠ i: y was from original list
    have h_orig := get?_set_ne l j i v hne
    rw [h_orig] at hj
    exact Or.inr ⟨j, hne, hj⟩

/-! ### modifyAt: Modify element at index

Core primitive for all status updates. Defining updates in terms of
`modifyAt` gives clean index lemmas for list manipulation. -/

/-- Modify element at index i using function f. Returns original list if i ≥ length. -/
def modifyAt {α : Type _} (l : List α) (i : Nat) (f : α → α) : List α :=
  match l.get? i with
  | some x => l.set i (f x)
  | none => l

/-- modifyAt preserves length. -/
theorem modifyAt_length {α : Type _} (l : List α) (i : Nat) (f : α → α) :
    (modifyAt l i f).length = l.length := by
  unfold modifyAt
  split
  · exact List.length_set l i _
  · rfl

/-- Key lemma: get? at modified index returns f applied to original. -/
theorem get?_modifyAt_eq {α : Type _} (l : List α) (i : Nat) (f : α → α) (x : α)
    (h : l.get? i = some x) : (modifyAt l i f).get? i = some (f x) := by
  unfold modifyAt
  simp only [h]
  have hi : i < l.length := get?_implies_lt l i x h
  exact get?_set_eq l i (f x) hi

/-- Key lemma: get? at other indices unchanged. -/
theorem get?_modifyAt_ne {α : Type _} (l : List α) (i j : Nat) (f : α → α)
    (hne : j ≠ i) : (modifyAt l i f).get? j = l.get? j := by
  unfold modifyAt
  split
  · next x _ =>
    exact get?_set_ne l j i (f x) hne
  · rfl

/-- modifyAt membership: elements are either original or modified.
    This is a helper lemma; for most preservation proofs we use
    the specific index lemmas (get?_modifyAt_eq/ne) directly.

    Technical note: Uses mem_set helper to handle both cases. -/
theorem mem_modifyAt {α : Type _} (l : List α) (i : Nat) (f : α → α) (y : α) :
    y ∈ modifyAt l i f →
    (∃ x, x ∈ l ∧ x = y) ∨ (∃ x, l.get? i = some x ∧ f x = y) := by
  intro hy
  unfold modifyAt at hy
  split at hy
  · next x hx =>
    -- y is in l.set i (f x)
    have h_mem := mem_set l i (f x) y hy
    cases h_mem with
    | inl h_eq =>
      -- y = f x at index i, so f x = y
      exact Or.inr ⟨x, hx, h_eq.1.symm⟩
    | inr h_other =>
      -- y is from original list at some other index j ≠ i
      let ⟨j, _, hj⟩ := h_other
      exact Or.inl ⟨y, get?_implies_mem l j y hj, rfl⟩
  · exact Or.inl ⟨y, hy, rfl⟩

/-! ### updateDepositStatus -/

/-- Update deposit status at index using modifyAt. -/
def updateDepositStatus (ledger : List (Deposit PropLike Standard ErrorModel Provenance))
    (d_idx : Nat) (newStatus : DepositStatus)
    : List (Deposit PropLike Standard ErrorModel Provenance) :=
  modifyAt ledger d_idx (fun d => { d with status := newStatus })

/-- Key lemma: updateDepositStatus at target index. -/
theorem get?_updateDepositStatus_eq
    (ledger : List (Deposit PropLike Standard ErrorModel Provenance))
    (d_idx : Nat) (newStatus : DepositStatus)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h : ledger.get? d_idx = some d) :
    (updateDepositStatus ledger d_idx newStatus).get? d_idx =
      some { d with status := newStatus } := by
  unfold updateDepositStatus
  exact get?_modifyAt_eq ledger d_idx _ d h

/-- Key lemma: updateDepositStatus at other indices unchanged. -/
theorem get?_updateDepositStatus_ne
    (ledger : List (Deposit PropLike Standard ErrorModel Provenance))
    (d_idx j : Nat) (newStatus : DepositStatus)
    (hne : j ≠ d_idx) :
    (updateDepositStatus ledger d_idx newStatus).get? j = ledger.get? j := by
  unfold updateDepositStatus
  exact get?_modifyAt_ne ledger d_idx j _ hne

/-- updateDepositStatus preserves length. -/
theorem updateDepositStatus_length
    (ledger : List (Deposit PropLike Standard ErrorModel Provenance))
    (d_idx : Nat) (newStatus : DepositStatus) :
    (updateDepositStatus ledger d_idx newStatus).length = ledger.length := by
  unfold updateDepositStatus
  exact modifyAt_length ledger d_idx _

/-! ## Step Relation -/

/-- Step: the labeled transition relation.

    `Step s a s'` means: from state s, action a leads to state s'.

    This is the core operational semantics. The predicates are structured
    so that proving "coordination requires bank" etc. becomes a matter of
    showing that certain outcomes cannot occur without certain features. -/
inductive Step : SystemState PropLike Standard ErrorModel Provenance →
    Action PropLike Standard ErrorModel Provenance Reason Evidence →
    SystemState PropLike Standard ErrorModel Provenance → Prop where

  /-- Submit: new deposit enters as Candidate.

      The submitting agent and target bubble are recorded for attribution.
      Authorization is an agent-level concern; the bank records the structural
      deposit event. -/
  | submit (s : SystemState PropLike Standard ErrorModel Provenance)
      (a : Agent) (d : Deposit PropLike Standard ErrorModel Provenance) :
      Step s (.Submit a d) { s with ledger := s.ledger ++ [{ d with status := .Candidate }] }

  /-- Withdraw: agent relies on deposit.
      Precondition: Deposited status. Attribution (agent, bubble) recorded.
      Authorization is an agent-level concern external to the bank's LTS. -/
  | withdraw (s : SystemState PropLike Standard ErrorModel Provenance)
      (a : Agent) (B : Bubble) (d_idx : Nat)
      (h_deposited : isDeposited s d_idx) :
      Step s (.Withdraw a B d_idx) s  -- state unchanged by successful withdrawal

  /-- Submit with source attribution: agent vouches that deposit came from B_src,
      depositing it directly as Deposited.

      The agent identifies the source bubble (B_src) for provenance attribution;
      d.h.V should record the source chain. The bank does not verify the claimed
      source — that is the agent's responsibility. The agent's vouching is the gate;
      presenting this step IS the assertion that the source is trusted.

      No bank-side precondition: same reasoning as hasTrustBridge removal from
      withdrawal. Trust relationships are per-deposit and per-agent, not systemic
      bank-layer lists. -/
  | submit_bridged (s : SystemState PropLike Standard ErrorModel Provenance)
      (a : Agent) (d : Deposit PropLike Standard ErrorModel Provenance)
      (B_src : Bubble) :
      Step s (.Submit a d) { s with ledger := s.ledger ++ [{ d with status := .Deposited }] }

  /-- Challenge: deposit enters quarantine.

      Precondition: Deposited status. Agent and bubble recorded for attribution.
      Authorization is an agent-level concern external to the bank's LTS. -/
  | challenge (s : SystemState PropLike Standard ErrorModel Provenance)
      (a : Agent) (B : Bubble) (c : EpArch.Challenge PropLike Reason Evidence) (d_idx : Nat)
      (h_deposited : isDeposited s d_idx) :
      Step s (.Challenge a B c)
        { s with ledger := updateDepositStatus s.ledger d_idx .Quarantined }

  /-- Tick: time advances. Clock is monotone: t' must be ≥ s.clock. -/
  | tick (s : SystemState PropLike Standard ErrorModel Provenance) (t' : Time)
      (h_mono : s.clock ≤ t') :
      Step s .Tick { s with clock := t' }

  /-- Revoke: deposit removed from circulation.

      Precondition: Quarantined status. Agent and bubble recorded for attribution.
      Authorization is an agent-level concern external to the bank's LTS. -/
  | revoke (s : SystemState PropLike Standard ErrorModel Provenance)
      (a : Agent) (B : Bubble) (d_idx : Nat)
      (h_quarantined : isQuarantined s d_idx) :
      Step s (.Revoke a B d_idx)
        { s with ledger := updateDepositStatus s.ledger d_idx .Revoked }

  /-- Repair: quarantined deposit re-enters as Candidate.

      When a deposit is repaired, it must go through revalidation:
      patching a claim does not bypass re-acceptance. The repair
      operator addresses a specific field but the deposit still
      must pass through Candidate status.
      Precondition: deposit must be Quarantined. Agent and bubble recorded for attribution. -/
  | repair (s : SystemState PropLike Standard ErrorModel Provenance)
      (a : Agent) (B : Bubble) (d_idx : Nat) (f : Field)
      (h_quarantined : isQuarantined s d_idx) :
      Step s (.Repair a B d_idx f)
        { s with ledger := updateDepositStatus s.ledger d_idx .Candidate }

  /-- Promote: bank operator advances a Candidate deposit to Deposited (live).

      Along with `submit_bridged`, one of two Step constructors that can produce
      a `.Deposited` entry. The deposit must be in Candidate status; after this
      step it is Deposited and live in the bank.

      Implementations may use multi-stage internal validation pipelines between
      Candidate and Deposited; this step represents the minimal architectural
      boundary at which a deposit becomes live. Agent and bubble recorded for attribution. -/
  | promote (s : SystemState PropLike Standard ErrorModel Provenance)
      (a : Agent) (B : Bubble) (d_idx : Nat)
      (h_candidate : isCandidate s d_idx) :
      Step s (.Promote a B d_idx)
        { s with ledger := updateDepositStatus s.ledger d_idx .Deposited }

/-! ## Ladder Invariants

The `ladder_map` field of `SystemState` is never modified by any Step.
Every constructor either returns `s` unchanged (`withdraw`) or uses
`{ s with <other-field> := ... }` which copies `ladder_map` from `s` by
Lean 4's struct-update semantics. -/

/-- Ladder state is invariant under all Steps. -/
theorem step_preserves_ladder_map
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Action PropLike Standard ErrorModel Provenance Reason Evidence)
    (h : Step (Reason := Reason) (Evidence := Evidence) s a s') :
    s'.ladder_map = s.ladder_map := by
  cases h <;> rfl

/-- Closure puzzle — Bank side: no Step auto-propagates deposits via entailment.
    The Ladder map is invariant across all Steps (operational closure invariant).
    Contextual alias of `step_preserves_ladder_map` for the closure puzzle. -/
theorem closure_ladder_invariant
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Action PropLike Standard ErrorModel Provenance Reason Evidence)
    (h : Step (Reason := Reason) (Evidence := Evidence) s a s') :
    s'.ladder_map = s.ladder_map :=
  step_preserves_ladder_map s s' a h

/-! ## Trace Type: Sequences of Steps

A Trace is a sequence of steps from one state to another.
This is the foundation for proving the competition gate theorem:
"domains that structurally prohibit revision cannot self-correct" -/

/-- A Trace is a sequence of zero or more steps from state s to state s'.
    This is the reflexive-transitive closure of Step.
    Inductive type: nil (reflexivity) and cons (one step + more steps). -/
inductive Trace : SystemState PropLike Standard ErrorModel Provenance →
    SystemState PropLike Standard ErrorModel Provenance → Type _ where
  /-- Empty trace: s reaches s in zero steps. -/
  | nil : (s : SystemState PropLike Standard ErrorModel Provenance) → Trace s s
  /-- Cons: one step followed by more steps. -/
  | cons : {s s' s'' : SystemState PropLike Standard ErrorModel Provenance} →
      (a : Action PropLike Standard ErrorModel Provenance Reason Evidence) →
      Step (Reason := Reason) (Evidence := Evidence) s a s' →
      Trace s' s'' →
      Trace s s''

/-- Is an action a "revision action" (Challenge or Revoke)?
    These are the actions that enable self-correction. -/
def Action.isRevision : Action PropLike Standard ErrorModel Provenance Reason Evidence → Bool
  | .Challenge _ _ _ => true
  | .Revoke _ _ _    => true
  | _                => false

/-- Does a trace contain any revision action? -/
def Trace.hasRevision : Trace (Reason := Reason) (Evidence := Evidence) s s' → Bool
  | .nil _ => false
  | .cons a _ rest => a.isRevision || rest.hasRevision

/-- A trace demonstrates "self-correction" if a deposit starts Deposited
    and ends Revoked (error was caught and removed via revision actions).
    This checks only the endpoints; the intermediate path (typically
    Deposited → Quarantined → Revoked) is enforced by Step preconditions. -/
def Trace.demonstratesSelfCorrection
    (_t : Trace (Reason := Reason) (Evidence := Evidence) s s') (d_idx : Nat) : Prop :=
  isDeposited s d_idx ∧
  (∃ d, s'.ledger.get? d_idx = some d ∧ d.status = .Revoked)

/-! ## Trace-Level Ladder Invariants

Lifted versions of `step_preserves_ladder_map` for full Traces.
These are the stronger impossibility-level results: no finite sequence
of Bank/LTS actions can generate or modify Ladder content. -/

/-- Ladder state is invariant under any Trace.

    Induction on Trace structure:
    - nil: reflexivity (no steps taken)
    - cons: the step contributes `step_preserves_ladder_map`, the rest by IH

    This is the trace-level closure of `step_preserves_ladder_map`. -/
theorem trace_preserves_ladder_map
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (t : Trace (Reason := Reason) (Evidence := Evidence) s s') :
    s'.ladder_map = s.ladder_map := by
  induction t with
  | nil _ => rfl
  | cons a h_step _rest ih => exact ih.trans (step_preserves_ladder_map _ _ a h_step)

/-- Point-wise form: no Trace changes the Ladder stage of any (agent, claim) pair. -/
theorem no_bank_trace_generates_ladder_content
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (t : Trace (Reason := Reason) (Evidence := Evidence) s s')
    (f : Agent) (P : PropLike) :
    s'.ladder_map f P = s.ladder_map f P :=
  congrFun (congrFun (trace_preserves_ladder_map s s' t) f) P

/-- No trace can elevate a Ladder stage from Ignorance.

    A trace that begins with the agent having no Ladder content for P ends
    with the same. Bank transitions cannot install Ladder entries. -/
theorem trace_cannot_elevate_ladder
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (t : Trace (Reason := Reason) (Evidence := Evidence) s s')
    (f : Agent) (P : PropLike) :
    s.ladder_map f P = LadderStage.Ignorance →
    s'.ladder_map f P = LadderStage.Ignorance :=
  fun h => (no_bank_trace_generates_ladder_content s s' t f P).trans h

/-- Bank traces cannot discharge closure.

    Any trace that starts with the Certainty stage set for (agent, P) ends
    with it intact. Closure is Ladder-internal; no Bank action can remove it. -/
theorem bank_trace_cannot_discharge_closure
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (t : Trace (Reason := Reason) (Evidence := Evidence) s s')
    (f : Agent) (P : PropLike) :
    s.ladder_map f P = LadderStage.Certainty →
    s'.ladder_map f P = LadderStage.Certainty :=
  fun h => (no_bank_trace_generates_ladder_content s s' t f P).trans h

/-- A system state "prohibits revision" if no reachable trace contains
    Challenge or Revoke actions. Captures domains where revision is
    structurally blocked: all traces have hasRevision = false. -/
def prohibits_revision (s : SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  ∀ (s' : SystemState PropLike Standard ErrorModel Provenance)
    (t : Trace (Reason := Reason) (Evidence := Evidence) s s'),
    t.hasRevision = false

/-- Helper: appending to a list preserves get? for earlier indices. -/
theorem List.get?_append_left' {α : Type u} (l1 l2 : List α) (i : Nat)
    (h : i < l1.length) : (l1 ++ l2).get? i = l1.get? i := by
  induction l1 generalizing i with
  | nil => exact absurd h (Nat.not_lt_zero i)
  | cons head tail ih =>
    cases i with
    | zero => rfl
    | succ j =>
      simp only [List.cons_append, List.get?]
      exact ih j (Nat.lt_of_succ_lt_succ h)

/-- Helper: if get? returns Some at index i, then i < length. -/
theorem List.get?_some_lt' {α : Type u} (l : List α) (i : Nat) (x : α)
    (h : l.get? i = some x) : i < l.length := by
  induction l generalizing i with
  | nil => cases h
  | cons head tail ih =>
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ j => exact Nat.succ_lt_succ (ih j h)

/-- Helper: non-revision steps cannot produce Revoked status.
    Only Step.revoke sets status to Revoked.

    The key insight is:
    - Submit appends elements (Candidate or Deposited), so existing indices unchanged
    - New elements have status ≠ Revoked
    - Withdraw/Tick don't modify ledger
    - Challenge/Revoke are revision actions (ruled out by h_not_rev) -/
theorem step_non_revision_preserves_non_revoked
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Action PropLike Standard ErrorModel Provenance Reason Evidence)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s a s')
    (h_not_rev : a.isRevision = false)
    (d_idx : Nat)
    (h_not_revoked : ∀ d, s.ledger.get? d_idx = some d → d.status ≠ .Revoked) :
    ∀ d, s'.ledger.get? d_idx = some d → d.status ≠ .Revoked := by
  intro d hd h_status
  cases h_step with
  | submit _ d_new =>
    -- Submit appends [{ d_new with status := .Candidate }]
    -- s'.ledger = s.ledger ++ [{ d_new with status := .Candidate }]
    -- Case split: d_idx < s.ledger.length or d_idx = s.ledger.length
    simp only at hd
    by_cases h_in_orig : d_idx < s.ledger.length
    · -- d_idx in original range: get? unchanged
      have h_eq : (s.ledger ++ [{ d_new with status := .Candidate }]).get? d_idx = s.ledger.get? d_idx :=
        List.get?_append_left' s.ledger _ d_idx h_in_orig
      rw [h_eq] at hd
      exact h_not_revoked d hd h_status
    · -- d_idx at new position: status = Candidate ≠ Revoked
      have h_len : d_idx ≥ s.ledger.length := Nat.ge_of_not_lt h_in_orig
      have h_idx_bound : d_idx < s.ledger.length + 1 := by
        have := List.get?_some_lt' _ d_idx d hd
        simp only [List.length_append, List.length] at this
        exact this
      have h_idx_eq : d_idx = s.ledger.length := Nat.le_antisymm (Nat.le_of_lt_succ h_idx_bound) h_len
      -- At index s.ledger.length, we get the new element with status = Candidate
      have h_get_new : (s.ledger ++ [{ d_new with status := .Candidate }]).get? s.ledger.length =
          some { d_new with status := .Candidate } := by
        induction s.ledger with
        | nil => rfl
        | cons _head tail ih => simp [List.get?, ih]
      rw [h_idx_eq] at hd
      rw [h_get_new] at hd
      cases hd
      -- d.status = Candidate ≠ Revoked
      exact DepositStatus.noConfusion h_status
  | submit_bridged _ d_new _ =>
    -- Submit_bridged appends [{ d_new with status := .Deposited }]
    simp only at hd
    by_cases h_in_orig : d_idx < s.ledger.length
    · have h_eq : (s.ledger ++ [{ d_new with status := .Deposited }]).get? d_idx =
          s.ledger.get? d_idx :=
        List.get?_append_left' s.ledger _ d_idx h_in_orig
      rw [h_eq] at hd
      exact h_not_revoked d hd h_status
    · have h_len : d_idx ≥ s.ledger.length := Nat.ge_of_not_lt h_in_orig
      have h_idx_bound : d_idx < s.ledger.length + 1 := by
        have := List.get?_some_lt' _ d_idx d hd
        simp only [List.length_append, List.length] at this
        exact this
      have h_idx_eq : d_idx = s.ledger.length := Nat.le_antisymm (Nat.le_of_lt_succ h_idx_bound) h_len
      have h_get_new : (s.ledger ++ [{ d_new with status := .Deposited }]).get? s.ledger.length =
          some { d_new with status := .Deposited } := by
        induction s.ledger with
        | nil => rfl
        | cons _head tail ih => simp [List.get?, ih]
      rw [h_idx_eq] at hd
      rw [h_get_new] at hd
      cases hd
      -- d.status = Deposited ≠ Revoked
      exact DepositStatus.noConfusion h_status
  | withdraw _ _ _ _ =>
    -- Withdraw doesn't change ledger at all
    exact h_not_revoked d hd h_status
  | challenge _ _ _ _ _ =>
    -- Challenge is revision, but h_not_rev rules it out
    simp only [Action.isRevision] at h_not_rev
  | tick _ _ =>
    -- Tick only changes clock, ledger unchanged
    exact h_not_revoked d hd h_status
  | revoke _ _ _ _ =>
    -- Revoke is revision, but h_not_rev rules it out
    simp only [Action.isRevision] at h_not_rev
  | repair _ _ d_repair_idx _ h_quarantined =>
    -- Repair: updateDepositStatus to Candidate
    -- Case split on whether d_idx is the repaired index
    simp only at hd
    -- The repaired ledger is: updateDepositStatus s.ledger d_repair_idx .Candidate
    -- Two cases: d_idx = d_repair_idx or d_idx ≠ d_repair_idx
    cases Nat.decEq d_idx d_repair_idx with
    | isTrue heq =>
      -- At the repaired index: status is now Candidate ≠ Revoked
      -- From h_quarantined, we know ∃ d_orig, s.ledger.get? d_repair_idx = some d_orig
      let ⟨d_orig, h_orig, _⟩ := h_quarantined
      -- Use the index lemma: get? at target gives {d_orig with status := Candidate}
      have h_get_updated := get?_updateDepositStatus_eq s.ledger d_repair_idx .Candidate d_orig h_orig
      rw [heq] at hd
      rw [h_get_updated] at hd
      -- So d = {d_orig with status := Candidate}, meaning d.status = Candidate
      cases hd
      -- d.status = Candidate ≠ Revoked
      exact DepositStatus.noConfusion h_status
    | isFalse hne =>
      -- At a different index: status unchanged from original
      have h_get_unchanged : (updateDepositStatus s.ledger d_repair_idx .Candidate).get? d_idx = s.ledger.get? d_idx :=
        get?_updateDepositStatus_ne s.ledger d_repair_idx d_idx .Candidate hne
      rw [h_get_unchanged] at hd
      exact h_not_revoked d hd h_status
  | promote _ _ d_p_idx h_cand =>
    -- Promote: updateDepositStatus to Deposited at d_p_idx; .Deposited ≠ .Revoked
    simp only at hd
    cases Nat.decEq d_idx d_p_idx with
    | isTrue heq =>
      -- At the promoted index: status is now Deposited ≠ Revoked
      let ⟨d_c, h_get_c, _⟩ := h_cand
      have h_get_updated := get?_updateDepositStatus_eq s.ledger d_p_idx .Deposited d_c h_get_c
      rw [heq] at hd
      rw [h_get_updated] at hd
      cases hd
      exact DepositStatus.noConfusion h_status
    | isFalse hne =>
      have h_get_unchanged : (updateDepositStatus s.ledger d_p_idx .Deposited).get? d_idx =
          s.ledger.get? d_idx :=
        get?_updateDepositStatus_ne s.ledger d_p_idx d_idx .Deposited hne
      rw [h_get_unchanged] at hd
      exact h_not_revoked d hd h_status

/-- Key lemma: traces without revision preserve non-Revoked status.
    Proof by induction on trace. -/
theorem trace_no_revision_preserves_non_revoked
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (t : Trace (Reason := Reason) (Evidence := Evidence) s s')
    (h_no_rev : t.hasRevision = false)
    (d_idx : Nat)
    (h_not_revoked : ∀ d, s.ledger.get? d_idx = some d → d.status ≠ .Revoked) :
    ∀ d, s'.ledger.get? d_idx = some d → d.status ≠ .Revoked := by
  induction t with
  | nil _ => exact h_not_revoked
  | cons a h_step rest ih =>
    -- In this case: t = Trace.cons a h_step rest
    -- where h_step : Step s a s_mid for some implicit s_mid
    -- and rest : Trace s_mid s'
    simp only [Trace.hasRevision] at h_no_rev
    -- Extract that both a.isRevision = false and rest.hasRevision = false
    have h_a_not_rev : a.isRevision = false := by
      cases ha : a.isRevision
      · rfl
      · simp [ha] at h_no_rev
    have h_rest_no_rev : rest.hasRevision = false := by
      cases hr : rest.hasRevision
      · rfl
      · simp [hr, h_a_not_rev] at h_no_rev
    -- Get the intermediate state from the Step
    -- h_step : Step s a ?s_mid, rest : Trace ?s_mid s'
    -- We need to show the step preserves non-Revoked
    -- The IH needs: ∀ d, ?s_mid.ledger.get? d_idx = some d → d.status ≠ .Revoked
    -- We get this from step_non_revision_preserves_non_revoked
    apply ih h_rest_no_rev
    exact step_non_revision_preserves_non_revoked _ _ a h_step h_a_not_rev d_idx h_not_revoked

/-- Key lemma: non-revision steps cannot change Deposited status to anything else.
    Challenge and Revoke are revision actions (isRevision = true); they are
    ruled out by h_not_rev.  Repair targets Quarantined deposits; if the deposit
    is already Deposited, Repair cannot fire at the same index.
    Submit/Export only append; existing indices are unchanged. -/
theorem step_no_revision_preserves_deposited
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Action PropLike Standard ErrorModel Provenance Reason Evidence)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s a s')
    (h_not_rev : a.isRevision = false)
    (d_idx : Nat)
    (h_dep : isDeposited s d_idx) :
    isDeposited s' d_idx := by
  let ⟨d, h_get, h_status⟩ := h_dep
  have h_in_orig : d_idx < s.ledger.length := List.get?_some_lt' s.ledger d_idx d h_get
  cases h_step with
  | submit _ d_new =>
    -- s'.ledger = s.ledger ++ [{ d_new with status := .Candidate }]
    refine ⟨d, ?_, h_status⟩
    exact (List.get?_append_left' s.ledger _ d_idx h_in_orig).trans h_get
  | submit_bridged _ d_new _ =>
    -- s'.ledger = s.ledger ++ [{ d_new with status := .Deposited }]
    -- Existing deposit at d_idx is unchanged (append only)
    refine ⟨d, ?_, h_status⟩
    exact (List.get?_append_left' s.ledger _ d_idx h_in_orig).trans h_get
  | withdraw _ _ _ _ =>
    -- Withdraw: s' = s (state unchanged)
    exact ⟨d, h_get, h_status⟩
  | challenge _ _ _ _ _ =>
    -- Challenge is isRevision = true; contradicts h_not_rev
    simp only [Action.isRevision] at h_not_rev
  | tick _ _ =>
    -- Tick: only clock changes; s'.ledger = s.ledger
    exact ⟨d, h_get, h_status⟩
  | revoke _ _ _ _ =>
    -- Revoke is isRevision = true; contradicts h_not_rev
    simp only [Action.isRevision] at h_not_rev
  | repair _ _ d_repair_idx _ h_quarantined =>
    -- Repair changes d_repair_idx from Quarantined → Candidate.
    -- Case: d_idx = d_repair_idx → the same deposit is both Deposited (h_dep)
    --   and Quarantined (h_quarantined), which is a contradiction.
    -- Case: d_idx ≠ d_repair_idx → updateDepositStatus preserves d_idx.
    cases Nat.decEq d_idx d_repair_idx with
    | isTrue heq =>
      let ⟨d_q, h_get_q, h_status_q⟩ := h_quarantined
      rw [heq] at h_get
      rw [h_get] at h_get_q
      cases h_get_q
      -- Now d_q = d (same deposit), so .Deposited = .Quarantined — contradiction
      rw [h_status] at h_status_q
      exact DepositStatus.noConfusion h_status_q
    | isFalse hne =>
      have h_unchanged : (updateDepositStatus s.ledger d_repair_idx .Candidate).get? d_idx =
          s.ledger.get? d_idx :=
        get?_updateDepositStatus_ne s.ledger d_repair_idx d_idx .Candidate hne
      exact ⟨d, h_unchanged ▸ h_get, h_status⟩
  | promote _ _ d_p_idx h_cand =>
    -- Promote changes d_p_idx from Candidate → Deposited.
    -- Case: d_idx = d_p_idx → deposit was both Deposited (h_dep) and Candidate
    --   (h_cand), which is a contradiction.
    -- Case: d_idx ≠ d_p_idx → updateDepositStatus preserves d_idx.
    cases Nat.decEq d_idx d_p_idx with
    | isTrue heq =>
      let ⟨d_c, h_get_c, h_status_c⟩ := h_cand
      rw [heq] at h_get
      rw [h_get] at h_get_c
      cases h_get_c
      -- d_c = d, so .Deposited = .Candidate — contradiction
      rw [h_status] at h_status_c
      exact DepositStatus.noConfusion h_status_c
    | isFalse hne =>
      have h_unchanged : (updateDepositStatus s.ledger d_p_idx .Deposited).get? d_idx =
          s.ledger.get? d_idx :=
        get?_updateDepositStatus_ne s.ledger d_p_idx d_idx .Deposited hne
      exact ⟨d, h_unchanged ▸ h_get, h_status⟩

/-- Trace-level version: revision-free traces preserve Deposited status.
    Proof by induction on trace using step_no_revision_preserves_deposited. -/
theorem trace_no_revision_preserves_deposited
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (t : Trace (Reason := Reason) (Evidence := Evidence) s s')
    (h_no_rev : t.hasRevision = false)
    (d_idx : Nat)
    (h_dep : isDeposited s d_idx) :
    isDeposited s' d_idx := by
  induction t with
  | nil _ => exact h_dep
  | cons a h_step rest ih =>
    simp only [Trace.hasRevision] at h_no_rev
    have h_a_not_rev : a.isRevision = false := by
      cases ha : a.isRevision
      · rfl
      · simp [ha] at h_no_rev
    have h_rest_no_rev : rest.hasRevision = false := by
      cases hr : rest.hasRevision
      · rfl
      · simp [hr, h_a_not_rev] at h_no_rev
    apply ih h_rest_no_rev
    exact step_no_revision_preserves_deposited _ _ a h_step h_a_not_rev d_idx h_dep

/-- COMPETITION GATE THEOREM:
    If revision is prohibited, self-correction is impossible.

    Operational grounding for
    "NoSelfCorrectionWithoutRevision" in EpArch.Commitments.

    The proof is structural: self-correction requires a deposit to
    go from Deposited to Revoked, which requires Challenge and Revoke
    actions. If those are prohibited, the transition cannot occur. -/
theorem no_revision_no_correction
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (t : Trace (Reason := Reason) (Evidence := Evidence) s s')
    (h_no_rev : prohibits_revision (Reason := Reason) (Evidence := Evidence) s)
    (d_idx : Nat) :
    ¬t.demonstratesSelfCorrection d_idx := by
  intro h_self_correct
  -- Self-correction means deposit went from Deposited to Revoked
  let ⟨h_deposited, d_final, hd_final, h_revoked⟩ := h_self_correct
  -- The trace has no revision
  have h_no_revision_in_t : t.hasRevision = false := h_no_rev s' t
  -- Deposited ⟹ status ≠ Revoked initially
  have h_init_not_revoked : ∀ d, s.ledger.get? d_idx = some d → d.status ≠ .Revoked := by
    intro d hd h_eq
    let ⟨d', hd', h_status⟩ := h_deposited
    rw [hd] at hd'
    cases hd'
    rw [h_status] at h_eq
    exact DepositStatus.noConfusion h_eq
  -- By the trace lemma, status stays non-Revoked
  have h_final_not_revoked := trace_no_revision_preserves_non_revoked
    s s' t h_no_revision_in_t d_idx h_init_not_revoked
  -- But we have a Revoked deposit, contradiction
  exact h_final_not_revoked d_final hd_final h_revoked

/-! ## Competition Gate Cluster

These theorems establish the core competition gate result:
domains cannot both self-correct AND prohibit revision. -/

/-- Self-correction requires revision (contrapositive form).

    If a trace demonstrates self-correction for some deposit,
    then that trace must contain a revision action.

    **COMPETITION GATE**: Any domain claiming self-correction
    must permit Challenge/Revoke actions. -/
theorem self_correction_requires_revision
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (t : Trace (Reason := Reason) (Evidence := Evidence) s s')
    (d_idx : Nat)
    (h_self_correct : t.demonstratesSelfCorrection d_idx) :
    t.hasRevision = true := by
  -- Proof by cases on hasRevision
  cases h : t.hasRevision with
  | false =>
    -- If hasRevision = false, derive contradiction
    -- Self-correction means deposit went Deposited → Revoked
    let ⟨h_deposited, d_final, hd_final, h_revoked⟩ := h_self_correct
    -- Initial deposit is not Revoked
    have h_init_not_revoked : ∀ d, s.ledger.get? d_idx = some d → d.status ≠ .Revoked := by
      intro d hd h_eq
      let ⟨d', hd', h_status⟩ := h_deposited
      rw [hd] at hd'
      cases hd'
      rw [h_status] at h_eq
      exact DepositStatus.noConfusion h_eq
    -- By trace preservation, final deposit is also not Revoked
    have h_final_not_revoked := trace_no_revision_preserves_non_revoked
      s s' t h d_idx h_init_not_revoked
    -- But we have Revoked, contradiction
    exact absurd h_revoked (h_final_not_revoked d_final hd_final)
  | true => rfl

/-- Self-correcting domains permit revision.

    If there exists any trace that demonstrates self-correction,
    then the system does not prohibit revision.

    **COMPETITION GATE**: Domains cannot both self-correct AND
    prohibit revision — they must choose. -/
theorem self_correcting_domain_permits_revision
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (h_self_corrects : ∃ (s' : SystemState PropLike Standard ErrorModel Provenance)
                         (t : Trace (Reason := Reason) (Evidence := Evidence) s s')
                         (d_idx : Nat), t.demonstratesSelfCorrection d_idx) :
    ¬prohibits_revision (Reason := Reason) (Evidence := Evidence) s := by
  -- Extract the witness
  let ⟨s', t, d_idx, h_self_correct⟩ := h_self_corrects
  -- By self_correction_requires_revision, t has revision
  have h_has_rev : t.hasRevision = true :=
    self_correction_requires_revision s s' t d_idx h_self_correct
  -- prohibits_revision means ALL traces have hasRevision = false
  intro h_prohibits
  -- But t.hasRevision = true
  have h_false : t.hasRevision = false := h_prohibits s' t
  -- Contradiction
  rw [h_has_rev] at h_false
  exact Bool.noConfusion h_false

/-! ## Legibility Structure

Legibility is the property that failures can be diagnosed and repaired.
This requires:
1. Field localization: knowing WHICH field (S, E, V, τ, etc.) is broken
2. Repair path: a Challenge → Quarantine → (Fix or Revoke) trace exists

The S/E/V factorization enables legibility because:
- Each field has a distinct validation protocol
- Failures route to the broken component
- Repair can target just that component

Without factorization (monolithic claims), failures are opaque:
"Something is wrong" without "THIS is wrong because X". -/

/-- A repair path exists for a deposit at a field iff:
    1. The deposit is in Deposited status (can be challenged)
    2. The field is a valid challenge target (is in the Field enum) -/
def HasRepairPath
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) (f : Field) : Prop :=
  isDeposited s d_idx ∧
  f ∈ [Field.S, Field.E, Field.V, Field.τ, Field.redeemability, Field.acl]

/-- A failure is legible iff the broken field is identified and
    a repair path exists for that field. -/
def Legible
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat)
    (BrokenField : Deposit PropLike Standard ErrorModel Provenance → Field → Prop) : Prop :=
  ∃ f : Field,
    (∃ d, s.ledger.get? d_idx = some d ∧ BrokenField d f) ∧
    HasRepairPath s d_idx f

/-- Structural fact: all Deposits in this model have S/E/V factorization by
    construction, because Header includes independent S, E, V fields.

    NOTE: This definition is True for all Deposits in this model and is not
    a discriminating predicate. It cannot be used to derive diagnosability or
    field localizability -- those require `has_strong_SEV_factorization`, which
    is a caller-supplied constraint on a BrokenField predicate. See below. -/
def has_SEV_factorization
    (_d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  True

/-- Factorization enables field identification.

    For any deposit, if a field is broken, it is one of the 6 canonical
    fields (S, E, V, τ, redeemability, acl). This follows from Field enum
    exhaustion. Note: has_SEV_factorization is defined as True for all
    deposits in this model, so the SEV premise (_h_sev) is vacuous. -/
theorem factorization_enables_field_identification
    (BrokenField : Deposit PropLike Standard ErrorModel Provenance → Field → Prop)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (_h_sev : has_SEV_factorization d)
    (h_broken : ∃ f : Field, BrokenField d f) :
    ∃ f : Field, BrokenField d f ∧ f ∈ [.S, .E, .V, .τ, .redeemability, .acl] := by
  match h_broken with
  | ⟨f, hf⟩ =>
    -- Every Field is in the list by exhaustive case analysis
    have h_in : f ∈ [.S, .E, .V, .τ, .redeemability, .acl] := by
      cases f with
      | S => exact List.Mem.head _
      | E => exact List.Mem.tail _ (List.Mem.head _)
      | V => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      | τ => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      | redeemability => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
      | acl => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    exact ⟨f, ⟨hf, h_in⟩⟩

/-- Legibility theorem: for a Deposited deposit with a broken field, the
    failure is Legible.

    Note: has_SEV_factorization is defined as True for all deposits in this
    model, so the SEV premise (_h_sev) is vacuous. The result follows from
    the Deposited status and Field enum exhaustion. -/
theorem factorization_enables_legibility
    (BrokenField : Deposit PropLike Standard ErrorModel Provenance → Field → Prop)
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat)
    (h_deposited : isDeposited s d_idx)
    (_h_sev : ∀ d, s.ledger.get? d_idx = some d → has_SEV_factorization d)
    (h_broken : ∃ d f, s.ledger.get? d_idx = some d ∧ BrokenField d f) :
    Legible s d_idx BrokenField := by
  -- Extract the broken field and deposit
  let ⟨d, f, hd, hf⟩ := h_broken
  -- Show this field is the witness
  refine ⟨f, ?_, ?_⟩
  · -- BrokenField holds
    exact ⟨d, hd, hf⟩
  · -- HasRepairPath holds: deposit is Deposited and field is valid
    unfold HasRepairPath
    refine ⟨h_deposited, ?_⟩
    -- Every Field is in the list by exhaustive case analysis
    cases f with
    | S => exact List.Mem.head _
    | E => exact List.Mem.tail _ (List.Mem.head _)
    | V => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    | τ => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    | redeemability => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    | acl => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

/-- "Strong" SEV factorization: a constraint on a BrokenField predicate asserting
    that every field the predicate marks as broken is one of the
    three core architectural fields S, E, or V.

    Unlike `has_SEV_factorization` (which is definitionally True for all
    deposits in this model and thus a vacuous premise), this predicate is
    supplied by the caller and does genuine work: it allows
    `strong_sev_localizes_to_core_fields` to conclude `f ∈ [S, E, V]`
    rather than merely `f ∈` the full 6-field Field enum. -/
def has_strong_SEV_factorization
    (BrokenField : Deposit PropLike Standard ErrorModel Provenance → Field → Prop)
    (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  ∀ f, BrokenField d f → f ∈ [Field.S, Field.E, Field.V]

/-- Strong SEV factorization localizes failures to the core S/E/V triple.

    IF every broken field for deposit d is in {S, E, V}
    (has_strong_SEV_factorization BrokenField d),
    THEN given any concrete broken field, it can be localized to
    exactly one of the three core architectural fields.

    The SEV premise does real work here: the conclusion `f ∈ [S, E, V]` is
    strictly stronger than the 6-field Field-enum completeness result in
    `factorization_enables_field_identification`, and cannot be derived
    without `h_sev`. -/
theorem strong_sev_localizes_to_core_fields
    (BrokenField : Deposit PropLike Standard ErrorModel Provenance → Field → Prop)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_sev : has_strong_SEV_factorization BrokenField d)
    (h_broken : ∃ f, BrokenField d f) :
    ∃ f, BrokenField d f ∧ f ∈ [Field.S, Field.E, Field.V] :=
  let ⟨f, hf⟩ := h_broken
  ⟨f, hf, h_sev f hf⟩

-- NOTE: `monolithic_implies_opaque_failures` was moved to EpArch.Theorems
-- as `bridge_monolithic_opaque`.

/-! ## Trace Metrics and Convergence

Convergence is the property that disputes eventually resolve.
Key insight: Headers make the suspected field *checkable* against
the deposit's actual S/E/V structure (`depositHasHeader` ↔ `field_checkable`).
Without headers, challenges can still name a field (all_challenges_field_specific
is a pure Field-enum tautology), but the named field cannot be verified
against deposit content — repair attempts are structurally unfocused.
Headers are what make `field_checkable` load-bearing, not what create
field-specificity in the first place. -/

/-- Length of a trace (number of steps). -/
def Trace.length : Trace (Reason := Reason) (Evidence := Evidence) s s' → Nat
  | .nil _ => 0
  | .cons _ _ rest => 1 + rest.length

/-- A deposit is "resolved" if it's either:
    1. Revoked (error caught and removed), or
    2. In stable Deposited status with no pending challenges

    For simplicity, we define resolution as reaching Revoked status,
    since that's the terminal state for error correction. -/
def isResolved (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) : Prop :=
  ∃ d, s.ledger.get? d_idx = some d ∧ d.status = .Revoked

/-- A trace "resolves" a deposit if it takes it from Deposited to Revoked. -/
def Trace.resolves
    (_t : Trace (Reason := Reason) (Evidence := Evidence) s s') (d_idx : Nat) : Prop :=
  isDeposited s d_idx ∧ isResolved s' d_idx

/-- A deposit "converges" from state s if there exists a trace that resolves it. -/
def converges (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) : Prop :=
  ∃ (s' : SystemState PropLike Standard ErrorModel Provenance)
    (t : Trace (Reason := Reason) (Evidence := Evidence) s s'),
    t.resolves d_idx

/-- A witness for convergence: a state, trace, and proof of resolution. -/
structure ConvergenceWitness
    (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) where
  final_state : SystemState PropLike Standard ErrorModel Provenance
  trace : Trace (Reason := Reason) (Evidence := Evidence) s final_state
  resolves : trace.resolves d_idx

/-- Extract convergence time from a witness. -/
def ConvergenceWitness.time
    {s : SystemState PropLike Standard ErrorModel Provenance} {d_idx : Nat}
    (w : ConvergenceWitness (Reason := Reason) (Evidence := Evidence) s d_idx) : Nat :=
  w.trace.length

/-- A challenge is "field-specific" if it targets a specific field.

    NOTE: This is a pure `Field`-enum tautology -- `challenge_is_field_specific c`
    holds for every `c` because `Field` has exactly these six constructors. It does
    NOT imply any header-dependency. Headers are load-bearing for bridged submission
    (agent presents provenance); challenge field-specificity is independent of headers. -/
def challenge_is_field_specific
    (c : EpArch.Challenge PropLike Reason Evidence) : Prop :=
  c.suspected ∈ [.S, .E, .V, .τ, .redeemability, .acl]

/-- All challenges are field-specific by construction.

    Proof: pure Field-enum exhaustion. This holds independently of headers. -/
theorem all_challenges_field_specific
    (c : EpArch.Challenge PropLike Reason Evidence) :
    challenge_is_field_specific c := by
  unfold challenge_is_field_specific
  cases c.suspected with
  | S => exact List.Mem.head _
  | E => exact List.Mem.tail _ (List.Mem.head _)
  | V => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | τ => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  | redeemability => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  | acl => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

-- NOTE: `stripped_challenges_lack_grounding` was moved to EpArch.Theorems
-- as `bridge_stripped_ungrounded`.

/-! ## Step-Preserved Invariants

An invariant is a property of SystemState that holds before and after
every step. These capture the "health conditions" for the epistemic system.

Key insight: Most invariants are already *encoded as preconditions* on Step.
What we prove here is that these preconditions are *inherited* through traces. -/


/-! ### Generic Invariant Preservation Lemma

This is the canonical pattern for proving safety properties:
1. Show invariant holds on initial state
2. Show single step preserves invariant
3. Conclude invariant holds on all reachable states (by induction on trace)
-/

/-- **Generic Invariant Preservation**

    If Inv holds initially and is preserved by single steps,
    then Inv holds on all states reachable via any trace.

    This is the fundamental induction principle for safety proofs.
    All specific invariant preservation theorems instantiate this pattern. -/
theorem generic_invariant_preservation
    (Inv : SystemState PropLike Standard ErrorModel Provenance → Prop)
    (h_step : ∀ (s s' : SystemState PropLike Standard ErrorModel Provenance)
              (a : Action PropLike Standard ErrorModel Provenance Reason Evidence),
              Step (Reason := Reason) (Evidence := Evidence) s a s' →
              Inv s → Inv s')
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (trace : Trace (Reason := Reason) (Evidence := Evidence) s s')
    (h_init : Inv s) :
    Inv s' := by
  induction trace with
  | nil _ => exact h_init
  | cons a h_step_witness _ ih =>
    have h_mid := h_step _ _ a h_step_witness h_init
    exact ih h_mid

/-- Corollary: For any initial state s0 satisfying Inv,
    ALL traces from s0 land in states satisfying Inv. -/
theorem all_traces_preserve_invariant
    (Inv : SystemState PropLike Standard ErrorModel Provenance → Prop)
    (h_step : ∀ (s s' : SystemState PropLike Standard ErrorModel Provenance)
              (a : Action PropLike Standard ErrorModel Provenance Reason Evidence),
              Step (Reason := Reason) (Evidence := Evidence) s a s' →
              Inv s → Inv s')
    (s0 : SystemState PropLike Standard ErrorModel Provenance)
    (h_init : Inv s0) :
    ∀ s', Trace (Reason := Reason) (Evidence := Evidence) s0 s' → Inv s' := by
  intro s' trace
  exact generic_invariant_preservation Inv h_step s0 s' trace h_init


/-- Invariant 1: All deposits in the ledger have valid status.
    (Deposited, Candidate, Quarantined, or Revoked) -/
def inv_valid_status (s : SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  ∀ d, d ∈ s.ledger → d.status ∈ [.Deposited, .Candidate, .Quarantined, .Revoked]

/-- Invariant 4: Bubbles referenced by deposits exist.
    (No deposits in unknown bubbles) -/
def inv_bubbles_exist (s : SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  ∀ d, d ∈ s.ledger → d.bubble ∈ s.bubbles

/-- Invariant 5: Revoked deposits stay revoked.
    No Step transition can change a Revoked deposit to any other status.
    Proved by case analysis: updateDepositStatus only fires with a precondition
    (isDeposited, isQuarantined, or isCandidate) that contradicts .Revoked. -/
def inv_revoked_terminal (s : SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  ∀ (R E : Type u), ∀ d_idx d, s.ledger.get? d_idx = some d → d.status = .Revoked →
    ∀ (s' : SystemState PropLike Standard ErrorModel Provenance)
      (a : Action PropLike Standard ErrorModel Provenance R E),
      Step (Reason := R) (Evidence := E) s a s' →
      ∃ d', s'.ledger.get? d_idx = some d' ∧ d'.status = .Revoked

/-- Invariant 6: Quarantine requires prior Deposited status.
    (Only active deposits can be challenged) -/
def inv_quarantine_from_deposited (_s : SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  -- This is enforced by Step.challenge requiring isDeposited
  True

/-- Combined well-formedness invariant. -/
def WellFormedState (s : SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  inv_valid_status s ∧
  inv_bubbles_exist s ∧
  inv_revoked_terminal s

/-- Valid status is preserved by submit.
    New deposits enter as Candidate, which is a valid status. -/
theorem submit_preserves_valid_status
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_inv : inv_valid_status s) :
    inv_valid_status { s with ledger := s.ledger ++ [{ d with status := .Candidate }] } := by
  unfold inv_valid_status at *
  intro d' hd'
  -- d' is either in old ledger (valid by h_inv) or is the new Candidate (valid)
  have h_mem := mem_append_iff d' s.ledger [{ d with status := .Candidate }]
  rw [h_mem] at hd'
  cases hd' with
  | inl h_old =>
    -- d' was in original ledger, use invariant
    exact h_inv d' h_old
  | inr h_new =>
    -- d' is the new deposit with status Candidate
    have h_eq := mem_singleton d' { d with status := DepositStatus.Candidate }
    rw [h_eq] at h_new
    rw [h_new]
    -- Candidate is in [.Deposited, .Candidate, .Quarantined, .Revoked]
    exact List.Mem.tail _ (List.Mem.head _)

/-- Valid status is preserved by submit_bridged.
    New deposits enter as Deposited, which is a valid status. -/
theorem submit_bridged_preserves_valid_status
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_inv : inv_valid_status s) :
    inv_valid_status { s with ledger := s.ledger ++ [{ d with status := .Deposited }] } := by
  unfold inv_valid_status at *
  intro d' hd'
  have h_mem := mem_append_iff d' s.ledger [{ d with status := .Deposited }]
  rw [h_mem] at hd'
  cases hd' with
  | inl h_old =>
    exact h_inv d' h_old
  | inr h_new =>
    have h_eq := mem_singleton d' { d with status := DepositStatus.Deposited }
    rw [h_eq] at h_new
    rw [h_new]
    -- Deposited is in [.Deposited, .Candidate, .Quarantined, .Revoked]
    exact List.Mem.head _

/-- Valid status is preserved by withdraw (state unchanged). -/
theorem withdraw_preserves_valid_status
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (h_inv : inv_valid_status s) :
    inv_valid_status s := h_inv

/-- Valid status is preserved by tick (ledger unchanged). -/
theorem tick_preserves_valid_status
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (t' : Time)
    (h_inv : inv_valid_status s) :
    inv_valid_status { s with clock := t' } := by
  unfold inv_valid_status at *
  exact h_inv

/-- Helper: updateDepositStatus preserves membership for unchanged indices. -/
theorem updateDepositStatus_preserves_membership
    (ledger : List (Deposit PropLike Standard ErrorModel Provenance))
    (d_idx : Nat) (newStatus : DepositStatus)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    d ∈ ledger →
    ∃ d', d' ∈ updateDepositStatus ledger d_idx newStatus ∧
      (d'.status = d.status ∨ d'.status = newStatus) := by
  intro hd
  -- Find index where d lives
  have ⟨i, hi⟩ := mem_implies_get? ledger d hd
  match Nat.decEq i d_idx with
  | isTrue heq =>
    -- i = d_idx: d gets modified
    rw [heq] at hi
    have h_upd := get?_updateDepositStatus_eq ledger d_idx newStatus d hi
    refine ⟨{ d with status := newStatus }, ?_, Or.inr rfl⟩
    exact get?_implies_mem _ _ _ h_upd
  | isFalse hne =>
    -- i ≠ d_idx: d is unchanged
    have h_same := get?_updateDepositStatus_ne ledger d_idx i newStatus hne
    rw [hi] at h_same
    refine ⟨d, ?_, Or.inl rfl⟩
    exact get?_implies_mem _ _ _ h_same

/-- Valid status is preserved by challenge (Deposited → Quarantined). -/
theorem challenge_preserves_valid_status
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat)
    (h_inv : inv_valid_status s) :
    inv_valid_status { s with ledger := updateDepositStatus s.ledger d_idx .Quarantined } := by
  unfold inv_valid_status at *
  intro d hd
  -- Use mem_modifyAt to determine where d came from
  unfold updateDepositStatus at hd
  have h_or := mem_modifyAt s.ledger d_idx (fun d => { d with status := .Quarantined }) d hd
  cases h_or with
  | inl h_orig =>
    -- d was in original ledger (possibly same as modified element)
    let ⟨d', hd'_mem, hd'_eq⟩ := h_orig
    rw [← hd'_eq]
    exact h_inv d' hd'_mem
  | inr h_mod =>
    -- d is the modified element with status = Quarantined
    let ⟨d_orig, _, h_eq⟩ := h_mod
    -- d = {d_orig with status := Quarantined}, so d.status = Quarantined
    rw [← h_eq]
    -- Quarantined is in the valid status list: [.Deposited, .Candidate, .Quarantined, .Revoked]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- Valid status is preserved by revoke (Quarantined → Revoked). -/
theorem revoke_preserves_valid_status
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat)
    (h_inv : inv_valid_status s) :
    inv_valid_status { s with ledger := updateDepositStatus s.ledger d_idx .Revoked } := by
  unfold inv_valid_status at *
  intro d hd
  unfold updateDepositStatus at hd
  have h_or := mem_modifyAt s.ledger d_idx (fun d => { d with status := .Revoked }) d hd
  cases h_or with
  | inl h_orig =>
    let ⟨d', hd'_mem, hd'_eq⟩ := h_orig
    rw [← hd'_eq]
    exact h_inv d' hd'_mem
  | inr h_mod =>
    let ⟨d_orig, _, h_eq⟩ := h_mod
    rw [← h_eq]
    -- Revoked is in [.Deposited, .Candidate, .Quarantined, .Revoked]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-- Valid status is preserved by repair (Quarantined → Candidate). -/
theorem repair_preserves_valid_status
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat)
    (h_inv : inv_valid_status s) :
    inv_valid_status { s with ledger := updateDepositStatus s.ledger d_idx .Candidate } := by
  unfold inv_valid_status at *
  intro d hd
  unfold updateDepositStatus at hd
  have h_or := mem_modifyAt s.ledger d_idx (fun d => { d with status := .Candidate }) d hd
  cases h_or with
  | inl h_orig =>
    let ⟨d', hd'_mem, hd'_eq⟩ := h_orig
    rw [← hd'_eq]
    exact h_inv d' hd'_mem
  | inr h_mod =>
    let ⟨d_orig, _, h_eq⟩ := h_mod
    rw [← h_eq]
    -- Candidate is in [.Deposited, .Candidate, .Quarantined, .Revoked]
    exact List.Mem.tail _ (List.Mem.head _)

/-- Valid status is preserved by promote (Candidate → Deposited). -/
theorem promote_preserves_valid_status
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat)
    (h_inv : inv_valid_status s) :
    inv_valid_status { s with ledger := updateDepositStatus s.ledger d_idx .Deposited } := by
  unfold inv_valid_status at *
  intro d hd
  unfold updateDepositStatus at hd
  have h_or := mem_modifyAt s.ledger d_idx (fun d => { d with status := .Deposited }) d hd
  cases h_or with
  | inl h_orig =>
    let ⟨d', hd'_mem, hd'_eq⟩ := h_orig
    rw [← hd'_eq]
    exact h_inv d' hd'_mem
  | inr h_mod =>
    let ⟨d_orig, _, h_eq⟩ := h_mod
    rw [← h_eq]
    -- Deposited is in [.Deposited, .Candidate, .Quarantined, .Revoked]
    exact List.Mem.head _

/-- STEP PRESERVATION THEOREM:
    Valid status is preserved by all Step transitions. -/
theorem step_preserves_valid_status
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Action PropLike Standard ErrorModel Provenance Reason Evidence)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s a s')
    (h_inv : inv_valid_status s) :
    inv_valid_status s' := by
  -- Case analysis on the step type
  cases h_step
  case submit a d =>
    exact submit_preserves_valid_status s d h_inv
  case submit_bridged a d _ =>
    exact submit_bridged_preserves_valid_status s d h_inv
  case withdraw =>
    exact h_inv
  case challenge _ _ _ d_idx _ =>
    exact challenge_preserves_valid_status s d_idx h_inv
  case tick t' _ =>
    exact tick_preserves_valid_status s t' h_inv
  case revoke _ _ d_idx _ =>
    exact revoke_preserves_valid_status s d_idx h_inv
  case repair _ _ d_idx f _ =>
    exact repair_preserves_valid_status s d_idx h_inv
  case promote a_p B_p d_p_idx _ =>
    exact promote_preserves_valid_status s d_p_idx h_inv

/-- TRACE PRESERVATION:
    Invariants preserved by single steps are preserved by traces. -/
theorem trace_preserves_valid_status
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (t : Trace (Reason := Reason) (Evidence := Evidence) s s')
    (h_inv : inv_valid_status s) :
    inv_valid_status s' := by
  induction t with
  | nil => exact h_inv
  | cons a h_step _ ih =>
    -- Apply step preservation, then induction hypothesis
    have h_mid := step_preserves_valid_status _ _ a h_step h_inv
    exact ih h_mid

/-- The separation invariant: traction vs. authorization are distinct concerns.

    In the abstract LTS, Step.withdraw requires only isDeposited (traction).
    Authorization is an agent-level concern outside the bank's model.

    - Traction = having the deposit (isDeposited) — bank-layer precondition
    - Authorization = agent verifies identity externally; not a bank gate

    These are separated: the bank records structural deposit facts; agents
    carry credentials to the interaction. -/
def inv_separation (_s : SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  -- Traction (isDeposited) is the bank's structural gate; authorization is agent-level.
  -- This is structural: Step.withdraw requires isDeposited as its sole precondition.
  True

/-- Separation is preserved by construction of Step. -/
theorem step_preserves_separation
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Action PropLike Standard ErrorModel Provenance Reason Evidence)
    (_h_step : Step (Reason := Reason) (Evidence := Evidence) s a s')
    (_h_inv : inv_separation s) :
    inv_separation s' := by
  unfold inv_separation at *
  trivial

/-- Auditability invariant: header provenance is carried by the Deposit struct itself.

    Export is not a bank primitive (see Step.submit_bridged for the bridge path),
    so there is no longer a Step-level gate on depositHasHeader. Auditability in the
    sense of traceable provenance is upheld by the Header fields (S, E, V, tau)
    that every Deposit carries. This definition is retained as a documentation anchor. -/
def inv_auditability (_s : SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  -- Header provenance is structural: every Deposit.h carries S/E/V/tau fields.
  True

/-- Auditability is preserved by construction of Step. -/
theorem step_preserves_auditability
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Action PropLike Standard ErrorModel Provenance Reason Evidence)
    (_h_step : Step (Reason := Reason) (Evidence := Evidence) s a s')
    (_h_inv : inv_auditability s) :
    inv_auditability s' := by
  unfold inv_auditability at *
  trivial

/-! ## Key Lemmas for Linking Axioms -/

/-- Withdrawal requires Deposited status.
    This grounds `withdrawal_gates` from EpArch.Theorems.
    Authorization is an agent-level concern; the bank records that withdrawal happened. -/
theorem withdrawal_requires_deposited
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat)
    (h_step : Step (Reason := Reason) (Evidence := Evidence)
      s (.Withdraw a B d_idx) s') :
    isDeposited s d_idx := by
  cases h_step
  assumption

/-- Challenge requires field localization.
    This grounds `challenge_requires_field_localization` from EpArch.Invariants. -/
theorem challenge_has_field_localization
    (c : EpArch.Challenge PropLike Reason Evidence) :
    ∃ f : Field, c.suspected = f := by
  exact ⟨c.suspected, rfl⟩

/-! ## Repair Step Theorems -/

/-- Repair requires quarantine: you can only repair what's been challenged.
    This ensures the repair loop requires going through Challenge first. -/
theorem repair_requires_quarantine
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat) (f : Field)
    (h_step : Step (Reason := Reason) (Evidence := Evidence)
      s (.Repair a B d_idx f) s') :
    isQuarantined s d_idx := by
  cases h_step
  assumption

/-- Repair records the targeted field: the action carries the field identity
    and the repaired ledger transitions the deposit to Candidate status.

    Theorem shape: given a Step.repair, the deposit at d_idx existed in the
    pre-state with Quarantined status, and the post-state ledger is
    updateDepositStatus applied at d_idx with .Candidate.
    Proof: cases h_step; isQuarantined witness from h_quarantined; rfl for ledger. -/
theorem repair_action_carries_field
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat) (f : Field)
    (h_step : Step (Reason := Reason) (Evidence := Evidence)
      s (.Repair a B d_idx f) s') :
    (∃ d, s.ledger.get? d_idx = some d ∧ d.status = .Quarantined) ∧
    s'.ledger = updateDepositStatus s.ledger d_idx .Candidate :=
  ⟨repair_requires_quarantine s s' a B d_idx f h_step, by cases h_step; rfl⟩

/-- Repair produces Candidate status: repaired deposits must be revalidated.

    When a deposit is repaired it re-enters as Candidate, requiring
    the bubble's Accept function before it becomes Deposited again.
    This grounds supersession_requires_validation operationally. -/
theorem repair_produces_candidate
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat) (f : Field)
    (h_step : Step (Reason := Reason) (Evidence := Evidence)
      s (.Repair a B d_idx f) s') :
    s'.ledger = updateDepositStatus s.ledger d_idx .Candidate := by
  cases h_step
  rfl

/-- Corollary: The repair loop (Challenge → Quarantine → Repair → Candidate)
    enforces revalidation for any deposit that's been challenged.

    This is the operational grounding for "supersession requires validation":
    1. Challenge puts deposit in Quarantine
    2. Repair is only possible from Quarantine (repair_requires_quarantine)
    3. Repair produces Candidate status (repair_produces_candidate)
    4. Candidate requires Accept to become Deposited again

    The key insight: repaired deposits have status = Candidate, which
    means they must go through the bubble's Accept function again. -/
theorem repair_resets_to_candidate
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat) (f : Field)
    (h_step : Step (Reason := Reason) (Evidence := Evidence)
      s (.Repair a B d_idx f) s') :
    ∀ d, s'.ledger.get? d_idx = some d →
      d.status = .Candidate ∨
      (∃ d_orig, s.ledger.get? d_idx = some d_orig ∧ d.status = d_orig.status) := by
  -- When Step is repair, s' = { s with ledger := updateDepositStatus s.ledger d_idx .Candidate }
  cases h_step
  intro d hd
  -- Now s'.ledger = updateDepositStatus s.ledger d_idx .Candidate
  -- and we have hd : s'.ledger.get? d_idx = some d
  -- Check if s.ledger.get? d_idx is some
  match h_orig : s.ledger.get? d_idx with
  | some d_orig =>
    -- Use get?_updateDepositStatus_eq: at d_idx we get { d_orig with status := .Candidate }
    have h_upd := get?_updateDepositStatus_eq s.ledger d_idx DepositStatus.Candidate d_orig h_orig
    rw [h_upd] at hd
    injection hd with heq
    rw [← heq]
    exact Or.inl rfl
  | none =>
    -- If original has none at d_idx, updateDepositStatus doesn't change anything at that index
    -- (modifyAt returns original when get? is none)
    -- So (updateDepositStatus s.ledger d_idx .Candidate).get? d_idx = s.ledger.get? d_idx = none
    unfold updateDepositStatus modifyAt at hd
    -- After simp, hd becomes type (none = some d) which is contradictory
    simp only [h_orig] at hd

/-! ## Feature Predicates (Operational Definitions) -/

/-- Operational definition: system has bubbles if ledger is scoped by bubble. -/
def sys_has_bubbles (s : SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  s.bubbles.length > 0 ∧ ∀ d, d ∈ s.ledger → d.bubble ∈ s.bubbles

/-- Operational definition: system has headers if deposits have preserved headers. -/
def sys_has_headers (s : SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  ∀ d, d ∈ s.ledger → header_preserved d

/-- Operational definition: system has revocation if quarantine → revoke path exists. -/
def sys_has_revocation (s : SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  ∃ d_idx, isQuarantined s d_idx

/-! ## Revocation-Terminal Invariant Proofs -/

/-- Helper: a single Step from s cannot change the ledger entry at d_idx
    if that entry has status .Revoked.

    Proof strategy: cases on the Step constructor.
    - submit/submit_bridged: appends; original index preserved by get?_append_left.
    - withdraw/tick: ledger unchanged or clock-only change.
    - challenge/revoke/repair/promote: updateDepositStatus at some index idx';
      if idx' = d_idx, the precondition (isDeposited/isQuarantined/isCandidate)
      contradicts d.status = .Revoked; else get?_updateDepositStatus_ne. -/
theorem revoked_stay_revoked_one_step
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Action PropLike Standard ErrorModel Provenance Reason Evidence)
    (d_idx : Nat) (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_get : s.ledger.get? d_idx = some d)
    (h_revoked : d.status = .Revoked)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s a s') :
    s'.ledger.get? d_idx = some d := by
  cases h_step with
  | submit =>
    exact (get?_append_left s.ledger _ d_idx (get?_implies_lt _ _ _ h_get)).trans h_get
  | submit_bridged =>
    -- submit_bridged appends [{ d with status := .Deposited }]; existing indices preserved
    exact (get?_append_left s.ledger _ d_idx (get?_implies_lt _ _ _ h_get)).trans h_get
  | withdraw => exact h_get
  | challenge _ _ c_var d_ch h_dep =>
    cases Nat.decEq d_ch d_idx with
    | isTrue heq =>
      let ⟨d_dep, h_dep_get, h_dep_status⟩ := h_dep
      rw [heq, h_get] at h_dep_get
      simp only [Option.some.injEq] at h_dep_get
      have h_status : d.status = .Deposited := by rw [h_dep_get]; exact h_dep_status
      exact absurd (h_revoked.symm.trans h_status) (by decide)
    | isFalse hne =>
      exact (get?_updateDepositStatus_ne s.ledger d_ch d_idx .Quarantined (Ne.symm hne)).trans h_get
  | tick t' _ => exact h_get
  | revoke _ _ d_rev h_q =>
    cases Nat.decEq d_rev d_idx with
    | isTrue heq =>
      let ⟨d_q, h_q_get, h_q_status⟩ := h_q
      rw [heq, h_get] at h_q_get
      simp only [Option.some.injEq] at h_q_get
      have h_status : d.status = .Quarantined := by rw [h_q_get]; exact h_q_status
      exact absurd (h_revoked.symm.trans h_status) (by decide)
    | isFalse hne =>
      exact (get?_updateDepositStatus_ne s.ledger d_rev d_idx .Revoked (Ne.symm hne)).trans h_get
  | repair _ _ d_rep _ h_q =>
    cases Nat.decEq d_rep d_idx with
    | isTrue heq =>
      let ⟨d_q, h_q_get, h_q_status⟩ := h_q
      rw [heq, h_get] at h_q_get
      simp only [Option.some.injEq] at h_q_get
      have h_status : d.status = .Quarantined := by rw [h_q_get]; exact h_q_status
      exact absurd (h_revoked.symm.trans h_status) (by decide)
    | isFalse hne =>
      exact (get?_updateDepositStatus_ne s.ledger d_rep d_idx .Candidate (Ne.symm hne)).trans h_get
  | promote a_p B_p d_prom h_cand =>
    cases Nat.decEq d_prom d_idx with
    | isTrue heq =>
      let ⟨d_c, h_c_get, h_c_status⟩ := h_cand
      rw [heq, h_get] at h_c_get
      simp only [Option.some.injEq] at h_c_get
      have h_status : d.status = .Candidate := by rw [h_c_get]; exact h_c_status
      exact absurd (h_revoked.symm.trans h_status) (by decide)
    | isFalse hne =>
      exact (get?_updateDepositStatus_ne s.ledger d_prom d_idx .Deposited (Ne.symm hne)).trans h_get

/-- The revoked-terminal invariant is preserved by every Step.

    Proof: the invariant says "any Revoked deposit in s stays Revoked after any
    step from s." To show it holds in s' too, we take a Revoked deposit in s' and
    show any step from s' also preserves it -- this follows directly from
    `revoked_stay_revoked_one_step`, which does not depend on the prior history. -/
theorem step_preserves_revoked_terminal
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Action PropLike Standard ErrorModel Provenance Reason Evidence)
    (_h_step : Step (Reason := Reason) (Evidence := Evidence) s a s')
    (_h_inv : inv_revoked_terminal s) :
    inv_revoked_terminal s' := by
  unfold inv_revoked_terminal
  intro R E d_idx d h_get h_revoked s'' a'' h_step_s'
  exact ⟨d, revoked_stay_revoked_one_step s' s'' a'' d_idx d h_get h_revoked h_step_s',
        h_revoked⟩

/-- Operational definition: system has bank if ledger is non-empty (shared records exist). -/
def sys_has_bank (s : SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  s.ledger.length > 0

/-- Operational definition: system has redeemability if deposits have constraint surface refs.
    Note: simplified to avoid universe level issues -/
def sys_has_redeemability (s : SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  ∀ d, d ∈ s.ledger → d.status = .Deposited → s.ledger.length > 0

-- `coordination_uses_shared_ledger` was removed: it dropped all meaningful premises
-- and duplicated `isDeposited` trivially. The grounded version lives in
-- `EpArch.Semantics.LinkingAxioms.grounded_coordination_requires_bank`.

end EpArch.StepSemantics
