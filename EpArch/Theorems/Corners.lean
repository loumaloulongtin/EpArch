/-
EpArch.Theorems.Corners — Competition Gate Corner Theorems

Corner theorems 1, 2, 6, 7, 8, 9 — each formalizes a competition gate:
a structural property that a rival architecture must implement or retreat.
Also includes:
- lottery_no_deposit_blocks_withdraw: operational step-grounded lottery gate
- The three lottery dissolution theorems (Corner 2 cluster)
- Entrenchment corollary
-/
import EpArch.Basic
import EpArch.Semantics.StepSemantics
import EpArch.Minimality

namespace EpArch

open StepSemantics

universe u

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}

/-! ## Corner 6 — Contestation blocked ⇒ frozen canon dynamics

    **Theorem shape:** If Challenge/Revoke/Repair steps are removed from
    the transition system, then bad deposits persist forever.

    **Implication:** Systems that structurally block contestation cannot
    eliminate errors — they have "frozen canon" dynamics. -/

/-- A "bad deposit" predicate: the deposit has some broken field. -/
def IsBadDeposit (BrokenField : Deposit PropLike Standard ErrorModel Provenance → Field → Prop)
    (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  ∃ f, BrokenField d f

/-- Is an action a "contestation action" (Challenge, Revoke, or Repair)?
    These are the actions that enable error correction. -/
def isContestationAction : Action PropLike Standard ErrorModel Provenance Reason Evidence → Bool
  | .Challenge _ => true
  | .Revoke _    => true
  | .Repair _ _  => true
  | _            => false

/-- A restricted step relation: only non-contestation actions allowed. -/
def RestrictedStep (s : SystemState PropLike Standard ErrorModel Provenance)
    (a : Action PropLike Standard ErrorModel Provenance Reason Evidence)
    (s' : SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  Step (Reason := Reason) (Evidence := Evidence) s a s' ∧ isContestationAction a = false

/-- CORNER 6 THEOREM: Under restricted transitions (no contestation),
    deposited items cannot become revoked.

    Key insight: Submit/Withdraw/Export/Tick don't revoke deposits.
    Only Revoke can produce .Revoked status, and it's blocked. -/
theorem frozen_canon_no_revocation
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Action PropLike Standard ErrorModel Provenance Reason Evidence)
    (d_idx : Nat)
    (h_step : RestrictedStep (Reason := Reason) (Evidence := Evidence) s a s')
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_get : s.ledger.get? d_idx = some d)
    (h_not_revoked : d.status ≠ .Revoked) :
    -- After the step, if the deposit still exists at d_idx, it's not Revoked
    ∀ d', s'.ledger.get? d_idx = some d' → d'.status ≠ .Revoked := by
  intro d' h_get'
  let ⟨h_real_step, h_not_contest⟩ := h_step
  cases h_real_step with
  | submit _ d_new _ =>
    -- s'.ledger = s.ledger ++ [new], so get? d_idx unchanged for existing indices
    have h_lt : d_idx < s.ledger.length := get?_implies_lt s.ledger d_idx d h_get
    have h_same : (s.ledger ++ [{ d_new with status := .Candidate }]).get? d_idx = s.ledger.get? d_idx :=
      get?_append_left s.ledger [{ d_new with status := .Candidate }] d_idx h_lt
    rw [h_same] at h_get'
    rw [h_get] at h_get'
    injection h_get' with h_eq
    rw [← h_eq]
    exact h_not_revoked
  | withdraw _ _ _ _ _ _ =>
    -- s' = s, so d' = d
    simp_all
  | inspect _ _ _ _ _ _ =>
    -- s' = s, so d' = d
    simp_all
  | export_with_bridge _ B2 d_exp_idx _ _ _ =>
    -- addToNewBubble either appends or leaves unchanged
    -- For existing indices < s.ledger.length, get? is unchanged
    have h_lt : d_idx < s.ledger.length := get?_implies_lt s.ledger d_idx d h_get
    -- addToNewBubble appends [new] or returns unchanged
    -- Either way, existing indices unchanged
    unfold addToNewBubble at h_get'
    split at h_get'
    · next d_exp _h_d_exp =>
      -- some case: appended
      have h_same : (s.ledger ++ [{ d_exp with bubble := B2, status := .Candidate }]).get? d_idx = s.ledger.get? d_idx :=
        get?_append_left s.ledger [{ d_exp with bubble := B2, status := .Candidate }] d_idx h_lt
      rw [h_same] at h_get'
      rw [h_get] at h_get'
      injection h_get' with h_eq
      rw [← h_eq]
      exact h_not_revoked
    · -- none case: unchanged
      rw [h_get] at h_get'
      injection h_get' with h_eq
      rw [← h_eq]
      exact h_not_revoked
  | export_revalidate _ B2 d_exp_idx _ _ _ =>
    -- Same as export_with_bridge
    have h_lt : d_idx < s.ledger.length := get?_implies_lt s.ledger d_idx d h_get
    unfold addToNewBubble at h_get'
    split at h_get'
    · next d_exp _h_d_exp =>
      have h_same : (s.ledger ++ [{ d_exp with bubble := B2, status := .Candidate }]).get? d_idx = s.ledger.get? d_idx :=
        get?_append_left s.ledger [{ d_exp with bubble := B2, status := .Candidate }] d_idx h_lt
      rw [h_same] at h_get'
      rw [h_get] at h_get'
      injection h_get' with h_eq
      rw [← h_eq]
      exact h_not_revoked
    · rw [h_get] at h_get'
      injection h_get' with h_eq
      rw [← h_eq]
      exact h_not_revoked
  | challenge _ _ _ =>
    -- Challenge is contestation, so h_not_contest gives False
    simp [isContestationAction] at h_not_contest
  | tick _ =>
    -- s' only differs in clock, ledger unchanged
    simp_all
  | revoke _ _ =>
    -- Revoke is contestation
    simp [isContestationAction] at h_not_contest
  | repair _ _ _ =>
    -- Repair is contestation
    simp [isContestationAction] at h_not_contest
  | promote _ _ d_p_idx _ h_cand =>
    -- Promote: updateDepositStatus to Deposited; .Deposited ≠ .Revoked
    cases Nat.decEq d_idx d_p_idx with
    | isTrue heq =>
      let ⟨d_c, h_get_c, _⟩ := h_cand
      have h_upd := get?_updateDepositStatus_eq s.ledger d_p_idx .Deposited d_c h_get_c
      rw [heq] at h_get'
      rw [h_upd] at h_get'
      injection h_get' with h_eq'
      intro h_rev
      rw [← h_eq'] at h_rev
      exact DepositStatus.noConfusion h_rev
    | isFalse hne =>
      have h_unch := get?_updateDepositStatus_ne s.ledger d_p_idx d_idx .Deposited hne
      rw [h_unch] at h_get'
      rw [h_get] at h_get'
      injection h_get' with h_eq'
      rw [← h_eq']
      exact h_not_revoked

/-- A trace where every action is non-contestation
    (no Challenge, no Revoke, no Repair). -/
def allRestrictedTrace {s s' : SystemState PropLike Standard ErrorModel Provenance} :
    Trace (Reason := Reason) (Evidence := Evidence) s s' → Prop
  | .nil _ => True
  | .cons a _ rest => isContestationAction a = false ∧ allRestrictedTrace rest

/-- A trace with no contestation actions contains no revision actions. -/
theorem allRestricted_implies_no_revision
    {s s' : SystemState PropLike Standard ErrorModel Provenance}
    (t : Trace (Reason := Reason) (Evidence := Evidence) s s') :
    allRestrictedTrace t → Trace.hasRevision t = false := by
  induction t with
  | nil _ => simp [Trace.hasRevision]
  | cons a _step rest ih =>
    simp only [allRestrictedTrace]
    intro ⟨h_not_contest, h_rest⟩
    simp only [Trace.hasRevision]
    have h_not_rev : a.isRevision = false := by
      cases a with
      | Submit _ _ | Withdraw _ _ _ | Export _ _ _ | Tick | Promote _ _ _ | Inspect _ _ _ =>
        simp [Action.isRevision]
      | Challenge _ | Revoke _ | Repair _ _ =>
        simp [isContestationAction] at h_not_contest
    simp [h_not_rev, ih h_rest]

/-- CORNER 6 TRACE THEOREM: Under all-restricted traces (no contestation ever),
    ¬Revoked is preserved across ALL steps — not just one.

    This extends `frozen_canon_no_revocation` (single restricted step) to
    full traces of arbitrary length. If every action in the trace is
    non-contestation, then ¬Revoked at the start implies ¬Revoked
    after any number of steps. The claim “contestation-blocking causes
    deposits to persist" holds for traces of arbitrary length. -/
theorem frozen_canon_no_revocation_trace
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (t : Trace (Reason := Reason) (Evidence := Evidence) s s')
    (d_idx : Nat)
    (h_restricted : allRestrictedTrace t)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_get : s.ledger.get? d_idx = some d)
    (h_not_revoked : d.status ≠ .Revoked) :
    ∀ d', s'.ledger.get? d_idx = some d' → d'.status ≠ .Revoked := by
  have h_no_rev := allRestricted_implies_no_revision t h_restricted
  have h_init : ∀ d'', s.ledger.get? d_idx = some d'' → d''.status ≠ .Revoked := by
    intro d'' h_get''
    rw [h_get] at h_get''
    have h_eq : d = d'' := by injection h_get''
    rw [← h_eq]; exact h_not_revoked
  exact trace_no_revision_preserves_non_revoked s s' t h_no_rev d_idx h_init


/-! ## Corner 7 — τ staleness gate (timeless justification fails under drift)

    **Theorem shape:** If the system lacks τ-aware refresh gating, then
    there exists a trace where an unrefreshed deposit remains action-authorizing
    across time drift, whereas τ-aware policy blocks it.

    **Implementation:** We show that withdrawal REQUIRES τ_valid (via
    Step.withdraw precondition), so time drift without refresh blocks withdrawal. -/

/-- Stale: a deposit's τ is no longer valid relative to the clock.
    This is the negation of τ_valid. -/
def Stale (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat) : Prop :=
  ∃ d, s.ledger.get? d_idx = some d ∧ ¬τ_valid s.clock d.h.τ

/-- CORNER 7 THEOREM: Withdrawal requires non-staleness.

    The Step.withdraw constructor explicitly requires isCurrentDeposit,
    which includes τ_valid. This is the τ gate. -/
theorem withdrawal_requires_fresh
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s') :
    isCurrentDeposit s d_idx := by
  cases h_step with
  | withdraw _ _ _ _ h_current _ => exact h_current

/-- CORNER 7 COROLLARY: Stale deposits cannot be withdrawn.

    If a deposit is stale, no withdrawal step can fire for it.
    This formalizes "timeless justification fails under drift." -/
theorem stale_blocks_withdrawal
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat)
    (h_stale : Stale s d_idx) :
    ¬∃ s', Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s' := by
  intro ⟨s', h_step⟩
  have h_current := withdrawal_requires_fresh s s' a B d_idx h_step
  let ⟨d, h_get, h_not_valid⟩ := h_stale
  let ⟨d', h_get', h_valid⟩ := h_current
  -- d and d' are the same deposit at d_idx
  rw [h_get] at h_get'
  injection h_get' with h_eq
  rw [← h_eq] at h_valid
  exact h_not_valid h_valid

/-- Time drift makes deposits stale.

    If clock advances past deposit's τ, the deposit becomes stale.
    This is the "drift" that τ-unaware systems ignore. -/
theorem tick_can_cause_staleness
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_get : s.ledger.get? d_idx = some d)
    (new_clock : Time)
    (h_past : new_clock < d.h.τ) :
    Stale { s with clock := new_clock } d_idx := by
  refine ⟨d, ?_, ?_⟩
  · simp only [h_get]
  · unfold τ_valid
    exact Nat.not_le_of_gt h_past


/-! ## Corner 9 — ACL/bubbles gate (leakage is structural if ACL ignored)

    **Theorem shape:** If export ignores ACL, a restricted deposit can
    become visible in a bubble lacking permission.

    **Implementation:** We define visibility and show that export
    preserves bubble assignment, making deposits visible in new bubbles. -/

/-- A deposit is visible in a bubble if it exists in that bubble. -/
def VisibleInBubble (s : SystemState PropLike Standard ErrorModel Provenance)
    (B : Bubble) (d_idx : Nat) : Prop :=
  ∃ d, s.ledger.get? d_idx = some d ∧ d.bubble = B

/-- CORNER 9 THEOREM: Export makes deposits visible in new bubbles.

    After an export step from B1 to B2, the exported deposit becomes
    visible in B2 (as a new entry at the end of the ledger). -/
theorem export_creates_visibility
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (B1 B2 : Bubble) (d_idx : Nat)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Export B1 B2 d_idx) s')
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_get : s.ledger.get? d_idx = some d) :
    -- The new deposit at the end of s'.ledger is visible in B2
    VisibleInBubble s' B2 s.ledger.length := by
  cases h_step with
  | export_with_bridge _ _ _ _ _ _ =>
    unfold VisibleInBubble addToNewBubble
    simp only [h_get]
    -- s'.ledger = s.ledger ++ [{ d with bubble := B2, status := .Candidate }]
    -- s'.ledger.get? s.ledger.length = some { d with bubble := B2, ... }
    refine ⟨{ d with bubble := B2, status := .Candidate }, ?_, rfl⟩
    -- Need: (s.ledger ++ [new]).get? s.ledger.length = some new
    have _h_len : s.ledger.length < (s.ledger ++ [{ d with bubble := B2, status := .Candidate }]).length := by
      simp [List.length_append]
      exact Nat.lt_succ_self _
    -- get? at length of original list gives the appended element
    have h_get_append : (s.ledger ++ [{ d with bubble := B2, status := .Candidate }]).get? s.ledger.length =
        some { d with bubble := B2, status := .Candidate } := by
      induction s.ledger with
      | nil => simp [List.get?]
      | cons x xs ih =>
        simp only [List.cons_append, List.get?, List.length]
        exact ih
    exact h_get_append
  | export_revalidate _ _ _ _ _ _ =>
    unfold VisibleInBubble addToNewBubble
    simp only [h_get]
    refine ⟨{ d with bubble := B2, status := .Candidate }, ?_, rfl⟩
    have h_get_append : (s.ledger ++ [{ d with bubble := B2, status := .Candidate }]).get? s.ledger.length =
        some { d with bubble := B2, status := .Candidate } := by
      induction s.ledger with
      | nil => simp [List.get?]
      | cons x xs ih =>
        simp only [List.cons_append, List.get?, List.length]
        exact ih
    exact h_get_append

/-- CORNER 9 COROLLARY (A.S4): Export creates a Candidate copy in B2 — step alone suffices.

    A cleaner statement than `export_creates_visibility`: the caller need not supply
    the deposit or its `get?` proof.  An export Step carries the `isDeposited`
    precondition internally, so we can extract the deposit and prove membership
    directly.  The returned element has `bubble = B2` and `status = .Candidate`. -/
theorem export_creates_B2_deposit
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (B1 B2 : Bubble) (d_idx : Nat)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Export B1 B2 d_idx) s') :
    ∃ d_new, d_new ∈ s'.ledger ∧ d_new.bubble = B2 ∧ d_new.status = .Candidate := by
  cases h_step with
  | export_with_bridge _ _ _ h_dep _ _ =>
    let ⟨d, h_get, _⟩ := h_dep
    refine ⟨{ d with bubble := B2, status := .Candidate }, ?_, rfl, rfl⟩
    unfold addToNewBubble
    simp only [h_get]
    have h_m := mem_append_iff { d with bubble := B2, status := .Candidate } s.ledger
                  [{ d with bubble := B2, status := .Candidate }]
    rw [h_m]
    exact Or.inr (List.Mem.head _)
  | export_revalidate _ _ _ h_dep _ _ =>
    let ⟨d, h_get, _⟩ := h_dep
    refine ⟨{ d with bubble := B2, status := .Candidate }, ?_, rfl, rfl⟩
    unfold addToNewBubble
    simp only [h_get]
    have h_m := mem_append_iff { d with bubble := B2, status := .Candidate } s.ledger
                  [{ d with bubble := B2, status := .Candidate }]
    rw [h_m]
    exact Or.inr (List.Mem.head _)

/-- CORNER 9 COROLLARY: Without ACL checks on export, any deposit can cross bubbles.

    The current export steps require isDeposited and depositHasHeader,
    but NOT ACL permission for the target bubble. This means exports
    can create visibility in bubbles without permission checks.

    This corners systems that ignore ACL on boundary crossing. -/
theorem export_ignores_target_acl
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (B1 B2 : Bubble) (d_idx : Nat)
    (h_deposited : isDeposited s d_idx)
    (h_header : depositHasHeader s d_idx)
    (h_bridge : hasTrustBridge s B1 B2)
    -- Note: NO ACL requirement for B2!
    : ∃ s', Step (Reason := Reason) (Evidence := Evidence) s (.Export B1 B2 d_idx) s' := by
  exact ⟨_, Step.export_with_bridge s B1 B2 d_idx h_deposited h_header h_bridge⟩


/-! ## Lottery Gate (Operational)

    `Step.withdraw` requires `isDeposited` as a hard precondition.
    Without a Deposited-status deposit the withdrawal transition is
    simply uninhabited — the operational machinery is blocked, not
    merely mislabelled.

    This is the step-grounded bridge between the case-type taxonomy
    (EpArch.Theorems.Cases.TypeErrors: LotteryIsTypeError) and the architectural dissolution
    below (Corner 2: lottery_paradox_dissolved_architecturally,
    candidate_blocks_withdrawal). -/

/-- Without an authorized deposit, no withdrawal Step can fire.
    `Step.withdraw` carries `h_deposited : isDeposited s d_idx` as a
    precondition; `h` provides `¬isDeposited`, so the Step is uninhabited. -/
theorem lottery_no_deposit_blocks_withdraw
    (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat)
    (h : ¬isDeposited s d_idx) :
    ¬∃ (s' : SystemState PropLike Standard ErrorModel Provenance) (a : Agent) (B : Bubble),
      Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s' := by
  intro ⟨_, _, _, h_step⟩
  cases h_step
  exact absurd ‹isDeposited s d_idx› h


/-! ## Corner 2 — Candidate/Deposited gate (lottery paradox blocked by lifecycle)

    **Theorem shape:** The lifecycle separation (Candidate vs Deposited)
    blocks premature authorization. A deposit must pass through validation
    before it can be withdrawn.

    **Implementation:** We show that withdrawal requires Deposited status,
    and new submissions enter as Candidate, so there's a mandatory gap. -/

/-- CORNER 2 THEOREM: Withdrawal requires Deposited status.

    You cannot withdraw from a Candidate deposit — it must be promoted
    to Deposited first. This is the "validation gate." -/
theorem withdrawal_requires_deposited
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s') :
    isDeposited s d_idx := by
  cases h_step with
  | withdraw _ _ _ _ _ h_dep => exact h_dep

/-- CORNER 2 THEOREM: New deposits enter as Candidate.

    Submissions cannot directly enter as Deposited — they must go through
    the Candidate → Deposited lifecycle. -/
theorem submit_produces_candidate
    (s s' : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_step : Step (Reason := Reason) (Evidence := Evidence) s (.Submit a d) s') :
    ∃ d', d' ∈ s'.ledger ∧ d'.status = .Candidate := by
  cases h_step
  refine ⟨{ d with status := .Candidate }, ?_, rfl⟩
  have h := mem_append_iff { d with status := DepositStatus.Candidate } s.ledger [{ d with status := DepositStatus.Candidate }]
  rw [h]
  exact Or.inr (List.Mem.head _)

/-- CORNER 2 COROLLARY: Candidate deposits cannot be withdrawn.

    This is the "lottery paradox blocker" — high credence (submission)
    does not equal authorization (Deposited). -/
theorem candidate_blocks_withdrawal
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (a : Agent) (B : Bubble) (d_idx : Nat)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_get : s.ledger.get? d_idx = some d)
    (h_candidate : d.status = .Candidate) :
    ¬∃ s', Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s' := by
  intro ⟨s', h_step⟩
  have h_deposited := withdrawal_requires_deposited s s' a B d_idx h_step
  let ⟨d', h_get', h_status'⟩ := h_deposited
  rw [h_get] at h_get'
  injection h_get' with h_eq
  rw [← h_eq, h_candidate] at h_status'
  cases h_status'


/-! ## Lottery Dissolution Gate (Extended)

    This section extends Corner 2 with explicit "closure" theorems showing
    how the Candidate/Deposited distinction blocks the lottery paradox.

    **Key insight:** The lottery paradox arises when high credence
    (I believe each ticket will lose) implies authorization
    (I can act as if I know they'll all lose). The status distinction
    breaks this: Candidate (high credence) ≠ Deposited (authorized). -/

/-! ## Corner 1 — Type-separation gate (one-state accounts can't do both jobs)

    **Theorem shape:** Traction (individual action-guiding) and Authorization
    (collective reliance / exportable) require different predicates. A single
    predicate cannot satisfy both without over-authorization or under-traction.

    **Implementation:** We define the two requirements and show they're
    structurally incompatible in edge cases. -/

/-- Traction requirement: an agent can act on P under uncertainty.
    This is the "lottery case" — I can act on "my ticket will lose"
    even without full validation, because the expected value is clear. -/
def AllowsTraction (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) : Prop :=
  -- Traction doesn't require Deposited — Candidate suffices for personal action
  ∃ d, s.ledger.get? d_idx = some d ∧ (d.status = .Candidate ∨ d.status = .Deposited)

/-- Authorization requirement: others can rely on P / it can be exported.
    This is the "knowledge" requirement — must be validated. -/
def AllowsAuthorization (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) : Prop :=
  -- Authorization requires Deposited — Candidate is not enough
  isDeposited s d_idx

/-- CORNER 1 COROLLARY: Authorization implies Traction, but not vice versa.

    If something is authorized (Deposited), you can certainly act on it.
    But you can act (Candidate) without authorization. -/
theorem authorization_implies_traction
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat)
    (h_auth : AllowsAuthorization s d_idx) :
    AllowsTraction s d_idx := by
  let ⟨d, h_get, h_status⟩ := h_auth
  exact ⟨d, h_get, Or.inr h_status⟩


/-! ## Lottery Dissolution Theorem Completion

    This theorem completes the lottery dissolution gate by showing that
    the Candidate/Deposited distinction creates exactly the gap needed. -/

/-- LOTTERY DISSOLUTION 3: The architecture is the solution.

    Summary theorem: The lottery paradox is dissolved architecturally by
    requiring explicit promotion from Candidate to Deposited.

    - Individual high-credence beliefs → Candidate (personal traction OK)
    - Authorized knowledge → Deposited (collective reliance OK)
    - Conjunction closure → NOT automatic (no lottery paradox)

    This is not a "solution to the lottery paradox" in the philosophical
    sense — it's a structural reason why the paradox doesn't arise in
    EpArch: the type system enforces the distinction. -/
theorem lottery_paradox_dissolved_architecturally
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_get : s.ledger.get? d_idx = some d)
    (h_candidate : d.status = .Candidate) :
    -- Candidate gives traction...
    AllowsTraction s d_idx ∧
    -- ...but NOT authorization
    ¬AllowsAuthorization s d_idx := by
  constructor
  · -- Candidate gives traction
    exact ⟨d, h_get, Or.inl h_candidate⟩
  · -- Candidate does NOT give authorization
    intro ⟨d', h_get', h_deposited⟩
    rw [h_get] at h_get'
    injection h_get' with h_eq
    rw [← h_eq, h_candidate] at h_deposited
    cases h_deposited


/-! ## Corner 8 — Bounded hygiene gate (scarcity forces TTL/triage policies)

    **Theorem shape:** If obligations require revalidating everything always,
    then for finite budget there exists a state where obligations can't be met.

    **Implementation:** A simple counting argument — more deposits than budget
    means some deposits can't be revalidated. -/

/-- Revalidation budget: how many deposits can be revalidated per cycle. -/
structure HygieneBudget where
  max_revalidations : Nat

/-- CORNER 8 THEOREM: Finite budget forces triage.

    If the ledger has more deposits than the budget allows for revalidation,
    then not all deposits can be revalidated in one cycle. -/
theorem finite_budget_forces_triage
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (budget : HygieneBudget)
    (h_overflow : s.ledger.length > budget.max_revalidations) :
    -- There exists some deposit that cannot be revalidated this cycle
    ∃ d_idx, d_idx < s.ledger.length ∧ d_idx ≥ budget.max_revalidations := by
  -- Take d_idx = budget.max_revalidations
  refine ⟨budget.max_revalidations, h_overflow, Nat.le_refl _⟩


/-! ## Entrenchment — Pathological Ladder State

    **Theorem shape:** An entrenched agent (Certainty + structural refusal to
    revise) who acts on a deposit that has been quarantined or revoked in the
    Bank violates safe withdrawal.

    **Implication:** Entrenchment is not mere stubbornness — it is an
    architectural defect. The agent's Ladder says "settled premise" while
    the Bank says "authorization suspended/revoked." Normal Certainty would
    re-check and demote; Entrenchment bypasses review entirely.

    This is the agent-level analog of Corner 6 (frozen_canon_no_revocation),
    which is bubble-level: if contestation actions are blocked system-wide,
    bad deposits persist. Entrenchment localizes the same pathology to a
    single agent's Ladder state. -/

/-- An entrenched agent: has certainty on P and structurally refuses
    to revise when the Bank signals quarantine or revocation. -/
structure EntrenchedAgent where
  agent : Agent
  claim : Claim
  /-- Agent treats P as settled premise (Certainty) -/
  has_certainty : certainty_L agent claim
  /-- Agent's revision channel is disconnected (opaque, non-trivial) -/
  refuses_demotion : ignores_bank_signal agent claim

/-- The Bank has suspended or revoked the deposit backing P. -/
def deposit_no_longer_active
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) : Prop :=
  ∃ d, s.ledger.get? d_idx = some d ∧
    (d.status = .Quarantined ∨ d.status = .Revoked)

/-- ENTRENCHMENT THEOREM: An entrenched agent who relies on a
    quarantined/revoked deposit cannot satisfy safe withdrawal.

    Forcing argument:
    1. Agent is at Certainty on P → treats P as closed premise
    2. Bank has quarantined or revoked the deposit backing P
    3. Normal revision would demote P to Belief or Ignorance
    4. Entrenchment blocks step 3 → agent still acts on P
    5. But withdrawal requires isDeposited (status = .Deposited)
    6. Quarantined/Revoked ≠ Deposited → withdrawal gate fails

    Therefore: Entrenchment + Bank status change → ¬safe withdrawal.
    Entrenchment blocks the demotion that Bank status change would require.

    The conclusion is a three-way conjunction, all genuinely proved from `ea`:
    - `certainty_L ea.agent ea.claim`: from `ea.has_certainty`; unfolds to
      `ladder_stage ea.agent ea.claim = .Certainty` (agent is at Ladder top)
    - `ignores_bank_signal ea.agent ea.claim`: from `ea.refuses_demotion` (opaque, non-trivial)
    - `¬isDeposited s d_idx`: from `h_inactive` (structural, the core pathology)
    All three fields of `ea` now participate in the proof. -/
theorem entrenchment_breaks_safe_withdrawal
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (ea : EntrenchedAgent)
    (d_idx : Nat)
    (h_inactive : deposit_no_longer_active s d_idx) :
    certainty_L ea.agent ea.claim ∧ ignores_bank_signal ea.agent ea.claim ∧ ¬isDeposited s d_idx := by
  refine ⟨ea.has_certainty, ea.refuses_demotion, ?_⟩
  intro h_dep
  let ⟨d, h_get, h_status⟩ := h_inactive
  let ⟨d', h_get', h_deposited⟩ := h_dep
  rw [h_get] at h_get'
  injection h_get' with h_eq
  rw [← h_eq] at h_deposited
  cases h_status with
  | inl h_q => rw [h_q] at h_deposited; cases h_deposited
  | inr h_r => rw [h_r] at h_deposited; cases h_deposited

/-- ENTRENCHMENT COROLLARY: An entrenched agent cannot withdraw from
    the Bank when the deposit has been quarantined or revoked.

    This combines entrenchment_breaks_safe_withdrawal with
    withdrawal_requires_deposited to show no Step.withdraw can fire. -/
theorem entrenched_cannot_withdraw
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (ea : EntrenchedAgent)
    (a : Agent) (B : Bubble) (d_idx : Nat)
    (h_inactive : deposit_no_longer_active s d_idx) :
    ¬∃ s', Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s' := by
  intro ⟨s', h_step⟩
  have h_dep := withdrawal_requires_deposited s s' a B d_idx h_step
  exact (entrenchment_breaks_safe_withdrawal s ea d_idx h_inactive).2.2 h_dep

end EpArch
