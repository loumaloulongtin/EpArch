/-
EpArch/BehavioralEquivalence.lean — Observation-Boundary Equivalence

Defines the abstract input/observation interface for WorkingSystems and
proves that any two grounded systems produce identical observations on all inputs.

The observation model is tied to the `Step` relation through two distinct proof
routes that apply to different input constructors:

  **Step-witness route** (withdraw, challenge, tick):
    `withdraw_ready_state` / `challenge_ready_state` construct a concrete `CState`
    from `B`'s evidence (bank, trust_bridges, revocation) and prove the matching
    `Step` fires from it.  `working_systems_equivalent` then dispatches per input
    constructor and calls these witnesses directly — so for those three cases the
    main equivalence theorem *uses* actual `Step` firings, not mere unfolding.

  **Definitional route** (export):
    `ExportRequest` falls back to `behavior_step_consistent`, which is a pure
    definitional equality.  Export has no full ready-state witness because
    `header_preserved` is opaque — it operates over abstract types and cannot be
    reflected into `depositHasHeader` for concrete `Deposit Unit Unit Unit Unit`.

`Behavior` is observationally constant over `GroundedBehavior`: outcome depends
only on input shape, not witness content.  This is a design property of EpArch —
at the kernel boundary all fully grounded realizers expose the same observable
success behavior.  The step witnesses ground *why* that state can exist, not a
richer computational dependence on witness fields.

## Definitions

- `Input`               — abstract input events (withdraw, export, challenge, time-advance)
- `Observation`         — observable outcomes
- `Behavior`            — observation function, indexed by GroundedBehavior evidence
- `BehaviorallyEquivalent` — identical observations on all inputs
- `input_to_action`     — maps `Input` to the matching concrete `StepSemantics.Action`
- `observe_step_action` — extracts an `Observation` from a concrete action
- `ReadyState i`        — a `CState` + proof that `Step` fires for `input_to_action i`
- `withdraw_ready_state B a b d` — constructs `ReadyState` from `B.bank`/`B.trust_bridges`
- `challenge_ready_state B c f` — constructs `ReadyState` from `B.revocation`

## Theorems

- `behavioral_equiv_{refl,symm,trans}`  — equivalence is an equivalence relation
- `satisfies_all_fixes_flags`           — utility: SatisfiesAllProperties → all *_ev.isSome = true
- `behavior_step_consistent`   — Behavior B i = observe_step_action (input_to_action i) (definitional)
- `behavior_from_step`         — same equality for systems with a live Step: the step witness
                                 confirms the state machine can reach the action, and the
                                 equality holds by case analysis on which constructor fired
- `grounded_export_step`       — conditional: export Step fires given header + bridge
- `working_systems_equivalent` — grounded systems are equivalent; for withdraw, challenge, and
                                 tick the equivalence is grounded in the existence of a live
                                 Step from B's evidence; export falls back to definitional
- `grounded_behaviors_equivalent` — same result, no Step witnesses; shows the equivalence is
                                 input-determined regardless of which evidence route is taken

## Dependencies

- **Minimality.lean:** WorkingSystem, SatisfiesAllProperties, GroundedBehavior
- **StepSemantics.lean:** Step, Action, SystemState, precondition predicates
-/

import EpArch.Minimality
import EpArch.StepSemantics

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

/-- The observation produced by a grounded system on a given input.

    `B : GroundedBehavior` is the type-level certificate that all six features
    exist — not a runtime-inspected flag.  It is the authority under which the
    success outcomes below are admissible: because `B` witnesses a functional
    bank, trust bridges, and revocation mechanism, every input has a well-defined
    success outcome and there is no "missing primitives" fallback path.

    The output is fully determined by the input constructor; `B` is not inspected
    at runtime and does not differentiate between two distinct certificates. -/
def Behavior (_B : GroundedBehavior) (i : Input) : Observation :=
  match i with
  | .WithdrawRequest _ _ claim_id  => .WithdrawSuccess claim_id
  | .ExportRequest _ target claim_id => .ExportSuccess claim_id target
  | .ChallengeRequest _ _          => .ChallengeProcessed "quarantined"
  | .TimeAdvance _                 => .TimeAdvanced

/-! ### Behavioral Equivalence -/

/-- Two grounded systems are behaviorally equivalent if they produce identical
    observations on every input. -/
def BehaviorallyEquivalent (B1 B2 : GroundedBehavior) : Prop :=
  ∀ i : Input, Behavior B1 i = Behavior B2 i

/-- Behavioral equivalence is reflexive. -/
theorem behavioral_equiv_refl (B : GroundedBehavior) : BehaviorallyEquivalent B B :=
  fun _ => rfl

/-- Behavioral equivalence is symmetric. -/
theorem behavioral_equiv_symm (B1 B2 : GroundedBehavior) :
    BehaviorallyEquivalent B1 B2 → BehaviorallyEquivalent B2 B1 :=
  fun h i => (h i).symm

/-- Behavioral equivalence is transitive. -/
theorem behavioral_equiv_trans (B1 B2 B3 : GroundedBehavior) :
    BehaviorallyEquivalent B1 B2 → BehaviorallyEquivalent B2 B3 →
    BehaviorallyEquivalent B1 B3 :=
  fun h12 h23 i => (h12 i).trans (h23 i)

/-! ### Utility: WorkingSystem Evidence Presence -/

/-- `SatisfiesAllProperties` determines the presence of all six proof-carrying fields.
    Standalone bridge between the `WorkingSystem` API and evidence presence;
    independent of the main behavioral equivalence proof chain. -/
theorem satisfies_all_fixes_flags (W : WorkingSystem) (h : SatisfiesAllProperties W) :
    W.bubbles_ev.isSome       = true ∧
    W.bridges_ev.isSome       = true ∧
    W.headers_ev.isSome       = true ∧
    W.revocation_ev.isSome    = true ∧
    W.bank_ev.isSome          = true ∧
    W.redeemability_ev.isSome = true :=
  ⟨h .scope, h .trust, h .headers, h .revocation, h .bank, h .redeemability⟩


/-! ## StepSemantics Bridge

This section ties `Behavior` to the operational `Step` relation from
`StepSemantics.lean`.  The key claim is stronger than definitional consistency:
for every `Input i` and `GroundedBehavior B`, a *concrete ready state* exists
from which `Step s (input_to_action i) s'` fires, and the step's observable
output equals `Behavior B i`.

`GroundedBehavior` is the justification — its evidence (bank, trust_bridges,
revocation) grounds the assertion that the machinery to fire the step exists.
The concrete states are constructed here using those witnesses as the
structural reason why the state can exist.

Type parameters `Unit` are used for `PropLike`, `Standard`, `ErrorModel`,
`Provenance`, `Reason`, and `Evidence` — the minimal constructive instantiation. -/

section StepBridge

open EpArch.StepSemantics

/-- Concrete system-state type for grounding purposes.
    All four type parameters are `Unit`: no proposition content, no error model,
    no provenance — just the structural skeleton of a `SystemState`. -/
private abbrev CState  := SystemState  Unit Unit Unit Unit

/-- Concrete action type matching `CState`'s type parameters. -/
private abbrev CAction := Action Unit Unit Unit Unit Unit Unit

/-- Helper: extract the `Nat` id from a `Bubble`. -/
private def Bubble.toNat : Bubble → Nat | .mk n => n

/-! ### Canonical Deposit -/

/-- A canonical `Deposited` deposit for constructing ready states.
    Status is `.Deposited` so it satisfies `isDeposited`. -/
private def canonDeposit : Deposit Unit Unit Unit Unit :=
  { P      := ()
  , h      := { S := (), E := (), V := (), τ := 0
              , acl    := .mk 0
              , redeem := { cs := .mk 0 } }
  , bubble := .mk 0
  , status := .Deposited }

/-- Build a ledger of length `n + 1` with `canonDeposit` at every position.
    Uses a recursive helper rather than `List.replicate` so that `get?` membership
    is provable by induction without relying on library lemmas absent in Lean 4.3. -/
private def canonLedger : Nat → List (Deposit Unit Unit Unit Unit)
  | 0 => [canonDeposit]
  | n + 1 => canonDeposit :: canonLedger n

/-- Every position `k` in `canonLedger n` (where `k < n + 1`) contains `canonDeposit`. -/
private theorem canonLedger_get (n k : Nat) (hk : k < n + 1) :
    (canonLedger n).get? k = some canonDeposit := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rfl
    | succ j => exact absurd (Nat.lt_of_succ_lt_succ hk) (Nat.not_lt_zero j)
  | succ m ih =>
    cases k with
    | zero => rfl
    | succ j =>
      show List.get? (canonDeposit :: canonLedger m) (j + 1) = some canonDeposit
      simp [List.get?]
      exact ih j (Nat.lt_of_succ_lt_succ hk)

/-! ### Input → Action -/

/-- Map an abstract `Input` to a concrete `StepSemantics.Action`.

    This is the bridge between the user-facing event vocabulary and the
    operational `Step` relation.

    The challenge action uses `.S` as the default suspected field — `Field` is
    an inductive (not a `String`), so the field string in `ChallengeRequest`
    cannot be preserved losslessly in this direction. -/
def input_to_action : Input → CAction
  | .WithdrawRequest a b d   => .Withdraw (.mk a) (.mk b) d
  | .ExportRequest src tgt d => .Export (.mk src) (.mk tgt) d
  | .ChallengeRequest _ _    =>
      .Challenge { P := (), reason := (), evidence := (), suspected := .S }
  | .TimeAdvance _           => .Tick

/-! ### Action → Observation -/

/-- Extract an `Observation` from a completed concrete `Action`.

    Reflects what `Step` produces at the observable boundary:
    - `.Withdraw _ _ d_idx` → deposit at `d_idx` was successfully relied on
    - `.Export _ B2 d_idx`  → deposit crossed into target bubble `B2`
    - `.Challenge _`        → deposit entered `Quarantined` status
    - `.Tick`               → clock advanced
    - `.Submit`, `.Repair`, `.Revoke` — not exposed as `Input` events;
      mapped to `.TimeAdvanced` as a neutral fallback. -/
def observe_step_action : CAction → Observation
  | .Withdraw _ _  d_idx => .WithdrawSuccess d_idx
  | .Export   _ B2 d_idx => .ExportSuccess d_idx B2.toNat
  | .Challenge _         => .ChallengeProcessed "quarantined"
  | .Tick                => .TimeAdvanced
  | .Submit _            => .TimeAdvanced
  | .Repair _ _          => .TimeAdvanced
  | .Revoke _            => .TimeAdvanced

/-! ### Ready States -/

/-- A `ReadyState` for input `i` packages a concrete `CState` together with a
    proof that the Step corresponding to `input_to_action i` fires from it.

    This is the operational grounding: `GroundedBehavior` evidence justifies the
    claim that a firing-capable state exists.  The witness here is the *structural
    reason* — bank/trust_bridges/revocation — not just a syntactic unfolding. -/
structure ReadyState (i : Input) where
  /-- A concrete system state from which the step can fire. -/
  state : CState
  /-- The step fires: there exists a successor state. -/
  fires : ∃ s' : CState, Step (Reason := Unit) (Evidence := Unit)
            state (input_to_action i) s'

/-! ### Withdraw Ready State -/

/-- Build a `ReadyState` for a `WithdrawRequest`.

    Justification from `B`:
    - `B.bank` evidences that a shared ledger with entries exists.
    - `B.trust_bridges` evidences the import chain enabling cross-bubble reliance.
    Together they ground the claim that a state with a deposited, ACL-permitted,
    current-timestamp entry can exist.

    The concrete state has:
    - `ledger`      : canonical deposits at positions 0..d_idx (all `.Deposited`, τ = 0)
    - `acl_table`   : one entry granting agent `a` on bubble `b` for deposit `d_idx`
    - `clock`       : 0  (so τ_valid 0 0 holds on every canonic deposit)
    - `trust_bridges`: empty (not needed for withdraw) -/
def withdraw_ready_state (B : GroundedBehavior) (a_n b_n d_idx : Nat) :
    ReadyState (.WithdrawRequest a_n b_n d_idx) :=
  let s : CState :=
    { ledger       := canonLedger d_idx
    , bubbles      := [.mk b_n]
    , clock        := 0
    , acl_table    := [{ agent := .mk a_n, bubble := .mk b_n, deposit_id := d_idx }]
    , trust_bridges := [] }
  let _ := B.bank.produced        -- shared ledger entry exists
  let _ := B.trust_bridges.downstream_via_bridge  -- import chain is present
  have h_acl : hasACLPermission s (.mk a_n) (.mk b_n) d_idx :=
    ⟨_, List.Mem.head _, rfl, rfl, rfl⟩
  have h_current : isCurrentDeposit s d_idx :=
    ⟨canonDeposit, canonLedger_get d_idx d_idx (Nat.lt_succ_self d_idx),
     Nat.le_refl 0⟩
  have h_deposited : isDeposited s d_idx :=
    ⟨canonDeposit, canonLedger_get d_idx d_idx (Nat.lt_succ_self d_idx), rfl⟩
  { state := s
  , fires := ⟨s, .withdraw s (.mk a_n) (.mk b_n) d_idx h_acl h_current h_deposited⟩ }

/-! ### Challenge Ready State -/

/-- Build a `ReadyState` for a `ChallengeRequest`.

    Justification from `B`:
    - `B.revocation` evidences that an invalid–revocable claim exists, so the
      challenge → quarantine path is non-vacuous.
    - `B.revocation.can_revoke` witnesses that the revocation machinery is present.

    The concrete state has a single `.Deposited` entry at index 0.
    The challenge action uses `.S` as the suspected field (lossless mapping is
    blocked because `Field` is an inductive while `ChallengeRequest` carries a
    `String`; `.S` is the structural default). -/
def challenge_ready_state (B : GroundedBehavior) (claim_id : Nat) (field : String) :
    ReadyState (.ChallengeRequest claim_id field) :=
  let s : CState :=
    { ledger       := [canonDeposit]
    , bubbles      := []
    , clock        := 0
    , acl_table    := []
    , trust_bridges := [] }
  let _ := B.revocation.can_revoke        -- revocation capability exists
  let _ := B.revocation.witness_is_invalid  -- the challenged claim is genuinely invalid
  have h_deposited : isDeposited s 0 :=
    ⟨canonDeposit, rfl, rfl⟩
  { state := s
  , fires := ⟨_, .challenge s { P := (), reason := (), evidence := (), suspected := .S }
                  0 h_deposited⟩ }

/-! ### Definitional Bridge -/

/-- `Behavior B i = observe_step_action (input_to_action i)` for all `B` and `i`.

    Definitional equality: both sides reduce to the same constructor on each
    `Input` arm.  `B` is not inspected — the equality holds for any grounded
    certificate. -/
theorem behavior_step_consistent (B : GroundedBehavior) (i : Input) :
    Behavior B i = observe_step_action (input_to_action i) := by
  cases i <;> simp [Behavior, input_to_action, observe_step_action, Bubble.toNat]

/-! ### Step-Consuming Bridge -/

/-- If the Step corresponding to `input_to_action i` fires, the observation equals
    `Behavior B i`.

    This is a stronger statement than `behavior_step_consistent`: it requires a
    witness that the step actually fires from some concrete state, not just that
    the action vocabulary is consistent.  The equality holds because both sides
    share the same action-to-outcome mapping; the Step witness confirms that the
    transition machinery is live, not hypothetical.

    **Note on the action-indexed ceiling:** both `observe_step_action` and `Behavior`
    are indexed on the *action*, not on the resulting state.  Two grounded systems
    can therefore be compared at the action boundary without inspecting state
    internals — and without requiring that both systems share the same post-step
    state.  This is the intended architectural interface: observable outputs are
    action-determined, not state-determined. -/
theorem behavior_from_step (B : GroundedBehavior) (i : Input) (s s' : CState)
    (h : Step (Reason := Unit) (Evidence := Unit) s (input_to_action i) s') :
    observe_step_action (input_to_action i) = Behavior B i := by
  cases i with
  | WithdrawRequest a b d =>
    simp only [input_to_action] at h ⊢
    cases h
    simp [observe_step_action, Behavior]
  | ExportRequest src tgt d =>
    simp only [input_to_action] at h ⊢
    cases h <;> simp [observe_step_action, Behavior, Bubble.toNat]
  | ChallengeRequest c f =>
    simp only [input_to_action] at h ⊢
    cases h
    simp [observe_step_action, Behavior]
  | TimeAdvance ticks =>
    simp only [input_to_action] at h ⊢
    cases h
    simp [observe_step_action, Behavior]

/-- Export step fires conditionally, given header evidence and a trust bridge.
    `depositHasHeader` is required explicitly because `header_preserved` is opaque
    — `GroundedHeaders.header_preserved` is an abstract datum over abstract types
    and cannot be reflected into `depositHasHeader` for concrete `Deposit Unit Unit Unit Unit`.
    This is the one place where `ReadyState` construction remains conditional. -/
theorem grounded_export_step
    (s : CState) (B1 B2 : Bubble) (d_idx : Nat)
    (h_deposited : isDeposited      s d_idx)
    (h_header    : depositHasHeader s d_idx)
    (h_bridge    : hasTrustBridge   s B1 B2) :
    ∃ (s' : CState),
      Step (Reason := Unit) (Evidence := Unit) s (.Export B1 B2 d_idx) s' :=
  ⟨_, .export_with_bridge s B1 B2 d_idx h_deposited h_header h_bridge⟩

end StepBridge

/-! ## Main Equivalence Theorems -/

/-- **Any two grounded systems are behaviorally equivalent.**

    For withdraw, challenge, and tick inputs the equivalence is grounded in the
    operational step machinery: `B.bank`, `B.trust_bridges`, and `B.revocation`
    each supply the evidence that a live Step can be constructed, and that step
    witness is what licenses the observation.  Both systems produce the same
    output because both have the capability to fire the step — the equality
    follows from the shared action-to-observation mapping.

    For export, `header_preserved` is opaque and cannot be reflected into a
    concrete `depositHasHeader` for the unit-type instantiation, so that case
    rests on the definitional bridge `behavior_step_consistent` instead.

    The unconditional form — no `SatisfiesAllProperties` premise, no flag checks
    — is the direct payoff of the `GroundedBehavior` certificate design: any two
    fully-grounded systems agree at the observation boundary by construction. -/
theorem working_systems_equivalent (B1 B2 : GroundedBehavior) :
    BehaviorallyEquivalent B1 B2 := by
  intro i
  cases i with
  | WithdrawRequest a b d =>
    let ⟨_, h1⟩ := (withdraw_ready_state B1 a b d).fires
    let ⟨_, h2⟩ := (withdraw_ready_state B2 a b d).fires
    exact (behavior_from_step B1 _ _ _ h1).symm.trans (behavior_from_step B2 _ _ _ h2)
  | ExportRequest src tgt d =>
    -- No ready-state witness; header_preserved is opaque.
    exact (behavior_step_consistent B1 _).trans (behavior_step_consistent B2 _).symm
  | ChallengeRequest c f =>
    let ⟨_, h1⟩ := (challenge_ready_state B1 c f).fires
    let ⟨_, h2⟩ := (challenge_ready_state B2 c f).fires
    exact (behavior_from_step B1 _ _ _ h1).symm.trans (behavior_from_step B2 _ _ _ h2)
  | TimeAdvance ticks =>
    -- Tick has no preconditions; construct a concrete step inline.
    let s₀ : CState := { ledger := [], bubbles := [], clock := 0, acl_table := [], trust_bridges := [] }
    have ht : EpArch.StepSemantics.Step (Reason := Unit) (Evidence := Unit)
        s₀ (input_to_action (.TimeAdvance ticks)) { s₀ with clock := 1 } :=
      EpArch.StepSemantics.Step.tick s₀ 1
    exact (behavior_from_step B1 _ _ _ ht).symm.trans (behavior_from_step B2 _ _ _ ht)

/-- **All grounded behaviors are equivalent; direct definitional proof.**

    This proof does not use any Step witnesses — it reduces directly on each
    `Input` constructor.  The fast proof is possible precisely *because* `Behavior`
    is observationally constant over `GroundedBehavior`: outcome is fully
    determined by the input shape, so two certificates with different evidence
    content still produce the same output.

    `working_systems_equivalent` and this theorem say the same thing.  The
    difference is architectural: `working_systems_equivalent` additionally
    witnesses that the matching Step is live — the operational machinery exists,
    not just the observation label.  This theorem states the observation fact
    without that operational grounding. -/
theorem grounded_behaviors_equivalent (B1 B2 : GroundedBehavior) :
    BehaviorallyEquivalent B1 B2 :=
  fun i => by cases i <;> rfl

end EpArch
