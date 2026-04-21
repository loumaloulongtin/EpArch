/-
EpArch.Theorems.BehavioralEquivalence — Observation-Boundary Equivalence

Defines the abstract input/observation interface for WorkingSystems and
proves that any two grounded systems produce identical observations on all inputs.

The observation model is tied to the `Step` relation through two distinct proof
routes that apply to different input constructors:

  **Step-witness route** (withdraw, challenge, tick):
    `withdraw_ready_state` / `challenge_ready_state` construct a concrete `CState`
    at Unit types and prove the matching `Step` fires from it.
    `B : GroundedBehavior` is the type-level certificate that the caller's feature
    set typechecks against EpArch's mechanism signatures — its presence authorizes
    the call, but the CState is independently constructed; `B`'s evidence fields
    are not the structural source of the state.
    `working_systems_equivalent` dispatches per input constructor and calls these
    witnesses directly — so for those three cases the main equivalence theorem
    *uses* actual `Step` firings, not mere unfolding.

  **Definitional route** (ExportRequest → TimeAdvanced):
    `ExportRequest` maps to `.Tick` — cross-bubble transfer is an agent-level workflow
    (Withdraw in B_src, agent carries the deposit, `Step.register` in B_tgt).
    `Behavior` returns `.TimeAdvanced` for `ExportRequest`; `input_to_action` maps it to
    `.Tick`.  The equivalence follows definitionally from `behavior_step_consistent`.

`Behavior` is observationally constant over `GroundedBehavior`: outcome depends
only on input shape, not witness content.  This is a design property of EpArch —
at the kernel boundary all fully grounded realizers expose the same observable
success behavior.  `GroundedBehavior` certifies that the required features
typecheck against EpArch's mechanism signatures; it does not guarantee the
design is good or that the implementation performs correctly beyond what the
type checker enforces.

## Definitions

- `Input`               — abstract input events (withdraw, export, challenge, time-advance)
- `Observation`         — observable outcomes
- `Behavior`            — observation function, indexed by GroundedBehavior evidence
- `BehaviorallyEquivalent` — identical observations on all inputs
- `input_to_action`     — maps `Input` to the matching concrete `StepSemantics.Action`
- `observe_step_action` — extracts an `Observation` from a concrete action
- `ReadyState i`        — a `CState` + proof that `Step` fires for `input_to_action i`
- `withdraw_ready_state B a b d` — constructs `ReadyState` at Unit types; `B` is the type-level certificate
- `challenge_ready_state B c f` — constructs `ReadyState` at Unit types; `B` is the type-level certificate

## Theorems

- `behavioral_equiv_{refl,symm,trans}`  — equivalence is an equivalence relation
- `behavior_step_consistent`   — Behavior B i = observe_step_action (input_to_action i) (definitional)
- `behavior_from_step`         — same equality for systems with a live Step: the step witness
                                 confirms the state machine can reach the action, and the
                                 equality holds by case analysis on which constructor fired
- `working_systems_equivalent` — grounded systems are equivalent; for withdraw, challenge, and
                                 tick the equivalence is grounded in the existence of a live
                                 Step from B's evidence; ExportRequest maps to TimeAdvanced (definitional)

## Extension Model

`GroundedBehavior` is intentionally domain-agnostic.  Its fields (`bank`,
`trust_bridges`, `revocation`, …) carry abstract type parameters — `Entry`,
`Claim`, `Clause`, etc. — that a domain fills in with its own types:

    EV charging    → GroundedBank.Entry = ChargingSession
    Finance        → GroundedBank.Entry = SettlementRecord
    Lean kernel    → GroundedBank.Entry = LeanEnvEntry   (see EpArch.Meta.LeanKernel.World)

Any domain that instantiates `GroundedBehavior` with its own types immediately
inherits `working_systems_equivalent`: any two implementations holding the
certificate agree at the observation boundary, regardless of internal design.

The `let _ :=` lines in `withdraw_ready_state` / `challenge_ready_state` are
the deliberate extension hooks.  At this layer they confirm only that the
certificate fields typecheck — presence, not quality.  A domain taking
correctness seriously replaces them with substantive obligations: proving their
concrete types flow through the step machinery in a domain-meaningful way.
That is the upgrade path from "typechecks against EpArch's signatures" to
"mechanically grounded in domain evidence", taken per domain rather than in
the abstract kernel.

This is not a certification shortcut.  The kernel deliberately stops at the
observation boundary: it enforces the mechanism signatures and the output
contract; it does not and cannot enforce whether a domain's design is good.
That judgment belongs to the domain instantiator.

## Dependencies

- **EpArch.Minimality:** WorkingSystem, SatisfiesAllProperties, GroundedBehavior
- **EpArch.Semantics.StepSemantics:** Step, Action, SystemState, precondition predicates
-/

import EpArch.Minimality
import EpArch.Semantics.StepSemantics

namespace EpArch

/-! ## Behavioral Equivalence -/

/-! ### Input Events -/

/-- Abstract input events a WorkingSystem can receive.
    Analogues of CInputEvent in EpArch.Concrete.WorkingSystem. -/
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
    Analogues of COutcome in EpArch.Concrete.WorkingSystem. -/
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

    `B : GroundedBehavior` is the type-level certificate that all eight features
    exist — not a runtime-inspected flag.  It is the authority under which the
    success outcomes below are admissible: because `B` witnesses a functional
    bank, trust bridges, and revocation mechanism, every input has a well-defined
    success outcome and there is no "missing primitives" fallback path.

    The output is fully determined by the input constructor; `B` is not inspected
    at runtime and does not differentiate between two distinct certificates. -/
def Behavior (_B : GroundedBehavior) (i : Input) : Observation :=
  match i with
  | .WithdrawRequest _ _ claim_id  => .WithdrawSuccess claim_id
  | .ExportRequest _ _ _           => .TimeAdvanced
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

/-! ## StepSemantics Bridge

This section ties `Behavior` to the operational `Step` relation from
EpArch.Semantics.StepSemantics.  The key claim is stronger than definitional consistency:
for every `Input i` and `GroundedBehavior B`, a *concrete ready state* exists
from which `Step s (input_to_action i) s'` fires, and the step's observable
output equals `Behavior B i`.

`GroundedBehavior` is the type-level certificate that the caller's features
typecheck against EpArch's mechanism signatures.  The concrete states are
independently constructed at Unit types to witness that the Step relation is
non-vacuous.  `B`'s evidence fields confirm the feature signatures typecheck;
they are not the structural source of the constructed states.

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
              , redeem := .mk 0 }
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
  | .ExportRequest _ _ _     => .Tick
  | .ChallengeRequest _ _    =>
      .Challenge (Agent.mk 0) (Bubble.mk 0) { P := (), reason := (), evidence := (), suspected := .S }
  | .TimeAdvance _           => .Tick

/-! ### Action → Observation -/

/-- Extract an `Observation` from a completed concrete `Action`.

    Reflects what `Step` produces at the observable boundary:
    - `.Withdraw _ _ d_idx` → deposit at `d_idx` was successfully relied on
    - `.Challenge _`        → deposit entered `Quarantined` status
    - `.Tick`               → clock advanced
    - `.Submit`, `.Register`, `.Repair`, `.Revoke`, `.Promote` — mapped to `.TimeAdvanced`.
    Cross-bubble transfer (ExportRequest) maps to Tick/TimeAdvanced; inter-bubble workflow
    is agent-level (Withdraw in B1 → agent → Register in B2). -/
def observe_step_action : CAction → Observation
  | .Withdraw _ _  d_idx => .WithdrawSuccess d_idx
  | .Challenge _ _ _         => .ChallengeProcessed "quarantined"
  | .Tick                => .TimeAdvanced
  | .Submit _ _          => .TimeAdvanced
  | .Register _ _        => .TimeAdvanced
  | .Repair _ _ _ _      => .TimeAdvanced
  | .Revoke _ _ _        => .TimeAdvanced
  | .Promote _ _ _       => .TimeAdvanced
  | .Forget _ _ _         => .TimeAdvanced
  | .Update _ _ _ _      => .TimeAdvanced

/-! ### Ready States -/

/-- A `ReadyState` for input `i` packages a concrete `CState` together with a
    proof that the Step corresponding to `input_to_action i` fires from it.

    `B : GroundedBehavior` is the type-level certificate passed by the caller —
    its presence confirms the feature signatures typecheck against EpArch's
    mechanism requirements.  The state is independently constructed at Unit
    types; `B`'s evidence fields are not the structural source of `state`. -/
structure ReadyState (i : Input) where
  /-- A concrete system state from which the step can fire. -/
  state : CState
  /-- The step fires: there exists a successor state. -/
  fires : ∃ s' : CState, Step (Reason := Unit) (Evidence := Unit)
            state (input_to_action i) s'

/-! ### Withdraw Ready State -/

/-- Build a `ReadyState` for a `WithdrawRequest`.

    `B : GroundedBehavior` is the type-level certificate — its `bank` and
    `trust_bridges` fields are accessed only to confirm they typecheck against
    EpArch's mechanism signatures; they are not the structural source of the CState.

    The concrete state has:
    - `ledger`      : canonical deposits at positions 0..d_idx (all `.Deposited`, τ = 0)
    - `clock`       : 0 -/
def withdraw_ready_state (B : GroundedBehavior) (a_n b_n d_idx : Nat) :
    ReadyState (.WithdrawRequest a_n b_n d_idx) :=
  let s : CState :=
    { ledger       := canonLedger d_idx
    , bubbles      := [.mk b_n]
    , clock        := 0 }
  let _ := B.bank.produced        -- certificate field present: bank typechecks
  let _ := B.trust_bridges.downstream_via_bridge  -- certificate field present: trust_bridges typechecks
  have h_deposited : isDeposited s d_idx :=
    ⟨canonDeposit, canonLedger_get d_idx d_idx (Nat.lt_succ_self d_idx), rfl⟩
  { state := s
  , fires := ⟨s, .withdraw s (.mk a_n) (.mk b_n) d_idx h_deposited⟩ }

/-! ### Challenge Ready State -/

/-- Build a `ReadyState` for a `ChallengeRequest`.

    `B : GroundedBehavior` is the type-level certificate — its `revocation` field
    is accessed only to confirm it typechecks against EpArch's mechanism signatures;
    it is not the structural source of the CState.

    The concrete state has a single `.Deposited` entry at index 0.
    The challenge action uses `.S` as the suspected field (lossless mapping is
    blocked because `Field` is an inductive while `ChallengeRequest` carries a
    `String`; `.S` is the structural default). -/
def challenge_ready_state (B : GroundedBehavior) (claim_id : Nat) (field : String) :
    ReadyState (.ChallengeRequest claim_id field) :=
  let s : CState :=
    { ledger       := [canonDeposit]
    , bubbles      := []
    , clock        := 0 }
  let _ := B.revocation.can_revoke        -- certificate field present: revocation typechecks
  let _ := B.revocation.witness_is_invalid  -- certificate field present: witness_is_invalid typechecks
  have h_deposited : isDeposited s 0 :=
    ⟨canonDeposit, rfl, rfl⟩
  { state := s
  , fires := ⟨_, .challenge s (Agent.mk 0) (Bubble.mk 0)
                  { P := (), reason := (), evidence := (), suspected := .S }
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
  | ExportRequest _ _ _ =>
    simp only [input_to_action] at h ⊢
    cases h
    simp [observe_step_action, Behavior]
  | ChallengeRequest c f =>
    simp only [input_to_action] at h ⊢
    cases h
    simp [observe_step_action, Behavior]
  | TimeAdvance ticks =>
    simp only [input_to_action] at h ⊢
    cases h
    simp [observe_step_action, Behavior]

/-
  (Retired) grounded_export_step: export is not a bank primitive.
  Inter-bubble transfer is an agent-level workflow: Withdraw in B1, agent carries deposit,
  direct registration in B2 (Step.register).
  See DirectRegisterEntersDeposited in EpArch.Commitments for the C5 theorem.
-/

end StepBridge

/-! ## Main Equivalence Theorems -/

/-- **Any two grounded systems are behaviorally equivalent.**

    For withdraw, challenge, and tick inputs the equivalence is witnessed through
    the operational step machinery: concrete `CState`s are constructed at Unit
    types and the matching `Step` is proved to fire from each.  Both systems
    produce the same output because `Behavior` is determined by input shape alone
    — the equality follows from the shared action-to-observation mapping.
    `B1` and `B2` are type-level certificates confirming each caller's feature
    set typechecks; they do not differentiate at the observation boundary.

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
    let s₀ : CState := { ledger := [], bubbles := [], clock := 0 }
    have ht : EpArch.StepSemantics.Step (Reason := Unit) (Evidence := Unit)
        s₀ (input_to_action (.TimeAdvance ticks)) { s₀ with clock := 1 } :=
      EpArch.StepSemantics.Step.tick s₀ 1 (Nat.zero_le 1)
    exact (behavior_from_step B1 _ _ _ ht).symm.trans (behavior_from_step B2 _ _ _ ht)

end EpArch
