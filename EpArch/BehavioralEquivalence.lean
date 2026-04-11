/-
EpArch/BehavioralEquivalence.lean — Observation-Boundary Equivalence

Defines the abstract input/observation interface for WorkingSystems and
proves that any two systems both satisfying all operational properties
produce identical observations on all inputs.

The observation model is connected to the `Step` relation in StepSemantics.lean:
- `input_to_action` maps abstract `Input`s to concrete `Step` actions
- `observe_step_action` extracts an `Observation` from a completed action
- `behavior_step_consistent` proves that for `GroundedBehavior` systems,
  `Behavior W i = observe_step_action (input_to_action i)` for all `i`
- Conditional step-firing theorems ground each `Input` kind in `Step` preconditions

## Definitions

- `Input`               — abstract input events (withdraw, export, challenge, time-advance)
- `Observation`         — observable outcomes
- `Behavior`            — observation function, dispatching on `*_ev` evidence fields
- `BehaviorallyEquivalent` — identical observations on all inputs
- `input_to_action`     — maps `Input` to the matching concrete `StepSemantics.Action`
- `observe_step_action` — extracts an `Observation` from a concrete action

## Theorems

- `working_systems_equivalent`   — SatisfiesAllProperties on both → behaviorally equivalent
- `behavior_from_grounded_*`     — Behavior is fully determined by GroundedBehavior evidence
- `behavior_step_consistent`     — Behavior matches `observe_step_action ∘ input_to_action`
- `grounded_withdraw_step`       — conditional: withdraw Step fires from a ready state
- `grounded_challenge_step`      — conditional: challenge Step fires from a deposited state
- `grounded_export_step`         — conditional: export Step fires given header + bridge
- `withdraw_step_behavior_match` — step outcome matches Behavior prediction
- `challenge_step_behavior_match`— step outcome matches Behavior prediction

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

/-- The observation produced by a WorkingSystem on a given input.
    Dispatches on the proof-carrying evidence fields: `bank_ev`, `bridges_ev`,
    `revocation_ev`.  Two systems with identical `isSome` values produce
    identical output.

    The challenge result is `"quarantined"` — matching the structural outcome
    of `Step.challenge` in StepSemantics.lean (deposit enters Quarantined status).
    The field string in `ChallengeRequest` is not surfaced here because the
    Step result is a status transition, not a string payload. -/
def Behavior (W : WorkingSystem) (i : Input) : Observation :=
  match i with
  | .WithdrawRequest _ _ claim_id =>
    if W.bank_ev.isSome && W.bridges_ev.isSome then
      .WithdrawSuccess claim_id
    else
      .WithdrawDenied "missing primitives"
  | .ExportRequest _ target claim_id =>
    if W.bank_ev.isSome && W.bridges_ev.isSome then
      .ExportSuccess claim_id target
    else
      .ExportDenied "missing primitives"
  | .ChallengeRequest _ _ =>
    if W.revocation_ev.isSome then
      .ChallengeProcessed "quarantined"
    else
      .ChallengeProcessed "no correction support"
  | .TimeAdvance _ =>
    .TimeAdvanced

/-! ### Behavioral Equivalence -/

/-- Two systems are behaviorally equivalent if they produce identical
    observations on every input. -/
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

/-- Systems with identical proof-carrying field presence produce identical observations.
    `Behavior` inspects `bank_ev.isSome`, `bridges_ev.isSome`, and `revocation_ev.isSome`. -/
theorem same_flags_same_behavior (W1 W2 : WorkingSystem)
    (h_bank    : W1.bank_ev.isSome    = W2.bank_ev.isSome)
    (h_bridges : W1.bridges_ev.isSome = W2.bridges_ev.isSome)
    (h_revoc   : W1.revocation_ev.isSome = W2.revocation_ev.isSome) :
    BehaviorallyEquivalent W1 W2 := by
  intro i
  simp [Behavior]
  cases i with
  | WithdrawRequest agent_id bubble_id claim_id =>
    simp [h_bank, h_bridges]
  | ExportRequest source target claim_id =>
    simp [h_bank, h_bridges]
  | ChallengeRequest claim_id field =>
    simp [h_revoc]
  | TimeAdvance ticks =>
    rfl

/-- `SatisfiesAllProperties` determines the presence of all six proof-carrying fields. -/
theorem satisfies_all_fixes_flags (W : WorkingSystem) (h : SatisfiesAllProperties W) :
    W.bubbles_ev.isSome       = true ∧
    W.bridges_ev.isSome       = true ∧
    W.headers_ev.isSome       = true ∧
    W.revocation_ev.isSome    = true ∧
    W.bank_ev.isSome          = true ∧
    W.redeemability_ev.isSome = true :=
  ⟨h .scope, h .trust, h .headers, h .revocation, h .bank, h .redeemability⟩

/-- Any two systems satisfying all properties are behaviorally equivalent. -/
theorem working_systems_equivalent (W1 W2 : WorkingSystem) :
    SatisfiesAllProperties W1 → SatisfiesAllProperties W2 → BehaviorallyEquivalent W1 W2 := by
  intro h_sat1 h_sat2
  have ⟨_, h1_bridges, _, h1_revoc, h1_bank, _⟩ := satisfies_all_fixes_flags W1 h_sat1
  have ⟨_, h2_bridges, _, h2_revoc, h2_bank, _⟩ := satisfies_all_fixes_flags W2 h_sat2
  exact same_flags_same_behavior W1 W2
    (h1_bank.trans h2_bank.symm)
    (h1_bridges.trans h2_bridges.symm)
    (h1_revoc.trans h2_revoc.symm)


/-! ## StepSemantics Bridge

This section ties the abstract `Behavior` function to the operational
`Step` relation from `StepSemantics.lean`.

Type parameters `Unit` are used for `PropLike`, `Standard`, `ErrorModel`,
`Provenance`, `Reason`, and `Evidence` — the minimal instantiation that
lets us exhibit actual `Step` witnesses while staying fully constructive. -/

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

/-! ### Behavior ↔ GroundedBehavior -/

/-- For a system built from `GroundedBehavior`, withdraw behavior is fully determined:
    `WithdrawSuccess claim_id`.  The evidence fields `bank_ev` and `bridges_ev`
    are `some` by construction, so the `if` condition is `true`. -/
theorem behavior_from_grounded_withdraw (B : GroundedBehavior) (base : WorkingSystem)
    (a b c : Nat) :
    Behavior (WorkingSystem.withGroundedBehavior B base) (.WithdrawRequest a b c) =
    .WithdrawSuccess c := by
  simp [Behavior, WorkingSystem.withGroundedBehavior, Option.isSome]

/-- For a system built from `GroundedBehavior`, export behavior is fully determined:
    `ExportSuccess claim_id target_bubble`. -/
theorem behavior_from_grounded_export (B : GroundedBehavior) (base : WorkingSystem)
    (src tgt c : Nat) :
    Behavior (WorkingSystem.withGroundedBehavior B base) (.ExportRequest src tgt c) =
    .ExportSuccess c tgt := by
  simp [Behavior, WorkingSystem.withGroundedBehavior, Option.isSome]

/-- For a system built from `GroundedBehavior`, challenge behavior is fully determined:
    `ChallengeProcessed "quarantined"`.  The evidence field `revocation_ev`
    is `some` by construction. -/
theorem behavior_from_grounded_challenge (B : GroundedBehavior) (base : WorkingSystem)
    (c : Nat) (f : String) :
    Behavior (WorkingSystem.withGroundedBehavior B base) (.ChallengeRequest c f) =
    .ChallengeProcessed "quarantined" := by
  simp [Behavior, WorkingSystem.withGroundedBehavior, Option.isSome]

/-- For any system, time-advance behavior is always `TimeAdvanced`. -/
theorem behavior_from_grounded_tick (B : GroundedBehavior) (base : WorkingSystem) (n : Nat) :
    Behavior (WorkingSystem.withGroundedBehavior B base) (.TimeAdvance n) = .TimeAdvanced := by
  simp [Behavior]

/-! ### Behavior ↔ Step Consistency -/

/-- **Main bridge theorem.**

    For a system built from `GroundedBehavior`, `Behavior W i` equals
    `observe_step_action (input_to_action i)` for every input `i`.

    This is the central connection: the abstract observation function is not
    independent of the `Step` relation — it computes exactly what a successful
    `Step` produces at the observable boundary.  The `GroundedBehavior` evidence
    is what guarantees every branch of `Behavior` matches the structural step
    outcome: all `*_ev` fields are `some`, so every `if` condition is `true`. -/
theorem behavior_step_consistent (B : GroundedBehavior) (base : WorkingSystem) (i : Input) :
    Behavior (WorkingSystem.withGroundedBehavior B base) i =
    observe_step_action (input_to_action i) := by
  cases i <;>
  simp [Behavior, input_to_action, observe_step_action, Bubble.toNat,
        WorkingSystem.withGroundedBehavior, Option.isSome]

/-! ### Conditional Step-Firing -/

/-- **Withdraw step fires from a ready state.**

    Given a state with ACL permission, a current-timestamp deposit, and a
    deposit in `Deposited` status, the concrete `Step.withdraw` fires.
    The `GroundedBehavior` evidence is not needed here — the step preconditions
    are purely on the `SystemState`. -/
theorem grounded_withdraw_step
    (s : CState) (a : Agent) (B : Bubble) (d_idx : Nat)
    (h_acl       : hasACLPermission s a B d_idx)
    (h_current   : isCurrentDeposit s d_idx)
    (h_deposited : isDeposited s d_idx) :
    Step (Reason := Unit) (Evidence := Unit) s (.Withdraw a B d_idx) s :=
  .withdraw s a B d_idx h_acl h_current h_deposited

/-- **Challenge step fires from a deposited state.**

    Given a deposit in `Deposited` status, the challenge step transitions it
    to `Quarantined`.  The challenge carries `Unit` type parameters. -/
theorem grounded_challenge_step
    (s : CState) (d_idx : Nat)
    (h_deposited : isDeposited s d_idx) :
    ∃ (s' : CState),
      Step (Reason := Unit) (Evidence := Unit) s
        (.Challenge { P := (), reason := (), evidence := (), suspected := .S }) s' :=
  ⟨_, .challenge s { P := (), reason := (), evidence := (), suspected := .S }
        d_idx h_deposited⟩

/-- **Export step fires given header evidence and a trust bridge.**

    Both `Step.export_with_bridge` and `Step.export_revalidate` require
    `depositHasHeader`.  Since `header_preserved` is opaque, this theorem is
    stated conditionally: the three hypotheses are precisely what
    `Step.export_with_bridge` requires. -/
theorem grounded_export_step
    (s : CState) (B1 B2 : Bubble) (d_idx : Nat)
    (h_deposited : isDeposited      s d_idx)
    (h_header    : depositHasHeader s d_idx)
    (h_bridge    : hasTrustBridge   s B1 B2) :
    ∃ (s' : CState),
      Step (Reason := Unit) (Evidence := Unit) s (.Export B1 B2 d_idx) s' :=
  ⟨_, .export_with_bridge s B1 B2 d_idx h_deposited h_header h_bridge⟩

/-! ### Step Outcome Matches Behavior Prediction -/

/-- For a withdraw step, the step's observable output matches the `Behavior`
    prediction of a `GroundedBehavior` system.

    Both reduce to `.WithdrawSuccess d_idx`. -/
theorem withdraw_step_behavior_match (B : GroundedBehavior) (base : WorkingSystem)
    (a_n b_n d_idx : Nat) (s : CState)
    (_ : Step (Reason := Unit) (Evidence := Unit)
          s (.Withdraw (.mk a_n) (.mk b_n) d_idx) s) :
    observe_step_action (.Withdraw (.mk a_n) (.mk b_n) d_idx) =
    Behavior (WorkingSystem.withGroundedBehavior B base) (.WithdrawRequest a_n b_n d_idx) := by
  simp [observe_step_action, Behavior, WorkingSystem.withGroundedBehavior, Option.isSome]

/-- For a challenge step, the step's observable output matches the `Behavior`
    prediction of a `GroundedBehavior` system.

    Both reduce to `.ChallengeProcessed "quarantined"`. -/
theorem challenge_step_behavior_match (B : GroundedBehavior) (base : WorkingSystem)
    (c : Nat) (f : String) (s s' : CState)
    (_ : Step (Reason := Unit) (Evidence := Unit) s
          (.Challenge { P := (), reason := (), evidence := (), suspected := .S }) s') :
    observe_step_action
        (.Challenge { P := (), reason := (), evidence := (), suspected := .S }) =
    Behavior (WorkingSystem.withGroundedBehavior B base) (.ChallengeRequest c f) := by
  simp [observe_step_action, Behavior, WorkingSystem.withGroundedBehavior, Option.isSome]

end StepBridge

end EpArch

