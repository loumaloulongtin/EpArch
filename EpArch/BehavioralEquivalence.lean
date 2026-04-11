/-
EpArch/BehavioralEquivalence.lean — Observation-Boundary Equivalence

Defines the abstract input/observation interface for WorkingSystems and
proves that any two grounded systems produce identical observations on all inputs.

The observation model is unified with the `Step` relation through a single chain:

    Behavior B i  =  observe_step_action (input_to_action i)   ∀ B i

(`behavior_step_consistent`).  `Behavior` takes `GroundedBehavior` as its
argument — the evidence is in the type, not inspected as a Boolean at runtime.
`working_systems_equivalent` is proved via `behavior_step_consistent` (through
Step) rather than through `Option.isSome` flag inspection — the two proof paths
from an earlier version have been eliminated in favour of one.

## Definitions

- `Input`               — abstract input events (withdraw, export, challenge, time-advance)
- `Observation`         — observable outcomes
- `Behavior`            — observation function, indexed by GroundedBehavior evidence
- `BehaviorallyEquivalent` — identical observations on all inputs
- `input_to_action`     — maps `Input` to the matching concrete `StepSemantics.Action`
- `observe_step_action` — extracts an `Observation` from a concrete action

## Theorems

- `behavioral_equiv_{refl,symm,trans}` — equivalence is an equivalence relation
- `satisfies_all_fixes_flags`          — utility: SatisfiesAllProperties → all *_ev.isSome = true
- `behavior_step_consistent`           — Behavior B i = observe_step_action (input_to_action i)
- `grounded_withdraw_step`             — conditional: withdraw Step fires from a ready state
- `grounded_challenge_step`            — conditional: challenge Step fires from a deposited state
- `grounded_export_step`               — conditional: export Step fires given header + bridge
- `withdraw_step_behavior_match`       — step outcome matches Behavior prediction
- `challenge_step_behavior_match`      — step outcome matches Behavior prediction
- `working_systems_equivalent`         — all GroundedBehavior values are equivalent; via Step
- `grounded_behaviors_equivalent`      — same result; direct definitional proof

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
    exist — not a runtime-inspected flag.  Each field of `B` grounds the
    corresponding output branch:
    - `B.bank` + `B.trust_bridges` ground `.WithdrawSuccess` / `.ExportSuccess`
    - `B.revocation`               grounds `.ChallengeProcessed "quarantined"`

    Since `GroundedBehavior` witnesses all six features, all branches always
    succeed — there is no "missing primitives" fallback path. -/
def Behavior (_B : GroundedBehavior) (i : Input) : Observation :=
  match i with
  | .WithdrawRequest _ _ claim_id  =>
      -- _B.bank evidences the shared ledger; _B.trust_bridges evidences the import chain
      .WithdrawSuccess claim_id
  | .ExportRequest _ target claim_id =>
      -- _B.bank + _B.trust_bridges also cover export
      .ExportSuccess claim_id target
  | .ChallengeRequest _ _ =>
      -- _B.revocation evidences the challenge → quarantine path
      .ChallengeProcessed "quarantined"
  | .TimeAdvance _ =>
      .TimeAdvanced

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
`StepSemantics.lean`, establishing that they compute the same observations
viewed at different levels of abstraction.

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

/-! ### Central Bridge Theorem -/

/-- **`Behavior B i = observe_step_action (input_to_action i)` for all `B` and `i`.**

    This is the single chain connecting the abstract observation function to the
    operational `Step` relation.  `Behavior` is not independent of `Step` — it
    computes exactly what a successful `Step` produces at the observable boundary.

    The proof reduces definitionally on both sides for every constructor of `Input`. -/
theorem behavior_step_consistent (B : GroundedBehavior) (i : Input) :
    Behavior B i = observe_step_action (input_to_action i) := by
  cases i <;> simp [Behavior, input_to_action, observe_step_action, Bubble.toNat]

/-! ### Conditional Step-Firing -/

/-- Withdraw step fires from a ready state.
    Preconditions are purely on `SystemState`, independent of `GroundedBehavior`. -/
theorem grounded_withdraw_step
    (s : CState) (a : Agent) (B : Bubble) (d_idx : Nat)
    (h_acl       : hasACLPermission s a B d_idx)
    (h_current   : isCurrentDeposit s d_idx)
    (h_deposited : isDeposited s d_idx) :
    Step (Reason := Unit) (Evidence := Unit) s (.Withdraw a B d_idx) s :=
  .withdraw s a B d_idx h_acl h_current h_deposited

/-- Challenge step fires from a deposited state, transitioning it to `Quarantined`. -/
theorem grounded_challenge_step
    (s : CState) (d_idx : Nat)
    (h_deposited : isDeposited s d_idx) :
    ∃ (s' : CState),
      Step (Reason := Unit) (Evidence := Unit) s
        (.Challenge { P := (), reason := (), evidence := (), suspected := .S }) s' :=
  ⟨_, .challenge s { P := (), reason := (), evidence := (), suspected := .S }
        d_idx h_deposited⟩

/-- Export step fires given header evidence and a trust bridge.
    `depositHasHeader` is required as a precondition because `header_preserved` is opaque. -/
theorem grounded_export_step
    (s : CState) (B1 B2 : Bubble) (d_idx : Nat)
    (h_deposited : isDeposited      s d_idx)
    (h_header    : depositHasHeader s d_idx)
    (h_bridge    : hasTrustBridge   s B1 B2) :
    ∃ (s' : CState),
      Step (Reason := Unit) (Evidence := Unit) s (.Export B1 B2 d_idx) s' :=
  ⟨_, .export_with_bridge s B1 B2 d_idx h_deposited h_header h_bridge⟩

/-! ### Step Outcome Matches Behavior Prediction -/

/-- Withdraw step outcome equals `Behavior` prediction.
    Both reduce to `.WithdrawSuccess d_idx`. -/
theorem withdraw_step_behavior_match (B : GroundedBehavior) (a_n b_n d_idx : Nat) (s : CState)
    (_ : Step (Reason := Unit) (Evidence := Unit)
          s (.Withdraw (.mk a_n) (.mk b_n) d_idx) s) :
    observe_step_action (.Withdraw (.mk a_n) (.mk b_n) d_idx) =
    Behavior B (.WithdrawRequest a_n b_n d_idx) := by
  simp [observe_step_action, Behavior]

/-- Challenge step outcome equals `Behavior` prediction.
    Both reduce to `.ChallengeProcessed "quarantined"`. -/
theorem challenge_step_behavior_match (B : GroundedBehavior) (c : Nat) (f : String)
    (s s' : CState)
    (_ : Step (Reason := Unit) (Evidence := Unit) s
          (.Challenge { P := (), reason := (), evidence := (), suspected := .S }) s') :
    observe_step_action
        (.Challenge { P := (), reason := (), evidence := (), suspected := .S }) =
    Behavior B (.ChallengeRequest c f) := by
  simp [observe_step_action, Behavior]

end StepBridge

/-! ## Main Equivalence Theorems -/

/-- **Any two grounded systems are behaviorally equivalent.**

    Proved through the Step bridge: both `B1` and `B2` satisfy
      `Behavior B i = observe_step_action (input_to_action i)`,
    so `Behavior B1 i = Behavior B2 i` follows by transitivity through the
    common Step-level observation.  No `Option.isSome` flag inspection required. -/
theorem working_systems_equivalent (B1 B2 : GroundedBehavior) :
    BehaviorallyEquivalent B1 B2 :=
  fun i => (behavior_step_consistent B1 i).trans (behavior_step_consistent B2 i).symm

/-- **All grounded behaviors are equivalent; direct definitional proof.**

    `Behavior` is constant over `GroundedBehavior`: the evidence content is not
    inspected at runtime — the type-level certificate is sufficient.

    Two independent proofs are available:
    - **Step route** (`working_systems_equivalent`): via `behavior_step_consistent`
    - **Direct route** (this theorem): by `rfl` per `Input` constructor

    This mirrors the two-route structure in `LeanKernelModel.lean` for
    `containsBankPrimitives`. -/
theorem grounded_behaviors_equivalent (B1 B2 : GroundedBehavior) :
    BehaviorallyEquivalent B1 B2 :=
  fun i => by cases i <;> rfl

end EpArch

