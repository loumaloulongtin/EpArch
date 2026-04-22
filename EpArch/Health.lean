/-
EpArch.Health — Health Predicates and Necessity Theorems

Health predicates defined over CoreModel/CoreOps, making necessity theorems
derivable from definitions rather than axioms.

Key exports:
- SafeWithdrawalGoal, ReliableExportGoal, CorrigibleLedgerGoal,
  SoundDepositsGoal, SelfCorrectionGoal, AutonomyUnderPRPGoal
- RiskAutonomyOps, RiskAutonomyModel, RiskAutonomyModel.toAutonomyModel
- Necessity theorems: corrigible_needs_revision,
  self_correction_needs_revision, sound_deposits_needs_verification,
  autonomy_forces_bridge_or_escalation, no_escalation_forces_bridge,
  residual_risk_forced_when_no_scratch_no_escalation,
  no_risk_free_bridge_when_all_usable_bridges_risky
- FullSystemHealth, AutonomyHealth, AutonomyRiskHealth (bundles)
- PRPObligationStream, forced_residual_risk_at_stream_index
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank
import EpArch.Invariants
import EpArch.Semantics.RevisionSafety

namespace EpArch

open RevisionSafety

/-! ## Health Goals as Core Predicates

Health goals are now predicates over CoreModel/CoreOps.
This makes them definitional: we can PROVE necessity theorems. -/

/-- SafeWithdrawalGoal: Every submitting bubble has revision capability.

    A bubble that accepts submissions must also be able to revise them —
    safe withdrawal requires the structural ability to correct mistakes.
    This is non-trivial: it rules out submit-only (append-only) bubbles
    as insufficient for the health goal. -/
def SafeWithdrawalGoal (M : CoreModel) : Prop :=
  ∀ (a : M.sig.Agent) (B : M.sig.Bubble) (d : M.sig.Deposit),
    M.ops.submit a B d → M.ops.hasRevision B  -- submission requires revision capability

/-- ReliableExportGoal: False deposits don't appear true across boundaries.

    If d is not true in B, then either d is also not true in B',
    or B' has revision capability (can revalidate). -/
def ReliableExportGoal (M : CoreModel) : Prop :=
  ∀ (B B' : M.sig.Bubble) (d : M.sig.Deposit),
    ¬M.ops.truth B d → ¬M.ops.truth B' d ∨
    M.ops.hasRevision B'  -- B' has revalidation capability

/-- CorrigibleLedgerGoal: The system has revision capability and corrections are sound.

    Corrigibility means being CAPABLE of correction — so at least one bubble
    must support revision. Additionally, when revision fires it produces truths.
    The existence component captures: "corrigible" means correction CAN happen,
    not merely that it WOULD BE sound IF it could.  This is the design-forcing
    predicate: satisfying CorrigibleLedgerGoal is sufficient to infer
    HasRevisionCapability without a separate existence witness. -/
def CorrigibleLedgerGoal (M : CoreModel) : Prop :=
  (∃ B : M.sig.Bubble, M.ops.hasRevision B) ∧
  ∀ (B : M.sig.Bubble),
    M.ops.hasRevision B →
    (∀ (d d' : M.sig.Deposit), M.ops.revise B d d' → M.ops.truth B d')

/-- SoundDepositsGoal: All deposits are verifiable within effective time.

    Definitional over verifyWithin and effectiveTime:
    deposits are meaningful only if they can be verified. -/
def SoundDepositsGoal (M : CoreModel) : Prop :=
  ∀ (B : M.sig.Bubble) (d : M.sig.Deposit),
    M.ops.truth B d →
    M.ops.verifyWithin B d (M.ops.effectiveTime B)

/-- SelfCorrectionGoal: The system can correct its errors.

    Defined as: selfCorrects → hasRevision.
    See `self_correction_is_revision_gate` for the equivalence with RevisionGate. -/
def SelfCorrectionGoal (M : CoreModel) : Prop :=
  ∀ B : M.sig.Bubble, M.ops.selfCorrects B → M.ops.hasRevision B

/-- AuthorizedWithdrawalGoal: deposit certification is agent-differentiated.

    In a multi-agent system where secrets exist, the certification surface
    (who can submit / certify claims into the shared ledger) must be
    non-uniform.  This goal holds when there exist two agents with different
    submission access — at least one agent cannot certify at least one
    (bubble, deposit) pair that another agent can.

    This is the abstract health goal corresponding to "ACL is non-trivial
    at the operational level."  SafeWithdrawalGoal (revision capability) is
    orthogonal: both can hold independently.

    Only relevant in the multi-agent collaboration case.  A single agent
    managing their own bank trivially fails this goal (no second agent exists)
    and does not need to satisfy it. -/
def AuthorizedWithdrawalGoal (M : CoreModel) : Prop :=
  ∃ (a₁ a₂ : M.sig.Agent), ∃ (B : M.sig.Bubble) (d : M.sig.Deposit),
    M.ops.submit a₁ B d ∧ ¬M.ops.submit a₂ B d

/-- SelfCorrectingSystem: A system that ACTIVELY self-corrects.

    Combines SelfCorrectionGoal (the conditional: selfCorrects → hasRevision)
    with the existence requirement (at least one bubble actually self-corrects).
    This is the design-forcing predicate for the necessity theorem:
    a system that demonstrably self-corrects must have revision capability. -/
def SelfCorrectingSystem (M : CoreModel) : Prop :=
  SelfCorrectionGoal M ∧ ∃ B : M.sig.Bubble, M.ops.selfCorrects B


/-! ## Autonomy Extension and Health Goal

Novel-claim coverage under PRP is not part of the frozen `CoreOps` surface.
It is a health-specific extension: the model needs an obligation trigger
(`mustHandle`), bridge availability, analogical similarity, bridge-based
verification, and a principled escalation path. -/

/-- Autonomy-specific operations extending the frozen core surface.

    These predicates describe how a system responds to required claims under
    PRP: either by scratch verification, by a budgeted analogical bridge from
    available prior material, or by principled escalation. -/
structure AutonomyOps (Sig : CoreSig) extends CoreOps Sig where
  /-- PRP trigger: deposit `d` is a claim this bubble is obligated to handle. -/
  mustHandle : Sig.Bubble → Sig.Deposit → Prop
  /-- Bridge candidate `b` is available/banked in bubble `B`. -/
  bridgeAvailable : Sig.Bubble → Sig.Deposit → Prop
  /-- Abstract similarity relation between prior material and required claim. -/
  analogSim : Sig.Deposit → Sig.Deposit → Prop
  /-- Claim `d` can be verified in `B` via bridge `b` within time `t`. -/
  verifyVia : Sig.Bubble → Sig.Deposit → Sig.Deposit → Sig.Time → Prop
  /-- Bubble `B` has a principled escalation path for deposit `d`. -/
  canEscalate : Sig.Bubble → Sig.Deposit → Prop

/-- A core model extended with autonomy-specific operations. -/
structure AutonomyModel where
  sig : CoreSig
  ops : AutonomyOps sig
  hasBubble : Nonempty sig.Bubble

/-- Forgetful projection from an autonomy extension back to the frozen core model.

    This makes the extension relationship explicit: `AutonomyModel` adds
    health-specific operations, but its underlying `CoreModel` is obtained by
    forgetting those extra predicates and keeping the inherited `CoreOps` fields. -/
def AutonomyModel.toCoreModel (M : AutonomyModel) : CoreModel where
  sig := M.sig
  ops := M.ops.toCoreOps
  hasBubble := M.hasBubble

/-- AutonomyUnderPRPGoal: every required claim has a sound response.

    For every deposit the system is obligated to handle, one of three branches
    must hold: scratch verification fits the budget; a budgeted analogical
    bridge is available from prior material; or a principled escalation path is
    available.  The goal is obligation-scoped (`mustHandle`), not universal over
    the whole deposit type.

    This is an operational predicate, not a metaphysical one: the bridge branch
    requires an available witness from the system's prior material, not a proof
    that no analogous item exists anywhere outside the system. -/
def AutonomyUnderPRPGoal (M : AutonomyModel) : Prop :=
  ∀ (B : M.sig.Bubble) (d : M.sig.Deposit),
    M.ops.mustHandle B d →
      M.ops.verifyWithin B d (M.ops.effectiveTime B) ∨
      (∃ b : M.sig.Deposit,
          M.ops.bridgeAvailable B b ∧
          M.ops.analogSim b d ∧
          M.ops.verifyVia B b d (M.ops.effectiveTime B)) ∨
      M.ops.canEscalate B d


/-! ## Capability Predicates (Definitional)

These predicates state what capabilities a system MUST have.
They're now defined structurally, not as opaques. -/

/-- System has submission capability. -/
def HasSubmitCapability (M : CoreModel) : Prop :=
  ∃ (a : M.sig.Agent) (B : M.sig.Bubble) (d : M.sig.Deposit),
    M.ops.submit a B d

/-- System has revision capability (at some bubble). -/
def HasRevisionCapability (M : CoreModel) : Prop :=
  ∃ (B : M.sig.Bubble), M.ops.hasRevision B

/-- System has verification capability. -/
def HasVerificationCapability (M : CoreModel) : Prop :=
  ∃ (B : M.sig.Bubble) (d : M.sig.Deposit) (t : M.sig.Time),
    M.ops.verifyWithin B d t

/-- System has self-correction capability. -/
def HasSelfCorrectionCapability (M : CoreModel) : Prop :=
  ∃ (B : M.sig.Bubble), M.ops.selfCorrects B


/-! ## Necessity Theorems (PROVED, not axioms)

These theorems follow from the definitions above.
The proofs are straightforward because health goals IMPLY capability requirements.
-/

/-- Corrigible ledger goal implies revision capability.

    **PROVED**: CorrigibleLedgerGoal now encodes the existence of revision
    capability directly, so the theorem follows from the first component of
    the conjunction.  Single-premise design-forcing: the goal alone forces
    the mechanism. -/
theorem corrigible_needs_revision (M : CoreModel)
    (h_corrig : CorrigibleLedgerGoal M) :
    HasRevisionCapability M := h_corrig.1

/-- Self-correcting system implies revision capability.

    **PROVED**: SelfCorrectingSystem bundles the conditional goal with an
    existence witness; the theorem extracts the witness via modus ponens.
    Single-premise: `SelfCorrectingSystem M` alone forces `HasRevisionCapability M`. -/
theorem self_correction_needs_revision (M : CoreModel)
    (h : SelfCorrectingSystem M) :
    HasRevisionCapability M :=
  let ⟨h_goal, B, h_sc⟩ := h
  ⟨B, h_goal B h_sc⟩

/-- Sound deposits goal implies verification capability.

    **PROVED**: If deposits must be verifiable, verification exists. -/
theorem sound_deposits_needs_verification (M : CoreModel)
    (h_sound : SoundDepositsGoal M)
    (h_exists_truth : ∃ B d, M.ops.truth B d) :
    HasVerificationCapability M := by
  match h_exists_truth with
  | ⟨B, d, h_truth⟩ =>
    have h_verify := h_sound B d h_truth
    exact ⟨B, d, M.ops.effectiveTime B, h_verify⟩

/-- Authorized withdrawal goal forces agent-differentiated certification.

    **PROVED**: If certification must be agent-differentiated, two distinct agents
    exist with different submit access.  Distinctness follows by contradiction:
    if a₁ = a₂, then h_sub and h_no_sub apply to the same agent — absurd. -/
theorem authorized_withdrawal_needs_differentiation (M : CoreModel)
    (h : AuthorizedWithdrawalGoal M) :
    ∃ (a₁ a₂ : M.sig.Agent), a₁ ≠ a₂ ∧
      ∃ (B : M.sig.Bubble) (d : M.sig.Deposit),
        M.ops.submit a₁ B d ∧ ¬M.ops.submit a₂ B d := by
  have ⟨a₁, a₂, B, d, h_sub, h_no_sub⟩ := h
  by_cases h_eq : a₁ = a₂
  · exact absurd (h_eq ▸ h_sub) h_no_sub
  · exact ⟨a₁, a₂, h_eq, B, d, h_sub, h_no_sub⟩

/-- Autonomy under PRP forces bridge-or-escalation for required claims that
    are not scratch-verifiable within the effective-time budget.

    **Theorem shape:** `AutonomyUnderPRPGoal M` + `mustHandle B d` +
    `¬verifyWithin B d (effectiveTime B)` → bridge-or-escalation at B for d.
    **Proof strategy:** apply `h_auto` to B, d, `h_required`; `cases` rules
    out the scratch branch via `h_scratch_fail`; the bridge and escalation
    branches pass through directly. -/
theorem autonomy_forces_bridge_or_escalation (M : AutonomyModel)
    (h_auto : AutonomyUnderPRPGoal M)
    (B : M.sig.Bubble) (d : M.sig.Deposit)
    (h_required : M.ops.mustHandle B d)
    (h_scratch_fail : ¬M.ops.verifyWithin B d (M.ops.effectiveTime B)) :
    (∃ b : M.sig.Deposit,
        M.ops.bridgeAvailable B b ∧
        M.ops.analogSim b d ∧
        M.ops.verifyVia B b d (M.ops.effectiveTime B)) ∨
    M.ops.canEscalate B d := by
  have h_response := h_auto B d h_required
  cases h_response with
  | inl h_scratch =>
      exact absurd h_scratch h_scratch_fail
  | inr h_rest =>
      cases h_rest with
      | inl h_bridge =>
          exact Or.inl h_bridge
      | inr h_esc =>
          exact Or.inr h_esc

/-- If escalation is unavailable, a budgeted bridge is forced.

    **Theorem shape:** same premises as `autonomy_forces_bridge_or_escalation`
    plus `¬canEscalate B d` → a budgeted bridge is the unique sound response.
    **Proof strategy:** delegates to `autonomy_forces_bridge_or_escalation`;
    `cases` on the Or; bridge branch is the conclusion directly; escalation
    branch contradicts `h_no_esc` via `False.elim`. -/
theorem no_escalation_forces_bridge (M : AutonomyModel)
    (h_auto : AutonomyUnderPRPGoal M)
    (B : M.sig.Bubble) (d : M.sig.Deposit)
    (h_required : M.ops.mustHandle B d)
    (h_scratch_fail : ¬M.ops.verifyWithin B d (M.ops.effectiveTime B))
    (h_no_esc : ¬M.ops.canEscalate B d) :
    ∃ b : M.sig.Deposit,
      M.ops.bridgeAvailable B b ∧
      M.ops.analogSim b d ∧
      M.ops.verifyVia B b d (M.ops.effectiveTime B) := by
  have h_response := autonomy_forces_bridge_or_escalation M h_auto B d h_required h_scratch_fail
  cases h_response with
  | inl h_bridge =>
    exact h_bridge
  | inr h_esc =>
    exact False.elim (h_no_esc h_esc)


/-! ## Combined System Health (Definitional) -/

/-- A fully healthy system satisfies all definitional health goals. -/
structure FullSystemHealth (M : CoreModel) where
  safe_withdrawal : SafeWithdrawalGoal M
  reliable_export : ReliableExportGoal M
  corrigible_ledger : CorrigibleLedgerGoal M
  sound_deposits : SoundDepositsGoal M
  self_correction : SelfCorrectionGoal M

/-- A healthy autonomy extension satisfies the novel-claim coverage goal. -/
structure AutonomyHealth (M : AutonomyModel) where
  autonomy_coverage : AutonomyUnderPRPGoal M


/-! ## Design Note

All necessity theorems (corrigible_needs_revision, self_correction_needs_revision,
sound_deposits_needs_verification, autonomy_forces_bridge_or_escalation,
no_escalation_forces_bridge) are proved from definitions, not axioms.

Note: SelfCorrectionGoal is definitionally identical to RevisionSafety.RevisionGate —
the two names refer to the same predicate; no bridge theorem is needed. -/


/-! ## Health Goals Summary

The health predicates connect to the architectural invariants:

| Health Goal | Necessary Capability | Core Operation | Context |
|-------------|----------------------|----------------|---------|
| SafeWithdrawalGoal | Revision capability | `submit`, `hasRevision` | All systems |
| ReliableExportGoal | Revalidation | `hasRevision`, `truth` | Multi-bubble |
| CorrigibleLedgerGoal | Revision | `revise`, `hasRevision` | All systems |
| SoundDepositsGoal | Verification | `verifyWithin`, `effectiveTime` | All systems |
| SelfCorrectionGoal | Revision | `hasRevision` (= RevisionGate) | All systems |
| AuthorizedWithdrawalGoal | Agent-differentiated certification | `submit` | Multi-agent only |
| AutonomyUnderPRPGoal | Budgeted bridge or escalation for required claims | `mustHandle`, `bridgeAvailable`, `analogSim`, `verifyVia`, `canEscalate` | PRP handling of required over-budget claims |

Core health goals are definitional predicates over CoreOps.
AutonomyUnderPRPGoal is a health-specific extension predicate over AutonomyModel.
Necessity theorems follow from what the corresponding health predicate means.

AuthorizedWithdrawalGoal is not part of FullSystemHealth because it is
only meaningful in the multi-agent collaboration case.  A single agent
managing their own bank does not satisfy it and does not need to.  The
world-level forcing story lives in WorldCtx.W_multi_agent_heterogeneous
and the bridge theorem w_multi_agent_forces_authorization_need in WorldBridges.

AutonomyUnderPRPGoal is packaged separately as `AutonomyHealth` because it is
defined over `AutonomyModel`, not `CoreModel`: the goal depends on health-specific
extension predicates rather than the frozen core surface.

RiskAutonomyModel extends AutonomyModel with a residual-risk predicate and is
packaged separately as `AutonomyRiskHealth` for the same reason: it adds a
classification predicate (`residualRiskVia`) beyond the frozen AutonomyOps surface.
-/


/-! ========================================================================
    RESIDUAL RISK UNDER AUTONOMOUS PRP OPERATION

    When a system operating under PRP cannot scratch-verify a required claim
    within budget, cannot escalate, and every available bridge for that claim
    carries residual risk, a risky bridge is the only remaining admissible
    response.  Risk-free handling is not available — this is a structural
    consequence, not an implementation defect.

    **Dependency chain:**
    `no_escalation_forces_bridge` supplies the bridge existential.
    `h_all_risky` is then applied to that bridge to yield the residual-risk witness.

    **Connection to Minimality §11:**
    `h_all_risky` is an abstract hypothesis here.  `ResidualRiskBridge` in
    Minimality.lean provides the structural Minimality-layer reason why any bridge
    cheaper than scratch for a novel over-budget claim cannot be risk-free.
    The two layers are independent; neither cites the other; they meet at
    the architectural reading.
    ======================================================================== -/

/-! ## Risk-Extended Operations and Model -/

/-- Risk-extended autonomy operations: adds a residual-risk predicate for
    bridge-based verification.  `residualRiskVia B b d` states that using bridge
    `b` to verify deposit `d` at bubble `B` carries irreducible residual risk.

    `AutonomyOps` is frozen; `RiskAutonomyOps` extends it non-destructively.
    Whether a bridge is risk-free is system-defined; the theorem only requires
    that the system can distinguish risky from risk-free bridges. -/
structure RiskAutonomyOps (Sig : CoreSig) extends AutonomyOps Sig where
  /-- Bridge `b` carries residual risk when used to verify `d` at `B`. -/
  residualRiskVia : Sig.Bubble → Sig.Deposit → Sig.Deposit → Prop

/-- An autonomy model extended with risk-classification operations. -/
structure RiskAutonomyModel where
  sig      : CoreSig
  ops      : RiskAutonomyOps sig
  hasBubble : Nonempty sig.Bubble

/-- Forgetful projection from a risk-extended model to the plain AutonomyModel.

    Drops `residualRiskVia`; keeps the inherited `AutonomyOps` fields intact.
    Used to apply `no_escalation_forces_bridge` to a `RiskAutonomyModel`
    without threading risk through every autonomy-model argument. -/
def RiskAutonomyModel.toAutonomyModel (M : RiskAutonomyModel) : AutonomyModel where
  sig       := M.sig
  ops       := M.ops.toAutonomyOps
  hasBubble := M.hasBubble


/-! ## Residual Risk Forced -/

/-- RESIDUAL RISK FORCED: when scratch verification fails, escalation is
    unavailable, and every usable bridge carries residual risk, a risky
    bridge is the only remaining admissible response.

    **Theorem shape:** `AutonomyUnderPRPGoal` + `mustHandle B d` +
    `¬verifyWithin B d (effectiveTime B)` + `¬canEscalate B d` +
    `h_all_risky` → forced risky bridge existential.
    **Proof strategy:**
    1. `no_escalation_forces_bridge` delivers `⟨b, h_avail, h_sim, h_verify⟩`.
    2. `h_all_risky b h_avail h_sim h_verify` yields `residualRiskVia B b d`.
    3. Package the four-component existential.

    `h_all_risky` is obligation-scoped: every bridge the system can actually
    use for this `B` and `d` is risky.  It does not claim risk-free bridges
    cannot exist in principle. -/
theorem residual_risk_forced_when_no_scratch_no_escalation (M : RiskAutonomyModel)
    (h_auto  : AutonomyUnderPRPGoal M.toAutonomyModel)
    (B : M.sig.Bubble) (d : M.sig.Deposit)
    (h_required    : M.ops.mustHandle B d)
    (h_scratch_fail : ¬M.ops.verifyWithin B d (M.ops.effectiveTime B))
    (h_no_esc      : ¬M.ops.canEscalate B d)
    (h_all_risky   : ∀ b : M.sig.Deposit,
        M.ops.bridgeAvailable B b →
        M.ops.analogSim b d →
        M.ops.verifyVia B b d (M.ops.effectiveTime B) →
        M.ops.residualRiskVia B b d) :
    ∃ b : M.sig.Deposit,
        M.ops.bridgeAvailable B b ∧
        M.ops.analogSim b d ∧
        M.ops.verifyVia B b d (M.ops.effectiveTime B) ∧
        M.ops.residualRiskVia B b d := by
  -- `no_escalation_forces_bridge`: scratch and escalation are closed → a budgeted bridge must exist
  have ⟨b, h_avail, h_sim, h_verify⟩ :=
    no_escalation_forces_bridge M.toAutonomyModel h_auto B d
      h_required h_scratch_fail h_no_esc
  -- h_all_risky applied to that bridge supplies the residual-risk component
  exact ⟨b, h_avail, h_sim, h_verify, h_all_risky b h_avail h_sim h_verify⟩


/-- If every usable bridge for `d` at `B` is risky, no usable bridge is risk-free.

    **Theorem shape:** `h_all_risky` alone → `¬∃ b, ... ∧ ¬residualRiskVia B b d`.
    Bridge-classification lemma: the proof does not require the autonomy regime
    (`AutonomyUnderPRPGoal`, `mustHandle`, scratch-fail, escalation are all absent).
    The autonomy-regime consequence is
    `residual_risk_forced_when_no_scratch_no_escalation`.
    **Proof strategy:** intro + apply `h_all_risky`; contradicts `h_no_risk`. -/
theorem no_risk_free_bridge_when_all_usable_bridges_risky (M : RiskAutonomyModel)
    (B : M.sig.Bubble) (d : M.sig.Deposit)
    (h_all_risky   : ∀ b : M.sig.Deposit,
        M.ops.bridgeAvailable B b →
        M.ops.analogSim b d →
        M.ops.verifyVia B b d (M.ops.effectiveTime B) →
        M.ops.residualRiskVia B b d) :
    ¬∃ b : M.sig.Deposit,
        M.ops.bridgeAvailable B b ∧
        M.ops.analogSim b d ∧
        M.ops.verifyVia B b d (M.ops.effectiveTime B) ∧
        ¬M.ops.residualRiskVia B b d := by
  intro ⟨b, h_avail, h_sim, h_verify, h_no_risk⟩
  -- h_all_risky forces risk on every available budgeted bridge; contradiction
  exact h_no_risk (h_all_risky b h_avail h_sim h_verify)


/-! ## AutonomyRiskHealth Bundle -/

/-- A risk-extended autonomy model satisfies the base PRP coverage goal.

    Does not assert that risks are bounded, accepted, eliminated, or calibrated;
    it only packages `AutonomyUnderPRPGoal` over `RiskAutonomyModel`.
    Separate from `AutonomyHealth` because it requires `RiskAutonomyModel`. -/
structure AutonomyRiskHealth (M : RiskAutonomyModel) where
  autonomy_coverage : AutonomyUnderPRPGoal M.toAutonomyModel


/-! ========================================================================
    PRP OBLIGATION STREAM — Residual Risk at a Specific Stream Index

    A `PRPObligationStream` packages two infinite sequences (bubbles and
    deposits) together with a witness index at which all three gates are
    closed: scratch verification fails, escalation is unavailable, and
    every usable bridge carries residual risk.  `forced_residual_risk_at_stream_index`
    shows that at that index the system is forced to a risky bridge.

    This is the stream-level consequence of
    `residual_risk_forced_when_no_scratch_no_escalation`: the gate-closure
    conditions live on the stream structure; the proof is a one-line
    delegation.
    ======================================================================== -/

/-! ## PRPObligationStream -/

/-- Two infinite obligation sequences with a distinguished index at
    which all gates are closed.

    Uses separate `bubble_stream` and `deposit_stream` functions (rather
    than a product-valued function) so that later field types contain only
    function applications, not product projections.

    Field `h_required` is the obligation premise at `risky_index`;
    `h_scratch_fail`, `h_no_esc`, and `h_all_risky` are the three
    gate-closure conditions.  All four transfer directly to
    `residual_risk_forced_when_no_scratch_no_escalation`. -/
structure PRPObligationStream (M : RiskAutonomyModel) where
  /-- The sequence of obligation bubbles. -/
  bubble_stream  : Nat → M.sig.Bubble
  /-- The sequence of obligation deposits. -/
  deposit_stream : Nat → M.sig.Deposit
  /-- Index at which all gate-closure conditions hold. -/
  risky_index    : Nat
  /-- The deposit at `risky_index` is a required claim. -/
  h_required     : M.ops.mustHandle
                     (bubble_stream risky_index)
                     (deposit_stream risky_index)
  /-- Scratch verification fails within the effective-time budget. -/
  h_scratch_fail : ¬M.ops.verifyWithin
                     (bubble_stream risky_index)
                     (deposit_stream risky_index)
                     (M.ops.effectiveTime (bubble_stream risky_index))
  /-- No principled escalation path is available. -/
  h_no_esc       : ¬M.ops.canEscalate
                     (bubble_stream risky_index)
                     (deposit_stream risky_index)
  /-- Every usable bridge for this obligation carries residual risk. -/
  h_all_risky    : ∀ b : M.sig.Deposit,
                     M.ops.bridgeAvailable (bubble_stream risky_index) b →
                     M.ops.analogSim b (deposit_stream risky_index) →
                     M.ops.verifyVia
                       (bubble_stream risky_index) b
                       (deposit_stream risky_index)
                       (M.ops.effectiveTime (bubble_stream risky_index)) →
                     M.ops.residualRiskVia
                       (bubble_stream risky_index) b
                       (deposit_stream risky_index)


/-! ## Stream-Level Residual Risk -/

/-- A risky bridge is forced at the gate-closure index of the obligation stream.

    **Theorem shape:** `AutonomyUnderPRPGoal` + `PRPObligationStream M` →
    forced risky bridge existential at `S.risky_index`.
    **Proof strategy:** one-line delegation to
    `residual_risk_forced_when_no_scratch_no_escalation`, supplying the
    obligation premise `h_required` and the three gate-closure fields
    `h_scratch_fail`, `h_no_esc`, `h_all_risky` from `S` directly. -/
theorem forced_residual_risk_at_stream_index (M : RiskAutonomyModel)
    (h_auto : AutonomyUnderPRPGoal M.toAutonomyModel)
    (S : PRPObligationStream M) :
    let B := S.bubble_stream S.risky_index
    let d := S.deposit_stream S.risky_index
    ∃ b : M.sig.Deposit,
        M.ops.bridgeAvailable B b ∧
        M.ops.analogSim b d ∧
        M.ops.verifyVia B b d (M.ops.effectiveTime B) ∧
        M.ops.residualRiskVia B b d :=
  residual_risk_forced_when_no_scratch_no_escalation M h_auto
    _ _ S.h_required S.h_scratch_fail S.h_no_esc S.h_all_risky

end EpArch
