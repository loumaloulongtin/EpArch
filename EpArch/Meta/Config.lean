/-
EpArch.Meta.Config — Configurable Certification Engine

Given an `EpArchConfig` specifying which constraints, goals, and world bundles
are active, this module computes and certifies:

  1. **Which theorem clusters are enabled** (`clusterEnabled` — computable `Bool`,
     defined in EpArch.Meta.ClusterRegistry).
  2. **Human-readable routing report** (`explainConfig`, `showConfig` — `#eval`-able,
     defined in EpArch.Meta.ClusterRegistry).
  3. **Machine-certified soundness** (`CertifiedProjection`, `certify`): every
     cluster returned as enabled is backed by a concrete machine-checked proof.

## Module split

EpArch.Meta.ClusterRegistry — pure metadata (no EpArch-specific imports):
  Types, per-family enumerations, routing, display strings.

EpArch.Meta.Config (this file) — proof-carrying layer:
  `ConstraintProof`, `ConstraintClusterSpec`, `GoalWitness`, `WorldWitness`,
  `Tier4Witness`, `MetaModularWitness`, `LatticeWitness`,
  `CertifiedProjection`, `certify`, completeness theorems,
  and the `cluster_*` named proof witnesses.

## Proof-carrying layers

- **Routing** — `clusterEnabled`, `CertifiedProjection.enabled/complete/sound`.
- **Constraint proofs** — `constraintSpec`/`constraintProof`: `ConstraintClusterSpec` carries
  a genuine Lean proposition and machine-checked proof for each Tier 2 cluster.
- **Indexed witnesses** — `goalWitness`, `worldWitness`, `tier4Witness`,
  `metaModularWitness`, `latticeWitness`: one indexed inductive per family,
  constructors store the real transport theorem as a Prop-valued argument.
- **Named witnesses** — `cluster_*` in §5b: universe-polymorphic standalone theorems
  for all 30 clusters, the authoritative typed form.

## Usage

```lean
-- See which clusters are active for your configuration:
#eval showConfig myConfig

-- Obtain a proof object certifying every enabled cluster:
#check certify myConfig

-- Access typed proof content for a specific cluster family:
(certify myConfig).goalWitnesses .goal_safeWithdrawal         -- GoalWitness
(certify myConfig).worldWitnesses .world_lies_possible        -- WorldWitness
(certify myConfig).tier4Witnesses .tier4_commitments          -- Tier4Witness
(certify myConfig).metaModularWitnesses .meta_modular         -- MetaModularWitness
(certify myConfig).latticeWitnesses .lattice_pack             -- LatticeWitness

-- Inspect a specific cluster's theorem:
#check cluster_forcing_distributed_agents
#check cluster_goal_safeWithdrawal
#check cluster_world_partial_observability
#check cluster_meta_modular
#check cluster_lattice_graceful
```
-/

import EpArch.Meta.ClusterRegistry
import EpArch.Minimality
import EpArch.Convergence
import EpArch.Health
import EpArch.Meta.TheoremTransport
import EpArch.Meta.Tier4Transport
import EpArch.Meta.Modular
import EpArch.WorldCtx
import EpArch.Adversarial.Obligations

namespace EpArch.Meta.Config

open EpArch
open RevisionSafety
open EpArch.Meta.TheoremTransport
open EpArch.Meta.Tier4Transport
open EpArch.Meta.Modular
open EpArch.AdversarialObligations

-- Universe parameter shared across all theorem-level propositions in this file.
-- Allows theorem declarations in §5b to reference universe-polymorphic types
-- (WorkingSystem, CoreModel, ExtModel, W_spoofedV) — standard for Lean 4 theorem declarations.
universe u


-- clusterValid is defined in §4g, after all indexed witness inductives.


/-! ## §4b  Constraint Proof Carrier

Tier 2 forcing clusters use a direct `ConstraintClusterSpec` record (extends
`ConstraintClusterMeta` from `ClusterRegistry` with a `witness : ConstraintProof`
field).  All other families use indexed inductive witnesses; see §4c–§4e'. -/


/-- Proof-carrying record for a Tier 2 constraint-forcing cluster:
    the actual Lean forcing proposition and its machine-checked proof. -/
structure ConstraintProof : Type 1 where
  /-- The actual Lean forcing proposition. -/
  statement : Prop
  /-- Machine-checked proof of `statement`. -/
  proof     : statement

/-- Registry entry for a Tier 2 constraint-forcing cluster.
    Extends the metadata record from `ClusterRegistry` with a machine-checked
    proof — the proof layer genuinely derived from the metadata layer. -/
structure ConstraintClusterSpec extends ConstraintClusterMeta : Type 1 where
  witness : ConstraintProof

/-- Authoritative per-constraint spec.  Extends `constraintMeta` (metadata source
    of truth in `ClusterRegistry`) with the machine-checked proof witness.
    `constraintProof` is derived from this as a one-liner. -/
def constraintSpec (c : EnabledConstraintCluster) : ConstraintClusterSpec :=
  { constraintMeta c with
    witness :=
      match c with
      | .forcing_distributed_agents => {
          statement := ∀ W : WorkingSystem, StructurallyForced W → handles_distributed_agents W → HasBubbles W
          proof     := fun _W sf => sf.forcing .scope }
      | .forcing_bounded_audit => {
          statement := ∀ W : WorkingSystem, StructurallyForced W → handles_bounded_audit W → HasTrustBridges W
          proof     := fun _W sf => sf.forcing .trust }
      | .forcing_export => {
          statement := ∀ W : WorkingSystem, StructurallyForced W → handles_export W → HasHeaders W
          proof     := fun _W sf => sf.forcing .headers }
      | .forcing_adversarial => {
          statement := ∀ W : WorkingSystem, StructurallyForced W → handles_adversarial W → HasRevocation W
          proof     := fun _W sf => sf.forcing .revocation }
      | .forcing_coordination => {
          statement := ∀ W : WorkingSystem, StructurallyForced W → handles_coordination W → HasBank W
          proof     := fun _W sf => sf.forcing .bank }
      | .forcing_truth => {
          statement := ∀ W : WorkingSystem, StructurallyForced W → handles_truth_pressure W → HasRedeemability W
          proof     := fun _W sf => sf.forcing .redeemability }
      | .forcing_multi_agent => {
          statement := ∀ W : WorkingSystem, StructurallyForced W → handles_multi_agent W → HasGranularACL W
          proof     := fun _W sf => sf.forcing .authorization } }

/-- Extract the proof carrier for constraint cluster `c` from `constraintSpec`. -/
def constraintProof (c : EnabledConstraintCluster) : ConstraintProof := (constraintSpec c).witness


/-! ## §4c  Goal Witness Carrier

Indexed proof-carrying inductive for Tier 3 health-goal transport clusters.
Each constructor stores the polymorphic transport theorem schema as a Prop-valued
argument.  Prop impredicativity keeps `∀ (E : ExtModel), ...P...` in `Prop`
even when `ExtModel` lives at `Type (u+1)`, delivering transport theorems
without universe conflicts. -/

/-- Indexed proof carrier for Tier 3 goal clusters.
    Each constructor `c (h : <transport schema>)` witnesses that the transport
    theorem for cluster `c` holds. -/
inductive GoalWitness : EnabledGoalCluster → Type 1 where
  | safeWithdrawal :
      (∀ (E : ExtModel) (C : CoreModel),
        Compatible E C → SafeWithdrawalGoal C → SafeWithdrawalGoal (forget E)) →
      GoalWitness .goal_safeWithdrawal
  | reliableExport :
      (∀ (E : ExtModel) (C : CoreModel),
        Compatible E C → ReliableExportGoal C → ReliableExportGoal (forget E)) →
      GoalWitness .goal_reliableExport
  | soundDeposits :
      (∀ (E : ExtModel) (C : CoreModel),
        Compatible E C → SoundDepositsGoal C → SoundDepositsGoal (forget E)) →
      GoalWitness .goal_soundDeposits
  | selfCorrection :
      (∀ (E : ExtModel) (C : CoreModel),
        Compatible E C → SelfCorrectionGoal C → SelfCorrectionGoal (forget E)) →
      GoalWitness .goal_selfCorrection
  | corrigibleUniversal :
      (∀ (E : ExtModel) (C : CoreModel),
        Compatible E C → CorrigibleLedgerGoal C →
        ∀ (B_E : (forget E).sig.Bubble), (forget E).ops.hasRevision B_E →
        ∀ (d_E d'_E : (forget E).sig.Deposit),
        (forget E).ops.revise B_E d_E d'_E → (forget E).ops.truth B_E d'_E) →
      GoalWitness .goal_corrigible_universal
  | corrigibleFull :
      (∀ (E : ExtModel) (C : CoreModel),
        SurjectiveCompatible E C → CorrigibleLedgerGoal C →
        CorrigibleLedgerGoal (forget E)) →
      GoalWitness .goal_corrigible_full

/-- For every Tier 3 goal cluster, deliver its `GoalWitness` backed by the
    corresponding transport theorem from `EpArch.Meta.TheoremTransport`. -/
def goalWitness : (c : EnabledGoalCluster) → GoalWitness c
  | .goal_safeWithdrawal       => .safeWithdrawal       transport_safe_withdrawal
  | .goal_reliableExport       => .reliableExport       transport_reliable_export
  | .goal_soundDeposits        => .soundDeposits        transport_sound_deposits
  | .goal_selfCorrection       => .selfCorrection       transport_self_correction
  | .goal_corrigible_universal => .corrigibleUniversal  transport_corrigible_universal
  | .goal_corrigible_full      => .corrigibleFull       transport_corrigible_ledger


/-! ## §4d  World Witness Carrier

Indexed proof carrier for world-bundle clusters.
Constructor arguments are Prop-valued (∀ over `WorldCtx` instantiations),
so `WorldWitness` lives in `Type 1`. -/

/-- Indexed proof carrier for world-bundle clusters. -/
inductive WorldWitness : EnabledWorldCluster → Type 1 where
  | liesPossible :
      (∀ (C : WorldCtx) (_ : C.W_lies_possible), ∃ w a P, C.Lie w a P) →
      WorldWitness .world_lies_possible
  | boundedAudit :
      (∀ (C : WorldCtx) (w : C.World) (P : C.Claim) (k t : Nat),
        C.RequiresSteps w P k → t < k → ¬C.VerifyWithin w P t) →
      WorldWitness .world_bounded_audit
  | asymmetricCosts :
      (∀ (C : WorldCtx) (W : C.W_asymmetric_costs), W.export_cost < W.defense_cost) →
      WorldWitness .world_asymmetric_costs
  | partialObservability :
      (∀ (C : WorldCtx) (_ : C.W_partial_observability), ∃ P, C.NotDeterminedByObs P) →
      WorldWitness .world_partial_observability
  | spoofedV :
      (∀ {PL SL EL PrL : Type}
        (_W : W_spoofedV (PropLike := PL) (Standard := SL) (ErrorModel := EL) (Provenance := PrL))
        (d : Deposit PL SL EL PrL) (a : Agent) (_p : PathExists d),
        (EpArch.V_spoof d ∨ EpArch.consultation_suppressed a) → False) →
      WorldWitness .world_spoofed_v
  | liesScale :
      (∀ (W : W_lies_scale), W.export_cost < W.defense_cost) →
      WorldWitness .world_lies_scale
  | rolexDdos :
      (∀ (W : W_rolex_ddos), same_structure W.rolex_structure W.ddos_structure) →
      WorldWitness .world_rolex_ddos
  | ddos :
      (∀ (_W : W_ddos) (a : Agent),
        (EpArch.ladder_overloaded a ∨ EpArch.V_channel_exhausted a ∨
         EpArch.E_field_poisoned a ∨ EpArch.denial_triggered a) →
        EpArch.verification_collapsed a) →
      WorldWitness .world_ddos

/-- For every world-bundle cluster, deliver its `WorldWitness`. -/
def worldWitness : (c : EnabledWorldCluster) → WorldWitness c
  | .world_lies_possible         => .liesPossible        WorldCtx.lie_possible_of_W
  | .world_bounded_audit         => .boundedAudit        WorldCtx.bounded_audit_fails
  | .world_asymmetric_costs      => .asymmetricCosts     WorldCtx.cost_asymmetry_of_W
  | .world_partial_observability => .partialObservability WorldCtx.partial_obs_no_omniscience
  | .world_spoofed_v             => .spoofedV            spoofed_V_blocks_path_of_W
  | .world_lies_scale            => .liesScale           lies_scale_of_W
  | .world_rolex_ddos            => .rolexDdos           rolex_ddos_structural_equivalence_of_W
  | .world_ddos                  => .ddos                ddos_causes_verification_collapse_of_W


/-! ## §4e  Tier 4 Witness Carrier

Indexed proof carrier for Tier 4 library clusters.
`commitments` and `structural` quantify over `Type`-universe variables;
`ltsUniversal` additionally quantifies over `Reason` and `Evidence`.
All constructor arguments are Prop-valued. -/

/-- Indexed proof carrier for Tier 4 clusters. -/
inductive Tier4Witness : EnabledTier4Cluster → Type 1 where
  | commitments :
      -- Standalone commitments pack (C3/C4b/C7b/C8).
      -- C4b (redeemability_requires_more_than_consensus) is the commitment-specific fact
      -- not present in structural_theorems_unconditional (Cluster B).
      -- C1/C2/C5/C6b are proved as separately named theorems.
      (∀ {PL SL EL PrL : Type},
        (∀ (d : Deposit PL SL EL PrL),
            ∃ (s : SL) (e : EL) (v : PrL), d.h.S = s ∧ d.h.E = e ∧ d.h.V = v) ∧
        (∀ (B : Bubble) (d : Deposit PL SL EL PrL),
            intra_bubble_only d → consensus B d.P → does_not_imply (consensus B d.P) (redeemable d)) ∧
        systematically_harder header_preserved_diagnosability header_stripped_diagnosability ∧
        (∀ (d1 d2 : Deposit PL SL EL PrL),
            refreshed d1 → unrefreshed d2 → ¬performs_equivalently d1 d2)) →
      Tier4Witness .tier4_commitments
  | structural :
      (∀ {PL SL EL PrL : Type},
        (∀ (d : Deposit PL SL EL PrL),
            ∃ (s : SL) (e : EL) (v : PrL), d.h.S = s ∧ d.h.E = e ∧ d.h.V = v) ∧
        (∀ (d1 d2 : Deposit PL SL EL PrL),
            refreshed d1 → unrefreshed d2 → ¬performs_equivalently d1 d2) ∧
        (¬∀ f1 f2 : FailureField, FailMonolithic f1 = FailMonolithic f2 → f1 = f2) ∧
        systematically_harder header_preserved_diagnosability header_stripped_diagnosability) →
      Tier4Witness .tier4_structural
  | ltsUniversal :
      (∀ {PL SL EL PrL : Type} {Reason Evidence : Type},
        (∀ (s s' : StepSemantics.SystemState PL SL EL PrL)
           (B : Bubble) (a : Agent) (d_idx : Nat),
           StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
             s (StepSemantics.Action.Withdraw a B d_idx) s' →
           ACL_OK_At s a B d_idx ∧ Current_At s d_idx ∧ ConsultedBank_At s d_idx) ∧
        (∀ (s s' : StepSemantics.SystemState PL SL EL PrL)
           (d_idx : Nat) (f : Field),
           StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
             s (StepSemantics.Action.Repair d_idx f) s' →
           s'.ledger = StepSemantics.updateDepositStatus s.ledger d_idx .Candidate) ∧
        (∀ (s s' : StepSemantics.SystemState PL SL EL PrL)
           (d_idx : Nat) (f : Field),
           StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
             s (StepSemantics.Action.Repair d_idx f) s' →
           StepSemantics.isQuarantined s d_idx) ∧
        (∀ (s s' : StepSemantics.SystemState PL SL EL PrL)
           (a : Agent) (d : Deposit PL SL EL PrL),
           StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
             s (StepSemantics.Action.Submit a d) s' →
           ∃ d', d' ∈ s'.ledger ∧ d'.status = DepositStatus.Candidate)) →
      Tier4Witness .tier4_lts_universal
  | bankGoalsCompat :
      (∀ (E : ExtModel) (C : CoreModel) (_ : Compatible E C)
        (_ : SafeWithdrawalGoal C) (_ : ReliableExportGoal C)
        (_ : SoundDepositsGoal C) (_ : SelfCorrectionGoal C)
        (_ : CorrigibleLedgerGoal C),
        SafeWithdrawalGoal (forget E) ∧ ReliableExportGoal (forget E) ∧
        SoundDepositsGoal (forget E) ∧ SelfCorrectionGoal (forget E) ∧
        (∀ B_E : (forget E).sig.Bubble, (forget E).ops.hasRevision B_E →
         ∀ d_E d'_E : (forget E).sig.Deposit,
         (forget E).ops.revise B_E d_E d'_E → (forget E).ops.truth B_E d'_E)) →
      Tier4Witness .tier4_bank_goals_compat
  | bankGoalsSurj :
      (∀ (E : ExtModel) (C : CoreModel) (_ : SurjectiveCompatible E C)
        (_ : SafeWithdrawalGoal C) (_ : ReliableExportGoal C)
        (_ : SoundDepositsGoal C) (_ : SelfCorrectionGoal C)
        (_ : CorrigibleLedgerGoal C),
        SafeWithdrawalGoal (forget E) ∧ ReliableExportGoal (forget E) ∧
        SoundDepositsGoal (forget E) ∧ SelfCorrectionGoal (forget E) ∧
        CorrigibleLedgerGoal (forget E)) →
      Tier4Witness .tier4_bank_goals_surj

/-- For every Tier 4 cluster, deliver its `Tier4Witness`. -/
def tier4Witness : (c : EnabledTier4Cluster) → Tier4Witness c
  | .tier4_commitments       => .commitments   commitments_pack
  | .tier4_structural        => .structural    structural_theorems_unconditional
  | .tier4_lts_universal     => .ltsUniversal  lts_theorems_step_universal
  | .tier4_bank_goals_compat => .bankGoalsCompat
      (fun E C h h_sw h_re h_sd h_sc h_cl =>
        ⟨transport_safe_withdrawal E C h h_sw,
         transport_reliable_export E C h h_re,
         transport_sound_deposits E C h h_sd,
         transport_self_correction E C h h_sc,
         transport_corrigible_universal E C h h_cl⟩)
  | .tier4_bank_goals_surj   => .bankGoalsSurj
      (fun E C h h_sw h_re h_sd h_sc h_cl =>
        ⟨transport_safe_withdrawal E C h.toCompatible h_sw,
         transport_reliable_export E C h.toCompatible h_re,
         transport_sound_deposits E C h.toCompatible h_sd,
         transport_self_correction E C h.toCompatible h_sc,
         transport_corrigible_ledger E C h h_cl⟩)


/-! ## §4eↇ  Meta-Modularity Witness Carrier

Indexed proof carrier for constraint-modularity meta-theorem clusters.
`WorkingSystem` and `ConstraintSubset` are monomorphic, so propositions are
purely Prop-valued; pattern is consistent with other witness families. -/

/-- Indexed proof carrier for constraint-modularity meta-theorem clusters. -/
inductive MetaModularWitness : EnabledMetaModularCluster → Type 1 where
  | modular :
      (forall (S : ConstraintSubset) (W : WorkingSystem),
        PartialWellFormed W S → projection_valid S W) →
      MetaModularWitness .meta_modular

/-- For every meta-modularity cluster, deliver its `MetaModularWitness`. -/
def metaModularWitness : (c : EnabledMetaModularCluster) → MetaModularWitness c
  | .meta_modular            => .modular    modular


/-! ## §4e←  Lattice-Stability Witness Carrier

Indexed proof carrier for lattice-stability clusters (`EpArch.Modularity`).
Quantifies over `CoreModel` and `ExtModel`, but all constructor arguments
are Prop-valued, keeping `LatticeWitness` in `Type 1`. -/

/-- Indexed proof carrier for lattice-stability clusters. -/
inductive LatticeWitness : EnabledLatticeCluster → Type 1 where
  | graceful :
      (forall (M : CoreModel), NoSelfCorrection M → RevisionGate M) →
      LatticeWitness .lattice_graceful
  | subSafety :
      (forall (S : SubBundle) (E : ExtModel),
        Compatible E S.model → RevisionGate S.model → RevisionGate (forget E)) →
      LatticeWitness .lattice_sub_safety
  | pack :
      ((forall (M : CoreModel), NoSelfCorrection M → RevisionGate M) ∧
       (forall (S : SubBundle) (E : ExtModel),
          Compatible E S.model → RevisionGate S.model → RevisionGate (forget E)) ∧
       (forall (C : CoreModel) (R : RevisionSafeExtension C),
          RevisionGate C → RevisionGate (forget R.ext))) →
      LatticeWitness .lattice_pack

/-- For every lattice-stability cluster, deliver its `LatticeWitness`. -/
def latticeWitness : (c : EnabledLatticeCluster) → LatticeWitness c
  | .lattice_graceful   => .graceful  graceful_degradation
  | .lattice_sub_safety => .subSafety sub_revision_safety
  | .lattice_pack       => .pack      modularity_pack


/-! ## §4g-pre  Universe-grounded cluster propositions (private)

Each `prop_*` def stores one blocked cluster's theorem statement with every
universe-polymorphic type pinned to `.{0}`.  With all universes concrete,
no free universe variable appears and the def compiles as a plain `Prop`.
These serve as the match-arm values in `clusterValid` for the 15 clusters
whose proposition types live at `Type (u+1)` (Goal, WorldCtx, Tier4-bank,
Lattice families). -/

private def prop_goal_safeWithdrawal : Prop :=
  ∀ (E : ExtModel.{0}) (C : CoreModel.{0}),
    Compatible.{0} E C → SafeWithdrawalGoal.{0} C → SafeWithdrawalGoal.{0} (forget.{0} E)
private def prop_goal_reliableExport : Prop :=
  ∀ (E : ExtModel.{0}) (C : CoreModel.{0}),
    Compatible.{0} E C → ReliableExportGoal.{0} C → ReliableExportGoal.{0} (forget.{0} E)
private def prop_goal_soundDeposits : Prop :=
  ∀ (E : ExtModel.{0}) (C : CoreModel.{0}),
    Compatible.{0} E C → SoundDepositsGoal.{0} C → SoundDepositsGoal.{0} (forget.{0} E)
private def prop_goal_selfCorrection : Prop :=
  ∀ (E : ExtModel.{0}) (C : CoreModel.{0}),
    Compatible.{0} E C → SelfCorrectionGoal.{0} C → SelfCorrectionGoal.{0} (forget.{0} E)
private def prop_goal_corrigible_universal : Prop :=
  ∀ (E : ExtModel.{0, 0}) (C : CoreModel.{0}),
    Compatible.{0, 0, 0} E C → CorrigibleLedgerGoal.{0} C →
    ∀ (B_E : (forget.{0, 0} E).sig.Bubble), (forget.{0, 0} E).ops.hasRevision B_E →
    ∀ (d_E d'_E : (forget.{0, 0} E).sig.Deposit),
    (forget.{0, 0} E).ops.revise B_E d_E d'_E → (forget.{0, 0} E).ops.truth B_E d'_E
private def prop_goal_corrigible_full : Prop :=
  ∀ (E : ExtModel.{0}) (C : CoreModel.{0}),
    SurjectiveCompatible.{0} E C → CorrigibleLedgerGoal.{0} C →
    CorrigibleLedgerGoal.{0} (forget.{0} E)
private def prop_tier4_bank_goals_compat : Prop :=
  ∀ (E : ExtModel.{0, 0}) (C : CoreModel.{0}),
    Compatible.{0, 0, 0} E C →
    SafeWithdrawalGoal.{0} C → ReliableExportGoal.{0} C →
    SoundDepositsGoal.{0} C → SelfCorrectionGoal.{0} C →
    CorrigibleLedgerGoal.{0} C →
    SafeWithdrawalGoal.{0} (forget.{0, 0} E) ∧ ReliableExportGoal.{0} (forget.{0, 0} E) ∧
    SoundDepositsGoal.{0} (forget.{0, 0} E) ∧ SelfCorrectionGoal.{0} (forget.{0, 0} E) ∧
    (∀ B_E : (forget.{0, 0} E).sig.Bubble, (forget.{0, 0} E).ops.hasRevision B_E →
     ∀ d_E d'_E : (forget.{0, 0} E).sig.Deposit,
     (forget.{0, 0} E).ops.revise B_E d_E d'_E → (forget.{0, 0} E).ops.truth B_E d'_E)
private def prop_tier4_bank_goals_surj : Prop :=
  ∀ (E : ExtModel.{0, 0}) (C : CoreModel.{0}),
    SurjectiveCompatible.{0, 0, 0} E C →
    SafeWithdrawalGoal.{0} C → ReliableExportGoal.{0} C →
    SoundDepositsGoal.{0} C → SelfCorrectionGoal.{0} C →
    CorrigibleLedgerGoal.{0} C →
    SafeWithdrawalGoal.{0} (forget.{0, 0} E) ∧ ReliableExportGoal.{0} (forget.{0, 0} E) ∧
    SoundDepositsGoal.{0} (forget.{0, 0} E) ∧ SelfCorrectionGoal.{0} (forget.{0, 0} E) ∧
    CorrigibleLedgerGoal.{0} (forget.{0, 0} E)
private def prop_world_lies_possible : Prop :=
  ∀ (C : WorldCtx.{0}) (_ : C.W_lies_possible), ∃ w a P, C.Lie w a P
private def prop_world_bounded_audit : Prop :=
  ∀ (C : WorldCtx.{0}) (w : C.World) (P : C.Claim) (k t : Nat),
    C.RequiresSteps w P k → t < k → ¬C.VerifyWithin w P t
private def prop_world_asymmetric_costs : Prop :=
  ∀ (C : WorldCtx.{0}) (W : C.W_asymmetric_costs), W.export_cost < W.defense_cost
private def prop_world_partial_observability : Prop :=
  ∀ (C : WorldCtx.{0}) (_ : C.W_partial_observability), ∃ P, C.NotDeterminedByObs P
private def prop_lattice_graceful : Prop :=
  ∀ (M : CoreModel.{0}), NoSelfCorrection.{0} M → RevisionGate.{0} M
private def prop_lattice_sub_safety : Prop :=
  ∀ (S : SubBundle.{0}) (E : ExtModel.{0}),
    Compatible.{0} E S.model → RevisionGate.{0} S.model → RevisionGate.{0} (forget.{0} E)
private def prop_lattice_pack : Prop :=
  (∀ (M : CoreModel.{0}), NoSelfCorrection.{0} M → RevisionGate.{0} M) ∧
  (∀ (S : SubBundle.{0}) (E : ExtModel.{0}),
     Compatible.{0} E S.model → RevisionGate.{0} S.model → RevisionGate.{0} (forget.{0} E)) ∧
  (∀ (C : CoreModel.{0}) (R : RevisionSafeExtension.{0} C),
     RevisionGate.{0} C → RevisionGate.{0} (forget.{0} R.ext))


/-! ## §4g  Cluster Validity — All 30 Clusters Wired

`clusterValid c` is the machine-proved proposition for all 30 clusters.
- Tier 2 (7): inline forcing propositions via `constraintSpec`.
- Tier 3 Goal (6): `prop_goal_*` — the transport theorem at universe 0.
- Tier 4 (3 inline + 2 via `prop_tier4_bank_goals_*`).
- World (4 inline adversarial + 4 via `prop_world_*`).
- Meta (1): inline.
- Lattice (3): `prop_lattice_*` — the lattice theorem at universe 0.

**Universe escape hatch:** the 15 blocked clusters use private `prop_*` defs
(§4g-pre) where every universe-polymorphic type is explicitly pinned to `.{0}`.
This eliminates all free universe variables, allowing the defs to appear as
match-arm values of `clusterValid : ClusterTag → Prop`. -/

/-- A cluster is valid: `clusterValid c` is the machine-proved proposition for all
    30 clusters.  Tier 2 and the 8 inline Tier 4/World/Meta clusters use raw
    propositions; the remaining 15 use `prop_*` defs pinned at universe 0 (see §4g). -/
def clusterValid (c : ClusterTag) : Prop :=
  match c with
  -- Tier 2 (7): forcing propositions via constraintSpec
  | .forcing_distributed_agents => (constraintSpec .forcing_distributed_agents).witness.statement
  | .forcing_bounded_audit      => (constraintSpec .forcing_bounded_audit).witness.statement
  | .forcing_export             => (constraintSpec .forcing_export).witness.statement
  | .forcing_adversarial        => (constraintSpec .forcing_adversarial).witness.statement
  | .forcing_coordination       => (constraintSpec .forcing_coordination).witness.statement
  | .forcing_truth              => (constraintSpec .forcing_truth).witness.statement
  | .forcing_multi_agent        => (constraintSpec .forcing_multi_agent).witness.statement
  -- Tier 3 Goal (6): transport theorems at universe 0
  | .goal_safeWithdrawal       => prop_goal_safeWithdrawal
  | .goal_reliableExport       => prop_goal_reliableExport
  | .goal_soundDeposits        => prop_goal_soundDeposits
  | .goal_selfCorrection       => prop_goal_selfCorrection
  | .goal_corrigible_universal => prop_goal_corrigible_universal
  | .goal_corrigible_full      => prop_goal_corrigible_full
  -- Tier 4 (3 inline + 2 via prop_tier4_bank_goals_*)
  | .tier4_commitments       =>
      ∀ {PL SL EL PrL : Type},
        (∀ (d : Deposit PL SL EL PrL),
            ∃ (s : SL) (e : EL) (v : PrL), d.h.S = s ∧ d.h.E = e ∧ d.h.V = v) ∧
        (∀ (B : Bubble) (d : Deposit PL SL EL PrL),
            intra_bubble_only d → consensus B d.P → does_not_imply (consensus B d.P) (redeemable d)) ∧
        systematically_harder header_preserved_diagnosability header_stripped_diagnosability ∧
        (∀ (d1 d2 : Deposit PL SL EL PrL),
            refreshed d1 → unrefreshed d2 → ¬performs_equivalently d1 d2)
  | .tier4_structural        =>
      ∀ {PL SL EL PrL : Type},
        (∀ (d : Deposit PL SL EL PrL),
            ∃ (s : SL) (e : EL) (v : PrL), d.h.S = s ∧ d.h.E = e ∧ d.h.V = v) ∧
        (∀ (d1 d2 : Deposit PL SL EL PrL),
            refreshed d1 → unrefreshed d2 → ¬performs_equivalently d1 d2) ∧
        (¬∀ f1 f2 : FailureField, FailMonolithic f1 = FailMonolithic f2 → f1 = f2) ∧
        systematically_harder header_preserved_diagnosability header_stripped_diagnosability
  | .tier4_lts_universal     =>
      ∀ {PL SL EL PrL : Type} {Reason Evidence : Type},
        (∀ (s s' : StepSemantics.SystemState PL SL EL PrL)
           (B : Bubble) (a : Agent) (d_idx : Nat),
           StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
             s (StepSemantics.Action.Withdraw a B d_idx) s' →
           ACL_OK_At s a B d_idx ∧ Current_At s d_idx ∧ ConsultedBank_At s d_idx) ∧
        (∀ (s s' : StepSemantics.SystemState PL SL EL PrL)
           (d_idx : Nat) (f : Field),
           StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
             s (StepSemantics.Action.Repair d_idx f) s' →
           s'.ledger = StepSemantics.updateDepositStatus s.ledger d_idx .Candidate) ∧
        (∀ (s s' : StepSemantics.SystemState PL SL EL PrL)
           (d_idx : Nat) (f : Field),
           StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
             s (StepSemantics.Action.Repair d_idx f) s' →
           StepSemantics.isQuarantined s d_idx) ∧
        (∀ (s s' : StepSemantics.SystemState PL SL EL PrL)
           (a : Agent) (d : Deposit PL SL EL PrL),
           StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
             s (StepSemantics.Action.Submit a d) s' →
           ∃ d', d' ∈ s'.ledger ∧ d'.status = DepositStatus.Candidate)
  -- Tier 4 bank_goals (2): theorems at universe 0
  | .tier4_bank_goals_compat => prop_tier4_bank_goals_compat
  | .tier4_bank_goals_surj   => prop_tier4_bank_goals_surj
  -- World (4 WorldCtx via prop_* + 4 inline adversarial)
  | .world_lies_possible        => prop_world_lies_possible
  | .world_bounded_audit        => prop_world_bounded_audit
  | .world_asymmetric_costs     => prop_world_asymmetric_costs
  | .world_partial_observability => prop_world_partial_observability
  | .world_spoofed_v  =>
      ∀ {PL SL EL PrL : Type}
        (_W : W_spoofedV (PropLike := PL) (Standard := SL)
              (ErrorModel := EL) (Provenance := PrL))
        (d : Deposit PL SL EL PrL) (a : Agent) (_p : PathExists d),
        (EpArch.V_spoof d ∨ EpArch.consultation_suppressed a) → False
  | .world_lies_scale  => ∀ (W : W_lies_scale), W.export_cost < W.defense_cost
  | .world_rolex_ddos  => ∀ (W : W_rolex_ddos),
        same_structure W.rolex_structure W.ddos_structure
  | .world_ddos        => ∀ (_W : W_ddos) (a : Agent),
        (EpArch.ladder_overloaded a ∨ EpArch.V_channel_exhausted a ∨
         EpArch.E_field_poisoned a ∨ EpArch.denial_triggered a) →
        EpArch.verification_collapsed a
  -- Meta (1): safe (WorkingSystem, ConstraintSubset are Type 0)
  | .meta_modular      => ∀ (S : ConstraintSubset) (W : WorkingSystem),
        PartialWellFormed W S → projection_valid S W
  -- Lattice (3): theorems at universe 0
  | .lattice_graceful  => prop_lattice_graceful
  | .lattice_sub_safety => prop_lattice_sub_safety
  | .lattice_pack      => prop_lattice_pack



/-! ## §4f  Correspondence Lemmas (support lemmas)

The `allXxxClusters` canonical lists used by `certify` and the membership
lemmas below are defined in EpArch.Meta.ClusterRegistry (they are metadata objects,
not proof objects).  `filterMap_mem_of_pos` is a local helper for
`List.filterMap` membership.

For ergonomic extraction of the schema carried by a witness, use the `cluster_*`
named theorems in §5b, or pattern-match directly:
`match w with | .safeWithdrawal f => f E C h hg`. -/

private theorem filterMap_mem_of_pos {α : Type} {β : Type 1}
    (f : α → Option β) : ∀ (l : List α) (a : α) (b : β),
    a ∈ l → f a = some b → b ∈ l.filterMap f
  | [], _, _, hmem, _ => nomatch hmem
  | _ :: tl, a, b, hmem, hf => by
      cases hmem with
      | head => simp only [List.filterMap, hf]; exact List.Mem.head _
      | tail _ htl =>
        simp only [List.filterMap]
        split
        · exact filterMap_mem_of_pos f tl a b htl hf
        · exact List.Mem.tail _ (filterMap_mem_of_pos f tl a b htl hf)

-- Membership witnesses for each family's "all clusters" list.
-- Used in the correspondence lemmas below.
private theorem enabledGoalCluster_mem_all (c : EnabledGoalCluster) :
    c ∈ allGoalClusters := by
  unfold allGoalClusters; cases c
  · exact .head _
  · exact .tail _ (.head _)
  · exact .tail _ (.tail _ (.head _))
  · exact .tail _ (.tail _ (.tail _ (.head _)))
  · exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))
  · exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))

private theorem enabledWorldCluster_mem_all (c : EnabledWorldCluster) :
    c ∈ allWorldClusters := by
  unfold allWorldClusters; cases c
  · exact .head _
  · exact .tail _ (.head _)
  · exact .tail _ (.tail _ (.head _))
  · exact .tail _ (.tail _ (.tail _ (.head _)))
  · exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))
  · exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  · exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  · exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))

private theorem enabledTier4Cluster_mem_all (c : EnabledTier4Cluster) :
    c ∈ allTier4Clusters := by
  unfold allTier4Clusters; cases c
  · exact .head _
  · exact .tail _ (.head _)
  · exact .tail _ (.tail _ (.head _))
  · exact .tail _ (.tail _ (.tail _ (.head _)))
  · exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))

private theorem enabledMetaModularCluster_mem_all (c : EnabledMetaModularCluster) :
    c ∈ allMetaModularClusters := by
  unfold allMetaModularClusters; cases c
  · exact .head _

private theorem enabledLatticeCluster_mem_all (c : EnabledLatticeCluster) :
    c ∈ allLatticeClusters := by
  unfold allLatticeClusters; cases c
  · exact .head _
  · exact .tail _ (.head _)
  · exact .tail _ (.tail _ (.head _))

/-! ## §5  Soundness: `clusterEnabled cfg c = true → clusterValid c` -/

/-- `clusterEnabled` is sound: every cluster it marks enabled satisfies `clusterValid`.
    All 30 clusters are non-trivially closed: Tier 2 by `constraintSpec.witness.proof`,
    inline Tier 4/World/Meta clusters by the corresponding theorem, and the 15
    `prop_*`-wrapped clusters by the corresponding transport/lattice/world theorem. -/
theorem clusterEnabled_sound (cfg : EpArchConfig) (c : ClusterTag)
    (_h : clusterEnabled cfg c = true) : clusterValid c := by
  unfold clusterValid
  match c with
  | .forcing_distributed_agents => exact (constraintSpec .forcing_distributed_agents).witness.proof
  | .forcing_bounded_audit      => exact (constraintSpec .forcing_bounded_audit).witness.proof
  | .forcing_export             => exact (constraintSpec .forcing_export).witness.proof
  | .forcing_adversarial        => exact (constraintSpec .forcing_adversarial).witness.proof
  | .forcing_coordination       => exact (constraintSpec .forcing_coordination).witness.proof
  | .forcing_truth              => exact (constraintSpec .forcing_truth).witness.proof
  | .forcing_multi_agent        => exact (constraintSpec .forcing_multi_agent).witness.proof
  | .goal_safeWithdrawal        => exact transport_safe_withdrawal
  | .goal_reliableExport        => exact transport_reliable_export
  | .goal_soundDeposits         => exact transport_sound_deposits
  | .goal_selfCorrection        => exact transport_self_correction
  | .goal_corrigible_universal  => exact transport_corrigible_universal
  | .goal_corrigible_full       => exact transport_corrigible_ledger
  | .tier4_commitments          => exact @commitments_pack
  | .tier4_structural           => exact @structural_theorems_unconditional
  | .tier4_lts_universal        => exact @lts_theorems_step_universal
  | .tier4_bank_goals_compat    =>
      exact fun E C h h_sw h_re h_sd h_sc h_cl =>
        ⟨transport_safe_withdrawal E C h h_sw,
         transport_reliable_export E C h h_re,
         transport_sound_deposits E C h h_sd,
         transport_self_correction E C h h_sc,
         transport_corrigible_universal E C h h_cl⟩
  | .tier4_bank_goals_surj =>
      exact fun E C h h_sw h_re h_sd h_sc h_cl =>
        ⟨transport_safe_withdrawal E C h.toCompatible h_sw,
         transport_reliable_export E C h.toCompatible h_re,
         transport_sound_deposits E C h.toCompatible h_sd,
         transport_self_correction E C h.toCompatible h_sc,
         transport_corrigible_ledger E C h h_cl⟩
  | .world_lies_possible        => exact WorldCtx.lie_possible_of_W
  | .world_bounded_audit        => exact WorldCtx.bounded_audit_fails
  | .world_asymmetric_costs     => exact WorldCtx.cost_asymmetry_of_W
  | .world_partial_observability => exact WorldCtx.partial_obs_no_omniscience
  | .world_spoofed_v            => exact @spoofed_V_blocks_path_of_W
  | .world_lies_scale           => exact lies_scale_of_W
  | .world_rolex_ddos           => exact rolex_ddos_structural_equivalence_of_W
  | .world_ddos                 => exact ddos_causes_verification_collapse_of_W
  | .meta_modular               => exact modular
  | .lattice_graceful           => exact graceful_degradation
  | .lattice_sub_safety         => exact sub_revision_safety
  | .lattice_pack               => exact modularity_pack


/-! ## §6  Certified Projection

`CertifiedProjection cfg` is a proof-carrying record: it names every enabled
cluster and holds machine-checked evidence that each one is valid. -/

/-- A certified bundle: the enabled clusters for `cfg`, with proofs.

    **Layer 1 (routing):** `enabled`, `complete`, `sound` — all 30 cluster tags.
    `sound` proves `clusterValid c` non-trivially for every enabled cluster.

    **Layer 2 (constraint proofs):** `constraintWitnesses` — full `ConstraintProof`
    for all seven Tier 2 forcing clusters (total, config-independent).
    `enabledConstraintWitnesses` — filtered to only the clusters enabled by `cfg`.

    **Layer 3 (indexed witnesses):** `goalWitnesses`, `worldWitnesses`, `tier4Witnesses`
    — indexed inductives packaging the real transport theorem for each cluster.
    `enabledGoalWitnesses`, `enabledWorldWitnesses`, `enabledTier4Witnesses` — filtered
    to only the clusters enabled by `cfg` (using dependent pairs `Σ c, WitnessType c`).

    **Layer 4 (proof-content):** `cluster_*` witnesses in §5b cover all 30 clusters. -/
structure CertifiedProjection (cfg : EpArchConfig) where
  /-- The list of enabled clusters (equal to `explainConfig cfg`). -/
  enabled                   : List ClusterTag
  /-- Faithfully mirrors `explainConfig`. -/
  complete                  : enabled = explainConfig cfg
  /-- Every enabled cluster satisfies `clusterValid`. For Tier 2 and the 8 inline
      clusters this is the raw proposition; for the 15 `prop_*`-wrapped clusters
      this is the theorem statement pinned at universe 0 (see §4g). -/
  sound                     : ∀ c, c ∈ enabled → clusterValid c
  /-- Tier 2 proof carriers (all seven, config-independent).
      `constraintWitnesses c` delivers the real proposition and proof for
      forcing cluster `c` regardless of which constraints `cfg` enables. -/
  constraintWitnesses        : (c : EnabledConstraintCluster) → ConstraintProof
  /-- Filtered Tier 2 proof carriers: only the constraint clusters enabled
      by `cfg`.  Each entry pairs the sub-tag with its `ConstraintProof`,
      so callers get proposition + proof for exactly the active clusters. -/
  enabledConstraintWitnesses : List (EnabledConstraintCluster × ConstraintProof)
  /-- Tier 3 goal proof carriers (all six, config-independent).
      Each `GoalWitness c` packages the polymorphic transport theorem for `c`. -/
  goalWitnesses              : (c : EnabledGoalCluster) → GoalWitness c
  /-- World-bundle proof carriers (all eight, config-independent). -/
  worldWitnesses             : (c : EnabledWorldCluster) → WorldWitness c
  /-- Tier 4 proof carriers (all five, config-independent). -/
  tier4Witnesses             : (c : EnabledTier4Cluster) → Tier4Witness c
  /-- Filtered Tier 3 goal witnesses: only the clusters enabled by `cfg`. -/
  enabledGoalWitnesses       : List (Σ c : EnabledGoalCluster, GoalWitness c)
  /-- Filtered world witnesses: only the clusters enabled by `cfg`. -/
  enabledWorldWitnesses      : List (Σ c : EnabledWorldCluster, WorldWitness c)
  /-- Filtered Tier 4 witnesses: only the clusters enabled by `cfg`. -/
  enabledTier4Witnesses      : List (Σ c : EnabledTier4Cluster, Tier4Witness c)
  /-- Constraint-modularity proof carriers (both, config-independent). -/
  metaModularWitnesses       : (c : EnabledMetaModularCluster) → MetaModularWitness c
  /-- Lattice-stability proof carriers (all three, config-independent). -/
  latticeWitnesses           : (c : EnabledLatticeCluster) → LatticeWitness c
  /-- Filtered meta-modularity witnesses: clusters enabled by `cfg` (always all one). -/
  enabledMetaModularWitnesses : List (Σ c : EnabledMetaModularCluster, MetaModularWitness c)
  /-- Filtered lattice-stability witnesses: clusters enabled by `cfg` (always all three). -/
  enabledLatticeWitnesses    : List (Σ c : EnabledLatticeCluster, LatticeWitness c)

/-- Compute and certify the full projection for any `EpArchConfig`. -/
def certify (cfg : EpArchConfig) : CertifiedProjection cfg where
  enabled             := explainConfig cfg
  complete            := rfl
  sound               := fun c h => clusterEnabled_sound cfg c (by
    -- Prove clusterEnabled cfg c = true from c ∈ allClusters.filter (clusterEnabled cfg).
    -- List.mem_filter is not available in Lean 4.3.0 core; proved by induction.
    suffices ∀ l : List ClusterTag, c ∈ l.filter (clusterEnabled cfg) →
        clusterEnabled cfg c = true from
      this allClusters h
    intro l
    induction l with
    | nil => intro hnil; exact nomatch hnil
    | cons hd tl ih =>
      intro hmem
      unfold List.filter at hmem
      cases hc : clusterEnabled cfg hd with
      | true =>
        simp only [hc] at hmem
        cases hmem with
        | head => exact hc
        | tail _ h => exact ih h
      | false =>
        simp only [hc] at hmem
        exact ih hmem)
  constraintWitnesses := constraintProof
  enabledConstraintWitnesses :=
    allConstraintClusters.filterMap fun c =>
      if clusterEnabled cfg c.toClusterTag
      then some (c, constraintProof c)
      else none
  goalWitnesses  := goalWitness
  worldWitnesses := worldWitness
  tier4Witnesses := tier4Witness
  enabledGoalWitnesses :=
    allGoalClusters.filterMap fun c =>
      if clusterEnabled cfg c.toClusterTag
      then some ⟨c, goalWitness c⟩
      else none
  enabledWorldWitnesses :=
    allWorldClusters.filterMap fun c =>
      if clusterEnabled cfg c.toClusterTag
      then some ⟨c, worldWitness c⟩
      else none
  enabledTier4Witnesses :=
    allTier4Clusters.filterMap fun c =>
      if clusterEnabled cfg c.toClusterTag
      then some ⟨c, tier4Witness c⟩
      else none
  metaModularWitnesses := metaModularWitness
  latticeWitnesses     := latticeWitness
  enabledMetaModularWitnesses :=
    allMetaModularClusters.filterMap fun c =>
      if clusterEnabled cfg c.toClusterTag
      then some ⟨c, metaModularWitness c⟩
      else none
  enabledLatticeWitnesses :=
    allLatticeClusters.filterMap fun c =>
      if clusterEnabled cfg c.toClusterTag
      then some ⟨c, latticeWitness c⟩
      else none

/-! ## §4f-cont  Correspondence Lemmas

These theorems prove the config-filtered witness lists are **complete**: every cluster
the `clusterEnabled` router marks enabled has a proof entry in the corresponding
`enabledXxxWitnesses` list.  They are placed here (after `certify`) because they
reference `(certify cfg).enabledXxxWitnesses`.  The private support lemmas
(`filterMap_mem_of_pos`, `enabledXxxCluster_mem_all`) live in §4f above. -/

/-- **Completeness** of `enabledGoalWitnesses`: every cluster `c` that `clusterEnabled`
    marks enabled has a proof entry `⟨c, goalWitness c⟩` in the filtered list.
    Together with the `sound` field, this closes the loop between routing and proofs. -/
theorem mem_enabledGoalWitnesses_of_enabled (cfg : EpArchConfig) (c : EnabledGoalCluster)
    (h : clusterEnabled cfg c.toClusterTag = true) :
    ⟨c, goalWitness c⟩ ∈ (certify cfg).enabledGoalWitnesses := by
  simp only [certify]
  exact filterMap_mem_of_pos _ _ c _ (enabledGoalCluster_mem_all c) (by simp [h])

/-- **Completeness** of `enabledWorldWitnesses`. -/
theorem mem_enabledWorldWitnesses_of_enabled (cfg : EpArchConfig) (c : EnabledWorldCluster)
    (h : clusterEnabled cfg c.toClusterTag = true) :
    ⟨c, worldWitness c⟩ ∈ (certify cfg).enabledWorldWitnesses := by
  simp only [certify]
  exact filterMap_mem_of_pos _ _ c _ (enabledWorldCluster_mem_all c) (by simp [h])

/-- **Completeness** of `enabledTier4Witnesses`. -/
theorem mem_enabledTier4Witnesses_of_enabled (cfg : EpArchConfig) (c : EnabledTier4Cluster)
    (h : clusterEnabled cfg c.toClusterTag = true) :
    ⟨c, tier4Witness c⟩ ∈ (certify cfg).enabledTier4Witnesses := by
  simp only [certify]
  exact filterMap_mem_of_pos _ _ c _ (enabledTier4Cluster_mem_all c) (by simp [h])

/-- **Completeness** of `enabledMetaModularWitnesses`. -/
theorem mem_enabledMetaModularWitnesses_of_enabled (cfg : EpArchConfig)
    (c : EnabledMetaModularCluster) (h : clusterEnabled cfg c.toClusterTag = true) :
    ⟨c, metaModularWitness c⟩ ∈ (certify cfg).enabledMetaModularWitnesses := by
  simp only [certify]
  exact filterMap_mem_of_pos _ _ c _ (enabledMetaModularCluster_mem_all c) (by simp [h])

/-- **Completeness** of `enabledLatticeWitnesses`. -/
theorem mem_enabledLatticeWitnesses_of_enabled (cfg : EpArchConfig)
    (c : EnabledLatticeCluster) (h : clusterEnabled cfg c.toClusterTag = true) :
    ⟨c, latticeWitness c⟩ ∈ (certify cfg).enabledLatticeWitnesses := by
  simp only [certify]
  exact filterMap_mem_of_pos _ _ c _ (enabledLatticeCluster_mem_all c) (by simp [h])

/-! ## §5b  Named Proof Witnesses

Each entry below is a named proof witness for its cluster — either a `def`
delegating to the upstream theorem or an explicit `theorem` where the signature
needs stating separately.  These are the authoritative typed witnesses behind
the routing engine.  Lean infers the universe parameters implicitly.

Usage:  `#check cluster_forcing_distributed_agents`
         → `∀ (W : WorkingSystem), StructurallyForced W → handles_distributed_agents W → HasBubbles W`
         `#check cluster_meta_modular`
         → `∀ (S : ConstraintSubset) (W : WorkingSystem), PartialWellFormed W S → projection_valid S W`
         `#check cluster_lattice_graceful`
         → `∀ (M : CoreModel), NoSelfCorrection M → RevisionGate M`

-- ── Tier 2 forcing ──────────────────────────────────────────────────────── -/

/-- Cluster `.forcing_distributed_agents`: distributed agents force HasBubbles. -/
def cluster_forcing_distributed_agents :
    ∀ W : WorkingSystem, StructurallyForced W → handles_distributed_agents W → HasBubbles W :=
  fun _W sf => sf.forcing .scope

/-- Cluster `.forcing_bounded_audit`: bounded audit forces HasTrustBridges. -/
def cluster_forcing_bounded_audit :
    ∀ W : WorkingSystem, StructurallyForced W → handles_bounded_audit W → HasTrustBridges W :=
  fun _W sf => sf.forcing .trust

/-- Cluster `.forcing_export`: export-across-boundaries forces HasHeaders. -/
def cluster_forcing_export :
    ∀ W : WorkingSystem, StructurallyForced W → handles_export W → HasHeaders W :=
  fun _W sf => sf.forcing .headers

/-- Cluster `.forcing_adversarial`: adversarial pressure forces HasRevocation. -/
def cluster_forcing_adversarial :
    ∀ W : WorkingSystem, StructurallyForced W → handles_adversarial W → HasRevocation W :=
  fun _W sf => sf.forcing .revocation

/-- Cluster `.forcing_coordination`: coordination need forces HasBank. -/
def cluster_forcing_coordination :
    ∀ W : WorkingSystem, StructurallyForced W → handles_coordination W → HasBank W :=
  fun _W sf => sf.forcing .bank

/-- Cluster `.forcing_truth`: truth pressure forces HasRedeemability. -/
def cluster_forcing_truth :
    ∀ W : WorkingSystem, StructurallyForced W → handles_truth_pressure W → HasRedeemability W :=
  fun _W sf => sf.forcing .redeemability

/-- Cluster `.forcing_multi_agent`: multi-agent heterogeneous access forces HasGranularACL. -/
def cluster_forcing_multi_agent :
    ∀ W : WorkingSystem, StructurallyForced W → handles_multi_agent W → HasGranularACL W :=
  fun _W sf => sf.forcing .authorization

-- ── Tier 3 goal transport ────────────────────────────────────────────────

/-- Cluster `.goal_safeWithdrawal`: SafeWithdrawalGoal is Compatible-transport-safe. -/
def cluster_goal_safeWithdrawal := transport_safe_withdrawal

/-- Cluster `.goal_reliableExport`: ReliableExportGoal is Compatible-transport-safe. -/
def cluster_goal_reliableExport := transport_reliable_export

/-- Cluster `.goal_soundDeposits`: SoundDepositsGoal is Compatible-transport-safe. -/
def cluster_goal_soundDeposits := transport_sound_deposits

/-- Cluster `.goal_selfCorrection`: SelfCorrectionGoal is Compatible-transport-safe. -/
def cluster_goal_selfCorrection := transport_self_correction

/-- Cluster `.goal_corrigible_universal`: CorrigibleLedgerGoal ∀-part is Compatible-safe. -/
def cluster_goal_corrigible_universal := transport_corrigible_universal

/-- Cluster `.goal_corrigible_full`: full CorrigibleLedgerGoal is SurjectiveCompatible-safe. -/
def cluster_goal_corrigible_full := transport_corrigible_ledger

-- ── Tier 4 bank goal bundles ─────────────────────────────────────────────

/-- Cluster `.tier4_bank_goals_compat`: all five ∀-health goals + universal
    corrigibility transport through any plain Compatible extension. -/
def cluster_tier4_bank_goals_compat
    (E : ExtModel) (C : CoreModel) (h : Compatible E C)
    (h_sw : SafeWithdrawalGoal C) (h_re : ReliableExportGoal C)
    (h_sd : SoundDepositsGoal C) (h_sc : SelfCorrectionGoal C)
    (h_cl : CorrigibleLedgerGoal C) :
    SafeWithdrawalGoal (forget E) ∧ ReliableExportGoal (forget E) ∧
    SoundDepositsGoal (forget E) ∧ SelfCorrectionGoal (forget E) ∧
    (∀ B_E : (forget E).sig.Bubble, (forget E).ops.hasRevision B_E →
     ∀ d_E d'_E : (forget E).sig.Deposit,
     (forget E).ops.revise B_E d_E d'_E → (forget E).ops.truth B_E d'_E) :=
  ⟨transport_safe_withdrawal E C h h_sw,
   transport_reliable_export E C h h_re,
   transport_sound_deposits E C h h_sd,
   transport_self_correction E C h h_sc,
   transport_corrigible_universal E C h h_cl⟩

/-- Cluster `.tier4_bank_goals_surj`: all five health goals including full
    CorrigibleLedgerGoal (∃+∀) transport via SurjectiveCompatible. -/
def cluster_tier4_bank_goals_surj
    (E : ExtModel) (C : CoreModel) (h : SurjectiveCompatible E C)
    (h_sw : SafeWithdrawalGoal C) (h_re : ReliableExportGoal C)
    (h_sd : SoundDepositsGoal C) (h_sc : SelfCorrectionGoal C)
    (h_cl : CorrigibleLedgerGoal C) :
    SafeWithdrawalGoal (forget E) ∧ ReliableExportGoal (forget E) ∧
    SoundDepositsGoal (forget E) ∧ SelfCorrectionGoal (forget E) ∧
    CorrigibleLedgerGoal (forget E) :=
  ⟨transport_safe_withdrawal E C h.toCompatible h_sw,
   transport_reliable_export E C h.toCompatible h_re,
   transport_sound_deposits E C h.toCompatible h_sd,
   transport_self_correction E C h.toCompatible h_sc,
   transport_corrigible_ledger E C h h_cl⟩

-- ── World-bundle obligation theorems ─────────────────────────────────────
-- Each theorem names and proves the machine-checked obligation associated with
-- its WorldTag.

/-- Cluster `.world_lies_possible`: lying is structurally possible when W_lies_possible holds. -/
def cluster_world_lies_possible := WorldCtx.lie_possible_of_W

/-- Cluster `.world_bounded_audit`: audit cannot complete before deadline under W_bounded_verification. -/
def cluster_world_bounded_audit := WorldCtx.bounded_audit_fails

/-- Cluster `.world_asymmetric_costs`: export cost strictly less than defense cost under W_asymmetric_costs. -/
def cluster_world_asymmetric_costs := WorldCtx.cost_asymmetry_of_W

/-- Cluster `.world_partial_observability`: partial observability blocks omniscience —
    there exists a proposition no agent can determine from observations alone. -/
def cluster_world_partial_observability := WorldCtx.partial_obs_no_omniscience

/-- Cluster `.world_spoofed_v`: spoofed provenance or consultation suppression contradicts
    any existing verification path. -/
theorem cluster_world_spoofed_v
    {PropLike Standard ErrorModel Provenance : Type u}
    (W : W_spoofedV (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (a : Agent) (p : PathExists d) :
    (EpArch.V_spoof d ∨ EpArch.consultation_suppressed a) → False :=
  spoofed_V_blocks_path_of_W W d a p

/-- Cluster `.world_lies_scale`: lies scale — export cost < defense cost under W_lies_scale. -/
def cluster_world_lies_scale := lies_scale_of_W

/-- Cluster `.world_rolex_ddos`: individual and population attacks are structurally equivalent. -/
def cluster_world_rolex_ddos := rolex_ddos_structural_equivalence_of_W

/-- Cluster `.world_ddos`: any DDoS vector causes verification collapse under W_ddos. -/
def cluster_world_ddos := ddos_causes_verification_collapse_of_W


-- ── Constraint-modularity meta-theorems ───────────────────────────────────────

/-- Cluster `.meta_modular`: the seven EpArch constraints are independent modules. -/
def cluster_meta_modular := modular


-- ── Lattice-stability theorems ─────────────────────────────────────────────────

/-- Cluster `.lattice_graceful`: graceful degradation — removing self-correction
    collapses the RevisionGate obligation to True (vacuously satisfied). -/
def cluster_lattice_graceful := graceful_degradation

/-- Cluster `.lattice_sub_safety`: compatible extension of any sub-bundle that
    already satisfies RevisionGate preserves RevisionGate. -/
def cluster_lattice_sub_safety := sub_revision_safety

/-- Cluster `.lattice_pack`: EpArch is a floor, not a cage — the full
    bidirectional lattice-stability result. -/
def cluster_lattice_pack := modularity_pack


/-! ## §8  Sample Configurations

Uncomment `#eval` lines to inspect routing interactively. -/

/-- Full EpArch configuration: all seven constraints, all five goals, all eight worlds. -/
def fullConfig : EpArchConfig where
  constraints := [.distributed_agents, .bounded_audit, .export_across_boundaries,
                  .adversarial_pressure, .coordination_need, .truth_pressure,
                  .multi_agent_access]
  goals       := [.safeWithdrawal, .reliableExport, .corrigibleLedger,
                  .soundDeposits, .selfCorrection]
  worlds      := [.lies_possible, .bounded_verification, .partial_observability,
                  .asymmetric_costs, .spoofedV, .lies_scale, .rolex_ddos, .ddos]

/-- Minimal configuration: one constraint, one goal, no worlds. -/
def minimalConfig : EpArchConfig where
  constraints := [.distributed_agents]
  goals       := [.safeWithdrawal]
  worlds      := []

/-- Goal-only configuration: no constraints declared, all five goals. -/
def goalsOnlyConfig : EpArchConfig where
  constraints := []
  goals       := [.safeWithdrawal, .reliableExport, .corrigibleLedger,
                  .soundDeposits, .selfCorrection]
  worlds      := []

-- #eval showConfig fullConfig
-- #eval showConfig minimalConfig
-- #eval showConfig goalsOnlyConfig

end EpArch.Meta.Config
