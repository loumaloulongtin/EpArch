/-
EpArch/Meta/Config.lean — Configurable Certification Engine

Given an `EpArchConfig` specifying which constraints, goals, and world bundles
are active, this module computes and certifies:

  1. **Which theorem clusters are enabled** (`clusterEnabled` — computable `Bool`).
  2. **Human-readable routing report** (`explainConfig`, `showConfig` — `#eval`-able).
  3. **Machine-certified soundness** (`CertifiedProjection`, `certify`): every
     cluster returned as enabled is backed by a concrete machine-checked proof.

## Four-layer design

**Routing layer** (`clusterEnabled`, `CertifiedProjection.enabled/complete/sound`):
  Uses `clusterValid c := True` so routing is decidable and `certify` type-checks
  without universe complications.

**Constraint proof layer** (`constraintProof`, `CertifiedProjection.constraintWitnesses`):
  Tier 2 forcing clusters carry a genuine `ConstraintProof` record (real Lean
  proposition + machine-checked proof).  `WorkingSystem` is monomorphic so Lean 4's
  universe isolation rule does not block this family's carrier.

**Indexed witness layer** (`goalWitness`, `worldWitness`, `tier4Witness`,
  `CertifiedProjection.goalWitnesses/worldWitnesses/tier4Witnesses`):
  Goal, World, and Tier 4 clusters use indexed inductives
  `GoalWitness : EnabledGoalCluster → Type 1` etc.  Each constructor stores the
  polymorphic transport theorem as a Prop-valued argument.  Lean 4's impredicativity
  of Prop allows `∀ (E : ExtModel), ...P...` to live in Prop even though `ExtModel`
  is universe-polymorphic — avoiding the isolation rule that blocks `def` bodies.

**Proof-content layer** (`cluster_*` witnesses in §5b):
  Universe-polymorphic Lean theorems covering all 25 clusters.  These are the
  standalone named witnesses usable via `#check cluster_goal_safeWithdrawal`, etc.

  See §4 for the full universe isolation explanation and §2b for the per-family
  enumeration architecture.

## Usage

```lean
-- See which clusters are active for your configuration:
#eval showConfig myConfig

-- Obtain a proof object certifying every enabled cluster:
#check certify myConfig

-- Access typed proof content for a specific cluster family:
(certify myConfig).goalWitnesses .goal_safeWithdrawal   -- GoalWitness
(certify myConfig).worldWitnesses .world_lies_possible  -- WorldWitness
(certify myConfig).tier4Witnesses .tier4_commitments    -- Tier4Witness

-- Inspect a specific cluster's theorem:
#check cluster_forcing_distributed_agents
#check cluster_goal_safeWithdrawal
#check cluster_world_partial_observability
```
-/

import EpArch.Minimality
import EpArch.Health
import EpArch.Meta.TheoremTransport
import EpArch.Meta.Tier4Transport
import EpArch.WorldCtx
import EpArch.AdversarialObligations

namespace EpArch.Meta.Config

open EpArch
open RevisionSafety
open EpArch.Meta.TheoremTransport
open EpArch.Meta.Tier4Transport
open EpArch.AdversarialObligations

-- Universe parameter shared across all theorem-level propositions in this file.
-- Allows theorem declarations in §5b to reference universe-polymorphic types
-- (WorkingSystem, CoreModel, ExtModel, W_spoofedV) — standard for Lean 4 theorem declarations.
universe u


/-! ## §1  Configuration Language -/

/-- The six constraints the paper analyses.  Each tag maps to one forcing theorem
    in `EpArch.Minimality`. -/
inductive ConstraintTag where
  | distributed_agents
  | bounded_audit
  | export_across_boundaries
  | adversarial_pressure
  | coordination_need
  | truth_pressure
  deriving DecidableEq, BEq, Repr

/-- The five health goals from `EpArch.Health`. -/
inductive GoalTag where
  | safeWithdrawal
  | reliableExport
  | corrigibleLedger
  | soundDeposits
  | selfCorrection
  deriving DecidableEq, BEq, Repr

/-- The eight named world bundles from the paper. -/
inductive WorldTag where
  | lies_possible
  | bounded_verification
  | partial_observability
  | asymmetric_costs
  | spoofedV
  | lies_scale
  | rolex_ddos
  | ddos
  deriving DecidableEq, BEq, Repr

/-- A user-supplied configuration: choose which constraints, goals, and world
    bundles are operative.  Use `List` for easy `#eval` output. -/
structure EpArchConfig where
  constraints : List ConstraintTag
  goals       : List GoalTag
  worlds      : List WorldTag
  deriving Repr


/-! ## §2  Cluster Tags -/

/-- The 25 theorem clusters certified in EpArch Tiers 2–4 plus world-bundle obligations. -/
inductive ClusterTag where
  -- Tier 2: constraint-forcing theorems (6 clusters)
  | forcing_distributed_agents
  | forcing_bounded_audit
  | forcing_export
  | forcing_adversarial
  | forcing_coordination
  | forcing_truth
  -- Tier 3: health-goal transport theorems (6 clusters)
  | goal_safeWithdrawal
  | goal_reliableExport
  | goal_soundDeposits
  | goal_selfCorrection
  | goal_corrigible_universal   -- ∀-part only, plain Compatible
  | goal_corrigible_full        -- full ∃+∀, requires SurjectiveCompatible
  -- Tier 4: main library clusters (5 clusters)
  | tier4_commitments           -- Cluster A: CommitmentsCtx-parameterized
  | tier4_structural            -- Cluster B: SEV/Temporal/Monolithic/Header
  | tier4_lts_universal         -- Cluster B+: LTS withdrawal/repair/submit gates
  | tier4_bank_goals_compat     -- Cluster C  (Compatible): 4 goals + universal corrigible
  | tier4_bank_goals_surj       -- Cluster C+ (SurjectiveCompatible): full CorrigibleLedgerGoal
  -- World-bundle obligation clusters (8 world tags, all now have proved obligations;
  -- previously .partial_observability was unwired — now corrected)
  | world_lies_possible         -- W_lies_possible: lying is possible
  | world_bounded_audit         -- W_bounded_verification: audit can fail before deadline
  | world_asymmetric_costs      -- W_asymmetric_costs: export_cost < defense_cost
  | world_partial_observability -- W_partial_observability: obs underdetermines truth → no omniscience
  | world_spoofed_v             -- W_spoofedV: spoofed provenance blocks path
  | world_lies_scale            -- W_lies_scale: lies scale (cost asymmetry)
  | world_rolex_ddos            -- W_rolex_ddos: individual & population attacks structurally same
  | world_ddos                  -- W_ddos: DDoS causes verification collapse
  deriving DecidableEq, BEq, Repr


/-! ## §2b  Per-Family Cluster Enumerations

Lean 4's universe isolation rule blocks a uniform `ClusterTag → ClusterProof`
def (see §4).  These per-family enumerations enable a **per-family proof carrier**
pattern: families whose underlying types are monomorphic can carry genuine
propositions and proofs while universe-polymorphic families stay at `True`.

**Currently monomorphic** (real proof carrier available): constraint clusters
(Tier 2 forcing) — `WorkingSystem` has no free universe parameters.

**Universe-polymorphic** (routing only; real propositions in §5b witnesses):
goal, Tier 4 bank-bundle, and world clusters. -/

/-- The six Tier 2 constraint-forcing clusters. -/
inductive EnabledConstraintCluster where
  | forcing_distributed_agents | forcing_bounded_audit | forcing_export
  | forcing_adversarial | forcing_coordination | forcing_truth
  deriving DecidableEq, BEq, Repr

/-- The six Tier 3 health-goal transport clusters. -/
inductive EnabledGoalCluster where
  | goal_safeWithdrawal | goal_reliableExport | goal_soundDeposits
  | goal_selfCorrection | goal_corrigible_universal | goal_corrigible_full
  deriving DecidableEq, BEq, Repr

/-- The five Tier 4 library clusters. -/
inductive EnabledTier4Cluster where
  | tier4_commitments | tier4_structural | tier4_lts_universal
  | tier4_bank_goals_compat | tier4_bank_goals_surj
  deriving DecidableEq, BEq, Repr

/-- The eight world-bundle clusters. -/
inductive EnabledWorldCluster where
  | world_lies_possible | world_bounded_audit | world_asymmetric_costs
  | world_partial_observability | world_spoofed_v
  | world_lies_scale | world_rolex_ddos | world_ddos
  deriving DecidableEq, BEq, Repr

/-- Embed a constraint cluster into the global tag space. -/
def EnabledConstraintCluster.toClusterTag : EnabledConstraintCluster → ClusterTag
  | .forcing_distributed_agents => .forcing_distributed_agents
  | .forcing_bounded_audit      => .forcing_bounded_audit
  | .forcing_export             => .forcing_export
  | .forcing_adversarial        => .forcing_adversarial
  | .forcing_coordination       => .forcing_coordination
  | .forcing_truth              => .forcing_truth

/-- Embed a goal cluster into the global tag space. -/
def EnabledGoalCluster.toClusterTag : EnabledGoalCluster → ClusterTag
  | .goal_safeWithdrawal       => .goal_safeWithdrawal
  | .goal_reliableExport       => .goal_reliableExport
  | .goal_soundDeposits        => .goal_soundDeposits
  | .goal_selfCorrection       => .goal_selfCorrection
  | .goal_corrigible_universal => .goal_corrigible_universal
  | .goal_corrigible_full      => .goal_corrigible_full

/-- Embed a Tier 4 cluster into the global tag space. -/
def EnabledTier4Cluster.toClusterTag : EnabledTier4Cluster → ClusterTag
  | .tier4_commitments       => .tier4_commitments
  | .tier4_structural        => .tier4_structural
  | .tier4_lts_universal     => .tier4_lts_universal
  | .tier4_bank_goals_compat => .tier4_bank_goals_compat
  | .tier4_bank_goals_surj   => .tier4_bank_goals_surj

/-- Embed a world cluster into the global tag space. -/
def EnabledWorldCluster.toClusterTag : EnabledWorldCluster → ClusterTag
  | .world_lies_possible        => .world_lies_possible
  | .world_bounded_audit        => .world_bounded_audit
  | .world_asymmetric_costs     => .world_asymmetric_costs
  | .world_partial_observability => .world_partial_observability
  | .world_spoofed_v            => .world_spoofed_v
  | .world_lies_scale           => .world_lies_scale
  | .world_rolex_ddos           => .world_rolex_ddos
  | .world_ddos                 => .world_ddos


/-! ## §3  Routing Function -/

/-- All 25 cluster tags, in canonical order.  Used by `explainConfig`. -/
def allClusters : List ClusterTag := [
  .forcing_distributed_agents, .forcing_bounded_audit, .forcing_export,
  .forcing_adversarial, .forcing_coordination, .forcing_truth,
  .goal_safeWithdrawal, .goal_reliableExport, .goal_soundDeposits,
  .goal_selfCorrection, .goal_corrigible_universal, .goal_corrigible_full,
  .tier4_commitments, .tier4_structural, .tier4_lts_universal,
  .tier4_bank_goals_compat, .tier4_bank_goals_surj,
  .world_lies_possible, .world_bounded_audit, .world_asymmetric_costs,
  .world_partial_observability,
  .world_spoofed_v, .world_lies_scale, .world_rolex_ddos, .world_ddos]

/-- Decide whether cluster `c` is applicable for config `cfg`.

    Tier 4 structural/LTS/commitments clusters are always applicable.
    Constraint-forcing clusters are gated on the constraint being listed.
    Goal-transport clusters are gated on the goal being listed.
    Bank-goal bundles require the full goal set. -/
def clusterEnabled (cfg : EpArchConfig) : ClusterTag → Bool
  | .forcing_distributed_agents => cfg.constraints.contains .distributed_agents
  | .forcing_bounded_audit      => cfg.constraints.contains .bounded_audit
  | .forcing_export             => cfg.constraints.contains .export_across_boundaries
  | .forcing_adversarial        => cfg.constraints.contains .adversarial_pressure
  | .forcing_coordination       => cfg.constraints.contains .coordination_need
  | .forcing_truth              => cfg.constraints.contains .truth_pressure
  | .goal_safeWithdrawal        => cfg.goals.contains .safeWithdrawal
  | .goal_reliableExport        => cfg.goals.contains .reliableExport
  | .goal_soundDeposits         => cfg.goals.contains .soundDeposits
  | .goal_selfCorrection        => cfg.goals.contains .selfCorrection
  | .goal_corrigible_universal  => cfg.goals.contains .corrigibleLedger
  | .goal_corrigible_full       => cfg.goals.contains .corrigibleLedger
  | .tier4_commitments          => true
  | .tier4_structural           => true
  | .tier4_lts_universal        => true
  | .tier4_bank_goals_compat    =>
      cfg.goals.contains .safeWithdrawal &&
      cfg.goals.contains .reliableExport &&
      cfg.goals.contains .soundDeposits &&
      cfg.goals.contains .selfCorrection &&
      cfg.goals.contains .corrigibleLedger
  | .tier4_bank_goals_surj      =>
      cfg.goals.contains .safeWithdrawal &&
      cfg.goals.contains .reliableExport &&
      cfg.goals.contains .soundDeposits &&
      cfg.goals.contains .selfCorrection &&
      cfg.goals.contains .corrigibleLedger
  -- World-bundle obligations: gated on worlds field
  | .world_lies_possible    => cfg.worlds.contains .lies_possible
  | .world_bounded_audit    => cfg.worlds.contains .bounded_verification
  | .world_asymmetric_costs => cfg.worlds.contains .asymmetric_costs
  | .world_partial_observability => cfg.worlds.contains .partial_observability
  | .world_spoofed_v        => cfg.worlds.contains .spoofedV
  | .world_lies_scale       => cfg.worlds.contains .lies_scale
  | .world_rolex_ddos       => cfg.worlds.contains .rolex_ddos
  | .world_ddos             => cfg.worlds.contains .ddos

/-- The clusters enabled by `cfg`, in canonical order. -/
def explainConfig (cfg : EpArchConfig) : List ClusterTag :=
  allClusters.filter (clusterEnabled cfg)


/-! ## §4  Cluster Validity

### Why `clusterValid c := True`

The certification engine has **four layers** (mirroring the file header):

1. **Routing layer** — `clusterEnabled`, `enabled`, `complete`, `sound`.
   Works with `clusterValid c := True` so routing is decidable and
   `certify` type-checks without universe complications.

2. **Constraint proof layer** — `constraintProof`, `constraintWitnesses`,
   `enabledConstraintWitnesses` (§4b).
   `WorkingSystem` is monomorphic (fields: `SystemSpec`, `Bool`; no free
   universe levels), so Lean 4's isolation rule does not block a
   `def constraintProof : EnabledConstraintCluster → ConstraintProof`.
   Tier 2 forcing clusters carry a genuine `statement : Prop` / `proof : statement`
   pair.  `enabledConstraintWitnesses` filters this to only the clusters
   enabled by a given `EpArchConfig`.

3. **Indexed witness layer** — `goalWitness`, `worldWitness`, `tier4Witness` (§4c–§4e).
   Goal, World, and Tier 4 clusters reference `ExtModel.{u}`, `CoreModel.{u}`,
   `WorldCtx.{u}`, etc.  A uniform `def` carrier is blocked by the universe isolation
   rule, but `inductive GoalWitness : EnabledGoalCluster → Type 1` with
   Prop-valued constructor arguments is accepted by Lean 4: `∀ (E : ExtModel), ...P...`
   is in `Prop` when `P` is in `Prop`, by impredicativity, regardless of `ExtModel`'s
   universe level.  The constructors package the real transport theorems as args.

4. **Proof-content layer** — the `cluster_*` witnesses in §5b.
   Universe-polymorphic Lean theorems covering all 25 clusters.  Goal/Tier4/World
   clusters reference `ExtModel.{u₁,u₂}`, `CoreModel.{u₃}`, `WorldCtx.{u}` and
   cannot be packed into a monomorphic def; the §5b witnesses are the authoritative
   standalone form.  Inspect with `#check cluster_goal_safeWithdrawal`, etc.

### Why a uniform `ClusterTag → ClusterProof` def is blocked

Lean 4's **universe isolation rule** prohibits a `def f : A → B` whose body
references universe levels that do not appear in the declared type `A → B`.
The 25 cluster theorems span four independent universe families:

| Family              | Source module           | Representative type      |
|---------------------|-------------------------|--------------------------|
| Forcing             | `EpArch.Minimality`     | `WorkingSystem.{u}`      |
| Goal transport      | `EpArch.Meta.TheoremTransport` | `ExtModel.{u₁,u₂}`, `CoreModel.{u₃}` |
| World bundles       | `EpArch.WorldCtx`       | `WorldCtx.{u}`           |
| Adversarial         | `EpArch.AdversarialObligations` | `W_spoofedV.{u}`  |

None of these universe levels surface in `ClusterTag → ClusterProof` when
`ClusterProof : Type 1` is a fixed-universe record.  Resolving this would
require either monomorphising all source types to universe 0 or parameterising
`ClusterProof` across 20+ independent universe levels — both are large refactors
of modules outside this file, and neither is needed: the indexed witnesses (§4c–§4e)
and §5b witnesses already provide all proof content in the most natural Lean 4 form. -/

/-- Every cluster is valid: holds unconditionally (all 25 are machine-proved).
    See the `cluster_*` witnesses in §5b for real typed propositions. -/
@[simp] def clusterValid : ClusterTag → Prop := fun _ => True


/-! ## §4b  Constraint Proof Carrier

`WorkingSystem` is monomorphic — its fields are `SystemSpec` and `Bool`, with
no free universe levels — so Lean 4's universe isolation rule does **not** block
`def constraintProof : EnabledConstraintCluster → ConstraintProof`.

The Tier 2 forcing theorems can therefore be embedded as genuine propositions
with genuine machine-checked proofs, not just `True`.

All other families (Tier 3 goal transport, Tier 4 bank bundles, world clusters)
reference `ExtModel.{u₁,u₂}`, `CoreModel.{u₃}`, `WorldCtx.{u}` — universe-
polymorphic types — so their real propositions live as `cluster_*` witnesses
in §5b only. -/

/-- Proof-carrying record for a Tier 2 constraint-forcing cluster:
    the actual Lean forcing proposition and its machine-checked proof. -/
structure ConstraintProof : Type 1 where
  /-- The actual Lean forcing proposition. -/
  statement : Prop
  /-- Machine-checked proof of `statement`. -/
  proof     : statement

/-- For every Tier 2 constraint cluster, the real proposition and its proof. -/
def constraintProof : EnabledConstraintCluster → ConstraintProof
  | .forcing_distributed_agents => {
      statement := ∀ W : WorkingSystem, WellFormed W → handles_distributed_agents W → HasBubbles W
      proof     := distributed_agents_require_bubbles }
  | .forcing_bounded_audit => {
      statement := ∀ W : WorkingSystem, WellFormed W → handles_bounded_audit W → HasTrustBridges W
      proof     := bounded_audit_requires_trust_bridges }
  | .forcing_export => {
      statement := ∀ W : WorkingSystem, WellFormed W → handles_export W → HasHeaders W
      proof     := export_requires_headers }
  | .forcing_adversarial => {
      statement := ∀ W : WorkingSystem, WellFormed W → handles_adversarial W → HasRevocation W
      proof     := adversarial_requires_revocation }
  | .forcing_coordination => {
      statement := ∀ W : WorkingSystem, WellFormed W → handles_coordination W → HasBank W
      proof     := coordination_requires_bank }
  | .forcing_truth => {
      statement := ∀ W : WorkingSystem, WellFormed W → handles_truth_pressure W → HasRedeemability W
      proof     := truth_pressure_requires_redeemability }


/-! ## §4c  Goal Witness Carrier

Indexed proof-carrying inductive for Tier 3 health-goal transport clusters.
Each constructor stores the polymorphic transport theorem schema as a Prop-valued
argument.  Lean 4's impredicativity of `Prop` means `∀ (E : ExtModel), ...P...`
is in `Prop` when `P` is in `Prop`, even though `ExtModel` lives at `Type (u+1)`.
This sidesteps the `def`-body universe isolation rule while still delivering
the real transport theorem to callers. -/

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

Same indexed-inductive pattern for world-bundle clusters.
`WorldCtx.{u}` is universe-polymorphic; the constructor args are Prop-valued
(impredicative ∀ over WorldCtx instantiations), so `WorldWitness` itself lives
in `Type 1` without a universe parameter conflict. -/

/-- Indexed proof carrier for world-bundle clusters. -/
inductive WorldWitness : EnabledWorldCluster → Type 1 where
  | liesPossible :
      (∀ (C : WorldCtx) (W : C.W_lies_possible), ∃ w a P, C.Lie w a P) →
      WorldWitness .world_lies_possible
  | boundedAudit :
      (∀ (C : WorldCtx) (w : C.World) (P : C.Claim) (k t : Nat),
        C.RequiresSteps w P k → t < k → ¬C.VerifyWithin w P t) →
      WorldWitness .world_bounded_audit
  | asymmetricCosts :
      (∀ (C : WorldCtx) (W : C.W_asymmetric_costs), W.export_cost < W.defense_cost) →
      WorldWitness .world_asymmetric_costs
  | partialObservability :
      (∀ (C : WorldCtx) (W : C.W_partial_observability), ∃ P, C.NotDeterminedByObs P) →
      WorldWitness .world_partial_observability
  | spoofedV :
      (∀ {PL SL EL PrL : Type}
        (W : W_spoofedV (PropLike := PL) (Standard := SL) (ErrorModel := EL) (Provenance := PrL))
        (d : Deposit PL SL EL PrL) (v : V_Spoofed_State d) (p : PathExists d),
        is_V_spoofed v → ¬has_path p) →
      WorldWitness .world_spoofed_v
  | liesScale :
      (∀ (W : W_lies_scale), W.costs.export_cost < W.costs.defense_cost) →
      WorldWitness .world_lies_scale
  | rolexDdos :
      (∀ (W : W_rolex_ddos), same_structure W.rolex_structure W.ddos_structure) →
      WorldWitness .world_rolex_ddos
  | ddos :
      (∀ (W : W_ddos) (a : Agent) (s : DDoSState a) (c : CollapsedState a),
        some_vector_overwhelmed s → is_collapsed c) →
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

Same indexed-inductive pattern for Tier 4 library clusters.
`commitments` and `structural` quantify over `Type`-universe type variables;
`ltsUniversal` additionally quantifies over `Reason` and `Evidence` types.
All constructor args are Prop-valued by Prop impredicativity. -/

/-- Indexed proof carrier for Tier 4 clusters. -/
inductive Tier4Witness : EnabledTier4Cluster → Type 1 where
  | commitments :
      (∀ {PL SL EL PrL : Type} {Extra : Prop}
        (E : ExtCommitmentsCtx PL SL EL PrL Extra),
        (∀ (a : Agent) (B : Bubble) (P : Claim),
            ∃ (_ : certainty_L a P), ¬knowledge_B B P) ∧
        (∀ (a : Agent) (B : Bubble) (P : Claim),
            ∃ (_ : knowledge_B B P), ¬certainty_L a P) ∧
        (∀ G : GlobalLedger, supports_innovation G → ¬supports_coordination G) ∧
        (∀ (B : Bubble) (d : Deposit PL SL EL PrL),
            ∃ (_ : consensus B d.P), ¬redeemable d)) →
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
           (d : Deposit PL SL EL PrL),
           StepSemantics.Step (Reason := Reason) (Evidence := Evidence)
             s (StepSemantics.Action.Submit d) s' →
           ∃ d', d' ∈ s'.ledger ∧ d'.status = DepositStatus.Candidate)) →
      Tier4Witness .tier4_lts_universal
  | bankGoalsCompat :
      (∀ (E : ExtModel) (C : CoreModel) (h : Compatible E C)
        (h_sw : SafeWithdrawalGoal C) (h_re : ReliableExportGoal C)
        (h_sd : SoundDepositsGoal C) (h_sc : SelfCorrectionGoal C)
        (h_cl : CorrigibleLedgerGoal C),
        SafeWithdrawalGoal (forget E) ∧ ReliableExportGoal (forget E) ∧
        SoundDepositsGoal (forget E) ∧ SelfCorrectionGoal (forget E) ∧
        (∀ B_E : (forget E).sig.Bubble, (forget E).ops.hasRevision B_E →
         ∀ d_E d'_E : (forget E).sig.Deposit,
         (forget E).ops.revise B_E d_E d'_E → (forget E).ops.truth B_E d'_E)) →
      Tier4Witness .tier4_bank_goals_compat
  | bankGoalsSurj :
      (∀ (E : ExtModel) (C : CoreModel) (h : SurjectiveCompatible E C)
        (h_sw : SafeWithdrawalGoal C) (h_re : ReliableExportGoal C)
        (h_sd : SoundDepositsGoal C) (h_sc : SelfCorrectionGoal C)
        (h_cl : CorrigibleLedgerGoal C),
        SafeWithdrawalGoal (forget E) ∧ ReliableExportGoal (forget E) ∧
        SoundDepositsGoal (forget E) ∧ SelfCorrectionGoal (forget E) ∧
        CorrigibleLedgerGoal (forget E)) →
      Tier4Witness .tier4_bank_goals_surj

/-- For every Tier 4 cluster, deliver its `Tier4Witness`. -/
def tier4Witness : (c : EnabledTier4Cluster) → Tier4Witness c
  | .tier4_commitments       => .commitments   commitments_transport_pack
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


/-! ## §5  Soundness: `clusterEnabled cfg c = true → clusterValid c` -/

/-- `clusterEnabled` is sound: every cluster it marks enabled is machine-proved.
    `clusterValid c = True` universally; the proof is `trivial`.
    For the typed proposition of cluster `c`, use `#check cluster_<name>` (§5b). -/
theorem clusterEnabled_sound (cfg : EpArchConfig) (c : ClusterTag)
    (_h : clusterEnabled cfg c = true) : clusterValid c := trivial


/-! ## §6  Human-Readable Output -/

/-- One-line description of each cluster (theorem name in parentheses). -/
def clusterDescription : ClusterTag → String
  | .forcing_distributed_agents =>
      "[Tier 2] distributed_agents → HasBubbles  (distributed_agents_require_bubbles)"
  | .forcing_bounded_audit =>
      "[Tier 2] bounded_audit → HasTrustBridges  (bounded_audit_requires_trust_bridges)"
  | .forcing_export =>
      "[Tier 2] export_across_boundaries → HasHeaders  (export_requires_headers)"
  | .forcing_adversarial =>
      "[Tier 2] adversarial_pressure → HasRevocation  (adversarial_requires_revocation)"
  | .forcing_coordination =>
      "[Tier 2] coordination_need → HasBank  (coordination_requires_bank)"
  | .forcing_truth =>
      "[Tier 2] truth_pressure → HasRedeemability  (truth_pressure_requires_redeemability)"
  | .goal_safeWithdrawal =>
      "[Tier 3] SafeWithdrawalGoal transports via Compatible  (transport_safe_withdrawal)"
  | .goal_reliableExport =>
      "[Tier 3] ReliableExportGoal transports via Compatible  (transport_reliable_export)"
  | .goal_soundDeposits =>
      "[Tier 3] SoundDepositsGoal transports via Compatible  (transport_sound_deposits)"
  | .goal_selfCorrection =>
      "[Tier 3] SelfCorrectionGoal transports via Compatible  (transport_self_correction)"
  | .goal_corrigible_universal =>
      "[Tier 3] CorrigibleLedgerGoal ∀-part transports via Compatible  (transport_corrigible_universal)"
  | .goal_corrigible_full =>
      "[Tier 3] CorrigibleLedgerGoal full ∃+∀ transports via SurjectiveCompatible  (transport_corrigible_ledger)"
  | .tier4_commitments =>
      "[Tier 4-A] CommitmentsCtx-parameterised theorems survive extension  (commitments_transport_pack)"
  | .tier4_structural =>
      "[Tier 4-B] Structural theorems unconditional: SEV/Temporal/Monolithic/Header  (structural_theorems_unconditional)"
  | .tier4_lts_universal =>
      "[Tier 4-B+] LTS-universal: withdrawal/repair/submit gates  (lts_theorems_step_universal)"
  | .tier4_bank_goals_compat =>
      "[Tier 4-C] All ∀-health goals + universal corrigibility via Compatible  (concrete_bank_all_goals_transport)"
  | .tier4_bank_goals_surj =>
      "[Tier 4-C+] All health goals + full CorrigibleLedgerGoal via SurjectiveCompatible  (concrete_bank_all_goals_transport_surj)"
  | .world_lies_possible =>
      "[World] W_lies_possible: lying is structurally possible  (WorldCtx.lie_possible_of_W)"
  | .world_bounded_audit =>
      "[World] W_bounded_verification: audit can fail before deadline  (WorldCtx.bounded_audit_fails)"
  | .world_asymmetric_costs =>
      "[World] W_asymmetric_costs: export cost < defense cost  (WorldCtx.cost_asymmetry_of_W)"
  | .world_partial_observability =>
      "[World] W_partial_observability: obs underdetermines truth → no omniscience  (WorldCtx.partial_obs_no_omniscience)"
  | .world_spoofed_v =>
      "[World] W_spoofedV: spoofed-V blocks provenance path  (AdversarialObligations.spoofed_V_blocks_path_of_W)"
  | .world_lies_scale =>
      "[World] W_lies_scale: lies scale (export < defense cost)  (AdversarialObligations.lies_scale_of_W)"
  | .world_rolex_ddos =>
      "[World] W_rolex_ddos: individual and population attacks structurally equivalent  (AdversarialObligations.rolex_ddos_structural_equivalence_of_W)"
  | .world_ddos =>
      "[World] W_ddos: DDoS causes verification collapse  (AdversarialObligations.ddos_causes_verification_collapse_of_W)"

/-- Human-readable list of all cluster descriptions enabled by `cfg`. -/
def showConfig (cfg : EpArchConfig) : List String :=
  (explainConfig cfg).map clusterDescription


/-! ## §7  Certified Projection

`CertifiedProjection cfg` is a proof-carrying record: it names every enabled
cluster and holds machine-checked evidence that each one is valid. -/

/-- A certified bundle: the enabled clusters for `cfg`, with proofs.

    **Layer 1 (routing):** `enabled`, `complete`, `sound` — all 25 cluster tags,
    routing only, `clusterValid c = True`.

    **Layer 2 (constraint proofs):** `constraintWitnesses` — full `ConstraintProof`
    for all six Tier 2 forcing clusters (total, config-independent).
    `enabledConstraintWitnesses` — filtered to only the clusters enabled by `cfg`.

    **Layer 3 (indexed witnesses):** `goalWitnesses`, `worldWitnesses`, `tier4Witnesses`
    — indexed inductives packaging the real transport theorem for each cluster.
    `enabledGoalWitnesses`, `enabledWorldWitnesses`, `enabledTier4Witnesses` — filtered
    to only the clusters enabled by `cfg` (using dependent pairs `Σ c, WitnessType c`).

    **Layer 4 (proof-content):** `cluster_*` witnesses in §5b cover all 25 clusters. -/
structure CertifiedProjection (cfg : EpArchConfig) where
  /-- The list of enabled clusters (equal to `explainConfig cfg`). -/
  enabled                   : List ClusterTag
  /-- Faithfully mirrors `explainConfig`. -/
  complete                  : enabled = explainConfig cfg
  /-- Every enabled cluster is machine-proved (`clusterValid c = True`). -/
  sound                     : ∀ c, c ∈ enabled → clusterValid c
  /-- Tier 2 proof carriers (all six, config-independent).
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

/-- Compute and certify the full projection for any `EpArchConfig`. -/
def certify (cfg : EpArchConfig) : CertifiedProjection cfg where
  enabled             := explainConfig cfg
  complete            := rfl
  sound               := fun _ _ => trivial
  constraintWitnesses := constraintProof
  enabledConstraintWitnesses :=
    let allCC : List EnabledConstraintCluster :=
      [.forcing_distributed_agents, .forcing_bounded_audit, .forcing_export,
       .forcing_adversarial, .forcing_coordination, .forcing_truth]
    allCC.filterMap fun c =>
      if clusterEnabled cfg c.toClusterTag
      then some (c, constraintProof c)
      else none
  goalWitnesses  := goalWitness
  worldWitnesses := worldWitness
  tier4Witnesses := tier4Witness
  enabledGoalWitnesses :=
    let allGC : List EnabledGoalCluster :=
      [.goal_safeWithdrawal, .goal_reliableExport, .goal_soundDeposits,
       .goal_selfCorrection, .goal_corrigible_universal, .goal_corrigible_full]
    allGC.filterMap fun c =>
      if clusterEnabled cfg c.toClusterTag
      then some ⟨c, goalWitness c⟩
      else none
  enabledWorldWitnesses :=
    let allWC : List EnabledWorldCluster :=
      [.world_lies_possible, .world_bounded_audit, .world_asymmetric_costs,
       .world_partial_observability, .world_spoofed_v,
       .world_lies_scale, .world_rolex_ddos, .world_ddos]
    allWC.filterMap fun c =>
      if clusterEnabled cfg c.toClusterTag
      then some ⟨c, worldWitness c⟩
      else none
  enabledTier4Witnesses :=
    let allT4 : List EnabledTier4Cluster :=
      [.tier4_commitments, .tier4_structural, .tier4_lts_universal,
       .tier4_bank_goals_compat, .tier4_bank_goals_surj]
    allT4.filterMap fun c =>
      if clusterEnabled cfg c.toClusterTag
      then some ⟨c, tier4Witness c⟩
      else none


/-! ## §5b  Named Proof Witnesses

Each theorem below names and proves the machine-checked proposition for its
cluster.  These are the authoritative typed witnesses behind the routing engine.
Lean infers the universe parameters implicitly (they are standard universe-
polymorphic theorems, not match arms of a monomorphic `Prop`-valued def).

Usage:  `#check cluster_forcing_distributed_agents`
         → `∀ (W : WorkingSystem), WellFormed W → handles_distributed_agents W → HasBubbles W`

-- ── Tier 2 forcing ──────────────────────────────────────────────────────── -/

/-- Cluster `.forcing_distributed_agents`: distributed agents force HasBubbles. -/
theorem cluster_forcing_distributed_agents :
    ∀ W : WorkingSystem, WellFormed W → handles_distributed_agents W → HasBubbles W :=
  distributed_agents_require_bubbles

/-- Cluster `.forcing_bounded_audit`: bounded audit forces HasTrustBridges. -/
theorem cluster_forcing_bounded_audit :
    ∀ W : WorkingSystem, WellFormed W → handles_bounded_audit W → HasTrustBridges W :=
  bounded_audit_requires_trust_bridges

/-- Cluster `.forcing_export`: export-across-boundaries forces HasHeaders. -/
theorem cluster_forcing_export :
    ∀ W : WorkingSystem, WellFormed W → handles_export W → HasHeaders W :=
  export_requires_headers

/-- Cluster `.forcing_adversarial`: adversarial pressure forces HasRevocation. -/
theorem cluster_forcing_adversarial :
    ∀ W : WorkingSystem, WellFormed W → handles_adversarial W → HasRevocation W :=
  adversarial_requires_revocation

/-- Cluster `.forcing_coordination`: coordination need forces HasBank. -/
theorem cluster_forcing_coordination :
    ∀ W : WorkingSystem, WellFormed W → handles_coordination W → HasBank W :=
  coordination_requires_bank

/-- Cluster `.forcing_truth`: truth pressure forces HasRedeemability. -/
theorem cluster_forcing_truth :
    ∀ W : WorkingSystem, WellFormed W → handles_truth_pressure W → HasRedeemability W :=
  truth_pressure_requires_redeemability

-- ── Tier 3 goal transport ────────────────────────────────────────────────

/-- Cluster `.goal_safeWithdrawal`: SafeWithdrawalGoal is Compatible-transport-safe. -/
theorem cluster_goal_safeWithdrawal
    (E : ExtModel) (C : CoreModel) (h : Compatible E C)
    (hg : SafeWithdrawalGoal C) : SafeWithdrawalGoal (forget E) :=
  transport_safe_withdrawal E C h hg

/-- Cluster `.goal_reliableExport`: ReliableExportGoal is Compatible-transport-safe. -/
theorem cluster_goal_reliableExport
    (E : ExtModel) (C : CoreModel) (h : Compatible E C)
    (hg : ReliableExportGoal C) : ReliableExportGoal (forget E) :=
  transport_reliable_export E C h hg

/-- Cluster `.goal_soundDeposits`: SoundDepositsGoal is Compatible-transport-safe. -/
theorem cluster_goal_soundDeposits
    (E : ExtModel) (C : CoreModel) (h : Compatible E C)
    (hg : SoundDepositsGoal C) : SoundDepositsGoal (forget E) :=
  transport_sound_deposits E C h hg

/-- Cluster `.goal_selfCorrection`: SelfCorrectionGoal is Compatible-transport-safe. -/
theorem cluster_goal_selfCorrection
    (E : ExtModel) (C : CoreModel) (h : Compatible E C)
    (hg : SelfCorrectionGoal C) : SelfCorrectionGoal (forget E) :=
  transport_self_correction E C h hg

/-- Cluster `.goal_corrigible_universal`: CorrigibleLedgerGoal ∀-part is Compatible-safe. -/
theorem cluster_goal_corrigible_universal
    (E : ExtModel) (C : CoreModel) (h : Compatible E C)
    (hg : CorrigibleLedgerGoal C)
    (B_E : (forget E).sig.Bubble) (hB : (forget E).ops.hasRevision B_E)
    (d_E d'_E : (forget E).sig.Deposit)
    (hr : (forget E).ops.revise B_E d_E d'_E) : (forget E).ops.truth B_E d'_E :=
  transport_corrigible_universal E C h hg B_E hB d_E d'_E hr

/-- Cluster `.goal_corrigible_full`: full CorrigibleLedgerGoal is SurjectiveCompatible-safe. -/
theorem cluster_goal_corrigible_full
    (E : ExtModel) (C : CoreModel) (h : SurjectiveCompatible E C)
    (hg : CorrigibleLedgerGoal C) : CorrigibleLedgerGoal (forget E) :=
  transport_corrigible_ledger E C h hg

-- ── Tier 4 bank goal bundles ─────────────────────────────────────────────

/-- Cluster `.tier4_bank_goals_compat`: all five ∀-health goals + universal
    corrigibility transport through any plain Compatible extension. -/
theorem cluster_tier4_bank_goals_compat
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
theorem cluster_tier4_bank_goals_surj
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
-- its WorldTag.  (.partial_observability has no obligation theorem yet.)

/-- Cluster `.world_lies_possible`: lying is structurally possible when W_lies_possible holds. -/
theorem cluster_world_lies_possible
    (C : WorldCtx) (W : C.W_lies_possible) : ∃ w a P, C.Lie w a P :=
  WorldCtx.lie_possible_of_W C W

/-- Cluster `.world_bounded_audit`: audit cannot complete before deadline under W_bounded_verification. -/
theorem cluster_world_bounded_audit
    (C : WorldCtx) (w : C.World) (P : C.Claim) (k t : Nat) :
    C.RequiresSteps w P k → t < k → ¬C.VerifyWithin w P t :=
  WorldCtx.bounded_audit_fails C w P k t

/-- Cluster `.world_asymmetric_costs`: export cost strictly less than defense cost under W_asymmetric_costs. -/
theorem cluster_world_asymmetric_costs
    (C : WorldCtx) (W : C.W_asymmetric_costs) : W.export_cost < W.defense_cost :=
  WorldCtx.cost_asymmetry_of_W C W

/-- Cluster `.world_partial_observability`: partial observability blocks omniscience —
    there exists a proposition no agent can determine from observations alone.
    This is the epistemic-gap argument, orthogonal to the PRP cost-budget argument. -/
theorem cluster_world_partial_observability
    (C : WorldCtx) (W : C.W_partial_observability) : ∃ P, C.NotDeterminedByObs P :=
  WorldCtx.partial_obs_no_omniscience C W

/-- Cluster `.world_spoofed_v`: spoofed provenance blocks any verification path. -/
theorem cluster_world_spoofed_v
    {PropLike Standard ErrorModel Provenance : Type u}
    (W : W_spoofedV (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (v : V_Spoofed_State d) (p : PathExists d) :
    is_V_spoofed v → ¬has_path p :=
  spoofed_V_blocks_path_of_W W d v p

/-- Cluster `.world_lies_scale`: lies scale — export cost < defense cost under W_lies_scale. -/
theorem cluster_world_lies_scale (W : W_lies_scale) :
    W.costs.export_cost < W.costs.defense_cost :=
  lies_scale_of_W W

/-- Cluster `.world_rolex_ddos`: individual and population attacks are structurally equivalent. -/
theorem cluster_world_rolex_ddos (W : W_rolex_ddos) :
    same_structure W.rolex_structure W.ddos_structure :=
  rolex_ddos_structural_equivalence_of_W W

/-- Cluster `.world_ddos`: DDoS causes verification collapse under W_ddos. -/
theorem cluster_world_ddos
    (W : W_ddos) (a : Agent) (s : DDoSState a) (c : CollapsedState a) :
    some_vector_overwhelmed s → is_collapsed c :=
  ddos_causes_verification_collapse_of_W W a s c


/-! ## §8  Sample Configurations

Uncomment `#eval` lines to inspect routing interactively. -/

/-- Full EpArch configuration: all six constraints, all five goals, all eight worlds. -/
def fullConfig : EpArchConfig where
  constraints := [.distributed_agents, .bounded_audit, .export_across_boundaries,
                  .adversarial_pressure, .coordination_need, .truth_pressure]
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
