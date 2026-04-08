/-
EpArch/Meta/ClusterRegistry.lean — Cluster Tag Registry and Routing

Defines the EpArchConfig language, the 25 ClusterTag values and their
per-family enumerations, the authoritative allXxxClusters lists, and the
routing/display functions.

No EpArch-specific imports — this layer is pure metadata: every type here
is self-contained and depends only on Lean 4 core.

Imported by `Meta/Config.lean`, which adds the proof-carrying layer on top.
-/

namespace EpArch.Meta.Config


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
  -- World-bundle obligation clusters (8 world tags)
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
def (see §4 in Config.lean).  These per-family enumerations enable a
**per-family proof carrier** pattern: families whose underlying types are
monomorphic can carry genuine propositions and proofs while universe-polymorphic
families stay at `True`.

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
  | .world_lies_possible         => .world_lies_possible
  | .world_bounded_audit         => .world_bounded_audit
  | .world_asymmetric_costs      => .world_asymmetric_costs
  | .world_partial_observability => .world_partial_observability
  | .world_spoofed_v             => .world_spoofed_v
  | .world_lies_scale            => .world_lies_scale
  | .world_rolex_ddos            => .world_rolex_ddos
  | .world_ddos                  => .world_ddos


/-! ## §3  Routing

`clusterEnabled` is the single source of truth for which clusters a given
`EpArchConfig` activates.  `explainConfig`/`showConfig` are derived from it. -/

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
  | .world_lies_possible         => cfg.worlds.contains .lies_possible
  | .world_bounded_audit         => cfg.worlds.contains .bounded_verification
  | .world_asymmetric_costs      => cfg.worlds.contains .asymmetric_costs
  | .world_partial_observability => cfg.worlds.contains .partial_observability
  | .world_spoofed_v             => cfg.worlds.contains .spoofedV
  | .world_lies_scale            => cfg.worlds.contains .lies_scale
  | .world_rolex_ddos            => cfg.worlds.contains .rolex_ddos
  | .world_ddos                  => cfg.worlds.contains .ddos

/-- The clusters enabled by `cfg`, in canonical order. -/
def explainConfig (cfg : EpArchConfig) : List ClusterTag :=
  allClusters.filter (clusterEnabled cfg)


/-! ## §4  Human-Readable Output -/

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
      "[Tier 4-A] All commitments proved as standalone theorems; CommitmentsCtx is empty  (commitments_transport_pack)"
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


end EpArch.Meta.Config
