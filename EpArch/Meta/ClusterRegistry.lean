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


/-! ## §2c  Constraint Cluster Metadata

`ConstraintClusterMeta` is the metadata-only record for a Tier 2 cluster.
It records the three fields that determine routing and display — no proofs.
`constraintMeta` is the single source of truth for this data; `clusterEnabled`,
`clusterDescription`, and `EnabledConstraintCluster.toClusterTag` all derive
their Tier 2 answers from it.  `Config.lean` extends this record with a
`witness : ConstraintProof` field via `ConstraintClusterSpec extends ConstraintClusterMeta`.

Placed here (after §2 and §2b) so both `ClusterTag` and `EnabledConstraintCluster`
are in scope. -/

/-- Metadata-only record for a Tier 2 constraint-forcing cluster.
    Contains the three fields needed for routing and display but **no proof**.
    Extended in `Config.lean` by `ConstraintClusterSpec` which adds `witness`. -/
structure ConstraintClusterMeta where
  globalTag   : ClusterTag
  enabledBy   : EpArchConfig → Bool
  description : String

/-- Authoritative metadata for each Tier 2 constraint-forcing cluster.
    `clusterEnabled`, `clusterDescription`, and `EnabledConstraintCluster.toClusterTag`
    all derive their Tier 2 answers from this function. -/
def constraintMeta : EnabledConstraintCluster → ConstraintClusterMeta
  | .forcing_distributed_agents => {
      globalTag   := .forcing_distributed_agents
      enabledBy   := fun cfg => cfg.constraints.contains .distributed_agents
      description := "[Tier 2] distributed_agents → HasBubbles  (distributed_agents_require_bubbles)" }
  | .forcing_bounded_audit => {
      globalTag   := .forcing_bounded_audit
      enabledBy   := fun cfg => cfg.constraints.contains .bounded_audit
      description := "[Tier 2] bounded_audit → HasTrustBridges  (bounded_audit_requires_trust_bridges)" }
  | .forcing_export => {
      globalTag   := .forcing_export
      enabledBy   := fun cfg => cfg.constraints.contains .export_across_boundaries
      description := "[Tier 2] export_across_boundaries → HasHeaders  (export_requires_headers)" }
  | .forcing_adversarial => {
      globalTag   := .forcing_adversarial
      enabledBy   := fun cfg => cfg.constraints.contains .adversarial_pressure
      description := "[Tier 2] adversarial_pressure → HasRevocation  (adversarial_requires_revocation)" }
  | .forcing_coordination => {
      globalTag   := .forcing_coordination
      enabledBy   := fun cfg => cfg.constraints.contains .coordination_need
      description := "[Tier 2] coordination_need → HasBank  (coordination_requires_bank)" }
  | .forcing_truth => {
      globalTag   := .forcing_truth
      enabledBy   := fun cfg => cfg.constraints.contains .truth_pressure
      description := "[Tier 2] truth_pressure → HasRedeemability  (truth_pressure_requires_redeemability)" }


/-- Embed a constraint cluster into the global tag space.
    Derived from `constraintMeta` — the single source of truth for Tier 2 routing.
    `toClusterTag c = (constraintMeta c).globalTag` by definition. -/
def EnabledConstraintCluster.toClusterTag (c : EnabledConstraintCluster) : ClusterTag :=
  (constraintMeta c).globalTag

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
`EpArchConfig` activates.  `explainConfig`/`showConfig` are derived from it.

The per-family canonical lists live here (not in `Config.lean`) because they
are metadata objects — pure enumeration facts, no proofs.  The global
`allClusters` list is derived from them so ordering stays consistent
automatically.  `constraintClusterOfTag?` enables Tier 2 routing and display
to dispatch through `constraintMeta` without re-enumerating the six
forcing constructors. -/

/-- All six Tier 2 constraint-forcing clusters, in canonical order. -/
def allConstraintClusters : List EnabledConstraintCluster :=
  [.forcing_distributed_agents, .forcing_bounded_audit, .forcing_export,
   .forcing_adversarial, .forcing_coordination, .forcing_truth]

/-- All six Tier 3 health-goal transport clusters, in canonical order. -/
def allGoalClusters : List EnabledGoalCluster :=
  [.goal_safeWithdrawal, .goal_reliableExport, .goal_soundDeposits,
   .goal_selfCorrection, .goal_corrigible_universal, .goal_corrigible_full]

/-- All five Tier 4 library clusters, in canonical order. -/
def allTier4Clusters : List EnabledTier4Cluster :=
  [.tier4_commitments, .tier4_structural, .tier4_lts_universal,
   .tier4_bank_goals_compat, .tier4_bank_goals_surj]

/-- All eight world-bundle clusters, in canonical order. -/
def allWorldClusters : List EnabledWorldCluster :=
  [.world_lies_possible, .world_bounded_audit, .world_asymmetric_costs,
   .world_partial_observability, .world_spoofed_v,
   .world_lies_scale, .world_rolex_ddos, .world_ddos]

/-- All 25 cluster tags, in canonical order.  Derived from the per-family lists
    so ordering stays consistent with those lists automatically.
    Used by `explainConfig`. -/
def allClusters : List ClusterTag :=
  (allConstraintClusters.map EnabledConstraintCluster.toClusterTag) ++
  (allGoalClusters.map      EnabledGoalCluster.toClusterTag) ++
  (allTier4Clusters.map     EnabledTier4Cluster.toClusterTag) ++
  (allWorldClusters.map     EnabledWorldCluster.toClusterTag)

/-- Reverse lookup: given a `ClusterTag`, return the matching
    `EnabledConstraintCluster` if it is a Tier 2 forcing tag, or `none`
    otherwise.  Used by `clusterEnabled` and `clusterDescription` to dispatch
    Tier 2 cases through `constraintMeta` without re-enumerating the
    six forcing constructors. -/
def constraintClusterOfTag? (t : ClusterTag) : Option EnabledConstraintCluster :=
  allConstraintClusters.find? fun c => c.toClusterTag == t

/-- Decide whether cluster `c` is applicable for config `cfg`.

    Tier 4 structural/LTS/commitments clusters are always applicable.
    Constraint-forcing clusters are gated on the constraint being listed.
    Goal-transport clusters are gated on the goal being listed.
    Bank-goal bundles require the full goal set. -/
def clusterEnabled (cfg : EpArchConfig) : ClusterTag → Bool
  -- Tier 3: health-goal transport clusters
  | .goal_safeWithdrawal        => cfg.goals.contains .safeWithdrawal
  | .goal_reliableExport        => cfg.goals.contains .reliableExport
  | .goal_soundDeposits         => cfg.goals.contains .soundDeposits
  | .goal_selfCorrection        => cfg.goals.contains .selfCorrection
  | .goal_corrigible_universal  => cfg.goals.contains .corrigibleLedger
  | .goal_corrigible_full       => cfg.goals.contains .corrigibleLedger
  -- Tier 4: structural clusters always enabled; bank bundles require all goals
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
  -- Tier 2: only forcing tags reach this arm; dispatch through constraintMeta
  | t => match constraintClusterOfTag? t with
         | some c => (constraintMeta c).enabledBy cfg
         | none   => false  -- unreachable

/-- The clusters enabled by `cfg`, in canonical order. -/
def explainConfig (cfg : EpArchConfig) : List ClusterTag :=
  allClusters.filter (clusterEnabled cfg)


/-! ## §4  Human-Readable Output -/

/-- One-line description of each cluster (theorem name in parentheses). -/
def clusterDescription : ClusterTag → String
  -- Tier 3: health-goal transport clusters
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
  -- Tier 2: only forcing tags reach this arm; dispatch through constraintMeta
  | t => match constraintClusterOfTag? t with
         | some c => (constraintMeta c).description
         | none   => ""  -- unreachable

/-- Human-readable list of all cluster descriptions enabled by `cfg`. -/
def showConfig (cfg : EpArchConfig) : List String :=
  (explainConfig cfg).map clusterDescription


end EpArch.Meta.Config
