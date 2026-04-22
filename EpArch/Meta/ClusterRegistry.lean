/-
EpArch.Meta.ClusterRegistry — Cluster Tag Registry and Routing

Defines the EpArchConfig language, the 32 ClusterTag values and their
per-family enumerations, the authoritative allXxxClusters lists, and the
routing/display functions.

No EpArch-specific imports — this layer is pure metadata: every type here
is self-contained and depends only on Lean 4 core.

Imported by EpArch.Meta.Config, which adds the proof-carrying layer on top.
-/

namespace EpArch.Meta.Config


/-! ## §1  Configuration Language -/

/-- The eight architectural constraints.  Each tag maps to one forcing theorem
    in `EpArch.Minimality`. -/
inductive ConstraintTag where
  | distributed_agents
  | bounded_audit
  | export_across_boundaries
  | adversarial_pressure
  | coordination_need
  | truth_pressure
  | multi_agent_access
  | bounded_storage
  deriving DecidableEq, BEq, Repr

/-- The six config-selectable health goals. The first five are CoreModel
    transport goals (gated on `GoalWitness`/`EnabledGoalCluster`). The sixth,
    `autonomyUnderPRP`, is an AutonomyModel necessity goal carried by
    `AutonomyWitness`/`EnabledAutonomyCluster`. -/
inductive GoalTag where
  | safeWithdrawal
  | reliableExport
  | corrigibleLedger
  | soundDeposits
  | selfCorrection
  | autonomyUnderPRP
  deriving DecidableEq, BEq, Repr

/-- The eight named world bundles. -/
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

/-- The 32 theorem clusters certified in EpArch Tiers 2–4 plus world-bundle obligations,
    constraint-modularity meta-theorems, lattice-stability results, and the
    AutonomyModel necessity cluster. -/
inductive ClusterTag where
  -- Tier 2: constraint-forcing theorems (8 clusters)
  | forcing_distributed_agents
  | forcing_bounded_audit
  | forcing_export
  | forcing_adversarial
  | forcing_coordination
  | forcing_truth
  | forcing_multi_agent
  | forcing_bounded_storage
  -- Tier 3: health-goal transport theorems (6 clusters)
  | goal_safeWithdrawal
  | goal_reliableExport
  | goal_soundDeposits
  | goal_selfCorrection
  | goal_corrigible_universal   -- ∀-part only, plain Compatible
  | goal_corrigible_full        -- full ∃+∀, requires SurjectiveCompatible
  -- Tier 4: main library clusters (5 clusters)
  | tier4_commitments           -- Cluster A: standalone commitments theorem family
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
  | world_rolex_ddos            -- rolex_ddos_share_path_failure_structure: both attacks force ¬PathExists
  | world_ddos                  -- W_ddos: DDoS causes verification collapse
  -- Meta-modularity clusters (from EpArch.Meta.Modular — constraint-subset independence)
  | meta_modular              -- modular: ∀ S W, PartialWellFormed W S → projection_valid S W
  -- Lattice-stability clusters (from EpArch.Modularity — floor not a cage)
  | lattice_graceful          -- graceful_degradation: NoSelfCorrection → RevisionGate
  | lattice_sub_safety        -- sub_revision_safety: Compatible sub-bundle extension is safe
  | lattice_pack              -- modularity_pack: full bidirectional lattice-stability
  -- Autonomy necessity cluster (AutonomyModel-specific health goal).
  -- Placed last in the constructor list for backwards compatibility;
  -- `allClusters` groups it with goal families (after CoreModel goals, before Tier 4).
  | goal_autonomyUnderPRP     -- autonomy_forces_bridge_or_escalation: forced bridge-or-escalation under PRP
  deriving DecidableEq, BEq, Repr


/-! ## §2b  Per-Family Cluster Enumerations

Six `EnabledXxxCluster` inductives — one per family — enable per-family proof
carriers in EpArch.Meta.Config.  Tier 2 uses a direct `ConstraintProof` record;
all other families use indexed inductive witness carriers. -/

/-- The eight Tier 2 constraint-forcing clusters. -/
inductive EnabledConstraintCluster where
  | forcing_distributed_agents | forcing_bounded_audit | forcing_export
  | forcing_adversarial | forcing_coordination | forcing_truth
  | forcing_multi_agent | forcing_bounded_storage
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

/-- The meta-modularity cluster (from `EpArch.Meta.Modular`). -/
inductive EnabledMetaModularCluster where
  | meta_modular
  deriving DecidableEq, BEq, Repr

/-- The three lattice-stability clusters (from `EpArch.Modularity`). -/
inductive EnabledLatticeCluster where
  | lattice_graceful | lattice_sub_safety | lattice_pack
  deriving DecidableEq, BEq, Repr

/-- Autonomy-goal clusters: health goals over `AutonomyModel`, not `CoreModel`.
    Carries necessity theorems directly (not transport-shaped).
    The correct home for any future AutonomyModel-specific health goals. -/
inductive EnabledAutonomyCluster where
  | goal_autonomyUnderPRP
  deriving DecidableEq, BEq, Repr


/-! ## §2c  Constraint Cluster Metadata

`ConstraintClusterMeta` is the metadata-only record for a Tier 2 cluster.
It records the three fields that determine routing — no proofs.
`constraintMeta` is the single source of truth for this data; `clusterEnabled`
and `EnabledConstraintCluster.toClusterTag` both derive their Tier 2 answers
from it.  EpArch.Meta.Config extends this record with a `witness : ConstraintProof`
field via `ConstraintClusterSpec extends ConstraintClusterMeta`.

Placed here (after §2 and §2b) so both `ClusterTag` and `EnabledConstraintCluster`
are in scope. -/

/-- Metadata-only record for a Tier 2 constraint-forcing cluster.
    Contains the three fields needed for routing but **no proof**.
    Extended in EpArch.Meta.Config by `ConstraintClusterSpec` which adds `witness`. -/
structure ConstraintClusterMeta where
  globalTag   : ClusterTag
  enabledBy   : EpArchConfig → Bool
  description : String

/-- Authoritative metadata for each Tier 2 constraint-forcing cluster.
    `clusterEnabled` and `EnabledConstraintCluster.toClusterTag` both derive
    their Tier 2 answers from this function. -/
def constraintMeta : EnabledConstraintCluster → ConstraintClusterMeta
  | .forcing_distributed_agents => {
      globalTag   := .forcing_distributed_agents
      enabledBy   := fun cfg => cfg.constraints.contains .distributed_agents
      description := "[Tier 2] distributed_agents -> HasBubbles  (disagreement_forces_bubbles)" }
  | .forcing_bounded_audit => {
      globalTag   := .forcing_bounded_audit
      enabledBy   := fun cfg => cfg.constraints.contains .bounded_audit
      description := "[Tier 2] bounded_audit -> HasTrustBridges  (bounded_verification_forces_trust_bridges)" }
  | .forcing_export => {
      globalTag   := .forcing_export
      enabledBy   := fun cfg => cfg.constraints.contains .export_across_boundaries
      description := "[Tier 2] export_across_boundaries -> HasHeaders  (discriminating_import_forces_headers)" }
  | .forcing_adversarial => {
      globalTag   := .forcing_adversarial
      enabledBy   := fun cfg => cfg.constraints.contains .adversarial_pressure
      description := "[Tier 2] adversarial_pressure -> HasRevocation  (monotonic_lifecycle_forces_revocation)" }
  | .forcing_coordination => {
      globalTag   := .forcing_coordination
      enabledBy   := fun cfg => cfg.constraints.contains .coordination_need
      description := "[Tier 2] coordination_need -> HasBank  (private_coordination_forces_bank)" }
  | .forcing_truth => {
      globalTag   := .forcing_truth
      enabledBy   := fun cfg => cfg.constraints.contains .truth_pressure
      description := "[Tier 2] truth_pressure -> HasRedeemability  (closed_endorsement_forces_redeemability)" }
  | .forcing_multi_agent => {
      globalTag   := .forcing_multi_agent
      enabledBy   := fun cfg => cfg.constraints.contains .multi_agent_access
      description := "[Tier 2] multi_agent_access -> HasGranularACL  (uniform_access_forces_acl)" }
  | .forcing_bounded_storage => {
      globalTag   := .forcing_bounded_storage
      enabledBy   := fun cfg => cfg.constraints.contains .bounded_storage
      description := "[Tier 2] bounded_storage -> HasStorageManagement  (bounded_storage_forces_storage_management)" }


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

/-- Embed a meta-modularity cluster into the global tag space. -/
def EnabledMetaModularCluster.toClusterTag : EnabledMetaModularCluster → ClusterTag
  | .meta_modular            => .meta_modular

/-- Embed a lattice-stability cluster into the global tag space. -/
def EnabledLatticeCluster.toClusterTag : EnabledLatticeCluster → ClusterTag
  | .lattice_graceful   => .lattice_graceful
  | .lattice_sub_safety => .lattice_sub_safety
  | .lattice_pack       => .lattice_pack

/-- Embed an autonomy-goal cluster into the global tag space. -/
def EnabledAutonomyCluster.toClusterTag : EnabledAutonomyCluster → ClusterTag
  | .goal_autonomyUnderPRP => .goal_autonomyUnderPRP


/-! ## §3  Routing

`clusterEnabled` is the single source of truth for which clusters a given
`EpArchConfig` activates.  `explainConfig`/`showConfig` are derived from it.

The per-family canonical lists live here (not in EpArch.Meta.Config) because they
are metadata objects — pure enumeration facts, no proofs.  The global
`allClusters` list is derived from them so ordering stays consistent
automatically.  `constraintClusterOfTag?` enables Tier 2 routing
to dispatch through `constraintMeta` without re-enumerating the eight
forcing constructors. -/

/-- All eight Tier 2 constraint-forcing clusters, in canonical order. -/
def allConstraintClusters : List EnabledConstraintCluster :=
  [.forcing_distributed_agents, .forcing_bounded_audit, .forcing_export,
   .forcing_adversarial, .forcing_coordination, .forcing_truth,
   .forcing_multi_agent, .forcing_bounded_storage]

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

/-- The meta-modularity cluster, in canonical order. -/
def allMetaModularClusters : List EnabledMetaModularCluster :=
  [.meta_modular]

/-- The three lattice-stability clusters, in canonical order. -/
def allLatticeClusters : List EnabledLatticeCluster :=
  [.lattice_graceful, .lattice_sub_safety, .lattice_pack]

/-- The autonomy-goal cluster, in canonical order. -/
def allAutonomyClusters : List EnabledAutonomyCluster :=
  [.goal_autonomyUnderPRP]

/-- All 32 cluster tags, in canonical order.  Derived from the per-family lists
    so ordering stays consistent with those lists automatically.
    Family order: constraints → CoreModel goals → AutonomyModel goals →
    Tier 4 library → world bundles → meta-modularity → lattice.
    Used by `explainConfig`. -/
def allClusters : List ClusterTag :=
  (allConstraintClusters.map  EnabledConstraintCluster.toClusterTag) ++
  (allGoalClusters.map        EnabledGoalCluster.toClusterTag) ++
  (allAutonomyClusters.map    EnabledAutonomyCluster.toClusterTag) ++
  (allTier4Clusters.map       EnabledTier4Cluster.toClusterTag) ++
  (allWorldClusters.map       EnabledWorldCluster.toClusterTag) ++
  (allMetaModularClusters.map EnabledMetaModularCluster.toClusterTag) ++
  (allLatticeClusters.map     EnabledLatticeCluster.toClusterTag)

/-- Reverse lookup: given a `ClusterTag`, return the matching
    `EnabledConstraintCluster` if it is a Tier 2 forcing tag, or `none`
    otherwise.  Used by `clusterEnabled` to dispatch Tier 2 cases through
    `constraintMeta` without re-enumerating the eight forcing constructors. -/
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
  -- Meta-modularity and lattice-stability clusters: always enabled
  | .meta_modular            => true
  | .lattice_graceful        => true
  | .lattice_sub_safety      => true
  | .lattice_pack            => true
  -- Autonomy necessity cluster: gated on goal
  | .goal_autonomyUnderPRP   => cfg.goals.contains .autonomyUnderPRP
  -- Tier 2: only forcing tags reach this arm; dispatch through constraintMeta
  | t => match constraintClusterOfTag? t with
         | some c => (constraintMeta c).enabledBy cfg
         | none   => panic! "unreachable: all non-Tier-2 ClusterTags are handled above"

/-- The clusters enabled by `cfg`, in canonical order. -/
def explainConfig (cfg : EpArchConfig) : List ClusterTag :=
  allClusters.filter (clusterEnabled cfg)


/-! ## §4  Human-Readable Output -/

/-- Human-readable list of enabled cluster tags for `cfg`.
    Each tag is shown by its constructor name (from `Repr ClusterTag`).
    Full descriptions of each cluster live in `DOCS/MODULARITY.md`. -/
def showConfig (cfg : EpArchConfig) : List String :=
  (explainConfig cfg).map reprStr


end EpArch.Meta.Config
