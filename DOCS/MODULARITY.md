# Modularity Registry

This document is the single reference for how EpArch's theorem corpus is modular:
what surfaces exist, which are user-facing, how to add or remove a cluster, and
the invariants that must never be broken.

**Key question answered here:** If a product/sub-system rejects some constraint or
goal, which theorems still apply, which don't, and how does the formalization
certify that?

---

## 1. What Modularity Means in This Repo

EpArch's theorem corpus is sliced into **29 certified clusters** across six families.
Constraint, goal, and world clusters are config-driven — activated by the `EpArchConfig`
a user provides. Meta-modularity, lattice-stability, and all Tier 4 clusters (commitments,
structural, LTS-universal, and bank-goal transport) are always-on: they hold
unconditionally and require no configuration.

| Family | Count | What it covers |
|---|---|---|
| **Forcing clusters** (Tier 2) | 6 | Each constraint forces a structural feature. Two paths: (1) `PartialWellFormed`/`handles_X W` biconditional path via `StructurallyForced`; (2) structural `Represents*`/`*_forces_*` path — no `handles_X W`, no biconditionals, strictly stronger. Per-dimension `*_forces_*` theorems are orthogonal: each fires independently (`disagreement_forces_bubbles`, `private_coordination_forces_bank`, `monotonic_lifecycle_forces_revocation`, `discriminating_import_forces_headers`, `bounded_verification_forces_trust_bridges`, `closed_endorsement_forces_redeemability`). |
| **Goal transport** (Tier 3) | 6 | Each health goal is preserved under compatible model extension |
| **Tier 4 library clusters** | 5 | Commitments pack, structural theorems, LTS-universal gates, bank-goal transport |
| **World obligations** (Tier 1) | 8 | Each `W_*` bundle enables a slice of adversarial/world theorems |
| **Meta-modularity** | 1 | `modular` — constraint-subset independence (`PartialWellFormed W S → projection_valid S W`) |
| **Lattice-stability** | 3 | `graceful_degradation`, `sub_revision_safety`, `modularity_pack` |

The 29 `ClusterTag` values in `ClusterRegistry.lean` are the canonical names for all of these.

**Why this matters architecturally:** Modularity is not only a proof-engineering convenience — it is a kernel design constraint. EpArch must remain applicable across agents that do not share the same internal epistemology or constraint bundle, including minimal agents (e.g., an odometer-like system tracking position) that face only a sub-bundle of the full set. The cluster architecture ensures the kernel scales down gracefully: a system that does not face `FallibilityConstraint` simply does not receive the clusters that depend on it, and the remaining claims stay sound. This is why the kernel boundary stops at coordination-relevant architectural requirements rather than agent-internal dynamics models.

**Structural forcing path (stronger than biconditionals):** Beyond the `PartialWellFormed`/`handles_X W` biconditional path, each Tier 2 cluster has a direct `Represents*`/`*_forces_*` proof that requires no `WellFormed`, no `handles_X W`, and no biconditionals. Any system that concretely instantiates one EpArch operational pressure (by supplying a `Represents*` witness) is forced to have the matching primitive. These six theorems are strictly orthogonal — each fires independently. Bundled together, `SystemOperationalBundle W` (scope + headers + bank) and `WorldBridgeBundle W` (revocation + trust + redeemability) feed the headline `bundled_structure_forces_bank_primitives` theorem in Feasibility.lean: four arguments, any world, no `WorldCtx`.

---

## 2. User-Facing vs. Internal

Three layers sit between a caller and the proof content. Understanding which layer
does what prevents confusion about where to look and where to edit.

### User-facing surface
- **`EpArchConfig`** — user-supplied record of `constraints`, `goals`, `worlds` lists.
- **`ClusterTag`** — the 30 cluster identifiers; what a user cites when requesting certification.
- **`certify`** — `certify : EpArchConfig → CertifiedProjection cfg`; returns a record with
  one indexed witness per family. Access proof content via:
  `(certify myConfig).goalWitnesses`, `.tier4Witnesses`, `.worldWitnesses`,
  `.metaModularWitnesses`, `.latticeWitnesses`.
- **`showConfig`** / `#eval` output — human-readable display; what appears when a user runs
  `#eval EpArch.Meta.Config.showConfig myConfig`.

### Routing/metadata layer — `Meta/ClusterRegistry.lean`
- Owns `ClusterTag`, all `EnabledXxxCluster` enumerations, `clusterDescription`,
  `clusterEnabled`, and every `toClusterTag` mapping.
- **No EpArch-specific imports.** It is pure metadata — all types are self-contained.
- Changing a cluster's description, family, or enabled status: edit here only.

### Proof-carrying layer — `Meta/Config.lean`
- Owns the Tier 2 proof carriers (`ConstraintProof`, `ConstraintClusterSpec`) and the
  indexed witness inductives (`GoalWitness`, `Tier4Witness`, `WorldWitness`,
  `MetaModularWitness`, `LatticeWitness`).
- Each carrier/constructor holds the actual Lean type of the theorem being certified.
- Owns the `constraintSpec`, `goalWitness`, `worldWitness`, `tier4Witness`, etc. match arms
  that wire tags to proofs.
- Changing what a cluster certifies (its type or proof term): edit here.

### Theorem modules — source of actual proof content
- `Minimality.lean` — Tier 2 six individual lifting theorems.
- `Convergence.lean` — `StructurallyForced`, `convergence_structural`, impossibility models, §1b–§6b alternative dismissals; six per-dimension `*_forces_*` theorems; `SystemOperationalBundle W` and `WorldBridgeBundle W` record structures.
- `Feasibility.lean` — `grounded_world_and_structure_force_bank_primitives` (explicit `Represents*` witnesses, no `WorldCtx`); `bundled_structure_forces_bank_primitives` (headline 4-argument form).
- `BehavioralEquivalence.lean` — bank-primitive behavioral-equivalence results.
- `Health.lean`, `Meta/TheoremTransport.lean` — Tier 3 goal predicates and transport.
- `Commitments.lean`, `Theorems.lean`, `Diagnosability.lean`, `Agent/*.lean`,
  `Invariants.lean`, `ScopeIrrelevance.lean`, `Predictions.lean`, `WorkedTraces.lean` — Tier 4.
- `WorldCtx.lean`, `AdversarialObligations.lean`, `WorldWitness.lean` — Tier 1 / world.
- `Meta/Modular.lean` — meta-modularity; `Modularity.lean` — lattice-stability.
- **Editing here does not change the cluster surface** unless Config.lean is updated too.

---

## 3. How to Add a New Cluster

Work through these layers **in order**. Each layer depends on the one above it.

### Step 1 — Prove or name the theorem in the source module

Add or identify the theorem in the appropriate `.lean` file.
It must be a fully closed term — no `sorry`, no empty structure fields.

```lean
-- Example: new Tier 2 forcing theorem in Minimality.lean
theorem my_constraint_requires_feature (W : WorkingSystem)
    (h : StructurallyForced W) (hC : handles_my_constraint W) : HasMyFeature W := ...
```

### Step 2 — Update `ClusterRegistry.lean`

Add a new `ClusterTag` constructor, the corresponding `EnabledXxxCluster` value,
`clusterDescription`, `clusterEnabled`, and `toClusterTag` routing.

```lean
-- In ClusterTag inductive:
| forcing_my_constraint   -- Tier 2: my_constraint forces HasMyFeature

-- In constraintMeta (or equivalent routing function):
| .my_constraint => { globalTag := .forcing_my_constraint,
                      description := "my_constraint forces HasMyFeature",
                      ... }
```

### Step 3 — Update `Config.lean`

Add a constructor to the appropriate witness inductive and a match arm
in the certifying function.

```lean
-- In constraintSpec match (constraintProof is derived from this):
| .forcing_my_constraint => {
    statement := ∀ W, StructurallyForced W → handles_my_constraint W → HasMyFeature W
    proof     := fun W sf => sf.my_forcing }
```

### Step 4 — Update `MODULARITY.md`

Only needed if the new cluster changes the public modularity surface or the cluster
count. Add a row to the relevant family table.

---

## 4. Family-Specific Recipes

Not all families are added the same way. The asymmetry is architectural, not style.

### Tier 2 — Forcing clusters

Use **direct `ConstraintProof`**: the theorem takes `StructurallyForced W` plus the
operational predicate for that constraint and returns the forced feature.
No witness inductive is needed — the proof term is the carrier.

```lean
-- Minimal pattern:
theorem my_constraint_requires_feature (W : WorkingSystem)
    (h : StructurallyForced W) (hC : handles_my_constraint W) : HasMyFeature W :=
  ... -- prove from h and hC
```

### Goal / World / Tier 4 / Meta / Lattice — indexed witness carriers

These families use **indexed inductive witness types** in `Config.lean`.
The reason is universe management: the proof terms for these families are
polymorphic or involve `Type 1` universes (model parameters, `CoreModel`,
`WorkingSystem`), and bundling them into a plain function type causes universe
issues. The inductive carrier keeps each proof at its natural universe level.

```lean
-- Tier 4 pattern:
| my_cluster :
    (∀ {PL SL EL PrL : Type}, MyTheoremStatement PL SL EL PrL) →
    Tier4Witness .tier4_my_cluster

-- Match arm:
| .tier4_my_cluster => .my_cluster my_theorem
```

If you see existing clusters using `fun` terms in the match arm body, that is
because the carrier constructor accepts a `∀`-quantified type — the `fun` just
supplies the universally-quantified argument.

---

## 5. How to Remove or Refactor a Cluster

### Rule: no empty compatibility shells

If a theorem family becomes standalone (proved unconditionally, needs no transport),
move its cluster to reflect that reality. Do **not** leave a transport shell
containing vacuous or identity proofs just because it matched an old structure.

The `CommitmentsCtx` refactor (`5a1cdea`) is the canonical example:
`CommitmentsCtx` was an empty structure that did nothing; `commitments_pack` now
directly bundles the four unconditional commitment theorems with no wrapper.

### Refactor discipline — touch layers in this order

1. **Proof module** — remove or rewrite the theorem.
2. **`Config.lean`** — remove the witness constructor and match arm; rewire any
   callers to the new proof term.
3. **`ClusterRegistry.lean`** — update description, family, or remove the tag entirely.
4. **`MODULARITY.md`** — update tables and prose to match the new reality.
5. **Grep** — search for the old name across all files and kill every stale mention.
   (`git grep <old_name>` or the `scripts/audit.ps1` script.)

### Rule: update routing, witnesses, and descriptions together

A mismatch between the registry description and what the witness actually carries
is a documentation bug. The three layers must always agree:

- `clusterDescription` in `ClusterRegistry.lean` says what is certified.
- The witness constructor type in `Config.lean` encodes exactly that.
- The proof term in the match arm delivers exactly the constructor type.

---

## 6. Minimal Copy-Paste Templates

### New Tier 2 forcing cluster

```lean
-- Minimality.lean
theorem my_constraint_requires_feature (W : WorkingSystem)
    (h : WellFormed W) (hC : handles_my_constraint W) : HasMyFeature W := ...

-- ClusterRegistry.lean — add to ClusterTag:
| forcing_my_constraint

-- ClusterRegistry.lean — add row in constraintMeta:
| .my_constraint => { globalTag := .forcing_my_constraint, ... }

-- Config.lean — add arm to constraintSpec match:
| .forcing_my_constraint => {
    statement := ∀ W, WellFormed W → handles_my_constraint W → HasMyFeature W
    proof     := my_constraint_requires_feature }
```

### New goal / world / Tier 4 cluster

```lean
-- Source module
theorem my_theorem {PL SL EL PrL : Type} ... : MyConclusion PL SL EL PrL := ...

-- ClusterRegistry.lean — add to ClusterTag:
| tier4_my_cluster  -- or goal_*, world_*, etc.

-- Config.lean — add to Tier4Witness (or GoalWitness, etc.):
| my_cluster :
    (∀ {PL SL EL PrL : Type}, MyConclusion PL SL EL PrL) →
    Tier4Witness .tier4_my_cluster

-- Config.lean — add match arm:
| .tier4_my_cluster => .my_cluster my_theorem
```

### New always-on meta cluster (unconditional, no universe polymorphism)

```lean
-- Source module
theorem my_meta_fact : MyMetaConclusion := ...

-- Config.lean — witness constructor (if MetaModularWitness family):
| my_meta :
    MyMetaConclusion →
    MetaModularWitness .meta_my_fact

-- Config.lean — match arm:
| .meta_my_fact => .my_meta my_meta_fact
```

---

## 7. Invariants — Do Not Break These

These rules prevent the registry, config, and docs from drifting apart.

| # | Invariant |
|---|---|
| **I1** | `ClusterRegistry.lean` owns all routing and display. No other file defines `clusterDescription` or `clusterEnabled`. |
| **I2** | `Config.lean` owns all proof carriers. Witness inductive constructors are the only place where theorem types are formally encoded against a `ClusterTag`. |
| **I3** | Named `cluster_*` pack theorems (e.g. `commitments_pack`, `structural_theorems_unconditional`, `lts_theorems_step_universal`) remain the authoritative typed witnesses. Config.lean match arms must reference them by name, not re-prove inline. |
| **I4** | Every `ClusterTag` constructor that exists must have a matching witness constructor in `Config.lean` and a description in `ClusterRegistry.lean`. Orphaned tags are a build-time bug. |
| **I5** | Documentation describes the cluster semantics as they exist now. Stale historical scaffolding (old transport wrappers, superseded pack shapes) must be removed — not left as comments or empty shells. |
| **I6** | The cluster count (currently 30) is a documented fact. If you add or remove a cluster, update the count in this doc and in `README.md`. |

---

## 8. Reference: Tier Detail Tables

The following tables describe each tier in depth. For the summary view, see §1.
For contributor instructions, see §§3–7 above.

---

## Tier 1 — World Bundles (already fully modular)

**Mechanism:** Every world-level claim is conditioned on an explicit `W_*` structure.
Disabling a world assumption = not providing a proof of that structure.
The type system then mechanically excludes all and only the theorems that depended on it.

**Files:** `WorldCtx.lean`, `AdversarialObligations.lean`, `WorldWitness.lean`

| World Bundle | Fields | What it enables | File | Disable by |
|---|---|---|---|---|
| `W_lies_possible` | `some_false`, `unrestricted_utterance` | `lie_possible_of_W`, `all_agents_can_lie_of_W` | WorldCtx.lean | Not providing proof |
| `W_bounded_verification` | `verification_has_cost` | Bounded-audit necessity results | WorldCtx.lean | Not providing proof |
| `W_partial_observability` | `obs_underdetermines` | Underdetermination results | WorldCtx.lean | Not providing proof |
| `W_asymmetric_costs` | `export_cost`, `defense_cost`, `asymmetry` | Cost-asymmetry obligation theorems | WorldCtx.lean | Not providing proof |
| `W_spoofedV` | `broken_chain_no_path` | `spoofed_V_blocks_path_of_W` | AdversarialObligations.lean | Not providing proof |
| `W_lies_scale` | (lies-scale fields) | `lies_scale_of_W` | AdversarialObligations.lean | Not providing proof |
| `W_rolex_ddos` | (rolex/ddos fields) | `rolex_ddos_structural_equivalence_of_W` | AdversarialObligations.lean | Not providing proof |
| `W_ddos` | (ddos fields) | `ddos_causes_verification_collapse_of_W`, `ddos_to_centralization_of_W` | AdversarialObligations.lean | Not providing proof |

**Transport:** `transport_lies_possible`, `transport_lie_possible` in `WorldCtx.lean` — world bundles are already transported through compatible extensions.

**Coverage:** All `AdversarialObligations` theorems, all `WorldWitness` non-vacuity witnesses.

**Gap:** None. This tier is complete.

---

## Tier 2 — Constraints / Forcing Results (already modular by conjunction separation)

**Mechanism:** The six lifting theorems in `Minimality.lean` (`distributed_agents_require_bubbles`, etc.) are each stated independently. Each takes `WellFormed W` plus the operational predicate for *that* constraint; they are logical consequences of the `WellFormed` biconditionals.

The **preferred forcing path** is `StructurallyForced W → SatisfiesAllProperties W → containsBankPrimitives W` (`convergence_structural`), where `StructurallyForced` packages the six forward implications independently justified by the structural impossibility models (`flat_scope_impossible`, `monotonic_no_exit`, etc.). `WellFormed W → StructurallyForced W` via `wellformed_implies_structurally_forced`, so the two paths are compatible. New forcing contributions should be added as `StructurallyForced` fields, not as additional `WellFormed`-taking theorems.

**Files:** `Minimality.lean` (six individual lifting theorems); `Convergence.lean` (`StructurallyForced`, `convergence_structural`, impossibility models, §1b–§6b alternative dismissals)

| Constraint | Operational predicate | Forced feature | Theorem |
|---|---|---|---|
| `distributed_agents` | `handles_distributed_agents` | `HasBubbles` | `distributed_agents_require_bubbles` |
| `bounded_audit` | `handles_bounded_audit` | `HasTrustBridges` | `bounded_audit_requires_trust_bridges` |
| `export_across_boundaries` | `handles_export` | `HasHeaders` | `export_requires_headers` |
| `adversarial_pressure` | `handles_adversarial` | `HasRevocation` | `adversarial_requires_revocation` |
| `coordination_need` | `handles_coordination` | `HasBank` | `coordination_requires_bank` |
| `truth_pressure` | `handles_truth_pressure` | `HasRedeemability` | `truth_pressure_requires_redeemability` |

**Global theorem:** `convergence_structural` = conjunction of all six (via `StructurallyForced`). `goals_force_bank_primitives` re-exports this under the `WellFormed` signature for backward compatibility. If you only accept k constraints, use the k individual forcing theorems instead — they all still hold.

**Relation to world bundles:** `adversarial_pressure` is downstream of `W_lies_possible` (lies possible + imperfect gate → adversarial deposits pass). They operate at different layers and are not interchangeable.

**Gap:** ✅ Closed by `Meta/Modular.lean`. The two previously missing pieces are now proved:

1. **`PartialWellFormed W S`** — a `WellFormed`-fragment type parameterized by a `ConstraintSubset` (6-Bool vector). For each constraint X with `S.X = false`, nothing is required. For `S.X = true`, the biconditional `handles_X W ↔ HasFeature_X W` is required. `WellFormed W ↔ PartialWellFormed W allConstraints`.

2. **`modular`** — the universally-quantified meta-theorem:
   ```
   ∀ (S : ConstraintSubset) (W : WorkingSystem),
     PartialWellFormed W S →
       (S.distributed = true → handles_distributed_agents W → HasBubbles W) ∧ ...
   ```
   This is a machine-checked proof, not a structural observation. Dropping constraint X = setting `S.X := false`; the X-conjunct becomes vacuously true.

3. **`wellformed_is_modular`** — every fully well-formed system is modular on every constraint subset.

---

## Tier 3 — Health Goals (already CoreModel-parameterized)

**Mechanism:** All health goal predicates and their necessity theorems are stated over `CoreModel`.
This means they are already halfway to being transport-safe — the predicate moves with the model.

**File:** `Health.lean`

| Health goal | `CoreOps` fields it references | File | Disable by |
|---|---|---|---|
| `SafeWithdrawalGoal` | `truth`, `obs`, `submit` | Health.lean | Not requiring it in your `SubBundle.SubGoal` |
| `ReliableExportGoal` | `submit`, `obs` | Health.lean | Not requiring it |
| `CorrigibleLedgerGoal` | `revise`, `hasRevision` | Health.lean | Not requiring it (→ `odometer_not_corrigible` in Modularity.lean) |
| `SoundDepositsGoal` | `verifyWithin`, `effectiveTime` | Health.lean | Not requiring it |
| `SelfCorrectionGoal` | `selfCorrects`, `hasRevision` | Health.lean | Not requiring it |

**`PaperFacing`** (the competition gate) references only `selfCorrects`, `hasRevision` — the minimal slice needed for the revision gate.

**Transport:** `transport_core` (RevisionSafety.lean) transports `PaperFacing` exactly.
`sub_revision_safety` (Modularity.lean) transports `PaperFacing` at sub-bundle level.
`graceful_degradation` (Modularity.lean) shows dropping `SelfCorrectionGoal` → `PaperFacing` holds vacuously.

**Gap:** ~~None~~ Closed. `transport_safe_withdrawal`, `transport_reliable_export`, `transport_sound_deposits`, `transport_self_correction` (and the full `transport_corrigible_ledger` via `SurjectiveCompatible`) are proved in `Meta/TheoremTransport.lean`. The `health_goal_transport_pack` headline theorem packages all five.

---

## Tier 4 — Main Theorem Library (transport schema complete)

**Files:** `Theorems.lean` (109 theorems), `Diagnosability.lean`, `Agent/Corroboration.lean`, `Agent/Resilience.lean`, `Invariants.lean`, `ScopeIrrelevance.lean`, `Predictions.lean`, `WorkedTraces.lean`

**Status:** ✅ Closed by `Meta/Tier4Transport.lean`.

**Three transport clusters:**

### Cluster A — Standalone commitments theorem family

All 8 architectural commitments are proved as standalone theorems in `Commitments.lean`.
`commitments_pack` bundles the unconditional ones (C3/C4b/C7b/C8); C1, C2, C5, C6b
are proved as separately named theorems.  C4b (`redeemability_requires_more_than_consensus`)
is the commitment-specific result that distinguishes Cluster A from Cluster B
(`structural_theorems_unconditional`).  Cluster A is an unconditional theorem
family — no transport machinery needed.

Examples: `commitments_pack`, `innovation_allows_traction_without_authorization`,
`caveated_authorization_does_not_force_certainty`, `innovation_excludes_coordination`,
`redeemability_requires_more_than_consensus`, all Gettier/Lottery/Fake Barn diagnoses,
`header_stripping_produces_pathology`.

### Cluster B — Standalone structural theorems

These theorems carry no world, commitment, or ops hypothesis — universally valid.

| Theorem | What it proves |
|---|---|
| `SEVFactorization` | Every deposit has three independent header fields |
| `TemporalValidity` | Refreshed ≠ unrefreshed (τ-policy) |
| `monolithic_not_injective` | Diagnostic compression is non-injective |
| `header_stripping_harder` | Stripped deposits have lower diagnosability |

**Mechanism:** None needed. `structural_theorems_unconditional` packages all four as a
machine-checked conjunction to formally certify the "no transport needed" status.

### Cluster C — SystemState/Step-concrete theorems

Shape: over `SystemState PropLike Standard ErrorModel Provenance` and `Step`.

Two sub-results fill this cluster:

**§3b — LTS-Universal Operational Theorems**  
The withdrawal/repair/submit theorems from `Theorems.lean` are structurally identical to Cluster B:
they hold for **every** `SystemState`/`Step` instance by virtue of `Step` constructor preconditions.
No model parameter varies, so no transport mechanism is needed.

- `lts_theorems_step_universal`: packages four key LTS facts as unconditionally valid —
  - Withdrawal gates: `Step.Withdraw` requires ACL + current τ + Deposited status
  - Repair revalidation: `Step.Repair` produces Candidate ledger status
  - Repair quarantine: `Step.Repair` requires input to be Quarantined
  - Submit Candidate: `Step.Submit` produces at least one Candidate deposit

**§3c — All Five Health Goals Transport**  
All five ∀-health goals are preserved by any compatible extension of `ConcreteBankModel`.
This is the real Cluster C result — not just the competition gate but the full health-goal suite.

- `ConcreteBankModel`: concrete EpArch bank types form a valid `CoreModel`
- `concrete_bank_all_goals_transport`: given that a `ConcreteBankModel` satisfies all five goals,
  any `Compatible` extension satisfies all five:
  - `SafeWithdrawalGoal (forget E)`
  - `ReliableExportGoal (forget E)`
  - `SoundDepositsGoal (forget E)`
  - `SelfCorrectionGoal / PaperFacing (forget E)`
  - Universal `CorrigibleLedgerGoal (forget E)` (the ∃ component requires `SurjectiveCompatible`)
- `tier4_full_pack`: headline theorem — Clusters B + C only (structural + LTS-universal + all
  five health goals); Cluster A (`commitments_pack`) is certified separately.

**Gap:** None. All four tier 4 clusters are machine-certified:
- Cluster A: all 8 commitments proved as standalone theorems; `commitments_pack` bundles the unconditional ones.
- Cluster B + §3b LTS-universal: structural and operational LTS theorems are universally valid.
- Cluster C §3c: all five ∀-health goals transport through compatible `ConcreteBankModel` extensions.

---

## Modularity Summary Table

| Layer | Mechanism | Current status | Certifying file |
|---|---|---|---|
| World bundles (`W_*`) | Explicit hypothesis — not providing proof disables | ✅ Complete | `WorldCtx.lean`, `AdversarialObligations.lean` |
| Constraints (6 forcing results) | Independent conjuncts + `PartialWellFormed`/`modular` meta-theorem | ✅ Complete | `Minimality.lean`, `Convergence.lean`, `Meta/Modular.lean` |
| `PaperFacing` / competition gate | `transport_core` + `sub_revision_safety` | ✅ Complete | `RevisionSafety.lean`, `Modularity.lean` |
| Health goals (5 predicates) | `CoreModel`-parameterized + individual transport theorems | ✅ Complete | `Health.lean`, `Meta/TheoremTransport.lean` |
| Main theorem library (109+) | Four-part schema: standalone commitments, structural unconditional, LTS-universal operational, all-five-health-goals bank bridge | ✅ Complete | `Meta/Tier4Transport.lean` |
| Certified cluster surface (30 clusters) | `EpArchConfig → ClusterTag → Bool` routing + indexed witness carriers; all 6 cluster families are proof-carrying; constraint/goal/world families are config-selectable; Tier 4/meta-modular/lattice families are always-on | ✅ Complete | `Meta/ClusterRegistry.lean`, `Meta/Config.lean` |

---

## 9. Product / User Handbook

**"I want to disable constraint X for my product."**
→ Go to Tier 2. Find X in the constraint table. The k forcing theorems not involving X all still apply. The global `convergence_structural` / `goals_force_bank_primitives` no longer applies.

**"I want to disable health goal G for my product."**
→ Go to Tier 3. Find G in the health goal table. Note which `CoreOps` fields it references.
→ Go to Tier 4, operation dependency map. Every theorem cluster that does *not* reference those fields survives. `PaperFacing` specifically is handled by Tier 3 (transport_core).

**"I want to disable world assumption W for my product."**
→ Go to Tier 1. Find W. Every theorem listed in that row becomes inapplicable. Everything else is unaffected — mechanically, by the type system.

**"I want to add my own constraint/goal on top."**
→ Tier 2: add a new forcing theorem of shape `WellFormed W → handles_yourConstraint W → HasYourFeature W`.
→ Tier 3: add a new `CoreModel`-parameterized predicate and its necessity theorem.
→ `RevisionSafety.lean` `premise_strengthening` guarantees adding constraints can't invalidate existing implications.
