# Modularity Registry

This document is the single reference for how EpArch's theorem corpus is modular.
It tracks what can be "disabled" (constraint, health goal, world bundle), by what mechanism, what theorems depend on each item, and what the formal status is.

**Key question answered here:** If a product/sub-system rejects some constraint or goal, which theorems still apply, which don't, and how does the formalization certify that?

---

## The Four Modularity Tiers

The formalization has four distinct modularity mechanisms, each at a different layer.
They are now all complete — see [Tier 4](#tier-4-main-theorem-library--transport-schema-complete) for the closure.

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

**Mechanism:** The six forcing theorems in `Minimality.lean` are each stated independently.
Each takes only `WellFormed W` plus the operational predicate for *that* constraint.
They are not bundled — disabling one constraint does not affect the others.

**File:** `Minimality.lean`

| Constraint | Operational predicate | Forced feature | Theorem | Impossibility theorem |
|---|---|---|---|---|
| `distributed_agents` | `handles_distributed_agents` | `HasBubbles` | `distributed_agents_require_bubbles` | `no_bubbles_implies_failure` |
| `bounded_audit` | `handles_bounded_audit` | `HasTrustBridges` | `bounded_audit_requires_trust_bridges` | `no_trust_bridges_implies_failure` |
| `export_across_boundaries` | `handles_export` | `HasHeaders` | `export_requires_headers` | `no_headers_implies_failure'` |
| `adversarial_pressure` | `handles_adversarial` | `HasRevocation` | `adversarial_requires_revocation` | `no_revocation_implies_failure` |
| `coordination_need` | `handles_coordination` | `HasBank` | `coordination_requires_bank` | `no_bank_implies_failure` |
| `truth_pressure` | `handles_truth_pressure` | `HasRedeemability` | `truth_pressure_requires_redeemability` | `no_redeemability_implies_failure` |

**Global theorem:** `convergence_under_constraints'` = conjunction of all six. If you only accept k constraints, use the k individual forcing theorems instead — they all still hold.

**Relation to world bundles:** `adversarial_pressure` is downstream of `W_lies_possible` (lies possible + imperfect gate → adversarial deposits pass). They operate at different layers and are not interchangeable.

**Gap:** None for the forcing layer itself. The theorems already compose modularly.

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

### Cluster A — CommitmentsCtx-parameterized theorems

Shape: `(C : CommitmentsCtx PropLike Standard ErrorModel Provenance) → ... → Claim`

Examples: `certainty_insufficient_for_authorization`, `authorization_insufficient_for_certainty`,
`innovation_excludes_coordination`, `redeemability_requires_more_than_consensus`,
all Gettier/Lottery/Fake Barn diagnoses, `header_stripping_produces_pathology`.

**Mechanism:** `premise_strengthening` from `RevisionSafety.lean` plus projection through
`ExtCommitmentsCtx.toCommitmentsCtx`. Adding more commitments never invalidates existing theorems.
`commitments_transport` and `commitments_transport_pack` package this formally.

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
- `tier4_full_pack`: headline theorem — Clusters A + B + LTS-universal + all five health goals

**Gap:** None. All four tier 4 clusters are machine-certified:
- Cluster A: CommitmentsCtx-parameterized theorems transport via premise strengthening.
- Cluster B + §3b LTS-universal: structural and operational LTS theorems are universally valid.
- Cluster C §3c: all five ∀-health goals transport through compatible `ConcreteBankModel` extensions.

---

## Modularity Summary Table

| Layer | Mechanism | Current status | Certifying file |
|---|---|---|---|
| World bundles (`W_*`) | Explicit hypothesis — not providing proof disables | ✅ Complete | `WorldCtx.lean`, `AdversarialObligations.lean` |
| Constraints (6 forcing results) | Independent conjuncts — cherry-pick freely | ✅ Complete | `Minimality.lean` |
| `PaperFacing` / competition gate | `transport_core` + `sub_revision_safety` | ✅ Complete | `RevisionSafety.lean`, `Modularity.lean` |
| Health goals (5 predicates) | `CoreModel`-parameterized + individual transport theorems | ✅ Complete | `Health.lean`, `Meta/TheoremTransport.lean` |
| Main theorem library (109+) | Four-part schema: CommitmentsCtx transport, structural unconditional, LTS-universal operational, all-five-health-goals bank bridge | ✅ Complete | `Meta/Tier4Transport.lean` |

---

## How to Use This Document

**"I want to disable constraint X for my product."**
→ Go to Tier 2. Find X in the constraint table. The k forcing theorems not involving X all still apply. The global `convergence_under_constraints'` no longer applies.

**"I want to disable health goal G for my product."**
→ Go to Tier 3. Find G in the health goal table. Note which `CoreOps` fields it references.
→ Go to Tier 4, operation dependency map. Every theorem cluster that does *not* reference those fields survives. `PaperFacing` specifically is handled by Tier 3 (transport_core).

**"I want to disable world assumption W for my product."**
→ Go to Tier 1. Find W. Every theorem listed in that row becomes inapplicable. Everything else is unaffected — mechanically, by the type system.

**"I want to add my own constraint/goal on top."**
→ Tier 2: add a new forcing theorem of shape `WellFormed W → handles_yourConstraint W → HasYourFeature W`.
→ Tier 3: add a new `CoreModel`-parameterized predicate and its necessity theorem.
→ `RevisionSafety.lean` `premise_strengthening` guarantees adding constraints can't invalidate existing implications.
