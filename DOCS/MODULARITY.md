# Modularity Registry

This document is the single reference for how EpArch's theorem corpus is modular.
It tracks what can be "disabled" (constraint, health goal, world bundle), by what mechanism, what theorems depend on each item, and what the formal status is.

**Key question answered here:** If a product/sub-system rejects some constraint or goal, which theorems still apply, which don't, and how does the formalization certify that?

---

## The Four Modularity Tiers

The formalization has four distinct modularity mechanisms, each at a different layer.
They are not unified yet — see [Tier 4](#tier-4-main-theorem-library--transport-schema-needed) for the gap.

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

**Gap:** The necessity theorems in `Health.lean` are `CoreModel`-parameterized but not yet individually wrapped in a transport schema. A generic `transport_health_goal` theorem stating `HealthGoal C → Compatible E C → HealthGoal (forget E)` per goal would close this. Currently each goal must be manually checked against the `CoreOps` fields of the sub-bundle.

---

## Tier 4 — Main Theorem Library (transport schema needed)

**Files:** `Theorems.lean` (109 theorems), `Diagnosability.lean`, `Agent/Corroboration.lean`, `Agent/Resilience.lean`, `Invariants.lean`, `ScopeIrrelevance.lean`, `Predictions.lean`, `WorkedTraces.lean`

**Current state:** Theorems are stated over the concrete types from `Basic.lean` — `Deposit PropLike Standard ErrorModel Provenance`, `Bubble`, etc. — not over `CoreModel`. They cannot be transported automatically.

**What is needed:** Re-state key theorems over `CoreModel` plus a generic transport theorem:

```lean
-- Shape of the missing layer:
theorem transport_generic (P : CoreModel → Prop)
    (h_compat : ∀ (E : ExtModel) (C : CoreModel), Compatible E C → P C → P (forget E))
    (E : ExtModel) (C : CoreModel) (h : Compatible E C) :
    P C → P (forget E)
```

Once a theorem `T` has shape `T (M : CoreModel) ...`, it is transport-safe and the
type system certifies it survives compatible extension.

**Operation dependency map** — which `CoreOps` fields each theorem cluster touches
(determines what survives dropping which constraint/goal):

| Cluster | `CoreOps` fields | Constraint/goal |
|---|---|---|
| Withdrawal gate theorems | `truth`, `obs`, `submit` | `coordination_need`, `SafeWithdrawalGoal` |
| Export gate / header theorems | `obs`, `deposit_header` | `export_across_boundaries` |
| Revision / competition gate | `revise`, `hasRevision`, `selfCorrects` | `adversarial_pressure`, `CorrigibleLedgerGoal` |
| Verification / audit | `verifyWithin`, `effectiveTime` | `bounded_audit`, `SoundDepositsGoal` |
| Diagnosability ordering | `obs`, `truth` | `export_across_boundaries`, `SafeWithdrawalGoal` |
| Scope/irrelevance | `selfCorrects`, `hasRevision` | `SelfCorrectionGoal`, `PaperFacing` |

**What a user can do today without the transport layer:**
Use the operation dependency map above to manually read off which theorem clusters are unaffected. This is reliable reasoning — it just isn't machine-certified by a transport theorem.

**Planned module:** `Meta/TheoremTransport.lean` — would add the polymorphic re-statements and the generic transport theorem.

---

## Modularity Summary Table

| Layer | Mechanism | Current status | Certifying file |
|---|---|---|---|
| World bundles (`W_*`) | Explicit hypothesis — not providing proof disables | ✅ Complete | `WorldCtx.lean`, `AdversarialObligations.lean` |
| Constraints (6 forcing results) | Independent conjuncts — cherry-pick freely | ✅ Complete | `Minimality.lean` |
| Health goals (5 predicates) | `CoreModel`-parameterized | ⚠️ Partial — no generic transport yet | `Health.lean`, `Modularity.lean` |
| `PaperFacing` / competition gate | `transport_core` + `sub_revision_safety` | ✅ Complete | `RevisionSafety.lean`, `Modularity.lean` |
| Main theorem library (109+) | Needs `CoreModel` re-parameterization | ❌ Not yet — operation map available for manual use | `Meta/TheoremTransport.lean` (planned) |

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
