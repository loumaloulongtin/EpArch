# Per-Dimension Forcing Chain

The reviewer map for the headline forcing argument. Each of EpArch's eight
architectural pressure dimensions follows the same three-layer chain:
semantic obstruction → system embedding → stored consequences. This file is
the route only — layer descriptions live in `architecture/`, the theorem
registry lives in [reference/THEOREMS.md](reference/THEOREMS.md).

## How to read this file

The eight dimensions are ordered for completeness, but the practical reviewer
entry point is the other end: start with `StructurallyForced` in
[`Convergence.lean`](../EpArch/Convergence.lean), then trace back through
`GroundedXStrict` in [`GroundedEvidence.lean`](../EpArch/GroundedEvidence.lean),
`Represents*` in [`Scenarios.lean`](../EpArch/Scenarios.lean), and finally the
Layer 1 model in [`Minimality.lean`](../EpArch/Minimality.lean). The dimensions
differ in proof depth — *genuinely semantic*, *interface-compositional*, and
*mostly definitional* — and the depth annotations below are not modesty: they
say where the mathematical content actually lives.

## Files on the route

| File                                                                          | Layer    | Contents                                                                 |
|-------------------------------------------------------------------------------|----------|--------------------------------------------------------------------------|
| [`Minimality.lean`](../EpArch/Minimality.lean)                                | Layer 1  | Abstract impossibility models and their impossibility theorems           |
| [`Scenarios.lean`](../EpArch/Scenarios.lean)                                  | Layer 2  | `Represents*` structures, `_without_*_embeds` and `_forces_*` theorems   |
| [`GroundedEvidence.lean`](../EpArch/GroundedEvidence.lean)                    | Layer 3a | `GroundedX` / `GroundedXStrict` evidence structures                      |
| [`Convergence.lean`](../EpArch/Convergence.lean)                              | Layer 3b | `StructurallyForced`, `ForcingEmbedding`, `convergence_structural`       |
| [`WorldBridges.lean`](../EpArch/WorldBridges.lean)                            | Capstone | `bundled_structure_forces_bank_primitives` (world-assumption-free path)  |

## Suggested first-read sequence

1. **This file** — the chain, the file layout, which dimensions are deep.
2. **[`Convergence.lean`](../EpArch/Convergence.lean)** — `StructurallyForced`,
   `ForcingEmbedding`, `embedding_to_structurally_forced`,
   `convergence_structural`. The top-level certificate.
3. **One Layer 1 model in [`Minimality.lean`](../EpArch/Minimality.lean)** —
   pick a *genuinely semantic* dimension (Adversarial/Revocation or Truth
   pressure/Redeemability) and follow the impossibility argument.
4. **[`Scenarios.lean`](../EpArch/Scenarios.lean)** — check a
   `_without_*_embeds` / `_forces_*` pair for the same dimension.
5. **[reference/THEOREMS.md](reference/THEOREMS.md)** and the
   `architecture/` docs — for everything off this route.

## Top-level aggregator (`Convergence.lean`)

- **`EvidenceConsequences W`** — one field per dimension, each reading its
  impossibility consequence off a `GroundedXStrict`. Wired inside
  `embedding_to_structurally_forced`.
- **`StructurallyForced W`** — packages `forcing` (eight `handles_* → Has*`
  implications, indexed by `Pressure`) and `evidence` (an
  `EvidenceConsequences`). The top-level certificate.
- **`ForcingEmbedding W`** — for each dimension: either the system has the
  feature, or it embeds into the abstract impossibility model.
- **`convergence_structural`** — `StructurallyForced W → SatisfiesAllProperties W → containsBankPrimitives W`.
- **`structural_impossibility`** — missing any feature blocks
  `SatisfiesAllProperties`.
- **`grounded_evidence_consequences`** — joint readout for all eight
  `GroundedXStrict` consequences under `SatisfiesAllProperties`.

---

## Dimension 1: Scope — Bubbles

**Constraint pressure.** Agents disagree over claim validity. Without a
scoped authorization boundary, no flat resolver can simultaneously accept
what one agent accepts and reject what the other rejects.

- **Layer 1.** `AgentDisagreement`; `flat_scope_impossible` (contradiction).
  *Genuinely semantic.*
- **Layer 2.** `RepresentsDisagreement`; `disagreement_without_bubbles_embeds`,
  `disagreement_forces_bubbles`.
- **Layer 3.** `GroundedBubblesStrict.no_flat_resolver`; aggregator wiring
  `scope_consequence := fun G _ => G.no_flat_resolver`. Field extraction;
  the content is in Layer 1.

## Dimension 2: Coordination — Bank

**Constraint pressure.** Multiple agents must rely on a common deposit.
Private-only storage isolates by construction; collective reliance is
unreachable.

- **Layer 1.** `PrivateOnlyStorage`; `private_storage_no_sharing`
  (contradiction via `isolation` field). *Mostly definitional.*
- **Layer 2.** `RepresentsPrivateCoordination`;
  `private_coordination_without_bank_embeds`,
  `private_coordination_forces_bank`.
- **Layer 3.** `GroundedBankStrict.has_shared_entry`; aggregator wiring
  `bank_consequence := fun G _ => G.has_shared_entry`.
  Interface-compositional readout.

## Dimension 3: Adversarial — Revocation

**Constraint pressure.** An adversary can arrange a deposit that becomes
invalid after acceptance. In a monotonic lifecycle, the accepted state is
absorbing; invalid deposits accumulate without bound.

- **Layer 1.** `MonotonicLifecycle`; `monotonic_no_exit` —
  `iter M.step n M.accepted = M.accepted` for all `n` (induction; the
  `absorbing` field carries the invariant). *Genuinely semantic.*
- **Layer 2.** `RepresentsMonotonicLifecycle`;
  `monotonic_lifecycle_without_revocation_embeds`,
  `monotonic_lifecycle_forces_revocation`.
- **Layer 3.** `GroundedRevocationStrict.has_invalid_revocable_witness`;
  aggregator wiring `revocation_consequence := fun G _ => G.has_invalid_revocable_witness`.

## Dimension 4: Export — Headers

**Constraint pressure.** Import must discriminate by content. A uniform
import function is jointly inconsistent with soundness and completeness on
claims that differ only in their headers.

- **Layer 1.** `DiscriminatingImport`; `no_sound_complete_uniform_import`
  (uniformity forces `f good = f bad`; soundness/completeness force opposite
  values; `Bool.noConfusion`). *Interface-compositional.*
- **Layer 2.** `RepresentsDiscriminatingImport`;
  `discriminating_import_without_headers_embeds`,
  `discriminating_import_forces_headers`.
- **Layer 3.** `GroundedHeadersStrict.routing_invariant`; aggregator wiring
  `headers_consequence := fun G _ => G.routing_invariant`. `congrArg` on
  `header_preserved` — definitional readout.

## Dimension 5: Bounded Verification — Trust Bridges

**Constraint pressure.** Every import budget has a ceiling; some claims
exceed it. Verification-only import cannot handle them.

- **Layer 1.** `BoundedVerification`; `verification_only_import_incomplete`
  (`Nat.not_le_of_gt` on `exceeds_budget`). *Mostly definitional.*
- **Layer 2.** `RepresentsBoundedVerification`;
  `bounded_verification_without_trust_embeds`,
  `bounded_verification_forces_trust_bridges`.
- **Layer 3.** `GroundedTrustBridgesStrict.bridge_forces_acceptance`;
  aggregator wiring `trust_consequence := fun G _ => G.bridge_forces_acceptance`.

## Dimension 6: Truth Pressure — Redeemability

**Constraint pressure.** A closed endorsement system — redeemability fixed
by internal consensus — is unfalsifiable by external evidence. Set-closure:
the redeemable set is closed under endorsement.

- **Layer 1.** `ClosedEndorsement`; `closed_system_unfalsifiable` (the
  closure hypothesis blocks any external witness). *Genuinely semantic.*
- **Layer 2.** `RepresentsClosedEndorsement`;
  `closed_endorsement_without_redeemability_embeds`,
  `closed_endorsement_forces_redeemability`.
- **Layer 3.** `GroundedRedeemabilityStrict.has_constrained_redeemable_witness`;
  aggregator wiring `redeemability_consequence := fun G _ => G.has_constrained_redeemable_witness`.

## Dimension 7: Authorization — Granular ACL

**Constraint pressure.** A two-tier access scheme cannot express
differential access for agents in the same tier; flat authorization is
structurally incapable of that discrimination.

- **Layer 1.** `TwoTierAccess`; `flat_authorization_impossible`
  (contradiction). *Genuinely semantic.*
- **Layer 2.** `RepresentsUniformAccess`; `uniform_access_without_acl_embeds`,
  `uniform_access_forces_acl`.
- **Layer 3.** `GroundedAuthorizationStrict.no_flat_tier`; aggregator wiring
  `authorization_consequence := fun G _ => G.no_flat_tier`.

## Dimension 8: Storage Management — Bounded Capacity

**Constraint pressure.** Active deposits accumulate monotonically without
explicit eviction. Under a fixed capacity budget, accumulation overflows.

- **Layer 1.** `BoundedStorage`; `monotone_active_accumulation_overflows`
  (apply universal bound to `deep_state` carrying `exceeds_budget`;
  `Nat.not_le`). *Mostly definitional.*
- **Layer 2.** `RepresentsBoundedCapacity`;
  `bounded_capacity_without_storage_embeds`,
  `bounded_capacity_forces_storage_management`.
- **Layer 3.** `GroundedStorageStrict.no_unbounded_accumulation`; aggregator
  wiring `storage_consequence := fun G _ => G.no_unbounded_accumulation`.

---

## Summary table

| Dimension                              | Layer 1 theorem                              | Proof technique             | Proof weight             |
|----------------------------------------|----------------------------------------------|-----------------------------|--------------------------|
| Scope / Bubbles                        | `flat_scope_impossible`                      | Contradiction               | Genuinely semantic       |
| Coordination / Bank                    | `private_storage_no_sharing`                 | Contradiction (field)       | Mostly definitional      |
| Adversarial / Revocation               | `monotonic_no_exit`                          | Induction                   | Genuinely semantic       |
| Export / Headers                       | `no_sound_complete_uniform_import`           | Contradiction               | Interface-compositional  |
| Bounded verification / Trust bridges   | `verification_only_import_incomplete`        | Arithmetic obstruction      | Mostly definitional      |
| Truth pressure / Redeemability         | `closed_system_unfalsifiable`                | Set-closure                 | Genuinely semantic       |
| Authorization / Granular ACL           | `flat_authorization_impossible`              | Contradiction               | Genuinely semantic       |
| Storage management / Bounded capacity  | `monotone_active_accumulation_overflows`     | Arithmetic obstruction      | Mostly definitional      |

Four of the eight Layer 1 theorems require a genuine mathematical argument
that cannot be collapsed into field extraction. The remaining four are
shallower at Layer 1; the architectural forcing is real, but the proof
machinery is lighter. Layer 2 embedding theorems are uniform across all eight.

---

## Adjacent layers

These are adjacency notes only; each layer is described in its own doc.

- **Operational gates.** [`Theorems/Withdrawal.lean`](../EpArch/Theorems/Withdrawal.lean)
  proves `withdrawal_gates`, `repair_enforces_revalidation`,
  `submit_enforces_revalidation`, `repair_requires_prior_challenge`,
  `register_enters_deposited` from the `Step` constructors. Layer description:
  [architecture/SEMANTICS.md](architecture/SEMANTICS.md).
- **Health-goal transport.** [`Agent/Imposition.lean`](../EpArch/Agent/Imposition.lean)
  (scenario style) and [`Health.lean`](../EpArch/Health.lean) (model style)
  prove that the mechanisms the forcing chain produces are necessary for the
  stated health goals. Same architectural conclusion via two routes.
- **World-bundle obligations.** [`WorldBridges.lean`](../EpArch/WorldBridges.lean),
  [`WorldCtx.lean`](../EpArch/WorldCtx.lean), and
  [`WorldWitness.lean`](../EpArch/WorldWitness.lean) connect explicit
  W-bundles to required behaviors; the world-assumption-free
  `bundled_structure_forces_bank_primitives` is the capstone. Layer
  description: [architecture/WORLD.md](architecture/WORLD.md).
- **Certification surface.** [`Meta/Config.lean`](../EpArch/Meta/Config.lean)
  and [`Meta/ClusterRegistry.lean`](../EpArch/Meta/ClusterRegistry.lean)
  expose the proof structure as a configurable, auditable composition API.
  No new mathematical content. Layer description:
  [architecture/MODULARITY.md](architecture/MODULARITY.md).
- **Adversarial obligations.** [`AdversarialBase.lean`](../EpArch/AdversarialBase.lean)
  and [`AdversarialObligations.lean`](../EpArch/AdversarialObligations.lean)
  formalize attack models as `W_* → attack_vector → Conclusion` obligations.
- **Corroboration.** [`Agent/Corroboration.lean`](../EpArch/Agent/Corroboration.lean)
  proves multi-source acceptance, common-mode failure, diversity requirement.
  Layer description: [architecture/CORROBORATION.md](architecture/CORROBORATION.md).
- **Non-vacuity.** [`Concrete/NonVacuity.lean`](../EpArch/Concrete/NonVacuity.lean)
  closes the "maybe the model has no instances" attack on the impossibility
  theorems. Layer description: [architecture/FEASIBILITY.md](architecture/FEASIBILITY.md).

The residual-risk obligation taxonomy
(`MitigatesObligation`, `mitigates_obligation_implies_grounded`,
`GloballyRiskFreeBridgePolicy`) and the PRP forcing results live in
[`ResidualRiskMitigation.lean`](../EpArch/ResidualRiskMitigation.lean) and
[`Health.lean`](../EpArch/Health.lean). They are a separate forcing surface
over `AutonomyModel` / `RiskAutonomyModel` and are documented in
[architecture/MODULARITY.md](architecture/MODULARITY.md).

## Go next

- [architecture/SEMANTICS.md](architecture/SEMANTICS.md),
  [architecture/WORLD.md](architecture/WORLD.md),
  [architecture/FEASIBILITY.md](architecture/FEASIBILITY.md),
  [architecture/CORROBORATION.md](architecture/CORROBORATION.md),
  [architecture/MODULARITY.md](architecture/MODULARITY.md) — layer descriptions.
- [reference/THEOREMS.md](reference/THEOREMS.md) — theorem registry by family.
