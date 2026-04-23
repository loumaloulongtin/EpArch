# EpArch — Per-Dimension Forcing Chain

This file documents the three-layer proof structure that underlies each of
EpArch's eight architectural pressure dimensions. The three layers are a
*per-dimension* axis: semantic obstruction (`Minimality.lean`) → system
embedding (`Scenarios.lean`) → stored consequences (`GroundedEvidence.lean`,
`Convergence.lean`). This is not the same axis as the cluster-registry
three-layer architecture described in `MODULARITY.md`, which covers the
routing / constraint-proof / proof-content structure of the `certify`
surface. Both axes are present in the repo; this file covers only the
per-dimension forcing chain.

**Reading direction.** The sections below are ordered Layer 1 → Layer 2 →
Layer 3 for completeness. For a reviewer asking *why* alternative
architectures fail, the practical entry point is the other end: start with
`StructurallyForced` in `Convergence.lean` and the impossibility witnesses
stored in each `GroundedXStrict`, then follow the chain back to the Layer 1
model in `Minimality.lean` for the proof content. `Minimality.lean` is where
you go to understand the argument, not where you go to understand what is
being claimed.

The eight dimensions are not uniform in proof depth. "Mostly definitional"
means the theorem is a direct extraction from constructor fields — correct
and useful, but not where the mathematical content lives. "Interface-
compositional" means the theorem composes several hypotheses cleanly but
introduces no new mathematical argument. "Genuinely semantic" means the
proof requires a real mathematical argument — induction over a sequence,
a set-closure property, or a counting obstruction — that cannot be replaced
by field extraction alone. That asymmetry is not a flaw. The theorems are
exactly as deep as their claims require.

---

## Dimension 1: Scope — Bubbles

**Constraint pressure:** Agents disagree over claim validity. Without a
scoped authorization boundary, no mechanism can resolve disagreement without
collapsing it — any flat resolver either over-accepts or over-rejects.

**Layer 1 — Semantic obstruction**
- Structure: `AgentDisagreement` in `Minimality.lean`
- Theorem: `flat_scope_impossible` — no single flat predicate can simultaneously
  accept all claims one agent accepts and reject all claims one agent rejects
  when the agents disagree
- Proof technique: contradiction — assumes a flat resolver exists, derives that
  it must both hold and not hold on a witness claim
- Proof weight: genuinely semantic

**Layer 2 — System embedding**
- Structure: `RepresentsDisagreement` in `Scenarios.lean`
- Embedding theorem: `disagreement_without_bubbles_embeds` — a `WorkingSystem`
  lacking `HasBubbles` embeds into `AgentDisagreement`
- Forcing theorem: `disagreement_forces_bubbles`
- Bridge condition: the system hosts two agents with conflicting acceptance
  predicates and no bubble boundary to scope them

**Layer 3 — Stored consequences (`GroundedBubblesStrict`)**
- Stored field: `no_flat_resolver` — the impossibility witness carried forward
- Aggregator wiring: `scope_consequence := fun G _h_ev => G.no_flat_resolver`
- Proof weight note: Layer 3 is direct field extraction; the mathematical
  content is entirely in Layer 1

---

## Dimension 2: Coordination — Bank

**Constraint pressure:** Multiple agents must rely on a common deposit.
Private-only storage guarantees isolation by construction; no deposit is
accessible to more than one agent, making collective reliance impossible.

**Layer 1 — Semantic obstruction**
- Structure: `PrivateOnlyStorage` in `Minimality.lean`
- Theorem: `private_storage_no_sharing` — in isolated storage, no deposit
  is accessible to both agents simultaneously
- Proof technique: contradiction — the `isolation` field directly refutes
  the existence of a shared deposit
- Proof weight: mostly definitional (the isolation field is the proof)

**Layer 2 — System embedding**
- Structure: `RepresentsPrivateCoordination` in `Scenarios.lean`
- Embedding theorem: `private_coordination_without_bank_embeds`
- Forcing theorem: `private_coordination_forces_bank`
- Bridge condition: the system has two agents that must share a ledger entry
  but no shared storage component

**Layer 3 — Stored consequences (`GroundedBankStrict`)**
- Stored field: `has_shared_entry` — a concrete shared ledger entry witness
- Aggregator wiring: `bank_consequence := fun G _h_ev => G.has_shared_entry`
- Proof weight note: interface-compositional readout from the grounded witness

---

## Dimension 3: Adversarial — Revocation

**Constraint pressure:** An adversary can arrange for a deposit to appear
valid at acceptance time but become invalid later. In a monotonic lifecycle
(no revocation), there is no exit from invalid states — the system
accumulates invalid-but-irremovable deposits without bound.

**Layer 1 — Semantic obstruction**
- Structure: `MonotonicLifecycle` in `Minimality.lean`
- Theorem: `monotonic_no_exit` — in a monotonic lifecycle the accepted
  state is absorbing: `iter M.step n M.accepted = M.accepted` for all `n`.
  No sequence of transitions can escape it; an adversarial deposit that
  passes acceptance stays accepted permanently
- Proof technique: induction on `n` — the `absorbing` field (`step accepted
  = accepted`) is applied at each successor step to preserve the invariant
- Proof weight: genuinely semantic (the induction is not eliminable; each
  step requires `absorbing` to hold the invariant across the iteration)

**Layer 2 — System embedding**
- Structure: `RepresentsMonotonicLifecycle` in `Scenarios.lean`
- Embedding theorem: `monotonic_lifecycle_without_revocation_embeds`
- Forcing theorem: `monotonic_lifecycle_forces_revocation`
- Bridge condition: the system has a deposit that can become invalid and
  no revocation mechanism to remove it

**Layer 3 — Stored consequences (`GroundedRevocationStrict`)**
- Stored field: `has_invalid_revocable_witness` — existence of a claim
  that is revocable and currently invalid
- Aggregator wiring: `revocation_consequence := fun G _h_ev => G.has_invalid_revocable_witness`
- Proof weight note: the existential is extracted from the grounded witness;
  the semantic weight is entirely in `monotonic_no_exit`

---

## Dimension 4: Export — Headers

**Constraint pressure:** Import must discriminate between claims by content.
A uniform import function applies the same acceptance decision to all claims
with the same surface form, making it impossible to simultaneously be sound
and complete across claims that differ only in their header content.

**Layer 1 — Semantic obstruction**
- Structure: `DiscriminatingImport` in `Minimality.lean`
- Theorem: `no_sound_complete_uniform_import` — a uniform import function
  that is also sound and complete derives `False`; uniformity and
  soundness+completeness are jointly inconsistent
- Proof technique: contradiction — `h_uniform` forces `f good = f bad`;
  `h_sound` and `h_complete` force `f bad = false` and `f good = true`;
  `Bool.noConfusion` closes the goal
- Proof weight: interface-compositional (the contradiction is assembled
  from three hypotheses; no new mathematical argument is introduced)

**Layer 2 — System embedding**
- Structure: `RepresentsDiscriminatingImport` in `Scenarios.lean`
- Embedding theorem: `discriminating_import_without_headers_embeds`
- Forcing theorem: `discriminating_import_forces_headers`
- Bridge condition: the system must route claims by content but carries no
  header preservation guarantee

**Layer 3 — Stored consequences (`GroundedHeadersStrict`)**
- Stored field: `routing_invariant` — for any router, the extracted header
  is invariant under export
- Aggregator wiring: `headers_consequence := fun G _h_ev => G.routing_invariant`
- Proof weight note: the routing invariant is a `congrArg` on the
  `header_preserved` field — definitional readout

---

## Dimension 5: Bounded Verification — Trust Bridges

**Constraint pressure:** Every import budget has a ceiling; some claims cost
more to verify from scratch than the budget permits. Verification-only import
cannot handle those claims.

**Layer 1 — Semantic obstruction**
- Structure: `BoundedVerification` in `Minimality.lean`
- Theorem: `verification_only_import_incomplete` — no verification-only
  import function can handle all claims within the budget; at least one
  claim exceeds it
- Proof technique: arithmetic obstruction — `Nat.not_le_of_gt` on the
  `exceeds_budget` field
- Proof weight: mostly definitional (the `exceeds_budget` field is the
  contradiction; the proof is a one-step arithmetic application)

**Layer 2 — System embedding**
- Structure: `RepresentsBoundedVerification` in `Scenarios.lean`
- Embedding theorem: `bounded_verification_without_trust_embeds`
- Forcing theorem: `bounded_verification_forces_trust_bridges`
- Bridge condition: the system imports across scope boundaries with a fixed
  verification budget and no trust-bridging mechanism

**Layer 3 — Stored consequences (`GroundedTrustBridgesStrict`)**
- Stored field: `bridge_forces_acceptance` — for any downstream acceptance
  policy, the bridge witness forces acceptance
- Aggregator wiring: `trust_consequence := fun G _h_ev => G.bridge_forces_acceptance`
- Proof weight note: `bridge_forces_acceptance` is a direct application of
  the `downstream_via_bridge` field — interface-compositional

---

## Dimension 6: Truth Pressure — Redeemability

**Constraint pressure:** A closed endorsement system — where the set of
redeemable claims is fixed by internal consensus alone — cannot be falsified
by external evidence. This is a set-closure property: the redeemable set
is closed under the endorsement relation, so no external claim can enter it.

**Layer 1 — Semantic obstruction**
- Structure: `ClosedEndorsement` in `Minimality.lean`
- Theorem: `closed_system_unfalsifiable` — in a closed endorsement system,
  no external claim can gain redeemability status
- Proof technique: set-closure — the closure hypothesis directly blocks any
  external witness from being redeemable
- Proof weight: genuinely semantic (the set-closure argument is not
  definitional; it requires reasoning about which claims are reachable
  under the endorsement relation)

**Layer 2 — System embedding**
- Structure: `RepresentsClosedEndorsement` in `Scenarios.lean`
- Embedding theorem: `closed_endorsement_without_redeemability_embeds`
- Forcing theorem: `closed_endorsement_forces_redeemability`
- Bridge condition: the system endorses claims without an external
  redeemability anchor

**Layer 3 — Stored consequences (`GroundedRedeemabilityStrict`)**
- Stored field: `has_constrained_redeemable_witness` — existence of a
  constrained claim that is also redeemable
- Aggregator wiring: `redeemability_consequence := fun G _h_ev => G.has_constrained_redeemable_witness`
- Proof weight note: the existential is extracted from the grounded
  `witness` / `is_constrained` / `has_path` fields — interface-compositional

---

## Dimension 7: Authorization — Granular ACL

**Constraint pressure:** A two-tier access system (all agents in tier A get
full access; all agents in tier B get none) cannot express differential
access for agents in the same tier. Flat authorization is structurally
incapable of the discrimination that multi-agent heterogeneous access
requires.

**Layer 1 — Semantic obstruction**
- Structure: `TwoTierAccess` in `Minimality.lean`
- Theorem: `flat_authorization_impossible` — no flat tier assignment can
  simultaneously grant differentiated access to two agents in the same tier
- Proof technique: contradiction — the flat tier hypothesis forces equal
  access decisions for same-tier agents, contradicting the differentiation
  requirement
- Proof weight: genuinely semantic (the contradiction requires reasoning
  about the interaction between tier membership and access decisions)

**Layer 2 — System embedding**
- Structure: `RepresentsUniformAccess` in `Scenarios.lean`
- Embedding theorem: `uniform_access_without_acl_embeds`
- Forcing theorem: `uniform_access_forces_acl`
- Bridge condition: the system has two agents that need different access
  levels but no granular ACL component

**Layer 3 — Stored consequences (`GroundedAuthorizationStrict`)**
- Stored field: `no_flat_tier` — no flat predicate can reproduce the
  differentiated access behavior
- Aggregator wiring: `authorization_consequence := fun G _h_ev => G.no_flat_tier`
- Proof weight note: direct field extraction; the mathematical content
  is entirely in `flat_authorization_impossible`

---

## Dimension 8: Storage Management — Bounded Capacity

**Constraint pressure:** Active deposits accumulate monotonically unless
explicitly evicted. Under a fixed capacity budget, unbounded accumulation
overflows the budget — making storage management not a policy choice but
a structural necessity.

**Layer 1 — Semantic obstruction**
- Structure: `BoundedStorage` in `Minimality.lean`
- Theorem: `monotone_active_accumulation_overflows` — no fixed capacity
  budget covers all states: applying the universal bound to `deep_state`
  (which carries `exceeds_budget`) yields a contradiction via `Nat.not_le`
- Proof technique: arithmetic obstruction from a single overflow witness —
  one application of the universal to `deep_state`, one `Nat` inequality
  contradiction
- Proof weight: mostly definitional (the `deep_state` / `exceeds_budget`
  fields supply the contradiction; no step-indexed induction is involved)

**Layer 2 — System embedding**
- Structure: `RepresentsBoundedCapacity` in `Scenarios.lean`
- Embedding theorem: `bounded_capacity_without_storage_embeds`
- Forcing theorem: `bounded_capacity_forces_storage_management`
- Bridge condition: the system operates under a bounded storage budget with
  no eviction or compaction mechanism

**Layer 3 — Stored consequences (`GroundedStorageStrict`)**
- Stored field: `no_unbounded_accumulation` — the overflow state refutes
  the assumption that all states fit within the budget
- Aggregator wiring: `storage_consequence := fun G _h_ev => G.no_unbounded_accumulation`
- Proof weight note: the refutation is a direct application of the
  `overflow_state` field — mostly definitional

---

## Summary Table

| Dimension | Layer 1 theorem | Proof technique | Proof weight |
|-----------|----------------|-----------------|--------------|
| Scope / Bubbles | `flat_scope_impossible` | Contradiction | Genuinely semantic |
| Coordination / Bank | `private_storage_no_sharing` | Contradiction (field) | Mostly definitional |
| Adversarial / Revocation | `monotonic_no_exit` | Induction | Genuinely semantic |
| Export / Headers | `routing_requires_header` | Algebraic obstruction | Interface-compositional |
| Bounded verification / Trust bridges | `verification_only_import_incomplete` | Arithmetic obstruction | Mostly definitional |
| Truth pressure / Redeemability | `closed_system_unfalsifiable` | Set-closure | Genuinely semantic |
| Authorization / Granular ACL | `flat_authorization_impossible` | Contradiction | Genuinely semantic |
| Storage management / Bounded capacity | `monotone_active_accumulation_overflows` | Arithmetic obstruction (single witness) | Mostly definitional |

Four of the eight Layer 1 theorems require a genuine mathematical argument
that cannot be collapsed into field extraction: `flat_scope_impossible`,
`monotonic_no_exit`, `closed_system_unfalsifiable`, and
`flat_authorization_impossible`. These carry the architectural claim that
the corresponding features are not design choices — they are the only
structures that can satisfy the stated constraint.

The remaining four are shallower at Layer 1 because the impossibility
argument at that layer is arithmetic or definitional; the architectural
forcing is real, but the proof machinery is lighter. The Layer 2 embedding
theorems for all eight dimensions are uniform in structure.

---

## What this does not cover

The residual-risk obligation taxonomy (`MitigatesObligation`,
`mitigates_obligation_implies_grounded`, `GloballyRiskFreeBridgePolicy`) and
the PRP forcing results live in `ResidualRiskMitigation.lean` and
`Health.lean`. They are a separate forcing surface operating over
`AutonomyModel` / `RiskAutonomyModel`, not over the per-dimension
`Scenarios` / `Convergence` / `GroundedEvidence` chain. They are outside
the scope of this file and are documented in `MODULARITY.md` §1d.
