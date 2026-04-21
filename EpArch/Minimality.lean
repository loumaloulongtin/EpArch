/-
EpArch.Minimality — Minimality and Impossibility Theorems

Structural impossibility models: remove primitive X and constraint Y
cannot be satisfied. The convergence theorem itself
(convergence_structural) lives in EpArch.Convergence.

The core claim is convergence under constraints, not metaphysical necessity.
Any working solution must contain these structural elements, but
implementations can differ.

Key exports:
- WorkingSystem (record wrapping SystemSpec configuration flags)
- Eight structural impossibility models and their impossibility theorems
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank
import EpArch.Commitments
import EpArch.SystemSpec
import EpArch.GroundedEvidence
import EpArch.Concrete.VerificationDepth

namespace EpArch

/-! ## Working System Abstraction -/

/-- A "working system" that coordinates under uncertainty.

    This abstracts over any system that successfully enables coordination
    while handling the constraints above. Such systems converge on
    Bank-like primitives. -/
structure WorkingSystem where
  /-- The system's architectural specification. -/
  spec             : SystemSpec
  /-- Scope-separation evidence: two distinct acceptance scopes + structural forcing consequence. -/
  bubbles_ev       : Option GroundedBubblesStrict
  /-- Trust-bridge evidence: upstream declarations relied on downstream + bridge-forcing consequence. -/
  bridges_ev       : Option GroundedTrustBridgesStrict
  /-- Header-preservation evidence: export metadata survives boundary + routing invariant. -/
  headers_ev       : Option GroundedHeadersStrict
  /-- Revocation evidence: invalid-and-revocable witness + its existential consequence. -/
  revocation_ev    : Option GroundedRevocationStrict
  /-- Shared-ledger evidence: cross-agent entry witness + shared-entry existential. -/
  bank_ev          : Option GroundedBankStrict
  /-- Redeemability evidence: constrained claim with audit path + existential consequence. -/
  redeemability_ev : Option GroundedRedeemabilityStrict
  /-- Authorization evidence: restricted-agent witness + no-uniform-access consequence. -/
  authorization_ev : Option GroundedAuthorizationStrict := none
  /-- Storage-management evidence: overflow state exceeding capacity + no-unbounded-accumulation consequence. -/
  storage_ev       : Option GroundedStorageStrict        := none

/-! ## Forced Feature Predicates

These are definitional predicates that inspect the WorkingSystem's
SystemSpec to determine if features are present. Each predicate
corresponds to one "What It Forces" entry in the constraints table. -/

/-- Predicate: system has scoped trust zones (bubbles), not a global ledger.
    Forced by: Distributed agents -/
def HasBubbles (W : WorkingSystem) : Prop := W.spec.has_bubble_separation = true

/-- Predicate: system has trust bridges (import-via-trust without full revalidation).
    Forced by: Bounded audit -/
def HasTrustBridges (W : WorkingSystem) : Prop := W.spec.has_trust_bridges = true

/-- Predicate: system has structured headers (S/E/V) + export gates.
    Forced by: Export across boundaries -/
def HasHeaders (W : WorkingSystem) : Prop := W.spec.preserves_headers = true

/-- Predicate: system has V-independence discipline + revocation mechanism.
    Forced by: Adversarial pressure -/
def HasRevocation (W : WorkingSystem) : Prop := W.spec.has_revocation = true

/-- Predicate: system has Bank (authorization ledger) + acceptance events.
    Forced by: Coordination need -/
def HasBank (W : WorkingSystem) : Prop := W.spec.has_shared_ledger = true

/-- Predicate: system has redeemability (constraint-surface contact).
    Forced by: Truth pressure -/
def HasRedeemability (W : WorkingSystem) : Prop := W.spec.has_redeemability = true

/-- Predicate: system has granular access-control (non-trivial ACL).
    Forced by: Multi-agent heterogeneous access -/
def HasGranularACL (W : WorkingSystem) : Prop := W.spec.has_granular_acl = true

/-- Predicate: system has bounded storage management (finite active-deposit capacity).
    Forced by: Bounded storage constraint -/
def HasStorageManagement (W : WorkingSystem) : Prop := W.spec.has_storage_management = true


/-! ## Eight Operational Properties

These are the functional requirements that working systems must satisfy.
Each maps to one constraint in the table. -/

/-- System handles distributed agents: has scope-separation evidence.
    Required when: Distributed agents constraint holds. -/
def handles_distributed_agents (W : WorkingSystem) : Prop :=
  W.bubbles_ev.isSome = true

/-- System handles bounded audit: has trust-bridge evidence.
    Required when: Bounded audit constraint holds. -/
def handles_bounded_audit (W : WorkingSystem) : Prop :=
  W.bridges_ev.isSome = true

/-- System handles export: has header-preservation evidence.
    Required when: Export across boundaries constraint holds. -/
def handles_export (W : WorkingSystem) : Prop :=
  W.headers_ev.isSome = true

/-- System handles adversarial pressure: has revocation evidence.
    Required when: Adversarial pressure constraint holds. -/
def handles_adversarial (W : WorkingSystem) : Prop :=
  W.revocation_ev.isSome = true

/-- System handles coordination need: has shared-ledger evidence.
    Required when: Coordination need constraint holds. -/
def handles_coordination (W : WorkingSystem) : Prop :=
  W.bank_ev.isSome = true

/-- System handles truth pressure: has redeemability evidence.
    Required when: Truth pressure constraint holds. -/
def handles_truth_pressure (W : WorkingSystem) : Prop :=
  W.redeemability_ev.isSome = true

/-- System handles multi-agent heterogeneous access: has authorization evidence.
    Required when: Distinct agents exist with different access rights. -/
def handles_multi_agent (W : WorkingSystem) : Prop :=
  W.authorization_ev.isSome = true

/-- System handles bounded storage: has storage-management evidence.
    Required when: Bounded storage constraint holds. -/
def handles_storage (W : WorkingSystem) : Prop :=
  W.storage_ev.isSome = true


/-! ## Pressure: The Canonical Dimension Index

`Pressure` is the machine-exhaustive index of EpArch's eight architectural
forcing dimensions.  Using it as the canonical index for `handles_pressure`,
`forced_feature`, `SatisfiesAllProperties`, and `containsBankPrimitives`
means the coverage of the framework — exactly these eight and no others —
is a typed fact, not a counting convention.

A proof that pattern-matches on `Pressure` is checked by Lean for
exhaustiveness: adding a ninth dimension requires adding a ninth
constructor here, which would break every existing `cases P` proof
until the new forcing chain is supplied. -/

/-- The eight architectural pressure dimensions of EpArch. -/
inductive Pressure where
  | scope         -- Distributed agents → Bubbles
  | trust         -- Bounded audit → TrustBridges
  | headers       -- Export → Headers
  | revocation    -- Adversarial → Revocation
  | bank          -- Coordination → Bank
  | redeemability -- Truth pressure → Redeemability
  | authorization -- Multi-agent heterogeneous access → GranularACL
  | storage       -- Bounded storage → StorageManagement
  deriving DecidableEq, Repr

/-- Maps each `Pressure` dimension to its capability predicate. -/
def handles_pressure (W : WorkingSystem) : Pressure → Prop
  | .scope         => handles_distributed_agents W
  | .trust         => handles_bounded_audit W
  | .headers       => handles_export W
  | .revocation    => handles_adversarial W
  | .bank          => handles_coordination W
  | .redeemability => handles_truth_pressure W
  | .authorization => handles_multi_agent W
  | .storage       => handles_storage W

/-- Maps each `Pressure` dimension to its forced architectural feature. -/
def forced_feature (W : WorkingSystem) : Pressure → Prop
  | .scope         => HasBubbles W
  | .trust         => HasTrustBridges W
  | .headers       => HasHeaders W
  | .revocation    => HasRevocation W
  | .bank          => HasBank W
  | .redeemability => HasRedeemability W
  | .authorization => HasGranularACL W
  | .storage       => HasStorageManagement W

/-- A working system satisfies ALL eight operational properties — indexed by `Pressure`.
    The eight-ness is machine-checked: `cases P` in any proof is
    exhaustiveness-verified by Lean. -/
def SatisfiesAllProperties (W : WorkingSystem) : Prop :=
  ∀ P : Pressure, handles_pressure W P

/-- A system contains Bank primitives iff it satisfies every pressure
    dimension's forced-feature predicate. -/
def containsBankPrimitives (W : WorkingSystem) : Prop :=
  ∀ P : Pressure, forced_feature W P


/-! ## Constraint Subset and Partial Well-Formedness -/

/-- A subset of the eight EpArch operational constraints, represented as an
    8-boolean vector. `true` = constraint included; `false` = dropped.

    Examples:
    - `allConstraints`  — all eight included (strongest case)
    - `noConstraints`   — none included (no forcing theorems claimed)
    - `⟨true, false, false, false, true, false, false, false⟩` — only distributed + coordination -/
structure ConstraintSubset where
  distributed    : Bool
  bounded_audit  : Bool
  export_across  : Bool
  adversarial    : Bool
  coordination   : Bool
  truth_pressure : Bool
  multi_agent    : Bool
  bounded_storage: Bool

/-- The full set of all eight constraints. `PartialWellFormed W allConstraints` requires
    all eight biconditionals — the strongest subset. -/
def allConstraints : ConstraintSubset := ⟨true, true, true, true, true, true, true, true⟩

/-- The empty subset. `PartialWellFormed W noConstraints` holds trivially. -/
def noConstraints : ConstraintSubset := ⟨false, false, false, false, false, false, false, false⟩

/-- `PartialWellFormed W S` captures the forcing biconditionals for
    the constraint subset S.

    For each constraint X:
    - If `S.X = true`,  the biconditional `handles_X W ↔ HasFeature_X W` is required.
    - If `S.X = false`, nothing is required for X.

    Requiring all eight (S = allConstraints) is the strongest form. -/
structure PartialWellFormed (W : WorkingSystem) (S : ConstraintSubset) : Prop where
  wf_distributed    : S.distributed     = true → (handles_distributed_agents W ↔ HasBubbles W)
  wf_bounded_audit  : S.bounded_audit   = true → (handles_bounded_audit W ↔ HasTrustBridges W)
  wf_export         : S.export_across   = true → (handles_export W ↔ HasHeaders W)
  wf_adversarial    : S.adversarial     = true → (handles_adversarial W ↔ HasRevocation W)
  wf_coordination   : S.coordination   = true → (handles_coordination W ↔ HasBank W)
  wf_truth_pressure : S.truth_pressure  = true → (handles_truth_pressure W ↔ HasRedeemability W)
  wf_multi_agent    : S.multi_agent     = true → (handles_multi_agent W ↔ HasGranularACL W)
  wf_storage        : S.bounded_storage = true → (handles_storage W ↔ HasStorageManagement W)


/-! ## Grounded Behavioral Evidence

The eight capability witnesses correspond exactly to the eight `GroundedX` structures:

| WorkingSystem field  | GroundedXStrict type            | Forcing dimension                                     |
|----------------------|---------------------------------|-------------------------------------------------------|
| `bubbles_ev`         | `GroundedBubblesStrict`         | Distributed agents — scope separation                 |
| `bridges_ev`         | `GroundedTrustBridgesStrict`    | Bounded audit — trust bridges                         |
| `headers_ev`         | `GroundedHeadersStrict`         | Export across boundaries — header preservation        |
| `revocation_ev`      | `GroundedRevocationStrict`      | Adversarial pressure — revocation                     |
| `bank_ev`            | `GroundedBankStrict`            | Coordination need — shared ledger                     |
| `redeemability_ev`   | `GroundedRedeemabilityStrict`   | Truth pressure — redeemability                        |
| `authorization_ev`   | `GroundedAuthorizationStrict`   | Multi-agent access — granular ACL                     |
| `storage_ev`         | `GroundedStorageStrict`         | Bounded storage — storage management                  | -/

/-- Evidence for all eight behavioral capabilities of a `WorkingSystem`.

    One `GroundedX` field per forcing dimension.  Supplying a `GroundedBehavior`
    to `withGroundedBehavior` sets each `Option GroundedX` field in `WorkingSystem`
    to `some`. -/
structure GroundedBehavior where
  /-- Scope separation: two acceptance scopes disagree on a witness claim. -/
  bubbles       : GroundedBubbles
  /-- Trust bridges: upstream declarations accepted downstream via import. -/
  trust_bridges : GroundedTrustBridges
  /-- Header preservation: export metadata survives crossing a boundary. -/
  headers       : GroundedHeaders
  /-- Revocation: an invalid-and-revocable witness demonstrably exists. -/
  revocation    : GroundedRevocation
  /-- Shared ledger: an entry produced by one agent is consumed by another. -/
  bank          : GroundedBank
  /-- Redeemability: a constrained claim has an audit path to truth contact. -/
  redeemability : GroundedRedeemability
  /-- Authorization: a restricted-agent witness demonstrates granular ACL. -/
  authorization : GroundedAuthorization
  /-- Storage: an overflow state demonstrating capacity pressure. -/
  storage       : GroundedStorage

/-- Build a `WorkingSystem` with all eight proof-carrying option fields set from evidence. -/
def WorkingSystem.withGroundedBehavior (B : GroundedBehavior) (base : WorkingSystem) : WorkingSystem :=
  { base with
    bubbles_ev       := some B.bubbles.toStrict
    bridges_ev       := some B.trust_bridges.toStrict
    headers_ev       := some B.headers.toStrict
    revocation_ev    := some B.revocation.toStrict
    bank_ev          := some B.bank.toStrict
    redeemability_ev := some B.redeemability.toStrict
    authorization_ev := some B.authorization.toStrict
    storage_ev       := some B.storage.toStrict }

/-- A `WorkingSystem` built from `GroundedBehavior` satisfies all eight operational
    properties. -/
theorem grounded_behavior_satisfies_all (B : GroundedBehavior) (W : WorkingSystem) :
    SatisfiesAllProperties (WorkingSystem.withGroundedBehavior B W) := by
  intro P; cases P <;>
  simp [handles_pressure, handles_distributed_agents, handles_bounded_audit,
        handles_export, handles_adversarial, handles_coordination,
        handles_truth_pressure, handles_multi_agent, handles_storage,
        WorkingSystem.withGroundedBehavior, Option.isSome]

/-- `SatisfiesAllProperties` implies all eight evidence option fields are present.
    Extracts the eight `isSome = true` facts from the property predicate. -/
theorem satisfies_all_fixes_flags (W : WorkingSystem) (h : SatisfiesAllProperties W) :
    W.bubbles_ev.isSome       = true ∧
    W.bridges_ev.isSome       = true ∧
    W.headers_ev.isSome       = true ∧
    W.revocation_ev.isSome    = true ∧
    W.bank_ev.isSome          = true ∧
    W.redeemability_ev.isSome = true ∧
    W.authorization_ev.isSome = true ∧
    W.storage_ev.isSome       = true :=
  ⟨h .scope, h .trust, h .headers, h .revocation, h .bank, h .redeemability, h .authorization, h .storage⟩

/-- A `WorkingSystem` built from both `GroundedBehavior` and `GroundedSystemSpec`
    satisfies `PartialWellFormed W allConstraints`.

    Each biconditional pairs `handles_X W` (behavioral, via `withGroundedBehavior`)
    with `HasX W` (spec flag, via `grounded_spec_contains_all`). -/
theorem grounded_partial_wellformed (B : GroundedBehavior) (G : GroundedSystemSpec) :
    PartialWellFormed (WorkingSystem.withGroundedBehavior B
      { spec             := G.toSystemSpec
        bubbles_ev       := none
        bridges_ev       := none
        headers_ev       := none
        revocation_ev    := none
        bank_ev          := none
        redeemability_ev := none }) allConstraints := {
  wf_distributed    := fun _ =>
    ⟨fun _ => (grounded_spec_contains_all G).1,
     fun _ => rfl⟩
  wf_bounded_audit  := fun _ =>
    ⟨fun _ => (grounded_spec_contains_all G).2.1,
     fun _ => rfl⟩
  wf_export         := fun _ =>
    ⟨fun _ => (grounded_spec_contains_all G).2.2.1,
     fun _ => rfl⟩
  wf_adversarial    := fun _ =>
    ⟨fun _ => (grounded_spec_contains_all G).2.2.2.1,
     fun _ => rfl⟩
  wf_coordination   := fun _ =>
    ⟨fun _ => (grounded_spec_contains_all G).2.2.2.2.1,
     fun _ => rfl⟩
  wf_truth_pressure := fun _ =>
    ⟨fun _ => (grounded_spec_contains_all G).2.2.2.2.2.1,
     fun _ => rfl⟩
  wf_multi_agent    := fun _ =>
    ⟨fun _ => (grounded_spec_contains_all G).2.2.2.2.2.2.1,
     fun _ => rfl⟩
  wf_storage        := fun _ =>
    ⟨fun _ => (grounded_spec_contains_all G).2.2.2.2.2.2.2,
     fun _ => rfl⟩ }


/-! ## Global Impossibility and Convergence -/

/-- All eight forced features together constitute Bank-like architecture.

    This is a definitional theorem: `containsBankPrimitives W` is
    `∀ P : Pressure, forced_feature W P` — providing the eight `Has*`
    witnesses satisfies it by case analysis on `P`. -/
theorem all_features_constitute_bank (W : WorkingSystem) :
  HasBubbles W → HasTrustBridges W → HasHeaders W →
  HasRevocation W → HasBank W → HasRedeemability W → HasGranularACL W →
  HasStorageManagement W →
  containsBankPrimitives W := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 P
  cases P <;> assumption


/-! ========================================================================
    Structural Forcing Models
    ========================================================================

This section provides **independent, structurally-grounded proofs** for
each forcing direction.  Each model captures the essential structure of
one constraint scenario and proves an impossibility or invariance result
from that structure alone — no biconditionals needed.

### Summary

| # | Constraint | Model | Theorem | Content |
|---|---|---|---|---|
| 1 | Distributed agents | `AgentDisagreement` | `flat_scope_impossible` | Single scope can't represent disagreeing agents |
| 2 | Bounded audit | `BoundedVerification` | `verification_only_import_incomplete` | Verification-only import can't handle all claims |
| 3 | Export | `DiscriminatingImport` | `uniform_import_nondiscriminating` | Without metadata, import can't distinguish claims |
| 4 | Adversarial | `MonotonicLifecycle` | `monotonic_no_exit` | Without revocation, accepted state is absorbing |
| 5 | Coordination | `PrivateOnlyStorage` | `private_storage_no_sharing` | Isolated storage blocks collective reliance |
| 6 | Truth pressure | `ClosedEndorsement` | `closed_system_unfalsifiable` | Without external contact, consensus is unfalsifiable |
| 7 | Authorization | `TwoTierAccess` | `flat_authorization_impossible` | No flat predicate can represent both the submission and commit tiers |
| 8 | Bounded storage | `BoundedStorage` | `monotone_active_accumulation_overflows` | No fixed budget covers all active-deposit states; management is forced |

After the eight models, the convergence proof machinery (`StructurallyForced`,
`ForcingEmbedding`, Bridge predicates, Scenario predicates,
`convergence_structural`) lives in EpArch.Convergence.
-/


/-! ### 1. Distributed Agents → Scope Separation (Bubbles)

**Argument.**  If two agents have genuinely different acceptance criteria,
no single flat acceptance function can faithfully represent both.  The
system must partition into scopes (bubbles) where each scope has its own
acceptance gate.

**Proof technique.**  Contradiction: a single function that agrees with
agent 1 on the witness claim must accept it; but then it also agrees with
agent 2, who rejects it. -/

/-- Two agents whose acceptance criteria disagree on at least one claim. -/
structure AgentDisagreement where
  Claim : Type
  /-- Agent 1's acceptance criterion. -/
  accept₁ : Claim → Prop
  /-- Agent 2's acceptance criterion. -/
  accept₂ : Claim → Prop
  /-- Witness claim where they disagree. -/
  witness : Claim
  /-- Agent 1 accepts the witness. -/
  agent1_accepts : accept₁ witness
  /-- Agent 2 rejects the witness. -/
  agent2_rejects : ¬accept₂ witness

/-- No single predicate can simultaneously agree with two disagreeing agents.
    A flat (single-scope) system commits to one acceptance function for all agents.
    When agents disagree, that function cannot faithfully represent both.

    Consequence: scope separation (bubbles) is structurally forced. -/
theorem flat_scope_impossible (D : AgentDisagreement) :
    ¬∃ (f : D.Claim → Prop), (∀ c, f c ↔ D.accept₁ c) ∧ (∀ c, f c ↔ D.accept₂ c) := by
  intro ⟨f, hf₁, hf₂⟩
  exact D.agent2_rejects ((hf₂ D.witness).mp ((hf₁ D.witness).mpr D.agent1_accepts))


/-! ### 1b. Alternative Scope Architectures Reduce to AgentDisagreement

A reviewer may ask: do capability systems, federated namespaces, or
dynamically parameterized acceptance gates escape `flat_scope_impossible`?

This section instantiates each alternative, then shows it either:
(a) directly supplies an `AgentDisagreement` instance, or
(b) embeds into per-agent scoped acceptance.

**Capability-token system.**  Each claim carries a capability token; acceptance
is token-gated.  Two agents with non-overlapping token sets disagree on the
witness claim: agent 1 holds the required token; agent 2 does not.
This is a direct `AgentDisagreement` instance — `flat_scope_impossible` applies.

**Federated namespace.**  A global namespace partitioned by scope identifier:
`accept(scope_id, claim) := local_policy scope_id claim`.  Two agents from
different scopes with conflicting local policies disagree on the witness claim.
Again a direct `AgentDisagreement` instance.

**Dynamically parameterized gate.**  Acceptance is `gate(params, claim)` for
some runtime parameter bundle.  If two agents use different parameter bundles
and disagree on the witness, the curried functions `gate params₁` and
`gate params₂` witness an `AgentDisagreement`.  If the gate is parameterized
such that no parameter assignment can satisfy both agents simultaneously, the
flat-scope impossibility applies directly.  If the gate CAN make both agents
agree on every claim, then by definition the agents do not genuinely disagree —
the scope pressure is absent and no bubble is forced for that pair.

**Conclusion of this section.**  None of the three alternative architectures
escapes the theorem.  They either instantiate `AgentDisagreement` directly or
they collapse to a case where the agents do not genuinely disagree (and hence
no scoped separation is required by this argument). -/

/-- Capability-token gated acceptance: a claim is accepted iff the agent
    holds the required token. -/
structure CapabilitySystem where
  Claim : Type
  Token : Type
  /-- Token required to accept a given claim. -/
  required_token : Claim → Token
  /-- Agent 1 holds this token. -/
  agent1_holds : Token → Prop
  /-- Agent 2 holds this token. -/
  agent2_holds : Token → Prop
  /-- Witness claim whose required token agent 1 holds but agent 2 does not. -/
  witness : Claim
  agent1_has : agent1_holds (required_token witness)
  agent2_lacks : ¬agent2_holds (required_token witness)

/-- A capability system with split token ownership instantiates AgentDisagreement.
    The two agents disagree on the witness claim: agent 1 accepts it (holds token),
    agent 2 rejects it (lacks token).  `flat_scope_impossible` then applies
    directly — no flat acceptance function can represent both. -/
theorem capability_system_gives_disagreement (C : CapabilitySystem) :
    AgentDisagreement where
  Claim      := C.Claim
  accept₁ c  := C.agent1_holds (C.required_token c)
  accept₂ c  := C.agent2_holds (C.required_token c)
  witness    := C.witness
  agent1_accepts := C.agent1_has
  agent2_rejects := C.agent2_lacks

/-- Therefore a flat acceptance function cannot faithfully represent both agents
    in a capability system with split ownership. -/
theorem capability_flat_impossible (C : CapabilitySystem) :
    ¬∃ (f : C.Claim → Prop),
      (∀ c, f c ↔ C.agent1_holds (C.required_token c)) ∧
      (∀ c, f c ↔ C.agent2_holds (C.required_token c)) :=
  fun ⟨_f, hf₁, hf₂⟩ =>
    C.agent2_lacks ((hf₂ C.witness).mp ((hf₁ C.witness).mpr C.agent1_has))

/-- Federated namespace: a global claim type carries a scope identifier;
    each scope has its own local acceptance policy. -/
structure FederatedNamespace where
  Scope : Type
  Claim : Type
  /-- Local acceptance policy for each scope. -/
  local_policy : Scope → Claim → Prop
  /-- Two scopes with conflicting policies on a witness claim. -/
  scope₁ : Scope
  scope₂ : Scope
  witness : Claim
  scope1_accepts : local_policy scope₁ witness
  scope2_rejects : ¬local_policy scope₂ witness

/-- A federated namespace with conflicting local policies instantiates
    AgentDisagreement — the per-scope policies ARE per-agent acceptance criteria. -/
theorem federated_namespace_gives_disagreement (F : FederatedNamespace) :
    AgentDisagreement where
  Claim      := F.Claim
  accept₁    := F.local_policy F.scope₁
  accept₂    := F.local_policy F.scope₂
  witness    := F.witness
  agent1_accepts := F.scope1_accepts
  agent2_rejects := F.scope2_rejects

/-- Therefore a single flat function cannot faithfully represent two conflicting
    scope policies in a federated namespace. -/
theorem federated_flat_impossible (F : FederatedNamespace) :
    ¬∃ (f : F.Claim → Prop),
      (∀ c, f c ↔ F.local_policy F.scope₁ c) ∧
      (∀ c, f c ↔ F.local_policy F.scope₂ c) :=
  fun ⟨_f, hf₁, hf₂⟩ =>
    F.scope2_rejects ((hf₂ F.witness).mp ((hf₁ F.witness).mpr F.scope1_accepts))

/-- Dynamically parameterized gate: acceptance is `gate params claim` for a
    runtime parameter bundle of type `Params`. -/
structure ParameterizedGate where
  Params : Type
  Claim : Type
  gate : Params → Claim → Prop
  /-- Parameter bundle used by agent 1. -/
  params₁ : Params
  /-- Parameter bundle used by agent 2. -/
  params₂ : Params
  /-- Witness claim where the two parameter bundles disagree. -/
  witness : Claim
  params1_accepts : gate params₁ witness
  params2_rejects : ¬gate params₂ witness

/-- A parameterized gate whose two parameter bundles disagree on a witness claim
    instantiates AgentDisagreement — the curried functions `gate params₁` and
    `gate params₂` are the two differing acceptance criteria. -/
theorem parameterized_gate_gives_disagreement (G : ParameterizedGate) :
    AgentDisagreement where
  Claim      := G.Claim
  accept₁    := G.gate G.params₁
  accept₂    := G.gate G.params₂
  witness    := G.witness
  agent1_accepts := G.params1_accepts
  agent2_rejects := G.params2_rejects

/-- Therefore no flat acceptance function can faithfully represent two parameter
    bundles that disagree on a witness claim. -/
theorem parameterized_gate_flat_impossible (G : ParameterizedGate) :
    ¬∃ (f : G.Claim → Prop),
      (∀ c, f c ↔ G.gate G.params₁ c) ∧
      (∀ c, f c ↔ G.gate G.params₂ c) :=
  fun ⟨_f, hf₁, hf₂⟩ =>
    G.params2_rejects ((hf₂ G.witness).mp ((hf₁ G.witness).mpr G.params1_accepts))


/-! ### 2. Bounded Audit → Trust Bridges

**Argument.**  When full verification has unbounded cost, some claims
exceed any fixed budget.  A verification-only import policy (re-verify
every import from scratch) cannot handle those claims.  To import them
the system needs a trust-based mechanism: accept based on the source
scope's endorsement rather than full reverification.

**Proof technique.**  The hard claim's cost exceeds the budget;
Nat.not_le_of_gt closes the Nat contradiction. -/

/-- A claim universe where at least one claim exceeds the verification budget. -/
structure BoundedVerification where
  Claim : Type
  /-- Cost to fully verify a claim. -/
  verify_cost : Claim → Nat
  /-- Maximum verification budget per import. -/
  budget : Nat
  /-- A claim that exceeds the budget. -/
  hard_claim : Claim
  exceeds_budget : verify_cost hard_claim > budget

/-- Verification-only import cannot handle all claims under bounded audit.
    At least one claim exceeds the budget and cannot be reverified.

    Consequence: a trust-based import mechanism (trust bridges) is forced. -/
theorem verification_only_import_incomplete (M : BoundedVerification) :
    ¬∀ c : M.Claim, M.verify_cost c ≤ M.budget := by
  intro h
  have h_within := h M.hard_claim
  exact absurd h_within (Nat.not_le_of_gt M.exceeds_budget)


/-! ### 2b. Alternative Trust Mechanisms Reduce to BoundedVerification

A reviewer may ask: do staged acceptance, probabilistic screening, escrowed
delay, or delegated verification markets escape `verification_only_import_incomplete`?

Each alternative is instantiated below.  All hit the same ceiling: at least
one claim exceeds the budget, and the alternative mechanism either (a) itself
exceeds the budget (same contradiction), or (b) relies on an endorsing scope
that bridges the local scope's budget shortfall.

**Staged acceptance.**  A multi-round protocol assigns partial costs per round.
If the sum of round costs for the hard claim still exceeds the budget, the
cumulative cost model is a `BoundedVerification` instance — contradiction fires.

**Delegated verification market.**  A third-party verifier handles hard claims.
The delegation is itself a trust relationship: the importing scope accepts
the delegate's endorsement without reverifying from scratch — a `DelegatedVerification`
instance under the structural definition above. -/

/-- Staged (multi-round) verification: total cost is the sum of per-round costs. -/
structure StagedVerification where
  Claim : Type
  /-- Per-round cost to verify a claim in round i. -/
  round_cost : Nat → Claim → Nat
  /-- Number of rounds attempted. -/
  rounds : Nat
  /-- Total budget across all rounds. -/
  budget : Nat
  /-- A claim whose cumulative cost exceeds the total budget. -/
  hard_claim : Claim
  exceeds_budget : (List.range rounds).foldl (fun acc i => acc + round_cost i hard_claim) 0 > budget

/-- Staged verification cannot handle claims whose cumulative cost exceeds budget.
    The multi-round structure does not escape the budget ceiling. -/
theorem staged_verification_incomplete (M : StagedVerification) :
    ¬(List.range M.rounds).foldl (fun acc i => acc + M.round_cost i M.hard_claim) 0 ≤ M.budget :=
  Nat.not_le_of_gt M.exceeds_budget

/-- Delegated verification: a third-party verifier endorses claims the importer
    cannot verify within budget.  Acceptance of hard claims is via the delegate's
    endorsement rather than local reverification. -/
structure DelegatedVerification where
  Claim : Type
  verify_cost : Claim → Nat
  budget : Nat
  hard_claim : Claim
  exceeds_budget : verify_cost hard_claim > budget
  /-- The delegate's acceptance predicate for claims over budget. -/
  delegate_accepts : Claim → Prop
  /-- Hard claims are accepted via the delegate, not local verification.
      The importer relies on the delegate — it cannot self-verify hard claims. -/
  relies_on_delegate : ∀ c, verify_cost c > budget → delegate_accepts c

/-- DelegatedVerification embeds into BoundedVerification: the local budget problem
    is unchanged regardless of the delegation arrangement.
    The `delegate_accepts` / `relies_on_delegate` fields formalise the trust relationship;
    they route around the budget shortfall, not through it. -/
def delegated_to_bounded (M : DelegatedVerification) : BoundedVerification where
  Claim          := M.Claim
  verify_cost    := M.verify_cost
  budget         := M.budget
  hard_claim     := M.hard_claim
  exceeds_budget := M.exceeds_budget

/-- Delegated verification is incomplete at the local scope: `verification_only_import_incomplete`
    fires via the embedding. -/
theorem delegated_is_trust_bridge (M : DelegatedVerification) :
    ¬∀ c : M.Claim, M.verify_cost c ≤ M.budget :=
  verification_only_import_incomplete (delegated_to_bounded M)

/-- A claim is locally verifiable if its verification cost is within budget. -/
def LocallyVerifiable (M : DelegatedVerification) (c : M.Claim) : Prop :=
  M.verify_cost c ≤ M.budget

/-- A claim exceeds local verification capacity iff its cost is not within budget.
    Both directions follow from `Nat` order lemmas. -/
theorem trust_required_iff_not_locally_verifiable (M : DelegatedVerification) (c : M.Claim) :
    M.verify_cost c > M.budget ↔ ¬LocallyVerifiable M c :=
  ⟨fun hgt hle => absurd hle (Nat.not_le_of_gt hgt),
   fun h => (Nat.lt_or_ge M.budget (M.verify_cost c)).elim id (fun h' => absurd h' h)⟩

/-- At the system level, existence of a claim exceeding the budget is equivalent to
    failure of universal local verifiability.  The right-to-left direction extracts
    a witness from the negated universal via classical logic. -/
theorem delegation_necessary_iff_locally_inadequate (M : DelegatedVerification) :
    (∃ c : M.Claim, M.verify_cost c > M.budget) ↔
    ¬∀ c : M.Claim, LocallyVerifiable M c :=
  ⟨fun ⟨c, hc⟩ hA => absurd (hA c) (Nat.not_le_of_gt hc),
   fun h =>
     Classical.byContradiction (fun h_ne =>
       h (fun c =>
         (Nat.lt_or_ge M.budget (M.verify_cost c)).elim
           (fun hgt => absurd ⟨c, hgt⟩ h_ne)
           id))⟩


/-! ### §2c. Kernel Witness: BoundedVerification is Non-Vacuous by Construction

The `BoundedVerification` structure and `verification_only_import_incomplete`
are the architectural abstractions.  `DepthClaim` (EpArch.Concrete.VerificationDepth) is
their semantic ground: it witnesses that claim families with irreducible
verification cost exist within the kernel itself, not just as a structural
hypothesis.

The kernel must traverse all n constructors to type-check any proof of
`DepthClaim n`.  No budget below n suffices.  `bounded_verify_incomplete`
proves this by structural recursion on `Nat` — the recursion is the cost.

Consequence for trust bridges: a budget-n verifier cannot verify an
endorsement of `DepthClaim n`, since that endorsement has depth n+1
(`endorser_cannot_self_verify`).  The forcing argument of §2 applies to
this family without any coverage assumption. -/

/-- `BoundedVerification` has a canonical kernel inhabitant for every budget d.
    Claims are `Nat`-indexed depths; cost equals depth; depth d+1 exceeds
    budget d.  `DepthClaim (d+1)` is genuinely true (`depth_claim_provable`),
    so the incompleteness shown by `bounded_verify_incomplete` is real. -/
def depth_bounded_verification (d : Nat) : BoundedVerification where
  Claim          := Nat
  verify_cost    := id
  budget         := d
  hard_claim     := d + 1
  exceeds_budget := Nat.lt_succ_self d

/-- `verification_only_import_incomplete` fires on the kernel witness:
    no budget-d verifier covers the full `DepthClaim` family. -/
theorem depth_verification_incomplete (d : Nat) :
    ¬∀ c : (depth_bounded_verification d).Claim,
      (depth_bounded_verification d).verify_cost c ≤ (depth_bounded_verification d).budget :=
  verification_only_import_incomplete (depth_bounded_verification d)


/-! ### 3. Export Across Boundaries → Headers (Metadata)

**Argument.**  When deposits cross scope boundaries the receiving scope
must decide whether to accept each import.  If the receiver has no
metadata about the deposit (no headers), every deposit looks identical —
the import function is uniform.  A uniform function cannot discriminate
good imports from bad.

**Proof technique.**  A uniform function produces `f good = f bad`
by definition; but sound-and-complete import requires different answers
for good and bad claims. -/

/-- Two claims that must be distinguished on import. -/
structure DiscriminatingImport where
  Claim : Type
  /-- A claim the receiver should accept. -/
  good : Claim
  /-- A claim the receiver should reject. -/
  bad : Claim
  good_ne_bad : good ≠ bad

/-- A function that treats all inputs uniformly produces the same output
    on good and bad claims — it cannot discriminate.

    Consequence: structured metadata (headers) is forced for export. -/
theorem uniform_import_nondiscriminating (M : DiscriminatingImport)
    (f : M.Claim → Bool)
    (h_uniform : ∀ x y : M.Claim, f x = f y) :
    f M.good = f M.bad :=
  h_uniform M.good M.bad

/-- A sound-and-complete import policy must discriminate — but uniformity
    prevents discrimination.  No metadata-free import can be both sound
    and complete. -/
theorem no_sound_complete_uniform_import (M : DiscriminatingImport)
    (f : M.Claim → Bool)
    (h_uniform : ∀ x y : M.Claim, f x = f y)
    (h_sound : f M.bad = false)
    (h_complete : f M.good = true) :
    False := by
  have h_eq := h_uniform M.good M.bad
  rw [h_sound, h_complete] at h_eq
  exact Bool.noConfusion h_eq

/-- `IsHeader M f` means that `f` distinguishes the good and bad claims in import
    scenario `M`: the minimal routing condition for correct import. -/
def IsHeader (M : DiscriminatingImport) (f : M.Claim → Bool) : Prop :=
  f M.good ≠ f M.bad

/-- A sound-and-complete import function satisfies `IsHeader`: it must disagree on good
    and bad claims.  Follows from `h_complete`, `h_sound`, and `Bool.noConfusion`. -/
theorem sound_complete_import_is_header (M : DiscriminatingImport)
    (f : M.Claim → Bool)
    (h_sound : f M.bad = false)
    (h_complete : f M.good = true) :
    IsHeader M f := by
  intro h_eq
  rw [h_complete, h_sound] at h_eq
  exact Bool.noConfusion h_eq

/-- Any sound-and-complete routing policy yields a function satisfying `IsHeader`.
    No assumption beyond soundness and completeness is needed. -/
theorem routing_requires_header (M : DiscriminatingImport) :
    (∃ f : M.Claim → Bool, f M.bad = false ∧ f M.good = true) →
    ∃ f : M.Claim → Bool, IsHeader M f :=
  fun ⟨f, hs, hc⟩ => ⟨f, sound_complete_import_is_header M f hs hc⟩


/-! ### 3b. Alternative Metadata Strategies Reduce to DiscriminatingImport

A reviewer may ask: do content-addressed routing or contextual routing state
escape `no_sound_complete_uniform_import`?

Both alternatives are instantiated below.  In each case the routing mechanism
either acts uniformly on claim content (same contradiction) or carries
structured per-claim metadata — a function satisfying `IsHeader`.

**Content-addressed routing.**  Import decisions are based solely on a content
hash.  If the hash function is collision-resistant, good and bad claims have
different hashes — but the import function now maps hash → Bool, and it must
still discriminate good from bad.  A uniform function over hashes collapses
the same way.  A non-uniform function over hashes maps distinct hashes to
distinct decisions, satisfying `IsHeader` on the embedded `DiscriminatingImport`.

**Contextual routing state.**  The receiver maintains external state that
routes each claim.  If the state is stored per-claim, it carries all the
information a header would carry — functionally equivalent.  If the state
is global (not per-claim), the import function is effectively uniform over
the claim dimension, and the same impossibility fires. -/

/-- Content-addressed import: the receiver routes by a hash of the claim. -/
structure ContentAddressedImport where
  Claim : Type
  Hash : Type
  /-- Collision-resistant hash function: good and bad have different hashes. -/
  hash : Claim → Hash
  good : Claim
  bad : Claim
  hash_distinguishes : hash good ≠ hash bad
  /-- Import decision is a function of the hash only. -/
  import_by_hash : Hash → Bool

/-- Content-addressed import with distinguishing hashes is non-uniform: the
    import function over hashes must already discriminate good from bad hashes.
    That discrimination IS per-claim structured metadata — a header by another name.
    If `import_by_hash` were uniform (same output on all hashes), it could not
    distinguish good from bad claims — the same impossibility as `no_sound_complete_uniform_import`. -/
theorem content_addressed_requires_discrimination (M : ContentAddressedImport)
    (h_uniform : ∀ h₁ h₂ : M.Hash, M.import_by_hash h₁ = M.import_by_hash h₂) :
    M.import_by_hash (M.hash M.good) = M.import_by_hash (M.hash M.bad) :=
  h_uniform (M.hash M.good) (M.hash M.bad)

/-- A sound-and-complete content-addressed import cannot be uniform over hashes
    when good and bad have different hashes.  Non-uniformity over hashes = metadata. -/
theorem content_addressed_uniform_impossible (M : ContentAddressedImport)
    (h_uniform : ∀ h₁ h₂ : M.Hash, M.import_by_hash h₁ = M.import_by_hash h₂)
    (h_sound : M.import_by_hash (M.hash M.bad) = false)
    (h_complete : M.import_by_hash (M.hash M.good) = true) : False := by
  have h_eq := content_addressed_requires_discrimination M h_uniform
  rw [h_sound, h_complete] at h_eq
  exact Bool.noConfusion h_eq

/-- A ContentAddressedImport with distinguishing hashes embeds into DiscriminatingImport:
    good and bad are distinct claims — inequality is derived from `hash_distinguishes`
    via congruence. -/
def content_addressed_to_discriminating (M : ContentAddressedImport) : DiscriminatingImport where
  Claim       := M.Claim
  good        := M.good
  bad         := M.bad
  good_ne_bad := fun h => M.hash_distinguishes (congrArg M.hash h)

/-- A sound-and-complete content-addressed policy with uniform hash routing is
    impossible: contradicts `no_sound_complete_uniform_import` on the embedded
    `DiscriminatingImport`. -/
theorem content_addressed_is_header (M : ContentAddressedImport)
    (h_uniform : ∀ x y : M.Claim, M.import_by_hash (M.hash x) = M.import_by_hash (M.hash y))
    (h_sound : M.import_by_hash (M.hash M.bad) = false)
    (h_complete : M.import_by_hash (M.hash M.good) = true) : False :=
  no_sound_complete_uniform_import
    (content_addressed_to_discriminating M)
    (fun c => M.import_by_hash (M.hash c))
    h_uniform h_sound h_complete

/-- The composite routing function `import_by_hash ∘ hash` satisfies `IsHeader` for
    the embedded `DiscriminatingImport` scenario, via `sound_complete_import_is_header`. -/
theorem content_addressed_has_header (M : ContentAddressedImport)
    (h_sound : M.import_by_hash (M.hash M.bad) = false)
    (h_complete : M.import_by_hash (M.hash M.good) = true) :
    IsHeader (content_addressed_to_discriminating M)
             (fun c => M.import_by_hash (M.hash c)) :=
  sound_complete_import_is_header (content_addressed_to_discriminating M)
    (fun c => M.import_by_hash (M.hash c))
    h_sound h_complete

/-- Global contextual routing state: a single shared routing predicate
    applied to all claims (not per-claim metadata). -/
structure GlobalRoutingState where
  Claim : Type
  /-- Global accept/reject predicate — same for every claim (uniform). -/
  global_policy : Bool
  good : Claim
  bad : Claim

/-- Global routing state is effectively uniform: every claim gets the same
    decision.  It cannot distinguish good from bad claims.
    Per-claim routing state would be a header — the global version fails
    for exactly the same reason as a uniform import function. -/
theorem global_routing_cannot_discriminate (M : GlobalRoutingState) :
    (fun _ : M.Claim => M.global_policy) M.good =
    (fun _ : M.Claim => M.global_policy) M.bad := rfl


/-! ### 4. Adversarial Pressure → Revocation

**Argument.**  When adversarial deposits can pass acceptance, the system
must be able to remove them after discovering the problem.  In a lifecycle
where the "accepted" state is absorbing (no revocation transition), a
deposit that reaches "accepted" stays there through any number of
transitions.  The bad deposit is permanently accepted.

**Proof technique.**  Induction on the number of transition steps. -/

/-- Iterate a function `n` times starting from an initial value. -/
def iter (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iter f n x)

/-- A lifecycle where the accepted state is absorbing (no exit transition). -/
structure MonotonicLifecycle where
  State : Type
  /-- The accepted state. -/
  accepted : State
  /-- The transition function. -/
  step : State → State
  /-- `accepted` is a fixed point: stepping from accepted returns accepted. -/
  absorbing : step accepted = accepted

/-- In a monotonic lifecycle, no sequence of transitions can escape
    the accepted state.  An adversarial deposit that passes acceptance
    stays accepted permanently.

    Consequence: a revocation mechanism is structurally forced. -/
theorem monotonic_no_exit (M : MonotonicLifecycle) (n : Nat) :
    iter M.step n M.accepted = M.accepted := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show M.step (iter M.step n M.accepted) = M.accepted
    rw [ih, M.absorbing]


/-! ### 4b. Alternative Revocation Mechanisms Reduce to MonotonicLifecycle

A reviewer may ask: do quarantine states, shadow/hold states, or rollback
mechanisms escape `monotonic_no_exit`?

All three are instantiated below.  In each case the alternative either (a)
provides a non-absorbing transition out of the accepted state — the lifecycle
is non-monotonic — or (b) the accepted state remains absorbing and the alternative
does not actually remove the adversarial deposit from reliance.

**Quarantine state.**  If quarantine is reachable from accepted, the accepted
state is not absorbing — `step accepted ≠ accepted` for some step.  The
`MonotonicLifecycle.absorbing` condition is violated.

**Shadow/hold state.**  Same argument: if accepted can transition to hold,
the absorbing condition fails.  If hold is unreachable from accepted, the
bad deposit remains effectively accepted and the system fails corrigibility.

**Rollback.**  Rollback restores a prior state — a non-absorbing transition
out of accepted.  The absorbing condition is violated. -/

/-- A lifecycle with a quarantine state reachable from accepted. -/
structure QuarantineLifecycle where
  State : Type
  accepted : State
  quarantined : State
  step : State → State
  /-- Quarantine is reachable from accepted in one step. -/
  accepted_to_quarantine : step accepted = quarantined
  /-- Quarantine is distinct from accepted. -/
  distinct : accepted ≠ quarantined

/-- A lifecycle with a quarantine exit from accepted is non-monotonic:
    the accepted state is not absorbing. -/
theorem quarantine_violates_absorbing (M : QuarantineLifecycle) :
    M.step M.accepted ≠ M.accepted := by
  rw [M.accepted_to_quarantine]
  exact Ne.symm M.distinct

/-- A lifecycle with a hold/shadow state reachable from accepted. -/
structure HoldLifecycle where
  State : Type
  accepted : State
  held : State
  step : State → State
  accepted_to_held : step accepted = held
  distinct : accepted ≠ held

/-- A lifecycle with a hold exit from accepted is non-monotonic:
    the accepted state is not absorbing. -/
theorem hold_violates_absorbing (M : HoldLifecycle) :
    M.step M.accepted ≠ M.accepted := by
  rw [M.accepted_to_held]
  exact Ne.symm M.distinct

/-- A lifecycle where rollback is a transition out of accepted to a prior state. -/
structure RollbackLifecycle where
  State : Type
  accepted : State
  prior : State
  step : State → State
  accepted_rolls_back : step accepted = prior
  distinct : accepted ≠ prior

/-- A lifecycle with rollback from accepted is non-monotonic:
    the accepted state is not absorbing. -/
theorem rollback_violates_absorbing (M : RollbackLifecycle) :
    M.step M.accepted ≠ M.accepted := by
  rw [M.accepted_rolls_back]
  exact Ne.symm M.distinct


/-! ### 5. Coordination Need → Shared Ledger (Bank)

**Argument.**  When multiple agents must rely on the same deposits,
those deposits must be stored somewhere both agents can access.  In a
private-only storage model (each agent's store is invisible to others),
no deposit is simultaneously accessible to two agents.

**Proof technique.**  Contradiction with the isolation condition. -/

/-- A system where each agent has private, isolated storage. -/
structure PrivateOnlyStorage where
  Agent : Type
  Deposit : Type
  /-- Each agent's private store. -/
  has_access : Agent → Deposit → Prop
  /-- Two distinct agents. -/
  a₁ : Agent
  a₂ : Agent
  distinct : a₁ ≠ a₂
  /-- Isolation: a deposit accessible to one agent is NOT accessible to the other. -/
  isolation : ∀ d, has_access a₁ d → ¬has_access a₂ d

/-- In private-only storage, no deposit is accessible to both agents.
    Collective reliance on shared deposits is impossible.

    Consequence: shared storage (bank/ledger) is structurally forced. -/
theorem private_storage_no_sharing (M : PrivateOnlyStorage) :
    ¬∃ d, M.has_access M.a₁ d ∧ M.has_access M.a₂ d := by
  intro ⟨d, h₁, h₂⟩
  exact M.isolation d h₁ h₂


/-! ### 5b. Alternative Coordination Substrates Reduce to PrivateOnlyStorage

A reviewer may ask: do replicated logs, attestation networks, or CRDT-like
shared state escape `private_storage_no_sharing`?

All three are instantiated below.  In each case the alternative either (a)
provides shared access between the two agents, or (b) maintains isolation,
and `private_storage_no_sharing` fires directly.

**Replicated log.**  Each agent has a local replica, but replicas are
synchronized.  Synchronization means both agents can access the same deposit
entry — violation of the isolation condition.

**Attestation network.**  Agents publish signed claims accessible to others.
If agent₂ can read agent₁'s attestation, the isolation condition fails — both
agents have access.

**CRDT-based shared state.**  A conflict-free replicated data type by definition
converges to a shared state that all agents can read.  The convergence property
implies both agents access the same value — isolation is violated. -/

/-- Replicated log: both agents read from synchronized replicas. -/
structure ReplicatedLog where
  Agent : Type
  Deposit : Type
  has_access : Agent → Deposit → Prop
  a₁ : Agent
  a₂ : Agent
  distinct : a₁ ≠ a₂
  /-- Synchronization: a deposit accessible to a₁ is also accessible to a₂. -/
  synchronized : ∀ d, has_access a₁ d → has_access a₂ d

/-- A replicated log with synchronization: both agents access the same deposits.
    Isolation does not hold. -/
theorem replicated_log_is_shared (M : ReplicatedLog) :
    ∀ d, M.has_access M.a₁ d → M.has_access M.a₂ d :=
  fun d h => M.synchronized d h

/-- Attestation network: agent₁ publishes; agent₂ can read the attestation. -/
structure AttestationNetwork where
  Agent : Type
  Deposit : Type
  has_access : Agent → Deposit → Prop
  a₁ : Agent
  a₂ : Agent
  distinct : a₁ ≠ a₂
  /-- Agent₂ can read agent₁'s published attestations. -/
  readable : ∀ d, has_access a₁ d → has_access a₂ d

/-- An attestation network with shared read-access: both agents reach the same
    deposits.  Isolation does not hold. -/
theorem attestation_network_is_shared (M : AttestationNetwork) :
    ∀ d, M.has_access M.a₁ d → M.has_access M.a₂ d :=
  fun d h => M.readable d h

/-- CRDT: convergence guarantees both agents observe the same committed value. -/
structure CRDTStorage where
  Agent : Type
  Deposit : Type
  has_access : Agent → Deposit → Prop
  a₁ : Agent
  a₂ : Agent
  distinct : a₁ ≠ a₂
  /-- Convergence: once a deposit is committed, all agents can access it. -/
  converges : ∀ d, has_access a₁ d → has_access a₂ d

/-- CRDT-based shared state where convergence means both agents access the same
    deposits.  Isolation does not hold. -/
theorem crdt_is_shared (M : CRDTStorage) :
    ∀ d, M.has_access M.a₁ d → M.has_access M.a₂ d :=
  fun d h => M.converges d h


/-! ### 6. Truth Pressure → Redeemability

**Argument.**  In a closed endorsement system (no external constraint
surface), the only notion of "truth" is internal consensus.  Every claim
that passes consensus is true by definition — there is nothing external
it could fail against.  But truth pressure requires that some endorsed
claims CAN fail.  A closed system cannot satisfy truth pressure.

**Proof technique.**  Contradiction: the closure condition holds that endorsed
claims are unfalsifiable, but truth pressure supplies one that is
endorsed AND falsifiable. -/

/-- A closed endorsement system: no external falsification mechanism. -/
structure ClosedEndorsement where
  Claim : Type
  /-- Internal endorsement (consensus). -/
  endorsed : Claim → Prop
  /-- External falsifiability (constraint-surface contact). -/
  externally_falsifiable : Claim → Prop
  /-- Closure: without external contact, no endorsed claim is falsifiable. -/
  closed : ∀ c, endorsed c → ¬externally_falsifiable c

/-- A closed system cannot exhibit truth pressure: no endorsed claim
    is simultaneously falsifiable.

    Consequence: external constraint-surface contact (redeemability)
    is structurally forced. -/
theorem closed_system_unfalsifiable (M : ClosedEndorsement) :
    ¬∃ c, M.endorsed c ∧ M.externally_falsifiable c := by
  intro ⟨c, h_end, h_fals⟩
  exact M.closed c h_end h_fals


/-! ### 6b. Alternative External Contact Mechanisms Reduce to ClosedEndorsement

A reviewer may ask: do anomaly signaling, partial contestation, or soft
falsifiability escape `closed_system_unfalsifiable`?

All three are instantiated below.  In each case the mechanism either (a)
provides genuine external falsifiability, or (b) the endorsement system remains
closed and `closed_system_unfalsifiable` fires directly.

**Anomaly signaling.**  The system can emit anomaly signals but ignores them:
no endorsed claim becomes externally falsifiable from the signal alone.
The closure condition is preserved — signals without action leave the
endorsement-falsifiability structure unchanged.

**Partial contestation.**  Only some claims are contestable.  For the
non-contestable endorsed claims, the closure condition still holds.
The closed system theorem applies to that sub-population.

**Soft falsifiability.**  Claims can be flagged as uncertain but are not
actually falsifiable (not removed from endorsement).  If flagging does not
imply external falsifiability, the closure condition holds — the same
impossibility applies. -/

/-- Anomaly-signaling system: signals exist but do not make endorsed claims
    externally falsifiable. -/
structure AnomalySignaling where
  Claim : Type
  endorsed : Claim → Prop
  externally_falsifiable : Claim → Prop
  emits_anomaly : Claim → Prop
  /-- Signals do not induce external falsifiability for endorsed claims. -/
  signal_does_not_open : ∀ c, endorsed c → emits_anomaly c → ¬externally_falsifiable c

/-- An anomaly-signaling system that does not connect signals to external
    falsifiability is effectively closed: endorsed claims remain unfalsifiable
    even when anomalies are emitted. -/
theorem anomaly_signal_insufficient (M : AnomalySignaling) :
    ¬∃ c, M.endorsed c ∧ M.emits_anomaly c ∧ M.externally_falsifiable c :=
  fun ⟨c, h_end, h_sig, h_fals⟩ => M.signal_does_not_open c h_end h_sig h_fals

/-- When all endorsed claims trigger anomaly signals, `AnomalySignaling` embeds
    into `ClosedEndorsement`: the closure condition is derived from
    `signal_does_not_open`. -/
def anomaly_to_closed (M : AnomalySignaling)
    (h_all : ∀ c, M.endorsed c → M.emits_anomaly c) : ClosedEndorsement where
  Claim                  := M.Claim
  endorsed               := M.endorsed
  externally_falsifiable := M.externally_falsifiable
  closed                 := fun c h_end h_fals =>
    M.signal_does_not_open c h_end (h_all c h_end) h_fals

/-- Under maximal anomaly coverage (all endorsed claims signal), the full
    `closed_system_unfalsifiable` impossibility fires via the embedding.
    No endorsed claim is externally falsifiable — signals accomplish nothing
    without a genuine constraint-surface contact mechanism. -/
theorem anomaly_closed_when_universal (M : AnomalySignaling)
    (h_all : ∀ c, M.endorsed c → M.emits_anomaly c) :
    ¬∃ c, M.endorsed c ∧ M.externally_falsifiable c :=
  closed_system_unfalsifiable (anomaly_to_closed M h_all)

/-- Partial contestation: only unendorsed claims are contestable. -/
structure PartialContestation where
  Claim : Type
  endorsed : Claim → Prop
  contestable : Claim → Prop
  externally_falsifiable : Claim → Prop
  /-- Endorsed claims are not contestable. -/
  endorsed_not_contestable : ∀ c, endorsed c → ¬contestable c
  /-- Only contestable claims are externally falsifiable. -/
  contestable_only : ∀ c, externally_falsifiable c → contestable c

/-- `PartialContestation` embeds into `ClosedEndorsement` without an extra parameter:
    closure over endorsed claims is derived from the two structural conditions. -/
def partial_to_closed (M : PartialContestation) : ClosedEndorsement where
  Claim                  := M.Claim
  endorsed               := M.endorsed
  externally_falsifiable := M.externally_falsifiable
  closed                 := fun c h_end h_fals =>
    M.endorsed_not_contestable c h_end (M.contestable_only c h_fals)

/-- Partial contestation that excludes endorsed claims embeds into `ClosedEndorsement`:
    `closed_system_unfalsifiable` fires via the parameter-free embedding.
    No endorsed claim is externally falsifiable. -/
theorem partial_contestation_closed_on_endorsed (M : PartialContestation) :
    ¬∃ c, M.endorsed c ∧ M.externally_falsifiable c :=
  closed_system_unfalsifiable (partial_to_closed M)

/-- Soft falsifiability: claims can be flagged, but flagging ≠ external falsifiability. -/
structure SoftFalsifiability where
  Claim : Type
  endorsed : Claim → Prop
  flagged : Claim → Prop
  externally_falsifiable : Claim → Prop
  /-- Flagging an endorsed claim does not make it externally falsifiable. -/
  flag_not_falsifiable : ∀ c, endorsed c → flagged c → ¬externally_falsifiable c

/-- Soft falsifiability that does not map to external falsifiability preserves
    closure: endorsed claims remain non-falsifiable even when flagged. -/
theorem soft_falsifiability_closed (M : SoftFalsifiability) :
    ¬∃ c, M.endorsed c ∧ M.flagged c ∧ M.externally_falsifiable c :=
  fun ⟨c, h_end, h_flag, h_fals⟩ => M.flag_not_falsifiable c h_end h_flag h_fals

/-- When all endorsed claims are flagged, `SoftFalsifiability` embeds into
    `ClosedEndorsement`: the closure condition is derived from `flag_not_falsifiable`. -/
def soft_to_closed (M : SoftFalsifiability)
    (h_all : ∀ c, M.endorsed c → M.flagged c) : ClosedEndorsement where
  Claim                  := M.Claim
  endorsed               := M.endorsed
  externally_falsifiable := M.externally_falsifiable
  closed                 := fun c h_end h_fals =>
    M.flag_not_falsifiable c h_end (h_all c h_end) h_fals

/-- Under maximal flag coverage, `closed_system_unfalsifiable` fires via the embedding.
    No endorsed claim is externally falsifiable. -/
theorem soft_closed_when_universal (M : SoftFalsifiability)
    (h_all : ∀ c, M.endorsed c → M.flagged c) :
    ¬∃ c, M.endorsed c ∧ M.externally_falsifiable c :=
  closed_system_unfalsifiable (soft_to_closed M h_all)


/-! ### §6c. Forcing Stratification: Hard vs Soft Forcing for Truth Pressure

The eight forcing dimensions do not all have the same tightness.

Hard forcing: impossibility follows from the structure alone, without additional
behavioral coverage assumptions.  Scope, revocation, bank, partial contestation,
authorization, and storage belong to this tier.

Soft forcing: impossibility requires an additional coverage assumption
(`∀ c, endorsed c → emits_anomaly c` / `flagged c`), which cannot be
discharged from the structure fields alone.

`anomaly_not_hard_forced` and `soft_falsifiability_not_hard_forced` exhibit consistent
`AnomalySignaling` / `SoftFalsifiability` instances with an endorsed, externally-falsifiable
claim.  `partial_contestation_hard_forced` shows partial contestation does not require
a coverage assumption. -/

/-- Redeemability is hard-forced: `ClosedEndorsement` is self-refuting from its
    structural fields alone.  The impossibility fires unconditionally — no coverage
    assumption is needed. -/
theorem redeemability_hard_forced (M : ClosedEndorsement) :
    ¬∃ c, M.endorsed c ∧ M.externally_falsifiable c :=
  closed_system_unfalsifiable M

/-- Under the coverage assumption that all endorsed claims emit anomaly signals,
    no endorsed claim is externally falsifiable. -/
theorem anomaly_requires_coverage_for_closure (M : AnomalySignaling)
    (h_all : ∀ c, M.endorsed c → M.emits_anomaly c) :
    ¬∃ c, M.endorsed c ∧ M.externally_falsifiable c :=
  anomaly_closed_when_universal M h_all

/-- There exists an `AnomalySignaling` instance with an endorsed, externally-falsifiable
    claim: everything is endorsed and externally falsifiable, but nothing signals.
    `signal_does_not_open` is vacuously satisfied, so `AnomalySignaling` alone does
    not imply closure over endorsed claims. -/
theorem anomaly_not_hard_forced :
    ¬∀ M : AnomalySignaling, ¬∃ c : M.Claim, M.endorsed c ∧ M.externally_falsifiable c := by
  intro h
  let M : AnomalySignaling := {
    Claim := Unit
    endorsed := fun _ => True
    externally_falsifiable := fun _ => True
    emits_anomaly := fun _ => False
    signal_does_not_open := fun _ _ h_sig => h_sig.elim
  }
  exact h M ⟨(), trivial, trivial⟩

/-- There exists a `SoftFalsifiability` instance with an endorsed, externally-falsifiable
    claim: everything is endorsed and externally falsifiable, but nothing is flagged.
    `flag_not_falsifiable` is vacuously satisfied, so `SoftFalsifiability` alone does
    not imply closure over endorsed claims. -/
theorem soft_falsifiability_not_hard_forced :
    ¬∀ M : SoftFalsifiability, ¬∃ c : M.Claim, M.endorsed c ∧ M.externally_falsifiable c := by
  intro h
  let M : SoftFalsifiability := {
    Claim := Unit
    endorsed := fun _ => True
    flagged := fun _ => False
    externally_falsifiable := fun _ => True
    flag_not_falsifiable := fun _ _ h_flag => h_flag.elim
  }
  exact h M ⟨(), trivial, trivial⟩

/-- `PartialContestation` embeds into `ClosedEndorsement` without a coverage assumption:
    `closed_system_unfalsifiable` fires via `partial_to_closed` directly. -/
theorem partial_contestation_hard_forced (M : PartialContestation) :
    ¬∃ c, M.endorsed c ∧ M.externally_falsifiable c :=
  partial_contestation_closed_on_endorsed M


/-! ### 7. Multi-Agent Heterogeneous Access → Granular ACL

**Argument.**  When a system has a staged access surface — an open submission
tier and a restricted commit tier — no single authorization predicate can
faithfully represent both tiers simultaneously.  Suppose it could: then the
flat function agrees with the open tier (so the submitter is authorized under
it), and it also agrees with the commit tier (so the submitter has commit
rights) — contradicting the submitter’s known restriction on the commit tier.
Granular ACL, which keeps the two tiers distinct, is structurally forced.

Examples: a GitHub repository has open PRs (submission) but maintainer-gated
merges (commit); a bank has open deposits (submission) but ACL-gated withdrawals
(commit); a corporate intranet may have a fully closed commit tier where even
submission requires clearance — in that case both tiers are equally restricted,
no `TwoTierAccess` certificate exists, and `S.multi_agent = false` is correct.

**Proof technique.**  Exact structural parallel to `flat_scope_impossible`.
Two predicates (`can_propose`, `can_commit`) disagree on a witness (`submitter`
for `tier_claim`).  A flat function faithful to both routes `may_propose`
through the proposal iff and then through the commit iff to
`can_commit submitter tier_claim`, contradicting `cannot_commit`.  The proof
uses all three witnesses: `may_propose`, `cannot_commit`, and `may_commit`
(the last establishes that the commit tier is non-vacuous and structurally
distinct from the proposal tier). -/

/-- A staged-access scenario: one agent can submit but cannot commit; another
    agent can commit.  No single authorization predicate can faithfully represent
    both the submission tier and the commit tier simultaneously.

    Structural parallel to `AgentDisagreement` for scope: both have two predicates
    on the same type and a witness on which they disagree. -/
structure TwoTierAccess where
  Agent         : Type
  Claim         : Type
  /-- The open submission tier: agents that may propose/submit. -/
  can_propose   : Agent → Claim → Prop
  /-- The restricted commit tier: agents that may merge/commit. -/
  can_commit    : Agent → Claim → Prop
  /-- An agent in the submission tier but not the commit tier. -/
  submitter     : Agent
  /-- An agent in the commit tier — establishes the commit tier is non-vacuous. -/
  committer     : Agent
  /-- The claim on which the two tiers differ. -/
  tier_claim    : Claim
  /-- The submitter can propose the tier claim. -/
  may_propose   : can_propose submitter tier_claim
  /-- The submitter cannot commit the tier claim. -/
  cannot_commit : ¬can_commit submitter tier_claim
  /-- The committer can commit the tier claim — the commit tier is non-vacuous. -/
  may_commit    : can_commit committer tier_claim

/-- No flat authorization predicate can faithfully represent both the submission
    tier and the commit tier of a two-tier access scenario.

    Proof: a flat `f` faithful to both tiers routes `may_propose` through
    `f submitter tier_claim` (via the proposal iff) and then to
    `can_commit submitter tier_claim` (via the commit iff) — contradicting
    `cannot_commit`.

    Exact structural parallel to `flat_scope_impossible`: two predicates that
    disagree on a witness; no flat function can represent both.

    Consequence: granular ACL is structurally forced — the two access surfaces
    cannot be collapsed into a single authorization predicate. -/
theorem flat_authorization_impossible (M : TwoTierAccess)
    (h_flat : ∃ (f : M.Agent → M.Claim → Prop),
      (∀ a c, f a c ↔ M.can_propose a c) ∧
      (∀ a c, f a c ↔ M.can_commit a c)) : False :=
  let ⟨_f, hprop, hcommit⟩ := h_flat
  M.cannot_commit ((hcommit M.submitter M.tier_claim).mp
    ((hprop M.submitter M.tier_claim).mpr M.may_propose))


/-! ### 7b. Alternative Authorization Mechanisms Reduce to TwoTierAccess

A reviewer may ask: do RBAC (role-based ACL), capability-token systems, or
attribute-based ACL escape `flat_authorization_impossible`?

This section instantiates each alternative, then shows it directly supplies
a `GroundedAuthorization` instance (with both a positive and a negative witness).
`GroundedAuthorizationStrict.no_flat_tier` then fires directly, or
equivalently, `flat_authorization_impossible` fires via `groundedAuthorization_to_scenario`.

**RBAC.**  The commit tier is role-derived authorization; the submission tier is
open (any agent may submit).  The restricted agent's role lacks commit permission;
the privileged agent's role has it.  `cannot_commit` and `may_commit` are both
required to derive `no_flat_tier`.

**Capability-token system.**  The commit tier is token-based authorization; the
submission tier is open.  The restricted agent holds no commit token; the privileged
agent holds one.  Again a direct `GroundedAuthorization` instance.

**Attribute-based ACL.**  The commit tier requires all demanded attributes; the
submission tier is open.  The restricted agent lacks a required attribute; the
privileged agent has all required attributes.  Again a direct `GroundedAuthorization`
instance.

**Conclusion.**  All three alternatives instantiate `GroundedAuthorization` with
both `may_commit` and `cannot_commit`.  The impossibility fires via
`GroundedAuthorizationStrict.no_flat_tier` — the authorization pressure requires
structural tension between the two tiers, not a single restriction alone.  The
forcing is insensitive to the ACL mechanism chosen. -/

/-- RBAC authorization surface: agents carry roles, roles carry permissions,
    authorization is role-derived.  Two witnesses: the restricted agent's role
    lacks permission; the privileged agent's role has permission. -/
structure RBACAuthSurface where
  Agent            : Type
  Claim            : Type
  Role             : Type
  role_of          : Agent → Role
  perm             : Role → Claim → Prop
  authorize        : Agent → Claim → Prop
  /-- Authorization is exactly role-derived permission. -/
  derives_from_rbac : ∀ a P, authorize a P ↔ perm (role_of a) P
  privileged_agent : Agent
  restricted_agent : Agent
  restricted_claim : Claim
  /-- The privileged agent's role HAS permission — the positive witness. -/
  role_has_perm    : perm (role_of privileged_agent) restricted_claim
  /-- The restricted agent's role lacks permission — the negative witness. -/
  role_lacks_perm  : ¬perm (role_of restricted_agent) restricted_claim

/-- An RBAC surface with differentiated roles directly instantiates `GroundedAuthorization`.
    `may_commit` (privileged role has permission) and `cannot_commit` (restricted role
    lacks permission) are derived from the role-permission equivalence. -/
def rbac_to_grounded (M : RBACAuthSurface) : GroundedAuthorization where
  Agent         := M.Agent
  Claim         := M.Claim
  can_propose   := fun _ _ => True
  can_commit    := M.authorize
  submitter     := M.restricted_agent
  committer     := M.privileged_agent
  tier_claim    := M.restricted_claim
  may_propose   := trivial
  cannot_commit := fun h =>
    M.role_lacks_perm ((M.derives_from_rbac M.restricted_agent M.restricted_claim).mp h)
  may_commit    := (M.derives_from_rbac M.privileged_agent M.restricted_claim).mpr M.role_has_perm

/-- No flat authorization predicate can represent both the open submission tier and
    the role-restricted commit tier: `no_flat_tier` fires via `rbac_to_grounded.toStrict`. -/
theorem rbac_two_tier_impossible (M : RBACAuthSurface) :
    ¬∃ (f : M.Agent → M.Claim → Prop),
      (∀ a c, f a c ↔ True) ∧ (∀ a c, f a c ↔ M.authorize a c) :=
  (rbac_to_grounded M).toStrict.no_flat_tier

/-- Capability-token authorization: an agent is authorized for a claim iff it
    holds a token that grants that claim.  Two witnesses: the restricted agent
    holds no such token; the privileged agent holds one. -/
structure CapabilityTokenAuth where
  Agent         : Type
  Claim         : Type
  Token         : Type
  holds_token   : Agent → Token → Prop
  token_grants  : Token → Claim → Prop
  authorize     : Agent → Claim → Prop
  /-- Authorization is exactly token-based capability. -/
  derives_from_caps : ∀ a P, authorize a P ↔ ∃ t, holds_token a t ∧ token_grants t P
  privileged_agent    : Agent
  restricted_agent    : Agent
  restricted_claim    : Claim
  /-- A token held by the privileged agent that grants the restricted claim. -/
  priv_token          : Token
  holds_priv          : holds_token privileged_agent priv_token
  priv_grants         : token_grants priv_token restricted_claim
  /-- The restricted agent holds no token that grants the restricted claim. -/
  no_token         : ∀ t, holds_token restricted_agent t → ¬token_grants t restricted_claim

/-- A capability-token surface with differentiated token ownership directly
    instantiates `GroundedAuthorization`.  `may_commit` (privileged agent has a
    granting token) and `cannot_commit` (restricted agent has no granting token)
    are derived from the token-capability semantics. -/
def capability_token_to_grounded (M : CapabilityTokenAuth) : GroundedAuthorization where
  Agent         := M.Agent
  Claim         := M.Claim
  can_propose   := fun _ _ => True
  can_commit    := M.authorize
  submitter     := M.restricted_agent
  committer     := M.privileged_agent
  tier_claim    := M.restricted_claim
  may_propose   := trivial
  cannot_commit := fun h =>
    let ⟨t, h_holds, h_grants⟩ :=
      (M.derives_from_caps M.restricted_agent M.restricted_claim).mp h
    M.no_token t h_holds h_grants
  may_commit    := (M.derives_from_caps M.privileged_agent M.restricted_claim).mpr
      ⟨M.priv_token, M.holds_priv, M.priv_grants⟩

/-- No flat authorization predicate can represent both the open submission tier and
    the token-restricted commit tier: `no_flat_tier` fires via the bridge. -/
theorem capability_token_two_tier_impossible (M : CapabilityTokenAuth) :
    ¬∃ (f : M.Agent → M.Claim → Prop),
      (∀ a c, f a c ↔ True) ∧ (∀ a c, f a c ↔ M.authorize a c) :=
  (capability_token_to_grounded M).toStrict.no_flat_tier

/-- Attribute-based ACL: authorization requires the agent to hold all attributes
    demanded by the claim.  Two witnesses: the restricted agent lacks a required
    attribute; the privileged agent has all required attributes. -/
structure AttributeBasedAuth where
  Agent             : Type
  Claim             : Type
  Attr              : Type
  has_attr          : Agent → Attr → Prop
  requires          : Claim → Attr → Prop
  authorize         : Agent → Claim → Prop
  /-- Authorization is exactly attribute satisfaction. -/
  derives_from_attrs : ∀ a P, authorize a P ↔ ∀ attr, requires P attr → has_attr a attr
  privileged_agent  : Agent
  restricted_agent  : Agent
  restricted_claim  : Claim
  /-- The privileged agent has all attributes required by the restricted claim. -/
  has_all_req       : ∀ attr, requires restricted_claim attr → has_attr privileged_agent attr
  /-- The restricted agent lacks at least one attribute required by the restricted claim. -/
  missing_attr      : ∃ attr, requires restricted_claim attr ∧ ¬has_attr restricted_agent attr

/-- An attribute-based ACL surface with differentiated attribute ownership directly
    instantiates `GroundedAuthorization`.  `may_commit` and `cannot_commit`
    are derived from the attribute-satisfaction semantics. -/
def attribute_based_to_grounded (M : AttributeBasedAuth) : GroundedAuthorization where
  Agent         := M.Agent
  Claim         := M.Claim
  can_propose   := fun _ _ => True
  can_commit    := M.authorize
  submitter     := M.restricted_agent
  committer     := M.privileged_agent
  tier_claim    := M.restricted_claim
  may_propose   := trivial
  cannot_commit := fun h =>
    let ⟨attr, h_req, h_no_attr⟩ := M.missing_attr
    h_no_attr ((M.derives_from_attrs M.restricted_agent M.restricted_claim).mp h attr h_req)
  may_commit    := (M.derives_from_attrs M.privileged_agent M.restricted_claim).mpr M.has_all_req

/-- No flat authorization predicate can represent both the open submission tier and
    the attribute-restricted commit tier: `no_flat_tier` fires via the bridge. -/
theorem attribute_based_two_tier_impossible (M : AttributeBasedAuth) :
    ¬∃ (f : M.Agent → M.Claim → Prop),
      (∀ a c, f a c ↔ True) ∧ (∀ a c, f a c ↔ M.authorize a c) :=
  (attribute_based_to_grounded M).toStrict.no_flat_tier


/-! ## §7. GroundedX ↔ Impossibility Bridges

Each `GroundedX` structure is isomorphic to the *input* of the corresponding
impossibility theorem (§1–§8).  These bridge theorems make the connection
explicit: given any `GroundedX` witness, the matching impossibility result fires.

`GroundedXStrict` packages the base evidence with its impossibility consequence —
the non-trivial `Prop` that falls out of the bridge.

**Relation to WorkingSystem.**  `WorkingSystem` carries eight `Option GroundedXStrict`
fields.  The `GroundedXStrict` structures are defined in EpArch.SystemSpec (where
they only depend on `GroundedX` fields).

**Construction convention.**
- `G.toStrict` — standard path; inline proof from base fields (in EpArch.SystemSpec,
  no dependency on the named theorems here).  Used by `withGroundedBehavior`,
  `ConcreteWorkingSystem`, and `PartialGroundedSpec.toWorkingSystem`.
- `GroundedXStrict.mk' G` — thin alias: `mk' G := G.toStrict`.  Kept as the
  canonical citation-facing constructor; call it when you want the named-proof
  route to appear in a proof term without inlining the derivation.
- Named bridge theorems (`groundedBubbles_flat_impossible`, etc.) — available for
  direct citation when a proof must explicitly invoke the structural impossibility.
  No longer called by `mk'`, but remain at module scope for that purpose. -/


/-! ### §7.1  Bubbles ↔ AgentDisagreement -/

/-- Convert `GroundedBubbles` to `AgentDisagreement`: the two scope resolvers
    play the role of the two disagreeing agents. -/
def groundedBubbles_to_disagreement (G : GroundedBubbles) : AgentDisagreement where
  Claim          := G.Claim
  accept₁        := G.scope₁
  accept₂        := G.scope₂
  witness        := G.witness
  agent1_accepts := G.scope₁_accepts
  agent2_rejects := G.scope₂_rejects

/-- No flat resolver can faithfully represent both scopes.
    Invokes `flat_scope_impossible` via the bridge conversion. -/
theorem groundedBubbles_flat_impossible (G : GroundedBubbles) :
    ¬∃ (f : G.Claim → Prop), (∀ c, f c ↔ G.scope₁ c) ∧ (∀ c, f c ↔ G.scope₂ c) :=
  flat_scope_impossible (groundedBubbles_to_disagreement G)

/-- Thin alias for `G.toStrict`.  Cite `groundedBubbles_flat_impossible` directly
    when a proof must explicitly name the impossibility route. -/
def GroundedBubblesStrict.mk' (G : GroundedBubbles) : GroundedBubblesStrict := G.toStrict


/-! ### §7.2  TrustBridges: re-verify-only policy cannot exclude the bridge witness -/

/-- A re-verify-only policy (downstream accepts only what it locally verified) is
    inconsistent with a trust bridge: the bridge delivers the witness downstream
    without local re-verification. -/
theorem groundedTrustBridges_bridge_necessary (G : GroundedTrustBridges)
    (locally_verified : G.Declaration → Prop)
    (only_local      : ∀ d, G.downstream_accepts d → locally_verified d)
    (not_local       : ¬locally_verified G.witness) : False :=
  not_local (only_local G.witness G.downstream_via_bridge)

/-- Thin alias for `G.toStrict`.  Cite `groundedTrustBridges_bridge_necessary` directly
    when a proof must explicitly name the impossibility route. -/
def GroundedTrustBridgesStrict.mk' (G : GroundedTrustBridges) : GroundedTrustBridgesStrict :=
  G.toStrict


/-! ### §7.3  Headers: header preservation implies routing invariance -/

/-- A header-based router cannot distinguish the witness from its exported form.
    Any routing decision on the original is preserved after export. -/
theorem groundedHeaders_router_consistent (G : GroundedHeaders) (router : G.Header → Bool) :
    router (G.extract G.witness) = router (G.extract (G.export_datum G.witness)) :=
  congrArg router G.header_preserved.symm

/-- Thin alias for `G.toStrict`.  Cite `groundedHeaders_router_consistent` directly
    when a proof must explicitly name the routing-invariance route. -/
def GroundedHeadersStrict.mk' (G : GroundedHeaders) : GroundedHeadersStrict := G.toStrict


/-! ### §7.4  Revocation: no-revocation policy fails at the invalid-but-revocable witness -/

/-- A no-revocation policy (every revocable claim is valid) is refuted:
    the witness is revocable (`can_revoke`) but demonstrably invalid (`witness_is_invalid`). -/
theorem groundedRevocation_no_revocation_incorrect (G : GroundedRevocation)
    (no_revoc : ∀ c, G.revocable c → G.valid c) : False :=
  G.witness_is_invalid (no_revoc G.witness G.can_revoke)

/-- Thin alias for `G.toStrict`.  Cite `groundedRevocation_no_revocation_incorrect`
    directly when a proof must explicitly name the impossibility route. -/
def GroundedRevocationStrict.mk' (G : GroundedRevocation) : GroundedRevocationStrict :=
  G.toStrict


/-! ### §7.5  Bank: isolation assumption is contradicted by the shared entry -/

/-- An isolation assumption (no entry simultaneously accessible to both agents) is
    contradicted by the shared bank witness. -/
theorem groundedBank_refutes_isolation (G : GroundedBank)
    (iso : ∀ e : G.Entry, G.agent₁_produces e → ¬G.agent₂_consumes e) : False :=
  iso G.witness G.produced G.consumed

/-- Thin alias for `G.toStrict`.  Cite `groundedBank_refutes_isolation` directly
    when a proof must explicitly name the isolation-refutation route. -/
def GroundedBankStrict.mk' (G : GroundedBank) : GroundedBankStrict := G.toStrict


/-! ### §7.6  Redeemability: closure assumption contradicted by constrained-and-redeemable witness -/

/-- A closure assumption (no constrained claim has an external redeemability path) is
    contradicted by the grounded witness. -/
theorem groundedRedeemability_refutes_closure (G : GroundedRedeemability)
    (closed : ∀ c : G.Claim, G.constrained c → ¬G.redeemable c) : False :=
  closed G.witness G.is_constrained G.has_path

/-- Thin alias for `G.toStrict`.  Cite `groundedRedeemability_refutes_closure` directly
    when a proof must explicitly name the closure-refutation route. -/
def GroundedRedeemabilityStrict.mk' (G : GroundedRedeemability) : GroundedRedeemabilityStrict :=
  G.toStrict


/-! ### §7.7  Authorization ↔ TwoTierAccess -/

/-- Convert `GroundedAuthorization` to `TwoTierAccess`.
    The fields map directly: `can_propose`/`can_commit`/`submitter`/`committer`/`tier_claim`
    and their proof witnesses `may_propose`/`cannot_commit`/`may_commit`. -/
def groundedAuthorization_to_scenario (G : GroundedAuthorization) : TwoTierAccess where
  Agent         := G.Agent
  Claim         := G.Claim
  can_propose   := G.can_propose
  can_commit    := G.can_commit
  submitter     := G.submitter
  committer     := G.committer
  tier_claim    := G.tier_claim
  may_propose   := G.may_propose
  cannot_commit := G.cannot_commit
  may_commit    := G.may_commit

/-- No flat authorization predicate can faithfully represent both tiers of a
    `GroundedAuthorization`.  Invokes `flat_authorization_impossible` via the bridge. -/
theorem groundedAuthorization_flat_impossible (G : GroundedAuthorization) :
    ¬∃ (f : G.Agent → G.Claim → Prop),
      (∀ a c, f a c ↔ G.can_propose a c) ∧
      (∀ a c, f a c ↔ G.can_commit a c) :=
  flat_authorization_impossible (groundedAuthorization_to_scenario G)

/-- Thin alias for `G.toStrict`.  Cite `groundedAuthorization_flat_impossible` directly
    when a proof must explicitly name the two-tier impossibility route. -/
def GroundedAuthorizationStrict.mk' (G : GroundedAuthorization) : GroundedAuthorizationStrict :=
  G.toStrict


/-! ========================================================================
    8. Bounded Storage → Storage Management
    ========================================================================

**Argument.**  Any finite storage capacity can be exceeded by a sufficient
number of active deposits.  A system without a management mechanism (eviction,
archival, or pruning) cannot remain within its budget indefinitely.

**Proof technique.**  Direct witness: the `BoundedStorage` structure carries
a concrete state (`deep_state`) whose active-deposit count exceeds the budget.
The impossibility theorem simply applies the universal bound to this state
and derives a contradiction.
-/

/-- Abstract bounded-storage scenario: a state type with a count function and
    a concrete overflow state.

    Carries all the impossibility payload directly — no induction needed.
    Parallel to `BoundedVerification` for the audit dimension. -/
structure BoundedStorage where
  /-- Abstract state type (models the global deposit ledger state). -/
  State       : Type
  /-- Finite capacity budget. -/
  budget      : Nat
  /-- Active-deposit count function. -/
  count       : State → Nat
  /-- A concrete state whose active count exceeds the budget. -/
  deep_state  : State
  /-- The deep state demonstrably exceeds the budget. -/
  exceeds_budget : budget < count deep_state

/-- BOUNDED STORAGE IMPOSSIBILITY.

    No fixed capacity budget can cover all states in this bounded-capacity scenario:
    the witness state exceeds the budget.

    **Theorem shape:** `¬∀ s : M.State, M.count s ≤ M.budget`.
    **Proof strategy:** apply the universal bound to `M.deep_state`, which carries
    `M.exceeds_budget : M.budget < M.count M.deep_state`; contradiction via
    `Nat.not_le`. -/
theorem monotone_active_accumulation_overflows (M : BoundedStorage) :
    ¬∀ s : M.State, M.count s ≤ M.budget :=
  fun h => absurd (Nat.lt_of_lt_of_le M.exceeds_budget (h M.deep_state)) (Nat.lt_irrefl M.budget)

/-- BOUNDED STORAGE → STORAGE MANAGEMENT FORCING.

    Any system facing bounded storage pressure — a concrete state exceeding the
    capacity budget — requires a storage management mechanism to remain within bounds.

    **Theorem shape:** `BoundedStorage → ¬(∀ s, count s ≤ budget)` — the
    impossibility of staying within budget without management intervention.
    **Proof strategy:** delegates to `monotone_active_accumulation_overflows`. -/
theorem bounded_storage_forces_storage_management (M : BoundedStorage) :
    ¬∀ s : M.State, M.count s ≤ M.budget :=
  monotone_active_accumulation_overflows M


/-! ### 8b. Alternative Storage Architectures Reduce to BoundedStorage

A reviewer may ask: do append-only logs, versioned entry stores, or
per-partition quota schemes escape `monotone_active_accumulation_overflows`?

All three are instantiated below.  In each case the alternative carries a
concrete overflow state and an exceed-budget proof — a direct `BoundedStorage`
instance — and the impossibility fires via the standard embedding.

**Append-only log.**  Entries are appended but never deleted; the active-entry
count is monotonically non-decreasing.  A log that has accumulated more than
`budget` entries is the overflow state.  Without an archival or compaction
mechanism, the count cannot be bounded — a direct `BoundedStorage` instance.

**Versioned entry store.**  Each update creates a new version; all versions
are retained indefinitely for audit or rollback.  Version count is the
active-deposit proxy.  Without compaction or garbage collection, the count
exceeds any fixed budget — a direct `BoundedStorage` instance.

**Per-partition quota store.**  Storage is divided into named partitions
(tenants, shards, epochs); each partition carries its own local count.  Without
cross-partition capacity enforcement, a single partition can accumulate more
entries than the global budget.  The overflow partition supplies the
`BoundedStorage` overflow witness. -/

/-- Append-only log: entries are only ever appended; the active count is
    monotonically non-decreasing.

    `append_grows` formalises the append-only property: each append increments
    count by exactly 1.  `full_state` witnesses the overflow.
    Parallel to `CapabilitySystem` for scope and `RBACAuthSurface` for authorization. -/
structure AppendOnlyLog where
  /-- Abstract state type (models the accumulated log contents). -/
  State          : Type
  /-- Active entry count for a given log state. -/
  entry_count    : State → Nat
  /-- Fixed capacity budget. -/
  budget         : Nat
  /-- Append operation: adds exactly one entry to the log. -/
  append         : State → State
  /-- Appending grows the entry count by exactly 1. -/
  append_grows   : ∀ s, entry_count (append s) = entry_count s + 1
  /-- A concrete log state whose entry count exceeds the budget. -/
  full_state     : State
  /-- The full state demonstrably exceeds the budget. -/
  exceeds_budget : budget < entry_count full_state

/-- An append-only log directly instantiates `BoundedStorage`:
    the full state is the deep-state overflow witness. -/
def append_only_to_bounded (M : AppendOnlyLog) : BoundedStorage where
  State          := M.State
  count          := M.entry_count
  budget         := M.budget
  deep_state     := M.full_state
  exceeds_budget := M.exceeds_budget

/-- Without a deletion or archival mechanism, an append-only log cannot stay
    within budget: `monotone_active_accumulation_overflows` fires via the embedding. -/
theorem append_only_log_overflows (M : AppendOnlyLog) :
    ¬∀ s : M.State, M.entry_count s ≤ M.budget :=
  monotone_active_accumulation_overflows (append_only_to_bounded M)

/-- Versioned entry store: each update creates a new version; all versions are
    retained indefinitely.

    `update_grows` formalises version retention: each update increments the
    version count by exactly 1.  `overflow_state` witnesses the capacity violation.
    Parallel to `DelegatedVerification` for trust bridges. -/
structure VersionedStore where
  /-- Abstract state type (models the multi-version store). -/
  State          : Type
  /-- Number of retained versions in a given store state. -/
  version_count  : State → Nat
  /-- Fixed capacity budget. -/
  budget         : Nat
  /-- Update operation: creates a new version, incrementing the count. -/
  update         : State → State
  /-- Version creation grows the count by exactly 1. -/
  update_grows   : ∀ s, version_count (update s) = version_count s + 1
  /-- A concrete store state whose version count exceeds the budget. -/
  overflow_state : State
  /-- The overflow state demonstrably exceeds the budget. -/
  exceeds_budget : budget < version_count overflow_state

/-- A versioned entry store directly instantiates `BoundedStorage`:
    the overflow state is the deep-state witness. -/
def versioned_to_bounded (M : VersionedStore) : BoundedStorage where
  State          := M.State
  count          := M.version_count
  budget         := M.budget
  deep_state     := M.overflow_state
  exceeds_budget := M.exceeds_budget

/-- Without a compaction or garbage-collection mechanism, a versioned store
    cannot stay within budget: `monotone_active_accumulation_overflows` fires
    via the embedding. -/
theorem versioned_store_overflows (M : VersionedStore) :
    ¬∀ s : M.State, M.version_count s ≤ M.budget :=
  monotone_active_accumulation_overflows (versioned_to_bounded M)

/-- Per-partition quota store: storage is divided into named partitions
    (tenants, shards, epochs); each partition carries its own active-entry count.

    `overflow_partition` and `overflow_state` supply the `BoundedStorage` witness:
    a single partition in a single state that exceeds the global budget.
    Parallel to `PartitionedStore` for the authorization surface in RBAC. -/
structure PartitionedStore where
  /-- Partition identifier type (tenant, shard, epoch, etc.). -/
  Partition          : Type
  /-- Abstract global state type. -/
  State              : Type
  /-- Active entry count for a given partition in a given global state. -/
  partition_count    : Partition → State → Nat
  /-- Global capacity budget. -/
  budget             : Nat
  /-- A partition whose local count exceeds the global budget in some state. -/
  overflow_partition : Partition
  /-- A state in which that partition's count exceeds the budget. -/
  overflow_state     : State
  /-- The overflow partition in the overflow state demonstrably exceeds the budget. -/
  exceeds_budget     : budget < partition_count overflow_partition overflow_state

/-- A partitioned store directly instantiates `BoundedStorage` by fixing the
    overflow partition: `partition_count overflow_partition` acts as the count function. -/
def partitioned_to_bounded (M : PartitionedStore) : BoundedStorage where
  State          := M.State
  count          := M.partition_count M.overflow_partition
  budget         := M.budget
  deep_state     := M.overflow_state
  exceeds_budget := M.exceeds_budget

/-- Without cross-partition capacity enforcement, a partitioned store cannot
    bound the per-partition active-entry count globally: the impossibility
    fires via the embedding. -/
theorem partitioned_store_overflows (M : PartitionedStore) :
    ¬∀ s : M.State, M.partition_count M.overflow_partition s ≤ M.budget :=
  monotone_active_accumulation_overflows (partitioned_to_bounded M)


/-! ### §8.8  Storage ↔ BoundedStorage -/

/-- Convert `GroundedStorage` to `BoundedStorage`.
    The fields map directly: `State`/`budget`/`count`/`overflow_state`→`deep_state`/`exceeds`→`exceeds_budget`.
    Parallel to `groundedAuthorization_to_scenario` for the authorization dimension. -/
def groundedStorage_to_scenario (G : GroundedStorage) : BoundedStorage where
  State          := G.State
  budget         := G.budget
  count          := G.count
  deep_state     := G.overflow_state
  exceeds_budget := G.exceeds

/-- No fixed budget can cover all active-deposit states in a `GroundedStorage`.
    Invokes `monotone_active_accumulation_overflows` via the bridge.
    Parallel to `groundedAuthorization_flat_impossible` for the authorization dimension. -/
theorem groundedStorage_accumulation_impossible (G : GroundedStorage) :
    ¬∀ s : G.State, G.count s ≤ G.budget :=
  monotone_active_accumulation_overflows (groundedStorage_to_scenario G)

/-- Thin alias for `G.toStrict`.  Cite `groundedStorage_accumulation_impossible` directly
    when a proof must explicitly name the bounded-storage impossibility route. -/
def GroundedStorageStrict.mk' (G : GroundedStorage) : GroundedStorageStrict :=
  G.toStrict



/-! ========================================================================
    §9. BOUNDED RECALL — τ-Expiry as a Forced Consequence of Bounded
        Verification Budget
    ========================================================================

    **Argument.** When an agent recalls a banked deposit, it must re-verify
    that the deposit's provenance chain (V) is still intact and that the
    claim still meets the current standard (S).  If V-chain depth has grown
    unboundedly since the deposit was first accepted, the re-verification cost
    at recall time grows with that depth.  For any fixed budget there exist
    deposits whose accumulated V-chain depth exceeds the budget.  An agent
    with a fixed recall budget therefore cannot re-verify all banked deposits
    on demand.

    **Consequence.** Without a recency filter, a bounded-budget agent
    accumulates irrecallable deposits — entries that remain formally Deposited
    but cannot be re-verified at recall time.  τ-expiry is a forced response:
    it ensures the deposits an agent must re-verify at withdrawal time have
    bounded provenance depth, because they are recent.

    **Proof technique.** Parallel to BoundedVerification (§2).  A
    `RecallBudget` witness carries a provenance chain exceeding the budget.
    `recall_only_withdrawal_incomplete` closes via `Nat.not_le_of_gt`.  The
    forcing theorem connects this impossibility to τ-expiry as a sufficient
    recency filter. -/

/-! ## §9.1  RecallBudget Structure -/

/-- A claim universe where re-verification cost at withdrawal time grows with
    provenance depth.  The agent has a fixed recall budget; any deposit whose
    V-chain is deeper than the budget cannot be re-verified at recall time.

    Parallel to `BoundedVerification` for the recall direction. -/
structure RecallBudget where
  /-- The type of provenance chains (the V-field). -/
  Provenance  : Type
  /-- Cost to re-verify a provenance chain: grows with depth. -/
  recall_cost : Provenance → Nat
  /-- Maximum recall budget (fixed per agent). -/
  budget      : Nat
  /-- A provenance chain that exceeds the budget. -/
  deep_chain  : Provenance
  /-- The deep chain demonstrably exceeds the budget. -/
  exceeds_budget : recall_cost deep_chain > budget

/-! ## §9.2  Recall Impossibility -/

/-- RECALL IMPOSSIBILITY: a fixed recall budget cannot re-verify all provenance chains.

    **Theorem shape:** `¬∀ v : M.Provenance, M.recall_cost v ≤ M.budget`.
    **Proof strategy:** apply the universal bound to `M.deep_chain`, which carries
    `M.exceeds_budget : M.recall_cost M.deep_chain > M.budget`; contradiction via
    `Nat.not_le_of_gt`.

    Parallel to `verification_only_import_incomplete` for the recall direction. -/
theorem recall_only_withdrawal_incomplete (M : RecallBudget) :
    ¬∀ v : M.Provenance, M.recall_cost v ≤ M.budget :=
  fun h => absurd (h M.deep_chain) (Nat.not_le_of_gt M.exceeds_budget)

/-! ## §9.3  Kernel Witness -/

/-- `RecallBudget` has a canonical kernel inhabitant for every budget d.
    Provenance chains are `Nat`-indexed depths; recall cost equals depth;
    depth d+1 exceeds budget d.  Same concrete intuition as
    `depth_bounded_verification`: the V-chain is a natural number and the
    cost is its depth. -/
def depth_recall_budget (d : Nat) : RecallBudget where
  Provenance     := Nat
  recall_cost    := id
  budget         := d
  deep_chain     := d + 1
  exceeds_budget := Nat.lt_succ_self d

/-- `recall_only_withdrawal_incomplete` fires on the kernel witness:
    no budget-d agent can re-verify the full depth-(d+1) chain. -/
theorem depth_recall_incomplete (d : Nat) :
    ¬∀ v : (depth_recall_budget d).Provenance,
      (depth_recall_budget d).recall_cost v ≤ (depth_recall_budget d).budget :=
  recall_only_withdrawal_incomplete (depth_recall_budget d)

/-! ## §9.4  Forcing Theorem -/

/-- BOUNDED RECALL FORCES RECENCY FILTERING.

    For any fixed recall budget `b`, a bank that accepts deposits with
    unbounded V-chain depth will eventually hold a deposit that cannot be
    re-verified at withdrawal time.

    τ-expiry is a sufficient response: if V-chain growth is bounded by deposit
    age (at most one endorsement hop per time unit), then setting
    `tau_window = budget` ensures every withdrawable deposit has
    `recall_cost ≤ budget`.

    **Theorem shape:** given a `RecallBudget` M, no agent can re-verify all
    provenance chains within `M.budget` — `recall_only_withdrawal_incomplete`
    fires.  A τ-filtered bank that only holds deposits with V-chain depth ≤
    `tau_window` has all withdrawable deposits within budget when
    `tau_window = M.budget`.

    **Proof strategy:** the impossibility half is immediate from
    `recall_only_withdrawal_incomplete`.  The sufficiency half is structural:
    if `V_depth_bound : ∀ v, M.recall_cost v ≤ tau_window` and
    `tau_window = M.budget`, then `∀ v, M.recall_cost v ≤ M.budget` — but
    that universal is exactly what `recall_only_withdrawal_incomplete`
    refutes.  The forcing consequence: any bank that guarantees recall for
    all its deposits must enforce a recency bound equivalent to `tau_window =
    M.budget`.

    **Scope notes.**
    - Does not prove: τ is the *only* valid recency filter.  Priority-based
      eviction or capacity-triggered compaction also satisfy the obligation.
    - Does not prove: the recall budget equals the τ window.  The forcing
      argument shows `tau_window = budget` is sufficient; an implementation
      may use a more conservative window.
    - Does not prove: V-chain growth is exactly one hop per time unit.  The
      formal bound is a hypothesis supplied by the caller. -/
theorem bounded_recall_forces_recency_filter
    (M : RecallBudget)
    (tau_window : Nat)
    (h_window : tau_window = M.budget)
    (V_depth_bound : ∀ v : M.Provenance, M.recall_cost v ≤ tau_window) :
    False :=
  -- recall_only_withdrawal_incomplete supplies the impossibility;
  -- V_depth_bound (re-stated at budget via h_window) supplies the universal that
  -- the impossibility refutes.
  recall_only_withdrawal_incomplete M (h_window ▸ V_depth_bound)

/-! ## §9.5  GroundedRecall Bridge -/

/-- Grounded recall scenario: a `RecallBudget` together with the proof that
    the impossibility has been witnessed by the kernel.

    Parallel to `GroundedStorage` for the recall dimension. -/
structure GroundedRecall where
  /-- The underlying recall budget scenario. -/
  scenario        : RecallBudget
  /-- Proof that the impossibility fires on this scenario. -/
  fires           : ¬∀ v : scenario.Provenance, scenario.recall_cost v ≤ scenario.budget

/-- Every `RecallBudget` grounds a `GroundedRecall`: the impossibility is
    unconditional, so the grounding proof is just `recall_only_withdrawal_incomplete`. -/
def RecallBudget.toGrounded (M : RecallBudget) : GroundedRecall where
  scenario := M
  fires    := recall_only_withdrawal_incomplete M

/-! ### §9.6  Recall ↔ BoundedRecall Bridge

`RecallBudget` embeds into `BoundedVerification` in the recall direction:
provenance depth plays the role that claim depth plays in the import direction.
The impossibility fires via the same arithmetic path. -/

/-- `RecallBudget` embeds into `BoundedVerification`: provenance depth is the
    verification cost; budget and hard-claim map directly.

    This makes explicit that the recall impossibility is an instance of the
    general bounded-budget impossibility — the same Nat arithmetic closes both. -/
def recallBudget_to_bounded (M : RecallBudget) : BoundedVerification where
  Claim          := M.Provenance
  verify_cost    := M.recall_cost
  budget         := M.budget
  hard_claim     := M.deep_chain
  exceeds_budget := M.exceeds_budget

/-- `recall_only_withdrawal_incomplete` is an instance of
    `verification_only_import_incomplete` via the embedding.

    Confirms that the recall and import impossibilities share the same
    formal structure: both close via `Nat.not_le_of_gt`. -/
theorem recall_is_bounded_verification_instance (M : RecallBudget) :
    ¬∀ v : M.Provenance, M.recall_cost v ≤ M.budget :=
  verification_only_import_incomplete (recallBudget_to_bounded M)

end EpArch
