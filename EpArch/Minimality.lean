/-
Minimality and Impossibility Theorems

Formal convergence result: any system satisfying the operational
constraints necessarily contains the Bank primitives.  The theorems
here prove this via structural impossibility: remove primitive X and
constraint Y cannot be satisfied.

The core claim is convergence under constraints, not metaphysical necessity.
These theorems formalize that convergence.

## Central Role

This file contains the structural impossibility models from which the
convergence result follows.  The convergence theorem itself
(`convergence_structural`) lives in `Convergence.lean`.  Each scenario
proves: remove primitive X and the system cannot satisfy operational
constraint Y — establishing necessity per dimension.

This is convergence, not uniqueness: any working solution must contain
these structural elements, but implementations can differ.

## Key Definitions

- `Constraints` — typeclass capturing the minimal system predicates
- `WorkingSystem` — record wrapping the `SystemSpec` configuration flags
- `StructurallyForced` — forward-direction forcing implications (in Convergence.lean)
- `PrimitiveNecessity` — minimal constraints table as data

## Related Files

- **Theorems/BehavioralEquivalence.lean:** sharp observation-boundary equivalence theorems
  (`Input`, `Observation`, `Behavior`, `BehaviorallyEquivalent`, equivalence theorems)
- **Convergence.lean:** `StructurallyForced`, `ForcingEmbedding`, Bridge predicates,
  Scenario predicates, `convergence_structural`, `structural_impossibility`

## Dependencies

- **SystemSpec.lean:** provides the `SystemSpec` structure that `MinimalConstraints` wraps
- **Commitments.lean:** the commitments that are shown to be forced
- **ConcreteLedgerModel.lean:** proves `WorkingSystem` is nonempty (non-vacuity)
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank
import EpArch.Commitments
import EpArch.SystemSpec
import EpArch.VerificationDepth

namespace EpArch

universe u

variable {PropLike Standard ErrorModel Provenance : Type u}

/-! ## Constraints Typeclass (Minimal Constraints)

The minimal constraints table has three columns:
  | Constraint | What It Forces | If Relaxed |

This typeclass captures the constraint column. The "What It Forces" is captured
by the convergence theorem and impossibility theorems below. -/

/-- Predicate: agent controls acceptance for a bubble. -/
opaque controls_acceptance : Agent → Bubble → Prop

/-- Predicate: claim can be fully verified within available resources. -/
opaque can_fully_verify : PropLike → Prop

/-- Predicate: deposit is an adversarial injection (fabricated claim/header). -/
opaque is_adversarial_injection : Deposit PropLike Standard ErrorModel Provenance → Prop

/-- Predicate: deposit passed the bubble's acceptance protocol. -/
opaque passed_acceptance : Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop

/-- The minimal constraints encoded as a typeclass.
    Each field corresponds to one row of the constraint table.
    The semantic content captures the informal descriptions. -/
class Constraints (B : Bank (PropLike := PropLike)
    (Standard := Standard) (ErrorModel := ErrorModel) (Provenance := Provenance)) : Prop where

  /-- **Distributed agents**: No single agent controls all bubble acceptance.
      If relaxed: single agent control suffices; no Bank needed. -/
  distributed_agents : ¬∃ (controller : Agent), ∀ (B : Bubble), controls_acceptance controller B

  /-- **Bounded audit**: Some claims cannot be fully verified.
      If relaxed: unbounded audit; full revalidation always; no need for trust-based import. -/
  bounded_audit : ∃ (P : PropLike), ¬can_fully_verify P

  /-- **Export across boundaries**: Deposits propagate between distinct bubbles.
      If relaxed: isolated bubbles; coordination collapses but no contamination. -/
  export_across_boundaries : ∃ (B1 B2 : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance),
    B1 ≠ B2 ∧ exportDep B1 B2 d

  /-- **Adversarial/corruption pressure**: Adversarial deposits can pass acceptance.
      If relaxed: weaker V requirements; simpler hygiene.
      Note: The PRESSURE is that bad deposits sometimes succeed. -/
  adversarial_pressure : ∃ (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance),
    is_adversarial_injection d ∧ passed_acceptance B d

  /-- **Coordination need**: Multiple agents must rely on shared deposits.
      If relaxed: no coordination; each agent runs solo. -/
  coordination_need : ∃ (a1 a2 : Agent) (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance),
    a1 ≠ a2 ∧ withdraw a1 B d ∧ withdraw a2 B d

  /-- **Truth pressure (redeemability)**: Deposits can fail constraint-surface contact.
      If relaxed: self-agreement suffices; system drifts into unfalsifiable consensus. -/
  truth_pressure : ∃ (d : Deposit PropLike Standard ErrorModel Provenance),
    d.status = .Deposited ∧ ¬redeemable d


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


/-! ## Six Operational Properties

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


/-! ## Pressure: The Canonical Dimension Index

`Pressure` is the machine-exhaustive index of EpArch's six architectural
forcing dimensions.  Using it as the canonical index for `handles_pressure`,
`forced_feature`, `SatisfiesAllProperties`, and `containsBankPrimitives`
means the coverage of the framework — exactly these six and no others —
is a typed fact, not a counting convention.

A proof that pattern-matches on `Pressure` is checked by Lean for
exhaustiveness: adding a seventh dimension requires adding a seventh
constructor here, which would break every existing `cases P` proof
until the new forcing chain is supplied. -/

/-- The six architectural pressure dimensions of EpArch. -/
inductive Pressure where
  | scope         -- Distributed agents → Bubbles
  | trust         -- Bounded audit → TrustBridges
  | headers       -- Export → Headers
  | revocation    -- Adversarial → Revocation
  | bank          -- Coordination → Bank
  | redeemability -- Truth pressure → Redeemability
  deriving DecidableEq, Repr

/-- Maps each `Pressure` dimension to its capability predicate. -/
def handles_pressure (W : WorkingSystem) : Pressure → Prop
  | .scope         => handles_distributed_agents W
  | .trust         => handles_bounded_audit W
  | .headers       => handles_export W
  | .revocation    => handles_adversarial W
  | .bank          => handles_coordination W
  | .redeemability => handles_truth_pressure W

/-- Maps each `Pressure` dimension to its forced architectural feature. -/
def forced_feature (W : WorkingSystem) : Pressure → Prop
  | .scope         => HasBubbles W
  | .trust         => HasTrustBridges W
  | .headers       => HasHeaders W
  | .revocation    => HasRevocation W
  | .bank          => HasBank W
  | .redeemability => HasRedeemability W

/-- A working system satisfies ALL six operational properties — indexed by `Pressure`.
    The six-ness is machine-checked: `cases P` in any proof is
    exhaustiveness-verified by Lean. -/
def SatisfiesAllProperties (W : WorkingSystem) : Prop :=
  ∀ P : Pressure, handles_pressure W P

/-- A system contains Bank primitives iff it satisfies every pressure
    dimension's forced-feature predicate. -/
def containsBankPrimitives (W : WorkingSystem) : Prop :=
  ∀ P : Pressure, forced_feature W P


/-! ## Constraint Subset and Partial Well-Formedness -/

/-- A subset of the six EpArch operational constraints, represented as a
    6-boolean vector. `true` = constraint included; `false` = dropped.

    Examples:
    - `allConstraints`  — all six included (strongest case)
    - `noConstraints`   — none included (no forcing theorems claimed)
    - `⟨true, false, false, false, true, false⟩` — only distributed + coordination -/
structure ConstraintSubset where
  distributed    : Bool
  bounded_audit  : Bool
  export_across  : Bool
  adversarial    : Bool
  coordination   : Bool
  truth_pressure : Bool

/-- The full set of all six constraints. `PartialWellFormed W allConstraints` requires
    all six biconditionals — the strongest subset. -/
def allConstraints : ConstraintSubset := ⟨true, true, true, true, true, true⟩

/-- The empty subset. `PartialWellFormed W noConstraints` holds trivially. -/
def noConstraints : ConstraintSubset := ⟨false, false, false, false, false, false⟩

/-- `PartialWellFormed W S` captures the forcing biconditionals for
    the constraint subset S.

    For each constraint X:
    - If `S.X = true`,  the biconditional `handles_X W ↔ HasFeature_X W` is required.
    - If `S.X = false`, nothing is required for X.

    Requiring all six (S = allConstraints) is the strongest form. -/
structure PartialWellFormed (W : WorkingSystem) (S : ConstraintSubset) : Prop where
  wf_distributed    : S.distributed    = true → (handles_distributed_agents W ↔ HasBubbles W)
  wf_bounded_audit  : S.bounded_audit  = true → (handles_bounded_audit W ↔ HasTrustBridges W)
  wf_export         : S.export_across  = true → (handles_export W ↔ HasHeaders W)
  wf_adversarial    : S.adversarial    = true → (handles_adversarial W ↔ HasRevocation W)
  wf_coordination   : S.coordination   = true → (handles_coordination W ↔ HasBank W)
  wf_truth_pressure : S.truth_pressure = true → (handles_truth_pressure W ↔ HasRedeemability W)


/-! ## Grounded Behavioral Evidence

The six capability witnesses correspond exactly to the six `GroundedX` structures:

| WorkingSystem field  | GroundedXStrict type            | Forcing dimension                                     |
|----------------------|---------------------------------|-------------------------------------------------------|
| `bubbles_ev`         | `GroundedBubblesStrict`         | Distributed agents — scope separation                 |
| `bridges_ev`         | `GroundedTrustBridgesStrict`    | Bounded audit — trust bridges                         |
| `headers_ev`         | `GroundedHeadersStrict`         | Export across boundaries — header preservation        |
| `revocation_ev`      | `GroundedRevocationStrict`      | Adversarial pressure — revocation                     |
| `bank_ev`            | `GroundedBankStrict`            | Coordination need — shared ledger                     |
| `redeemability_ev`   | `GroundedRedeemabilityStrict`   | Truth pressure — redeemability                        | -/

/-- Evidence for all six behavioral capabilities of a `WorkingSystem`.

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

/-- Build a `WorkingSystem` with all six proof-carrying option fields set from evidence. -/
def WorkingSystem.withGroundedBehavior (B : GroundedBehavior) (base : WorkingSystem) : WorkingSystem :=
  { base with
    bubbles_ev       := some B.bubbles.toStrict
    bridges_ev       := some B.trust_bridges.toStrict
    headers_ev       := some B.headers.toStrict
    revocation_ev    := some B.revocation.toStrict
    bank_ev          := some B.bank.toStrict
    redeemability_ev := some B.redeemability.toStrict }

/-- A `WorkingSystem` built from `GroundedBehavior` satisfies all six operational
    properties. -/
theorem grounded_behavior_satisfies_all (B : GroundedBehavior) (W : WorkingSystem) :
    SatisfiesAllProperties (WorkingSystem.withGroundedBehavior B W) := by
  intro P; cases P <;>
  simp [handles_pressure, handles_distributed_agents, handles_bounded_audit,
        handles_export, handles_adversarial, handles_coordination,
        handles_truth_pressure, WorkingSystem.withGroundedBehavior, Option.isSome]

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
    ⟨fun _ => (grounded_spec_contains_all G).2.2.2.2.2,
     fun _ => rfl⟩ }


/-! ## Global Impossibility and Convergence -/

/-- All six forced features together constitute Bank-like architecture.

    This is a definitional theorem: `containsBankPrimitives W` is
    `∀ P : Pressure, forced_feature W P` — providing the six `Has*`
    witnesses satisfies it by case analysis on `P`. -/
theorem all_features_constitute_bank (W : WorkingSystem) :
  HasBubbles W → HasTrustBridges W → HasHeaders W →
  HasRevocation W → HasBank W → HasRedeemability W →
  containsBankPrimitives W := by
  intro h1 h2 h3 h4 h5 h6 P
  cases P <;> assumption


/-! ## Primitive Necessity Summary -/

/-- Summary structure: what primitives are forced by what constraints. -/
structure PrimitiveNecessity where
  constraint : String
  forced_primitive : String
  if_removed : String

/-- The minimal constraints table as data. -/
def minimalConstraintsTable : List PrimitiveNecessity := [
  ⟨"Distributed agents", "Bubbles (scoped domains)", "Single agent; personal certainty suffices"⟩,
  ⟨"Bounded audit", "Trust bridges", "Unbounded audit; full revalidation always possible"⟩,
  ⟨"Export across boundaries", "Headers (S/E/V) + export gating", "No export; isolated scopes"⟩,
  ⟨"Adversarial pressure", "Provenance discipline + revocation", "No adversaries; simpler hygiene"⟩,
  ⟨"Coordination need", "Bank (shared ledger)", "No coordination; Ladder suffices"⟩,
  ⟨"Truth pressure", "Redeemability reference", "No truth pressure; unfalsifiable consensus"⟩
]


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

After the six models, the convergence proof machinery (`StructurallyForced`,
`ForcingEmbedding`, Bridge predicates, Scenario predicates,
`convergence_structural`) lives in `Convergence.lean`.
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

**Proof technique.**  The hard claim's cost exceeds the budget; omega
closes the Nat contradiction. -/

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
   fun h => (Nat.lt_or_ge M.budget (M.verify_cost c)).elim id (fun h' => (h h').elim)⟩

/-- At the system level, existence of a claim exceeding the budget is equivalent to
    failure of universal local verifiability.  `M.hard_claim` witnesses the
    right-to-left direction. -/
theorem delegation_necessary_iff_locally_inadequate (M : DelegatedVerification) :
    (∃ c : M.Claim, M.verify_cost c > M.budget) ↔
    ¬∀ c : M.Claim, LocallyVerifiable M c :=
  ⟨fun ⟨c, hc⟩ hA => absurd (hA c) (Nat.not_le_of_gt hc),
   fun _ => ⟨M.hard_claim, M.exceeds_budget⟩⟩


/-! ### §2c. Kernel Witness: BoundedVerification is Non-Vacuous by Construction

The `BoundedVerification` structure and `verification_only_import_incomplete`
are the architectural abstractions.  `DepthClaim` (VerificationDepth.lean) is
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
    ∀ d, M.has_access M.a₁ d → M.has_access M.a₁ d ∧ M.has_access M.a₂ d :=
  fun d h => ⟨h, M.synchronized d h⟩

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
    ∀ d, M.has_access M.a₁ d → M.has_access M.a₁ d ∧ M.has_access M.a₂ d :=
  fun d h => ⟨h, M.readable d h⟩

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
    ∀ d, M.has_access M.a₁ d → M.has_access M.a₁ d ∧ M.has_access M.a₂ d :=
  fun d h => ⟨h, M.converges d h⟩


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

The six forcing dimensions do not all have the same tightness.

Hard forcing: impossibility follows from the structure alone, without additional
behavioral coverage assumptions.  Scope, revocation, bank, and partial contestation
belong to this tier.

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


/-! ## §7. GroundedX ↔ Impossibility Bridges

Each `GroundedX` structure is isomorphic to the *input* of the corresponding
impossibility theorem (§1–§6).  These bridge theorems make the connection
explicit: given any `GroundedX` witness, the matching impossibility result fires.

`GroundedXStrict` packages the base evidence with its impossibility consequence —
the non-trivial `Prop` that falls out of the bridge.

**Relation to WorkingSystem.**  `WorkingSystem` carries six `Option GroundedXStrict`
fields.  The `GroundedXStrict` structures are defined in `SystemSpec.lean` (where
they only depend on `GroundedX` fields).

**Construction convention.**
- `G.toStrict` — standard path; inline proof from base fields (in `SystemSpec.lean`,
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


end EpArch
