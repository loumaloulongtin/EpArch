/-
Convergence

The central convergence theorem and the full structural proof machinery:
any WorkingSystem that is StructurallyForced and satisfies all six
operational properties necessarily contains Bank primitives.

## Structure

1. `StructurallyForced` — forward-only forcing implications (capability → feature),
   each field independently justified by a structural model in Minimality.lean.
2. `ForcingEmbedding` — auditable disjunction connecting WorkingSystems to the abstract
   structural models; `embedding_to_structurally_forced` derives StructurallyForced
   constructively (no Classical reasoning).
4. Bridge predicates (`BridgeBubbles` … `BridgeRedeemability`) and
   `bridge_*_impossible` theorems — system-independent impossibility: committing to
   the impossible scenario for any dimension is universally False.
5. Six Scenario predicates (RepresentsDisagreement, RepresentsPrivateCoordination,
   RepresentsMonotonicLifecycle, RepresentsDiscriminatingImport,
   RepresentsBoundedVerification, RepresentsClosedEndorsement) — enriched
   WorkingSystem instantiations that let the abstract structural models fire
   on concrete systems.
6. `convergence_structural` — the central theorem:
   StructurallyForced W → SatisfiesAllProperties W → containsBankPrimitives W.
7. `structural_impossibility` — missing any feature blocks all-property satisfaction.

## Proof Chain

    ForcingEmbedding ──┐
                       ├── StructurallyForced ──► convergence_structural
    Structural models ─┘

## Dependencies

- **Minimality.lean:** WorkingSystem, SatisfiesAllProperties,
  containsBankPrimitives, Has*, handles_*, all six structural models and their
  impossibility theorems (AgentDisagreement, BoundedVerification,
  DiscriminatingImport, MonotonicLifecycle, PrivateOnlyStorage, ClosedEndorsement,
  flat_scope_impossible, verification_only_import_incomplete,
  no_sound_complete_uniform_import, monotonic_no_exit, private_storage_no_sharing,
  closed_system_unfalsifiable, iter).
-/

import EpArch.Minimality

namespace EpArch

/-! ## StructurallyForced: Forward-Direction Forcing

`StructurallyForced` packages the six `handles_X → HasY` forcing implications,
each independently justified by a structural impossibility model in
`Minimality.lean`.  It is constructive (no Classical reasoning) and requires
no biconditionals — just the forward direction is needed for convergence. -/

/-- A system is structurally forced if each operational capability implies
    the corresponding architectural feature.  Each field is independently
    justified by a structural forcing model. -/
structure StructurallyForced (W : WorkingSystem) : Prop where
  /-- Handling distributed agents requires scope separation.
      Justified by: `flat_scope_impossible` -/
  scope_forcing : handles_distributed_agents W → HasBubbles W
  /-- Handling bounded audit requires trust bridges.
      Justified by: `verification_only_import_incomplete` -/
  trust_forcing : handles_bounded_audit W → HasTrustBridges W
  /-- Handling export requires headers/metadata.
      Justified by: `uniform_import_nondiscriminating` and
      `no_sound_complete_uniform_import` -/
  header_forcing : handles_export W → HasHeaders W
  /-- Handling adversarial pressure requires revocation.
      Justified by: `monotonic_no_exit` -/
  revocation_forcing : handles_adversarial W → HasRevocation W
  /-- Handling coordination requires shared ledger.
      Justified by: `private_storage_no_sharing` -/
  bank_forcing : handles_coordination W → HasBank W
  /-- Handling truth pressure requires redeemability.
      Justified by: `closed_system_unfalsifiable` -/
  redeemability_forcing : handles_truth_pressure W → HasRedeemability W

/-! ## Forcing Embeddings: Translation Layer

The structural models above prove clean no-go lemmas on abstract scenarios.
`StructurallyForced` packages the forward implications (capability → feature).
The remaining gap: the `StructurallyForced` fields are narratively "justified by"
the structural models but not mechanically derived from them.

`ForcingEmbedding` closes this gap.  Each field says:

> "A system handling capability X either already has feature Y, or it
>  embeds the abstract scenario whose impossibility is already proven."

The derivation `embedding_to_structurally_forced` is then a generic,
mechanical combination: for each direction, take the `Or`, and in the
right branch apply the structural impossibility theorem to produce `False`.
The left branch is the feature itself.

The proof chain becomes:

    ForcingEmbedding ──┐
                       ├── StructurallyForced ──► convergence_structural
    Structural models ─┘

The `ForcingEmbedding` instance encodes when a system without feature X
facing constraint Y is in the impossible scenario.  The derivation is
uniform and constructive (no Classical reasoning — `Or.elim` is intuitionistic). -/

/-! ## Bridge Predicates and System-Independent Forcing Theorems

A **bridge predicate** `Bridge_X W` names the commitment a system would
have to make in dimension X if it lacks feature X.  Each is an existential
over the abstract structural model's scenario data.

The `bridge_*_impossible` theorems are system-independent: for ANY `W`,
committing to the impossible scenario forces the feature.  They are
derived directly from the structural impossibility theorems — no
`StructurallyForced` or `convergence_structural` involved.

**Separation of concerns:**
- The concrete good system proves `StructurallyForced` via `ForcingEmbedding`
  (the full convergence pipeline, using `Or.inl` everywhere).
- Deficient systems prove `Bridge_X DeficientSystem → False` directly via
  `bridge_X_impossible`: the bridge commitment data is universally absurd.
  `SatisfiesAllProperties`, ¬HasFeature, and the convergence pipeline are
  not involved.

This matches what is actually proven: deficient systems + bridge hypothesis ⇒
contradiction, NOT deficient system alone ⇒ contradiction. -/

/-- A system is bridge-committed on scope: it provides a flat acceptance
    function faithful to two disagreeing agents. -/
def BridgeBubbles (_W : WorkingSystem) : Prop :=
  ∃ D : AgentDisagreement, ∃ f : D.Claim → Prop,
    (∀ c, f c ↔ D.accept₁ c) ∧ (∀ c, f c ↔ D.accept₂ c)

/-- The scope bridge scenario is universally impossible: no flat acceptance
    function can faithfully represent two genuinely disagreeing agents.
    `_W` is a phantom parameter — the impossibility is system-independent. -/
theorem bridge_bubbles_impossible (_W : WorkingSystem) : ¬BridgeBubbles _W :=
  fun ⟨D, f, hf⟩ => flat_scope_impossible D ⟨f, hf⟩

/-- A system is bridge-committed on trust: all claims fit within budget. -/
def BridgeTrust (_W : WorkingSystem) : Prop :=
  ∃ M : BoundedVerification, ∀ c, M.verify_cost c ≤ M.budget

/-- The trust bridge scenario is universally impossible: no budget can cover
    a claim whose cost exceeds it. -/
theorem bridge_trust_impossible (_W : WorkingSystem) : ¬BridgeTrust _W :=
  fun ⟨M, hM⟩ => verification_only_import_incomplete M hM

/-- A system is bridge-committed on headers: a uniform import function
    is both sound and complete. -/
def BridgeHeaders (_W : WorkingSystem) : Prop :=
  ∃ M : DiscriminatingImport, ∃ f : M.Claim → Bool,
    (∀ x y, f x = f y) ∧ f M.bad = false ∧ f M.good = true

/-- The headers bridge scenario is universally impossible: no uniform import
    function can be both sound and complete on distinct claims. -/
theorem bridge_headers_impossible (_W : WorkingSystem) : ¬BridgeHeaders _W :=
  fun ⟨M, f, hu, hs, hc⟩ => no_sound_complete_uniform_import M f hu hs hc

/-- A system is bridge-committed on revocation: the accepted state escapes. -/
def BridgeRevocation (_W : WorkingSystem) : Prop :=
  ∃ M : MonotonicLifecycle, ∃ n, iter M.step n M.accepted ≠ M.accepted

/-- The revocation bridge scenario is universally impossible: an absorbing
    accepted state cannot be escaped at any step count. -/
theorem bridge_revocation_impossible (_W : WorkingSystem) : ¬BridgeRevocation _W :=
  fun ⟨M, n, hn⟩ => hn (monotonic_no_exit M n)

/-- A system is bridge-committed on bank: isolated agents share a deposit. -/
def BridgeBank (_W : WorkingSystem) : Prop :=
  ∃ M : PrivateOnlyStorage, ∃ d, M.has_access M.a₁ d ∧ M.has_access M.a₂ d

/-- The bank bridge scenario is universally impossible: isolated agents cannot
    share a deposit. -/
theorem bridge_bank_impossible (_W : WorkingSystem) : ¬BridgeBank _W :=
  fun ⟨M, d, hd⟩ => private_storage_no_sharing M ⟨d, hd⟩

/-- A system is bridge-committed on redeemability: a closed system has an
    endorsed-and-falsifiable claim. -/
def BridgeRedeemability (_W : WorkingSystem) : Prop :=
  ∃ M : ClosedEndorsement, ∃ c, M.endorsed c ∧ M.externally_falsifiable c

/-- The redeemability bridge scenario is universally impossible: a closed system
    cannot have an endorsed claim that is externally falsifiable. -/
theorem bridge_redeemability_impossible (_W : WorkingSystem) : ¬BridgeRedeemability _W :=
  fun ⟨M, c, hc⟩ => closed_system_unfalsifiable M ⟨c, hc⟩


/-- Forcing embeddings: connects a `WorkingSystem` to the abstract
    structural models via an auditable disjunction.

    Each field says: a system handling the constraint EITHER already
    has the feature, OR is bridge-committed to the impossible scenario
    for that dimension.  Since bridge commitment forces the feature
    (via `bridge_*_impossible`), the feature holds in both branches. -/
structure ForcingEmbedding (W : WorkingSystem) : Prop where
  /-- Distributed agents: either bubbles exist, or the system is
      bridge-committed on scope (`BridgeBubbles`). -/
  scope_embed : handles_distributed_agents W →
    HasBubbles W ∨ BridgeBubbles W
  /-- Bounded audit: either trust bridges exist, or the system is
      bridge-committed on trust (`BridgeTrust`). -/
  trust_embed : handles_bounded_audit W →
    HasTrustBridges W ∨ BridgeTrust W
  /-- Export: either headers exist, or the system is bridge-committed
      on headers (`BridgeHeaders`). -/
  header_embed : handles_export W →
    HasHeaders W ∨ BridgeHeaders W
  /-- Adversarial: either revocation exists, or the system is
      bridge-committed on revocation (`BridgeRevocation`). -/
  revocation_embed : handles_adversarial W →
    HasRevocation W ∨ BridgeRevocation W
  /-- Coordination: either shared ledger exists, or the system is
      bridge-committed on bank (`BridgeBank`). -/
  bank_embed : handles_coordination W →
    HasBank W ∨ BridgeBank W
  /-- Truth pressure: either redeemability exists, or the system is
      bridge-committed on redeemability (`BridgeRedeemability`). -/
  redeemability_embed : handles_truth_pressure W →
    HasRedeemability W ∨ BridgeRedeemability W

/-- Mechanical derivation: `ForcingEmbedding` → `StructurallyForced`.

    Each field is derived by `Or.elim`: the left branch is the feature
    itself (`id`); the right branch applies `bridge_X_impossible`, which
    proves `¬Bridge_X W` directly — so the right branch is universally
    absurd.  Fully constructive — no `Classical.byContradiction`. -/
theorem embedding_to_structurally_forced (W : WorkingSystem) (E : ForcingEmbedding W) :
    StructurallyForced W where
  scope_forcing h := (E.scope_embed h).elim id fun hb => absurd hb (bridge_bubbles_impossible W)
  trust_forcing h := (E.trust_embed h).elim id fun hb => absurd hb (bridge_trust_impossible W)
  header_forcing h := (E.header_embed h).elim id fun hb => absurd hb (bridge_headers_impossible W)
  revocation_forcing h := (E.revocation_embed h).elim id fun hb => absurd hb (bridge_revocation_impossible W)
  bank_forcing h := (E.bank_embed h).elim id fun hb => absurd hb (bridge_bank_impossible W)
  redeemability_forcing h := (E.redeemability_embed h).elim id fun hb => absurd hb (bridge_redeemability_impossible W)


/-! ## Scenario Predicates: Enriching WorkingSystems with Structural Content

The structural models prove impossibility on abstract scenarios.
The `ForcingEmbedding` connects these to working systems via disjunctions.
For a system that already has all features (like `ConcreteWorkingSystem`),
`Or.inl` suffices — but the abstract models never fire.

Scenario predicates supply the concrete data needed to instantiate the
abstract structural models.  When a system has a scenario predicate and
lacks the corresponding feature, a right-branch embedding theorem proves
the system instantiates the impossible scenario — and the structural model fires. -/


/-! ### Scenario 1: Distributed Disagreement -/

/-- A system represents distributed disagreement if it carries two
    acceptance predicates over some claim type that genuinely disagree:
    agent 1 accepts a witness claim that agent 2 rejects.

    When such a system lacks bubbles, it is in the `AgentDisagreement`
    scenario: a single flat scope must represent both acceptance profiles
    simultaneously — which `flat_scope_impossible` proves impossible.

    This is not a hypothetical: any system that claims to "handle
    distributed agents" must accommodate disagreeing acceptance criteria
    (otherwise there's no distributed agency to handle). -/
structure RepresentsDisagreement (W : WorkingSystem) where
  /-- The claim type the agents reason over. -/
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

/-- Extract the `AgentDisagreement` abstract model from a system that
    `RepresentsDisagreement`. -/
def RepresentsDisagreement.toDisagreement {W : WorkingSystem}
    (R : RepresentsDisagreement W) : AgentDisagreement where
  Claim := R.Claim
  accept₁ := R.accept₁
  accept₂ := R.accept₂
  witness := R.witness
  agent1_accepts := R.agent1_accepts
  agent2_rejects := R.agent2_rejects

/-- **Right-branch embedding (scope direction).**

    A system that represents distributed disagreement and lacks bubbles
    yields the `AgentDisagreement` scenario.  In a flat (single-scope) system
    the acceptance function must agree with both agents — but
    `flat_scope_impossible` proves this is contradictory.

    The hypothesis `flat_accept` is the bridge condition: without scope
    separation, the system commits to a single acceptance predicate that
    purports to faithfully represent both agents.  The right branch of
    `ForcingEmbedding.scope_embed` is then constructible, and
    `embedding_to_structurally_forced` closes it via `flat_scope_impossible`.

    This theorem demonstrates the abstract model doing real work: the
    structural lemma is used essentially here. -/
theorem disagreement_without_bubbles_embeds
    (W : WorkingSystem)
    (R : RepresentsDisagreement W)
    (_h_no_bubbles : ¬HasBubbles W)
    (flat_accept : R.Claim → Prop)
    (hf₁ : ∀ c, flat_accept c ↔ R.accept₁ c)
    (hf₂ : ∀ c, flat_accept c ↔ R.accept₂ c) :
    False :=
  let D := R.toDisagreement
  flat_scope_impossible D ⟨flat_accept, hf₁, hf₂⟩

/-- **Per-dimension structural forcing (scope).**

    Any system carrying a `RepresentsDisagreement` witness and a flat
    acceptance function is forced to have bubbles.  No `handles_distributed_agents W`
    required — the structural contradiction alone suffices. -/
theorem disagreement_forces_bubbles
    (W : WorkingSystem) (R : RepresentsDisagreement W)
    (flat_accept : ¬HasBubbles W → R.Claim → Prop)
    (hf₁ : ∀ h c, flat_accept h c ↔ R.accept₁ c)
    (hf₂ : ∀ h c, flat_accept h c ↔ R.accept₂ c) :
    HasBubbles W := by
  by_cases h : HasBubbles W
  · exact h
  · exact (disagreement_without_bubbles_embeds W R h (flat_accept h) (hf₁ h) (hf₂ h)).elim

/-- `ForcingEmbedding` for a system with distributed disagreement:
    the scope direction uses the right branch (structural model fires)
    when ¬HasBubbles; other directions use the feature directly.

    This is how you build a `ForcingEmbedding` instance for a deficient
    system — the scope field routes through `Or.inr`, and the structural
    impossibility carries the proof. -/
theorem disagreement_scope_embed
    (W : WorkingSystem) (R : RepresentsDisagreement W)
    (flat_accept : ¬HasBubbles W → R.Claim → Prop)
    (hflat₁ : ∀ h, ∀ c, flat_accept h c ↔ R.accept₁ c)
    (hflat₂ : ∀ h, ∀ c, flat_accept h c ↔ R.accept₂ c) :
    handles_distributed_agents W →
    HasBubbles W ∨
    (∃ D : AgentDisagreement, ∃ f : D.Claim → Prop,
      (∀ c, f c ↔ D.accept₁ c) ∧ (∀ c, f c ↔ D.accept₂ c)) := by
  intro _
  by_cases h : HasBubbles W
  · exact Or.inl h
  · exact Or.inr ⟨R.toDisagreement, flat_accept h, hflat₁ h, hflat₂ h⟩


/-! ### Scenario 2: Private-Only Coordination -/

/-- A system represents private-only coordination if it carries
    evidence that its storage layer, absent a shared ledger, isolates
    agents: deposits accessible to one agent are not accessible to the other.

    When such a system lacks a shared ledger (bank), it is in the
    `PrivateOnlyStorage` scenario: agents must share a deposit for
    coordination, but isolation prevents this — which
    `private_storage_no_sharing` proves impossible. -/
structure RepresentsPrivateCoordination (W : WorkingSystem) where
  /-- Agent type. -/
  Agent : Type
  /-- Deposit type. -/
  Deposit : Type
  /-- Access relation. -/
  has_access : Agent → Deposit → Prop
  /-- Two distinct agents needing coordination. -/
  a₁ : Agent
  a₂ : Agent
  distinct : a₁ ≠ a₂
  /-- Without a shared ledger, storage is isolated. -/
  isolation_without_bank : ¬HasBank W → ∀ d, has_access a₁ d → ¬has_access a₂ d

/-- Extract `PrivateOnlyStorage` from a system that
    `RepresentsPrivateCoordination` and lacks a shared ledger. -/
def RepresentsPrivateCoordination.toPrivateStorage {W : WorkingSystem}
    (R : RepresentsPrivateCoordination W) (h_no_bank : ¬HasBank W) :
    PrivateOnlyStorage where
  Agent := R.Agent
  Deposit := R.Deposit
  has_access := R.has_access
  a₁ := R.a₁
  a₂ := R.a₂
  distinct := R.distinct
  isolation := R.isolation_without_bank h_no_bank

/-- **Right-branch embedding (coordination direction).**

    A system that represents private-only coordination and lacks a bank
    yields the `PrivateOnlyStorage` scenario.  The system claims agents
    coordinate by sharing deposits, but storage is isolated —
    `private_storage_no_sharing` proves this is contradictory. -/
theorem private_coordination_without_bank_embeds
    (W : WorkingSystem)
    (R : RepresentsPrivateCoordination W)
    (h_no_bank : ¬HasBank W)
    (d : R.Deposit)
    (h₁ : R.has_access R.a₁ d) (h₂ : R.has_access R.a₂ d) :
    False :=
  let P := R.toPrivateStorage h_no_bank
  private_storage_no_sharing P ⟨d, h₁, h₂⟩

/-- **Per-dimension structural forcing (bank).**

    Any system carrying a `RepresentsPrivateCoordination` witness and a
    shared deposit is forced to have a bank.  No `handles_coordination W`
    required. -/
theorem private_coordination_forces_bank
    (W : WorkingSystem) (R : RepresentsPrivateCoordination W)
    (shared_deposit : ¬HasBank W → R.Deposit)
    (h₁ : ∀ h, R.has_access R.a₁ (shared_deposit h))
    (h₂ : ∀ h, R.has_access R.a₂ (shared_deposit h)) :
    HasBank W := by
  by_cases h : HasBank W
  · exact h
  · exact (private_coordination_without_bank_embeds W R h (shared_deposit h) (h₁ h) (h₂ h)).elim

/-- `ForcingEmbedding` bank field for a system with private-only
    coordination: uses the right branch when ¬HasBank.

    The `shared_deposit` field provides the witness: agents claim to
    coordinate on this deposit, but the isolation condition makes the
    scenario impossible. -/
theorem private_coordination_bank_embed
    (W : WorkingSystem) (R : RepresentsPrivateCoordination W)
    (shared_deposit : ¬HasBank W → R.Deposit)
    (h_access₁ : ∀ h, R.has_access R.a₁ (shared_deposit h))
    (h_access₂ : ∀ h, R.has_access R.a₂ (shared_deposit h)) :
    handles_coordination W →
    HasBank W ∨
    (∃ M : PrivateOnlyStorage, ∃ d, M.has_access M.a₁ d ∧ M.has_access M.a₂ d) := by
  intro _
  by_cases h : HasBank W
  · exact Or.inl h
  · exact Or.inr ⟨R.toPrivateStorage h, shared_deposit h,
      h_access₁ h, h_access₂ h⟩


/-! ### Scenario 3: Monotonic Lifecycle (Adversarial → Revocation)

A system facing adversarial pressure has a deposit lifecycle.  If revocation
is absent, the "accepted" state is absorbing — once a deposit passes
acceptance, no transition can remove it.  `monotonic_no_exit` proves
(by induction) that an accepted deposit stays accepted through any
number of steps.

`RepresentsMonotonicLifecycle` enriches a `WorkingSystem` with a
concrete lifecycle (states, transition function, absorbing accepted state)
and an adversarial witness: a bad deposit that reaches the accepted state.
When `¬HasRevocation`, the system is in the `MonotonicLifecycle` scenario. -/

/-- A system represents a monotonic lifecycle if, absent revocation,
    its deposit lifecycle has an absorbing "accepted" state: once a
    deposit is accepted, no transition can remove it.

    The `bad_deposit_accepted` field is the adversarial witness:
    a deposit that should not be accepted but reaches the accepted
    state.  Without revocation, it stays there permanently. -/
structure RepresentsMonotonicLifecycle (W : WorkingSystem) where
  /-- The lifecycle state type. -/
  State : Type
  /-- The accepted state. -/
  accepted : State
  /-- The lifecycle transition function. -/
  step : State → State
  /-- Without revocation, accepted is absorbing. -/
  absorbing_without_revocation : ¬HasRevocation W → step accepted = accepted

/-- Extract `MonotonicLifecycle` from a system that
    `RepresentsMonotonicLifecycle` and lacks revocation. -/
def RepresentsMonotonicLifecycle.toLifecycle {W : WorkingSystem}
    (R : RepresentsMonotonicLifecycle W) (h_no_rev : ¬HasRevocation W) :
    MonotonicLifecycle where
  State := R.State
  accepted := R.accepted
  step := R.step
  absorbing := R.absorbing_without_revocation h_no_rev

/-- **Right-branch embedding (adversarial direction).**

    A system with a monotonic lifecycle and no revocation:
    `monotonic_no_exit` fires by induction, proving that the accepted
    state cannot be escaped at any step count `n`.  This is the
    strongest proof in the repo — genuine induction, not just
    hypothesis contradiction. -/
theorem monotonic_lifecycle_without_revocation_embeds
    (W : WorkingSystem)
    (R : RepresentsMonotonicLifecycle W)
    (h_no_rev : ¬HasRevocation W)
    (n : Nat) :
    iter R.step n R.accepted = R.accepted :=
  monotonic_no_exit (R.toLifecycle h_no_rev) n

/-- **Per-dimension structural forcing (revocation).**

    Any system carrying a `RepresentsMonotonicLifecycle` witness and evidence
    that the accepted state escapes after `n` steps is forced to have revocation.
    No `handles_adversarial W` required. -/
theorem monotonic_lifecycle_forces_revocation
    (W : WorkingSystem) (R : RepresentsMonotonicLifecycle W)
    (n : Nat)
    (h_escape : ¬HasRevocation W → iter R.step n R.accepted ≠ R.accepted) :
    HasRevocation W := by
  by_cases h : HasRevocation W
  · exact h
  · exact absurd (monotonic_lifecycle_without_revocation_embeds W R h n) (h_escape h)


/-! ### Scenario 4: Discriminating Import (Export → Headers)

When deposits cross scope boundaries, the receiver must decide which
to accept.  Without metadata (headers), every deposit looks identical
— the import function is uniform.  But sound-and-complete import
requires accepting good claims and rejecting bad ones.  A uniform
function cannot discriminate.

`RepresentsDiscriminatingImport` enriches a `WorkingSystem` with
two concrete claims (good and bad) that the import function must
distinguish.  When `¬HasHeaders`, the system is in the
`DiscriminatingImport` scenario. -/

/-- A system represents a discriminating import scenario if it faces
    two claims that must be distinguished on import: one should be
    accepted, one rejected.

    The structural point: without metadata (headers), claims are
    indistinguishable, so any import function is uniform.
    `no_sound_complete_uniform_import` proves that a uniform function
    cannot be both sound and complete — any proposed function either
    accepts the bad claim or rejects the good one.

    Whether a system's import function is ACTUALLY uniform (the bridge
    hypothesis) depends on the system and is carried as a separate hypothesis
    in the right-branch embedding theorems. -/
structure RepresentsDiscriminatingImport (W : WorkingSystem) where
  /-- The claim type crossing scope boundaries. -/
  Claim : Type
  /-- A claim the receiver should accept. -/
  good : Claim
  /-- A claim the receiver should reject. -/
  bad : Claim
  /-- The claims are distinct. -/
  good_ne_bad : good ≠ bad

/-- Extract `DiscriminatingImport` from a system that
    `RepresentsDiscriminatingImport`. -/
def RepresentsDiscriminatingImport.toImport {W : WorkingSystem}
    (R : RepresentsDiscriminatingImport W) : DiscriminatingImport where
  Claim := R.Claim
  good := R.good
  bad := R.bad
  good_ne_bad := R.good_ne_bad

/-- **Right-branch embedding (export direction).**

    A system with discriminating import needs and no headers:
    any import function `f` must satisfy `f good = true` and
    `f bad = false` for sound-and-complete import.  The bridge hypothesis
    (`h_uniform`) says that without headers,
    the import function is uniform: `f x = f y` for all `x y`.
    `no_sound_complete_uniform_import` fires via `Bool.noConfusion`
    to derive False. -/
theorem discriminating_import_without_headers_embeds
    (W : WorkingSystem)
    (R : RepresentsDiscriminatingImport W)
    (_h_no_headers : ¬HasHeaders W)
    (f : R.Claim → Bool)
    (h_uniform : ∀ x y, f x = f y)
    (h_sound : f R.bad = false)
    (h_complete : f R.good = true) :
    False :=
  no_sound_complete_uniform_import R.toImport f h_uniform h_sound h_complete

/-- **Per-dimension structural forcing (headers).**

    Any system carrying a `RepresentsDiscriminatingImport` witness and a
    uniform-yet-sound-and-complete import function is forced to have headers.
    No `handles_export W` required. -/
theorem discriminating_import_forces_headers
    (W : WorkingSystem) (R : RepresentsDiscriminatingImport W)
    (f : ¬HasHeaders W → R.Claim → Bool)
    (h_unif : ∀ h x y, f h x = f h y)
    (h_sound : ∀ h, f h R.bad = false)
    (h_complete : ∀ h, f h R.good = true) :
    HasHeaders W := by
  by_cases h : HasHeaders W
  · exact h
  · exact (discriminating_import_without_headers_embeds W R h (f h) (h_unif h) (h_sound h) (h_complete h)).elim


/-! ### Scenario 5: Bounded Verification (Bounded Audit → Trust Bridges)

When full verification is costly, some claims exceed any fixed budget.
A verification-only import policy cannot handle those claims.

`RepresentsBoundedVerification` enriches a `WorkingSystem` with a
concrete claim universe where at least one claim exceeds the verification
budget.  When `¬HasTrustBridges`, the system is in the
`BoundedVerification` scenario. -/

/-- A system represents bounded verification if, absent trust bridges,
    it faces claims whose verification cost exceeds the budget.

    The `hard_claim_without_trust` field is the bridge condition: without
    trust-based import, the system must reverify every claim, but at
    least one claim exceeds the budget. -/
structure RepresentsBoundedVerification (W : WorkingSystem) where
  /-- The claim type. -/
  Claim : Type
  /-- Cost to fully verify a claim. -/
  verify_cost : Claim → Nat
  /-- Maximum verification budget per import. -/
  budget : Nat
  /-- A claim that exceeds the budget. -/
  hard_claim : Claim
  /-- The hard claim genuinely exceeds the budget. -/
  exceeds_budget : verify_cost hard_claim > budget

/-- Extract `BoundedVerification` from a system that
    `RepresentsBoundedVerification`. -/
def RepresentsBoundedVerification.toVerification {W : WorkingSystem}
    (R : RepresentsBoundedVerification W) : BoundedVerification where
  Claim := R.Claim
  verify_cost := R.verify_cost
  budget := R.budget
  hard_claim := R.hard_claim
  exceeds_budget := R.exceeds_budget

/-- **Right-branch embedding (trust direction).**

    A system with bounded verification and no trust bridges:
    `verification_only_import_incomplete` fires via Nat arithmetic
    to prove that at least one claim cannot be reverified within
    budget. -/
theorem bounded_verification_without_trust_embeds
    (W : WorkingSystem)
    (R : RepresentsBoundedVerification W)
    (_h_no_trust : ¬HasTrustBridges W)
    (h_all_within : ∀ c, R.verify_cost c ≤ R.budget) :
    False :=
  verification_only_import_incomplete R.toVerification h_all_within

/-- **Per-dimension structural forcing (trust bridges).**

    Any system carrying a `RepresentsBoundedVerification` witness and evidence
    that all claims fit within the budget is forced to have trust bridges.
    No `handles_bounded_audit W` required. -/
theorem bounded_verification_forces_trust_bridges
    (W : WorkingSystem) (R : RepresentsBoundedVerification W)
    (h_all : ¬HasTrustBridges W → ∀ c, R.verify_cost c ≤ R.budget) :
    HasTrustBridges W := by
  by_cases h : HasTrustBridges W
  · exact h
  · exact (bounded_verification_without_trust_embeds W R h (h_all h)).elim


/-! ### Scenario 6: Closed Endorsement (Truth Pressure → Redeemability)

In a closed endorsement system (no external constraint surface), the
only notion of truth is internal consensus.  Every endorsed claim is
true by definition — there is nothing external it could fail against.

`RepresentsClosedEndorsement` enriches a `WorkingSystem` with a
concrete claim, its endorsement, and evidence that the system is
closed absent redeemability.  When `¬HasRedeemability`, the system
is in the `ClosedEndorsement` scenario. -/

/-- A system represents a closed endorsement scenario if, absent
    redeemability, endorsed claims cannot be externally falsified.

    The `closed_without_redeemability` field is the bridge condition:
    without external constraint-surface contact, no endorsed claim
    is falsifiable. -/
structure RepresentsClosedEndorsement (W : WorkingSystem) where
  /-- The claim type. -/
  Claim : Type
  /-- Internal endorsement (consensus). -/
  endorsed : Claim → Prop
  /-- External falsifiability. -/
  externally_falsifiable : Claim → Prop
  /-- Without redeemability, the system is closed. -/
  closed_without_redeemability :
    ¬HasRedeemability W → ∀ c, endorsed c → ¬externally_falsifiable c

/-- Extract `ClosedEndorsement` from a system that
    `RepresentsClosedEndorsement` and lacks redeemability. -/
def RepresentsClosedEndorsement.toClosed {W : WorkingSystem}
    (R : RepresentsClosedEndorsement W) (h_no_redeem : ¬HasRedeemability W) :
    ClosedEndorsement where
  Claim := R.Claim
  endorsed := R.endorsed
  externally_falsifiable := R.externally_falsifiable
  closed := R.closed_without_redeemability h_no_redeem

/-- **Right-branch embedding (truth pressure direction).**

    A system with closed endorsement and no redeemability:
    `closed_system_unfalsifiable` fires to prove no endorsed claim
    can be simultaneously falsifiable — contradicting truth pressure. -/
theorem closed_endorsement_without_redeemability_embeds
    (W : WorkingSystem)
    (R : RepresentsClosedEndorsement W)
    (h_no_redeem : ¬HasRedeemability W)
    (c : R.Claim)
    (h_end : R.endorsed c)
    (h_fals : R.externally_falsifiable c) :
    False :=
  let M := R.toClosed h_no_redeem
  closed_system_unfalsifiable M ⟨c, h_end, h_fals⟩

/-- **Per-dimension structural forcing (redeemability).**

    Any system carrying a `RepresentsClosedEndorsement` witness, an endorsed
    claim, and evidence that it is externally falsifiable absent redeemability,
    is forced to have redeemability.  No `handles_truth_pressure W` required. -/
theorem closed_endorsement_forces_redeemability
    (W : WorkingSystem) (R : RepresentsClosedEndorsement W)
    (c : R.Claim)
    (h_end : R.endorsed c)
    (h_fals : ¬HasRedeemability W → R.externally_falsifiable c) :
    HasRedeemability W := by
  by_cases h : HasRedeemability W
  · exact h
  · exact (closed_endorsement_without_redeemability_embeds W R h c h_end (h_fals h)).elim


/-! ## Bundled Witness Packages

Two structures replace the 20+ loose parameters of the all-six forcing theorem
with named records, separated by the nature of the evidence they carry.

**`SystemOperationalBundle W`** — the three *architectural* dimensions:
scope disagreement, discriminating import, private coordination.  These are
purely operational/topological facts about the system.  They have no
world-semantic counterpart in `WorldCtx`.

**`WorldBridgeBundle W`** — the three *world-adjacent* dimensions:
monotonic lifecycle (revocation), bounded verification (trust), closed
endorsement (redeemability).  These correspond semantically to the W_* world
bundles, but the `Represents*` instances and their bridge hypotheses are
W-specific data that cannot be derived from W_* bundles alone.  A future
bridge layer may close that gap; for now they are supplied explicitly. -/

/-- Bundled witnesses for the three purely architectural dimensions:
    scope (disagreement), headers (discriminating import), bank (coordination).

    Each field group is: a `Represents*` structural witness followed by the
    per-dimension bridge hypothesis that makes the impossible scenario
    constructible when the corresponding feature is absent.

    None of these fields carry world-semantic content — they describe
    the system's operational topology independently of any `WorldCtx`. -/
structure SystemOperationalBundle (W : WorkingSystem) where
  /-- Scope dimension: a disagreement scenario witness. -/
  Rd          : RepresentsDisagreement W
  /-- Without bubbles, a flat acceptance function faithfully represents both agents. -/
  flat_accept : ¬HasBubbles W → Rd.Claim → Prop
  hflat₁      : ∀ h c, flat_accept h c ↔ Rd.accept₁ c
  hflat₂      : ∀ h c, flat_accept h c ↔ Rd.accept₂ c
  /-- Headers dimension: a discriminating import scenario witness. -/
  Ri          : RepresentsDiscriminatingImport W
  /-- Without headers, the import function is uniform. -/
  f_import    : ¬HasHeaders W → Ri.Claim → Bool
  h_unif      : ∀ h x y, f_import h x = f_import h y
  h_sound     : ∀ h, f_import h Ri.bad = false
  h_complete  : ∀ h, f_import h Ri.good = true
  /-- Bank dimension: a private coordination scenario witness. -/
  Rp             : RepresentsPrivateCoordination W
  /-- Without a shared ledger, both agents still access this deposit. -/
  shared_deposit : ¬HasBank W → Rp.Deposit
  h_access₁      : ∀ h, Rp.has_access Rp.a₁ (shared_deposit h)
  h_access₂      : ∀ h, Rp.has_access Rp.a₂ (shared_deposit h)

/-- Bundled witnesses for the three world-adjacent dimensions:
    revocation (adversarial/lies), trust (bounded verification),
    redeemability (truth pressure).

    These dimensions are semantically sourced by the EpArch W_* world bundles,
    but the structural scenario witnesses and their bridge hypotheses are
    W-specific: `RepresentsMonotonicLifecycle W`, `RepresentsBoundedVerification W`,
    and `RepresentsClosedEndorsement W` carry data about the concrete system `W`,
    not about the world context. -/
structure WorldBridgeBundle (W : WorkingSystem) where
  /-- Revocation dimension: a monotonic lifecycle scenario witness. -/
  Rm           : RepresentsMonotonicLifecycle W
  /-- The step count at which the accepted state escapes absent revocation. -/
  n_rev        : Nat
  h_rev_escape : ¬HasRevocation W → iter Rm.step n_rev Rm.accepted ≠ Rm.accepted
  /-- Trust dimension: a bounded verification scenario witness. -/
  Rb           : RepresentsBoundedVerification W
  h_trust_all  : ¬HasTrustBridges W → ∀ c, Rb.verify_cost c ≤ Rb.budget
  /-- Redeemability dimension: a closed endorsement scenario witness. -/
  Re           : RepresentsClosedEndorsement W
  c_re         : Re.Claim
  h_endorsed   : Re.endorsed c_re
  h_fals       : ¬HasRedeemability W → Re.externally_falsifiable c_re


/-! ## Convergence and Impossibility (Structural Versions) -/

/-- Convergence theorem (structural version): under structural forcing,
    any system satisfying all properties contains Bank primitives.

    The proof does **not** depend on assumed biconditionals — only on the
    forward-direction implications justified by the structural models. -/
theorem convergence_structural (W : WorkingSystem) (h_sf : StructurallyForced W) :
    SatisfiesAllProperties W → containsBankPrimitives W := by
  intro ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h_sf.scope_forcing h1, h_sf.trust_forcing h2, h_sf.header_forcing h3,
         h_sf.revocation_forcing h4, h_sf.bank_forcing h5, h_sf.redeemability_forcing h6⟩

/-- Structural impossibility: missing any feature blocks all-property satisfaction. -/
theorem structural_impossibility (W : WorkingSystem) (h_sf : StructurallyForced W) :
    (¬HasBubbles W ∨ ¬HasTrustBridges W ∨ ¬HasHeaders W ∨
     ¬HasRevocation W ∨ ¬HasBank W ∨ ¬HasRedeemability W) →
    ¬SatisfiesAllProperties W := by
  intro h_missing h_sat
  have h_bp := convergence_structural W h_sf h_sat
  unfold containsBankPrimitives at h_bp
  cases h_missing with
  | inl h => exact h h_bp.1
  | inr h => cases h with
    | inl h => exact h h_bp.2.1
    | inr h => cases h with
      | inl h => exact h h_bp.2.2.1
      | inr h => cases h with
        | inl h => exact h h_bp.2.2.2.1
        | inr h => cases h with
          | inl h => exact h h_bp.2.2.2.2.1
          | inr h => exact h h_bp.2.2.2.2.2

end EpArch
