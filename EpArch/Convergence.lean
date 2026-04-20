/-
EpArch.Convergence — Convergence Theorem and Structural Proof Machinery

The central convergence theorem: any WorkingSystem that is StructurallyForced
and satisfies all eight forcing dimensions necessarily contains Bank primitives.

Key exports:
- StructurallyForced (forward-only forcing implications, capability → feature)
- ForcingEmbedding (auditable disjunction connecting WorkingSystems to
  structural models; embedding_to_structurally_forced derives
  StructurallyForced constructively)
- Bridge predicates (BridgeBubbles … BridgeAuthorization) and
  bridge_*_impossible theorems (system-independent impossibility)
- convergence_structural (the central theorem)
- structural_impossibility (missing any feature blocks all-property satisfaction)

Depends on EpArch.Minimality for WorkingSystem, structural models, and
impossibility theorems. Scenario predicates (Represents*) live in
EpArch.Scenarios.
-/

import EpArch.Minimality

namespace EpArch

/-! ## StructurallyForced: Forward-Direction Forcing

`StructurallyForced` packages the eight `handles_X → HasY` forcing implications
as a single universally-quantified field indexed by `Pressure`.  Pattern-matching
on `Pressure` is machine-exhaustive: if a new dimension is added, every `cases P`
proof requires a new case.

Each `handles_pressure W P → forced_feature W P` instance is independently
justified by a structural impossibility model in EpArch.Minimality. -/

/-- The eight structural impossibility consequences readable from a `WorkingSystem`'s
    stored `GroundedXStrict` evidence.

    Separated from `StructurallyForced` so that the forcing interface and the
    evidence-readout bundle remain conceptually distinct.  When strict evidence
    is present the consequence is already carried by the value — these eight fields
    simply expose it. -/
structure EvidenceConsequences (W : WorkingSystem) : Prop where
  /-- Scope separation is structurally forced: no flat resolver can represent both scopes. -/
  scope_consequence : ∀ G : GroundedBubblesStrict, W.bubbles_ev = some G →
      ¬∃ (f : G.base.Claim → Prop),
          (∀ c, f c ↔ G.base.scope₁ c) ∧ (∀ c, f c ↔ G.base.scope₂ c)
  /-- Trust bridge forcing: any downstream-sound policy must accept the bridge witness. -/
  trust_consequence : ∀ G : GroundedTrustBridgesStrict, W.bridges_ev = some G →
      ∀ (policy : G.base.Declaration → Prop),
          (∀ d, G.base.downstream_accepts d → policy d) → policy G.base.witness
  /-- Header routing invariant: no router changes its decision at the export boundary. -/
  headers_consequence : ∀ G : GroundedHeadersStrict, W.headers_ev = some G →
      ∀ (router : G.base.Header → Bool),
          router (G.base.extract G.base.witness) =
          router (G.base.extract (G.base.export_datum G.base.witness))
  /-- Revocation forcing: an invalid-but-revocable witness is known. -/
  revocation_consequence : ∀ G : GroundedRevocationStrict, W.revocation_ev = some G →
      ∃ c : G.base.Claim, G.base.revocable c ∧ ¬G.base.valid c
  /-- Bank forcing: a cross-agent shared entry is known. -/
  bank_consequence : ∀ G : GroundedBankStrict, W.bank_ev = some G →
      ∃ e : G.base.Entry, G.base.agent₁_produces e ∧ G.base.agent₂_consumes e
  /-- Redeemability forcing: a constrained-and-redeemable witness is known. -/
  redeemability_consequence : ∀ G : GroundedRedeemabilityStrict, W.redeemability_ev = some G →
      ∃ c : G.base.Claim, G.base.constrained c ∧ G.base.redeemable c
  /-- Authorization forcing: no flat predicate can represent both the submission and commit tiers. -/
  authorization_consequence : ∀ G : GroundedAuthorizationStrict, W.authorization_ev = some G →
      ¬∃ (f : G.base.Agent → G.base.Claim → Prop),
          (∀ a c, f a c ↔ G.base.can_propose a c) ∧ (∀ a c, f a c ↔ G.base.can_commit a c)
  /-- Storage forcing: no fixed budget covers all states in this bounded-capacity scenario. -/
  storage_consequence : ∀ G : GroundedStorageStrict, W.storage_ev = some G →
      ¬(∀ s : G.base.State, G.base.count s ≤ G.base.budget)

/-- A system is structurally forced: for every pressure dimension, handling
    the capability implies the forced architectural feature.

    `forcing` is the core convergence interface: the eight unguarded
    capability→feature implications, derived from the `ForcingEmbedding`.

    `evidence` is the structural consequence bundle: impossibility proofs
    read directly from the system's stored `GroundedXStrict` fields.  The two
    are logically independent — `forcing` is about implication chains;
    `evidence` is about what the stored proof objects already carry. -/
structure StructurallyForced (W : WorkingSystem) : Prop where
  /-- For every pressure dimension P, handling capability P forces feature P.
      Justified per-dimension by the structural models in EpArch.Minimality. -/
  forcing : ∀ P : Pressure, handles_pressure W P → forced_feature W P
  /-- Structural consequence bundle: the eight impossibility results read from
      the stored `GroundedXStrict` evidence. -/
  evidence : EvidenceConsequences W

/-! ## Forcing Embeddings: Translation Layer

The structural models above prove clean no-go lemmas on abstract scenarios.
`StructurallyForced` packages the forward implications (capability → feature).
`ForcingEmbedding` provides the mechanical derivation.  Each field says:

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

/-- A system is bridge-committed on authorization: a single flat predicate represents
    both the submission tier and the commit tier simultaneously.  The commitment that
    lat_authorization_impossible proves is universally impossible: the scenario
    already carries a submitter that can propose but not commit. -/
def BridgeAuthorization (_W : WorkingSystem) : Prop :=
  ∃ M : TwoTierAccess, ∃ f : M.Agent → M.Claim → Prop,
    (∀ a c, f a c ↔ M.can_propose a c) ∧ (∀ a c, f a c ↔ M.can_commit a c)

/-- The authorization bridge scenario is universally impossible: no flat predicate
    can represent both tiers of a TwoTierAccess scenario.
    Proof: passes the flat predicate hypothesis directly to lat_authorization_impossible. -/
theorem bridge_authorization_impossible (_W : WorkingSystem) : ¬BridgeAuthorization _W :=
  fun ⟨M, h_flat⟩ => flat_authorization_impossible M h_flat
/-- A system is bridge-committed on storage: all active-deposit states stay within budget. -/
def BridgeStorage (_W : WorkingSystem) : Prop :=
  ∃ M : BoundedStorage, ∀ s : M.State, M.count s ≤ M.budget

/-- The storage bridge scenario is universally impossible: no fixed budget covers
    all states in any bounded-capacity scenario: the witness state exceeds the budget. -/
theorem bridge_storage_impossible (_W : WorkingSystem) : ¬BridgeStorage _W :=
  fun ⟨M, hM⟩ => monotone_active_accumulation_overflows M hM

/-- Maps each `Pressure` dimension to its bridge-scenario predicate.
    Used as the right disjunct in `ForcingEmbedding.embed`. -/
def bridge_scenario (W : WorkingSystem) : Pressure → Prop
  | .scope         => BridgeBubbles W
  | .trust         => BridgeTrust W
  | .headers       => BridgeHeaders W
  | .revocation    => BridgeRevocation W
  | .bank          => BridgeBank W
  | .redeemability => BridgeRedeemability W
  | .authorization => BridgeAuthorization W
  | .storage       => BridgeStorage W

/-- Every bridge scenario is universally impossible: committing to the
    impossible scenario for any dimension yields `False`.
    Proof by exhaustive pattern match — Lean verifies all eight cases. -/
theorem all_bridges_impossible (W : WorkingSystem) (P : Pressure) : ¬bridge_scenario W P := by
  cases P
  · exact bridge_bubbles_impossible W
  · exact bridge_trust_impossible W
  · exact bridge_headers_impossible W
  · exact bridge_revocation_impossible W
  · exact bridge_bank_impossible W
  · exact bridge_redeemability_impossible W
  · exact bridge_authorization_impossible W
  · exact bridge_storage_impossible W

/-- Forcing embeddings: connects a `WorkingSystem` to the abstract
    structural models via an auditable disjunction, indexed by `Pressure`.

    The single field says: for every pressure dimension P, a system handling
    capability P either already has the forced feature, OR is bridge-committed
    to the impossible scenario for that dimension.  Since bridge commitment
    forces the feature (via `all_bridges_impossible`), the feature holds
    in both branches. -/
structure ForcingEmbedding (W : WorkingSystem) : Prop where
  /-- For every pressure dimension P, handling capability P either yields
      the forced feature or commits to the universally impossible scenario. -/
  embed : ∀ P : Pressure, handles_pressure W P →
    forced_feature W P ∨ bridge_scenario W P

/-- Mechanical derivation: `ForcingEmbedding` → `StructurallyForced`.

    The `forcing` field is derived by `Or.elim`: the left branch is the feature
    itself (`id`); the right branch applies `all_bridges_impossible P`, which
    proves `¬bridge_scenario W P` directly — so the right branch is universally
    absurd.  Fully constructive — no `Classical.byContradiction`.

    The `evidence` bundle reads proof terms directly from the stored
    `GroundedXStrict` evidence: each consequence is already carried by the
    value, so each field is `fun G _h_ev => G.consequence`.  `_h_ev` is named
    (not `_`) to acknowledge the discarded equality `W.*_ev = some G`; it is
    structurally redundant here because any `G : GroundedXStrict` self-certifies
    the consequence by type.  For pinned-evidence proofs that use the stored
    witness identity, see `concrete_structurally_forced` and
    `grounded_evidence_consequences`. -/
theorem embedding_to_structurally_forced (W : WorkingSystem) (E : ForcingEmbedding W) :
    StructurallyForced W where
  forcing P h := (E.embed P h).elim id (fun hb => absurd hb (all_bridges_impossible W P))
  evidence := {
    scope_consequence         := fun G _h_ev => G.no_flat_resolver
    trust_consequence         := fun G _h_ev => G.bridge_forces_acceptance
    headers_consequence       := fun G _h_ev => G.routing_invariant
    revocation_consequence    := fun G _h_ev => G.has_invalid_revocable_witness
    bank_consequence          := fun G _h_ev => G.has_shared_entry
    redeemability_consequence := fun G _h_ev => G.has_constrained_redeemable_witness
    authorization_consequence := fun G _h_ev => G.no_flat_tier
    storage_consequence       := fun G _h_ev => G.no_unbounded_accumulation }


/-! ## Convergence and Impossibility (Structural Versions) -/

/-- Convergence theorem (structural version): under structural forcing,
    any system satisfying all properties contains Bank primitives.

    The proof does **not** depend on assumed biconditionals — only on the
    forward-direction implications justified by the structural models. -/
theorem convergence_structural (W : WorkingSystem) (h_sf : StructurallyForced W) :
    SatisfiesAllProperties W → containsBankPrimitives W :=
  fun h_sat P => h_sf.forcing P (h_sat P)

/-- Structural impossibility: missing any feature blocks all-property satisfaction. -/
theorem structural_impossibility (W : WorkingSystem) (h_sf : StructurallyForced W) :
    (∃ P : Pressure, ¬forced_feature W P) → ¬SatisfiesAllProperties W :=
  fun ⟨P, h_miss⟩ h_sat => absurd (h_sf.forcing P (h_sat P)) h_miss

/-- When a structurally forced system satisfies all properties, each stored
    `GroundedXStrict` witness satisfies its dimension's structural consequence.
    `SatisfiesAllProperties W` forces each `*_ev` field to be `some G`;
    the `none` branch is contradicted by `h_sat` via `Bool.noConfusion`.
    `h_sf.evidence.X_consequence G h_ev` then extracts the consequence from G. -/
theorem grounded_evidence_consequences (W : WorkingSystem)
    (h_sf : StructurallyForced W) (h_sat : SatisfiesAllProperties W) :
    containsBankPrimitives W ∧
    (∃ G : GroundedBubblesStrict, W.bubbles_ev = some G ∧
        ¬∃ (f : G.base.Claim → Prop),
            (∀ c, f c ↔ G.base.scope₁ c) ∧ (∀ c, f c ↔ G.base.scope₂ c)) ∧
    (∃ G : GroundedTrustBridgesStrict, W.bridges_ev = some G ∧
        ∀ (policy : G.base.Declaration → Prop),
            (∀ d, G.base.downstream_accepts d → policy d) → policy G.base.witness) ∧
    (∃ G : GroundedHeadersStrict, W.headers_ev = some G ∧
        ∀ (router : G.base.Header → Bool),
            router (G.base.extract G.base.witness) =
            router (G.base.extract (G.base.export_datum G.base.witness))) ∧
    (∃ G : GroundedRevocationStrict, W.revocation_ev = some G ∧
        ∃ c : G.base.Claim, G.base.revocable c ∧ ¬G.base.valid c) ∧
    (∃ G : GroundedBankStrict, W.bank_ev = some G ∧
        ∃ e : G.base.Entry, G.base.agent₁_produces e ∧ G.base.agent₂_consumes e) ∧
    (∃ G : GroundedRedeemabilityStrict, W.redeemability_ev = some G ∧
        ∃ c : G.base.Claim, G.base.constrained c ∧ G.base.redeemable c) ∧
    (∃ G : GroundedAuthorizationStrict, W.authorization_ev = some G ∧
        ¬∃ (f : G.base.Agent → G.base.Claim → Prop),
            (∀ a c, f a c ↔ G.base.can_propose a c) ∧ (∀ a c, f a c ↔ G.base.can_commit a c)) ∧
    (∃ G : GroundedStorageStrict, W.storage_ev = some G ∧
        ¬(∀ s : G.base.State, G.base.count s ≤ G.base.budget)) := by
  refine ⟨convergence_structural W h_sf h_sat, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- Each goal: none-branch contradicted via Bool.noConfusion h2;
  -- some G branch closed via h_sf.evidence.X_consequence G h_ev.
  · have h2 : W.bubbles_ev.isSome = true := by
      have h := h_sat .scope
      simp only [handles_pressure, handles_distributed_agents] at h; exact h
    cases h_ev : W.bubbles_ev with
    | none   => rw [h_ev] at h2; exact Bool.noConfusion h2
    | some G => exact ⟨G, rfl, h_sf.evidence.scope_consequence G h_ev⟩
  · have h2 : W.bridges_ev.isSome = true := by
      have h := h_sat .trust
      simp only [handles_pressure, handles_bounded_audit] at h; exact h
    cases h_ev : W.bridges_ev with
    | none   => rw [h_ev] at h2; exact Bool.noConfusion h2
    | some G => exact ⟨G, rfl, h_sf.evidence.trust_consequence G h_ev⟩
  · have h2 : W.headers_ev.isSome = true := by
      have h := h_sat .headers
      simp only [handles_pressure, handles_export] at h; exact h
    cases h_ev : W.headers_ev with
    | none   => rw [h_ev] at h2; exact Bool.noConfusion h2
    | some G => exact ⟨G, rfl, h_sf.evidence.headers_consequence G h_ev⟩
  · have h2 : W.revocation_ev.isSome = true := by
      have h := h_sat .revocation
      simp only [handles_pressure, handles_adversarial] at h; exact h
    cases h_ev : W.revocation_ev with
    | none   => rw [h_ev] at h2; exact Bool.noConfusion h2
    | some G => exact ⟨G, rfl, h_sf.evidence.revocation_consequence G h_ev⟩
  · have h2 : W.bank_ev.isSome = true := by
      have h := h_sat .bank
      simp only [handles_pressure, handles_coordination] at h; exact h
    cases h_ev : W.bank_ev with
    | none   => rw [h_ev] at h2; exact Bool.noConfusion h2
    | some G => exact ⟨G, rfl, h_sf.evidence.bank_consequence G h_ev⟩
  · have h2 : W.redeemability_ev.isSome = true := by
      have h := h_sat .redeemability
      simp only [handles_pressure, handles_truth_pressure] at h; exact h
    cases h_ev : W.redeemability_ev with
    | none   => rw [h_ev] at h2; exact Bool.noConfusion h2
    | some G => exact ⟨G, rfl, h_sf.evidence.redeemability_consequence G h_ev⟩
  · have h2 : W.authorization_ev.isSome = true := by
      have h := h_sat .authorization
      simp only [handles_pressure, handles_multi_agent] at h; exact h
    cases h_ev : W.authorization_ev with
    | none   => rw [h_ev] at h2; exact Bool.noConfusion h2
    | some G => exact ⟨G, rfl, h_sf.evidence.authorization_consequence G h_ev⟩
  · have h2 : W.storage_ev.isSome = true := by
      have h := h_sat .storage
      simp only [handles_pressure, handles_storage] at h; exact h
    cases h_ev : W.storage_ev with
    | none   => rw [h_ev] at h2; exact Bool.noConfusion h2
    | some G => exact ⟨G, rfl, h_sf.evidence.storage_consequence G h_ev⟩


end EpArch
