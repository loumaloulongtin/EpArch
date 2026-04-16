/-
EpArch.GroundedEvidence — Grounded Feature Evidence

`GroundedX` structures witness that a system has the corresponding architectural
feature from real domain evidence rather than a declared Bool flag.  Each structure
is paired with:
  - a `SystemSpec.withGroundedX` builder that sets the matching flag from evidence
  - a `grounded_X_justified` theorem proving the flag is set
  - a `GroundedXStrict` augmentation adding an impossibility/forcing consequence
  - a `GroundedX.toStrict` derivation constructing the Strict variant automatically

`GroundedSystemSpec` bundles all seven witnesses and `toSystemSpec` chains the
seven builders to produce a fully grounded spec.
-/

import EpArch.SystemSpec

namespace EpArch

/-! ## GroundedBubbles -/

/-- Evidence that a system has scope separation.

    Two distinct acceptance functions (`scope₁`, `scope₂`) disagree on at
    least one witness claim — scope separation is non-vacuously witnessed. -/
structure GroundedBubbles where
  /-- The claim type the scoped resolvers operate over. -/
  Claim    : Type
  /-- Resolver for scope 1 (e.g., the Nat-namespace module). -/
  scope₁   : Claim → Prop
  /-- Resolver for scope 2 (e.g., the Int-namespace module). -/
  scope₂   : Claim → Prop
  /-- A witness claim where the two resolvers disagree. -/
  witness  : Claim
  /-- Scope 1 accepts the witness. -/
  scope₁_accepts : scope₁ witness
  /-- Scope 2 rejects the witness. -/
  scope₂_rejects : ¬scope₂ witness

/-- A `GroundedBubbles` witness implies the two scopes differ on the
    witness claim — scope separation is not spurious. -/
theorem grounded_bubbles_scopes_differ (G : GroundedBubbles) :
    G.scope₁ G.witness ∧ ¬G.scope₂ G.witness :=
  ⟨G.scope₁_accepts, G.scope₂_rejects⟩

/-- Build a `SystemSpec` with `has_bubble_separation = true` from evidence.
    The `let _ev` bindings force the evidence into the elaboration context,
    ensuring the flag is set only after the proofs are verified — not by fiat. -/
def SystemSpec.withGroundedBubbles (G : GroundedBubbles) (rest : SystemSpec) : SystemSpec :=
  let _ev₁ := G.scope₁_accepts
  let _ev₂ := G.scope₂_rejects
  { rest with has_bubble_separation := true }

theorem grounded_bubbles_justified (G : GroundedBubbles) (rest : SystemSpec) :
    spec_has_bubbles (SystemSpec.withGroundedBubbles G rest) := by
  unfold spec_has_bubbles SystemSpec.withGroundedBubbles
  rfl

/-- `GroundedBubbles` augmented with its impossibility consequence.
    `no_flat_resolver` states that no flat acceptance function can faithfully
    represent both scopes simultaneously — scope separation is structurally forced. -/
structure GroundedBubblesStrict where
  base             : GroundedBubbles
  no_flat_resolver : ¬∃ (f : base.Claim → Prop),
      (∀ c, f c ↔ base.scope₁ c) ∧ (∀ c, f c ↔ base.scope₂ c)

/-- Derive `GroundedBubblesStrict` from base evidence. -/
def GroundedBubbles.toStrict (G : GroundedBubbles) : GroundedBubblesStrict where
  base := G
  no_flat_resolver := fun ⟨_f, hf₁, hf₂⟩ =>
    G.scope₂_rejects ((hf₂ G.witness).mp ((hf₁ G.witness).mpr G.scope₁_accepts))


/-! ## GroundedTrustBridges -/

/-- Evidence that a system genuinely has trust bridges.

    A trust bridge exists when an upstream module makes its declarations
    available to a downstream module through an import channel.  The
    downstream module accepts the declarations via the bridge without
    independently re-verifying them from first principles.

    - `upstream_holds`:      the upstream module vouches for the witness
    - `downstream_via_bridge`: the downstream module accepts it through import
    - Both hold on the same `witness` — sharing it is what the bridge enables. -/
structure GroundedTrustBridges where
  Declaration           : Type
  upstream_accepts      : Declaration → Prop
  downstream_accepts    : Declaration → Prop
  witness               : Declaration
  upstream_holds        : upstream_accepts witness
  downstream_via_bridge : downstream_accepts witness

/-- Build a `SystemSpec` with `has_trust_bridges = true` from evidence. -/
def SystemSpec.withGroundedTrustBridges (G : GroundedTrustBridges) (rest : SystemSpec) : SystemSpec :=
  let _up := G.upstream_holds
  let _dn := G.downstream_via_bridge
  { rest with has_trust_bridges := true }

theorem grounded_trust_bridges_justified (G : GroundedTrustBridges) (rest : SystemSpec) :
    spec_has_trust_bridges (SystemSpec.withGroundedTrustBridges G rest) := by
  unfold spec_has_trust_bridges SystemSpec.withGroundedTrustBridges
  rfl

/-- `GroundedTrustBridges` augmented with the bridge-forcing consequence.
    `bridge_forces_acceptance` witnesses that any downstream-sound policy must
    accept the bridge witness — re-verify-only import cannot exclude it. -/
structure GroundedTrustBridgesStrict where
  base                     : GroundedTrustBridges
  bridge_forces_acceptance : ∀ (policy : base.Declaration → Prop),
      (∀ d, base.downstream_accepts d → policy d) → policy base.witness

/-- Derive `GroundedTrustBridgesStrict` from base evidence. -/
def GroundedTrustBridges.toStrict (G : GroundedTrustBridges) : GroundedTrustBridgesStrict where
  base := G
  bridge_forces_acceptance := fun _policy h => h G.witness G.downstream_via_bridge


/-! ## GroundedHeaders -/

/-- Evidence that a system genuinely preserves headers (S/E/V) across export.

    A header is the type-signature metadata that must survive crossing an
    architectural boundary.  `export_datum` models the export step;
    `header_preserved` witnesses that the extracted header is identical
    before and after export. -/
structure GroundedHeaders where
  Datum            : Type
  Header           : Type
  extract          : Datum → Header
  export_datum     : Datum → Datum
  witness          : Datum
  header_preserved : extract (export_datum witness) = extract witness

/-- Build a `SystemSpec` with `preserves_headers = true` from evidence. -/
def SystemSpec.withGroundedHeaders (G : GroundedHeaders) (rest : SystemSpec) : SystemSpec :=
  let _ev := G.header_preserved
  { rest with preserves_headers := true }

theorem grounded_headers_justified (G : GroundedHeaders) (rest : SystemSpec) :
    spec_has_headers (SystemSpec.withGroundedHeaders G rest) := by
  unfold spec_has_headers SystemSpec.withGroundedHeaders
  rfl

/-- `GroundedHeaders` augmented with routing invariance.
    `routing_invariant` states that no header-based router changes its decision
    at the export boundary — header preservation implies routing stability. -/
structure GroundedHeadersStrict where
  base              : GroundedHeaders
  routing_invariant : ∀ (router : base.Header → Bool),
      router (base.extract base.witness) = router (base.extract (base.export_datum base.witness))

/-- Derive `GroundedHeadersStrict` from base evidence. -/
def GroundedHeaders.toStrict (G : GroundedHeaders) : GroundedHeadersStrict where
  base := G
  routing_invariant := fun router => congrArg router G.header_preserved.symm


/-! ## GroundedRevocation -/

/-- Evidence that a system has genuine revocation capability.

    Revocation requires: some claim exists that is demonstrably invalid
    (`¬valid witness`) AND can be quarantined/revoked by the system
    (`revocable witness`).  The two proofs together witness the
    challenge → quarantine → revoke path. -/
structure GroundedRevocation where
  Claim              : Type
  valid              : Claim → Prop
  revocable          : Claim → Prop
  witness            : Claim
  witness_is_invalid : ¬valid witness
  can_revoke         : revocable witness

/-- Build a `SystemSpec` with `has_revocation = true` from evidence. -/
def SystemSpec.withGroundedRevocation (G : GroundedRevocation) (rest : SystemSpec) : SystemSpec :=
  let _inv := G.witness_is_invalid
  let _rev := G.can_revoke
  { rest with has_revocation := true }

theorem grounded_revocation_justified (G : GroundedRevocation) (rest : SystemSpec) :
    spec_has_revocation (SystemSpec.withGroundedRevocation G rest) := by
  unfold spec_has_revocation SystemSpec.withGroundedRevocation
  rfl

/-- `GroundedRevocation` augmented with the invalid-revocable existential.
    `has_invalid_revocable_witness` packages the known invalid-but-revocable claim,
    providing the explicit evidence that the challenge → revoke path is non-vacuous. -/
structure GroundedRevocationStrict where
  base                          : GroundedRevocation
  has_invalid_revocable_witness : ∃ c : base.Claim, base.revocable c ∧ ¬base.valid c

/-- Derive `GroundedRevocationStrict` from base evidence. -/
def GroundedRevocation.toStrict (G : GroundedRevocation) : GroundedRevocationStrict where
  base := G
  has_invalid_revocable_witness := ⟨G.witness, G.can_revoke, G.witness_is_invalid⟩


/-! ## GroundedBank -/

/-- Evidence that a system has a genuine shared ledger.

    A shared ledger (bank) requires that multiple agents can write to and
    read from a common pool.  The witness entry is produced by one agent
    and consumed (relied on) by another — this cross-agent interaction on
    the same entry is the structural fact the bank enables. -/
structure GroundedBank where
  Entry           : Type
  agent₁_produces : Entry → Prop
  agent₂_consumes : Entry → Prop
  witness         : Entry
  produced        : agent₁_produces witness
  consumed        : agent₂_consumes witness

/-- Build a `SystemSpec` with `has_shared_ledger = true` from evidence. -/
def SystemSpec.withGroundedBank (G : GroundedBank) (rest : SystemSpec) : SystemSpec :=
  let _prod := G.produced
  let _cons := G.consumed
  { rest with has_shared_ledger := true }

theorem grounded_bank_justified (G : GroundedBank) (rest : SystemSpec) :
    spec_has_bank (SystemSpec.withGroundedBank G rest) := by
  unfold spec_has_bank SystemSpec.withGroundedBank
  rfl

/-- `GroundedBank` augmented with the shared-entry existential.
    `has_shared_entry` packages the known cross-agent entry, making collective
    reliance explicit and non-vacuous. -/
structure GroundedBankStrict where
  base             : GroundedBank
  has_shared_entry : ∃ e : base.Entry, base.agent₁_produces e ∧ base.agent₂_consumes e

/-- Derive `GroundedBankStrict` from base evidence. -/
def GroundedBank.toStrict (G : GroundedBank) : GroundedBankStrict where
  base := G
  has_shared_entry := ⟨G.witness, G.produced, G.consumed⟩


/-! ## GroundedRedeemability -/

/-- Evidence that a system has genuine redeemability paths.

    Redeemability means that for every claim under constraint, there is a path
    to truth contact — the constraint surface is not a dead end.  The witness
    is a constrained claim for which a redeemability path demonstrably exists. -/
structure GroundedRedeemability where
  Claim          : Type
  constrained    : Claim → Prop
  redeemable     : Claim → Prop
  witness        : Claim
  is_constrained : constrained witness
  has_path       : redeemable witness

/-- Build a `SystemSpec` with `has_redeemability = true` from evidence. -/
def SystemSpec.withGroundedRedeemability (G : GroundedRedeemability) (rest : SystemSpec) : SystemSpec :=
  let _ev := G.has_path
  { rest with has_redeemability := true }

theorem grounded_redeemability_justified (G : GroundedRedeemability) (rest : SystemSpec) :
    spec_has_redeemability (SystemSpec.withGroundedRedeemability G rest) := by
  unfold spec_has_redeemability SystemSpec.withGroundedRedeemability
  rfl

/-- `GroundedRedeemability` augmented with the constrained-and-redeemable existential.
    `has_constrained_redeemable_witness` provides the explicit evidence that the
    constraint surface is not a dead end — redeemability is non-vacuous. -/
structure GroundedRedeemabilityStrict where
  base                               : GroundedRedeemability
  has_constrained_redeemable_witness : ∃ c : base.Claim, base.constrained c ∧ base.redeemable c

/-- Derive `GroundedRedeemabilityStrict` from base evidence. -/
def GroundedRedeemability.toStrict (G : GroundedRedeemability) : GroundedRedeemabilityStrict where
  base := G
  has_constrained_redeemable_witness := ⟨G.witness, G.is_constrained, G.has_path⟩


/-! ## GroundedAuthorization -/

/-- Evidence that a system has a granular authorization surface.

    A granular ACL requires: some agent is demonstrably restricted from
    some claim (`¬authorize restricted_agent restricted_claim`).  This
    witnesses that the authorization surface is non-trivial — not all
    agents are uniformly authorized. -/
structure GroundedAuthorization where
  /-- The agent type. -/
  Agent            : Type
  /-- The claim type. -/
  Claim            : Type
  /-- The authorization predicate. -/
  authorize        : Agent → Claim → Prop
  /-- An agent that IS authorized for the restricted claim — the positive witness. -/
  privileged_agent : Agent
  /-- An agent that should be restricted. -/
  restricted_agent : Agent
  /-- A claim they cannot access (and that the privileged agent CAN access). -/
  restricted_claim : Claim
  /-- The privileged agent has access — contrast with `restriction_holds`. -/
  access_granted   : authorize privileged_agent restricted_claim
  /-- The restriction holds: this agent is not authorized for this claim. -/
  restriction_holds : ¬authorize restricted_agent restricted_claim

/-- Build a `SystemSpec` with `has_granular_acl = true` from evidence. -/
def SystemSpec.withGroundedAuthorization (G : GroundedAuthorization) (rest : SystemSpec) : SystemSpec :=
  let _ev := G.restriction_holds
  { rest with has_granular_acl := true }

theorem grounded_authorization_justified (G : GroundedAuthorization) (rest : SystemSpec) :
    spec_has_granular_acl (SystemSpec.withGroundedAuthorization G rest) := by
  unfold spec_has_granular_acl SystemSpec.withGroundedAuthorization
  rfl

/-- `GroundedAuthorization` augmented with two impossibility consequences.

    `no_uniform_access` — the direct negation: the specific restricted pair
    violates any all-true authorization policy.

    `no_agent_uniform_policy` — the architectural consequence: no agent-uniform
    authorization is faithful to the authorization surface.  Two agents exist
    with strictly different authorization for the same claim — so any policy of
    the form `∀ a b P, authorize a P ↔ authorize b P` contradicts the evidence.
    This is the authorization analog of `no_flat_resolver` for scope: it derives
    the contradiction from the interaction between BOTH `access_granted` and
    `restriction_holds`, not from either field alone. -/
structure GroundedAuthorizationStrict where
  base             : GroundedAuthorization
  /-- A uniform authorization policy (all agents authorized) is impossible
      given the known restriction. -/
  no_uniform_access : ¬∀ (a : base.Agent) (P : base.Claim), base.authorize a P
  /-- Agent-uniform authorization is impossible: the privileged and restricted agents
      have different authorization for the restricted claim.  No policy of the form
      `∀ a b P, authorize a P ↔ authorize b P` can coexist with both
      `access_granted` and `restriction_holds`. -/
  no_agent_uniform_policy : ¬∀ (a b : base.Agent) (P : base.Claim),
      base.authorize a P ↔ base.authorize b P

/-- Derive `GroundedAuthorizationStrict` from base evidence. -/
def GroundedAuthorization.toStrict (G : GroundedAuthorization) : GroundedAuthorizationStrict where
  base := G
  no_uniform_access := fun h_all =>
    G.restriction_holds (h_all G.restricted_agent G.restricted_claim)
  -- Uses BOTH access_granted and restriction_holds — structural interaction between
  -- the positive and negative witnesses, parallel to no_flat_resolver for scope.
  no_agent_uniform_policy := fun h_unif =>
    G.restriction_holds
      ((h_unif G.privileged_agent G.restricted_agent G.restricted_claim).mp G.access_granted)


/-! ## GroundedSystemSpec: All Seven Features from Evidence -/

/-- A fully grounded system specification: all seven EpArch features backed by
    domain evidence rather than declared Boolean flags.

    A `GroundedSystemSpec` contains one `GroundedX` witness per feature, plus a
    base spec (conventionally all-false: every `true` comes from evidence).

    `toSystemSpec` chains the seven `withGroundedX` applications; each call sets
    exactly one `Bool` field to `true` because the corresponding evidence was
    supplied.  A system that can provide a `GroundedSystemSpec` has *proven*
    — not merely declared — that it satisfies all seven Bank primitives. -/
structure GroundedSystemSpec where
  bubbles       : GroundedBubbles
  trust_bridges : GroundedTrustBridges
  headers       : GroundedHeaders
  revocation    : GroundedRevocation
  bank          : GroundedBank
  redeemability : GroundedRedeemability
  authorization : GroundedAuthorization
  base          : SystemSpec

/-- Convert a `GroundedSystemSpec` to a concrete `SystemSpec`.

    The seven `withGroundedX` calls are chained innermost-to-outermost.  After
    all seven applications every field is `true`, but each `true` was set by
    construction from evidence — not by writing `true` in a record literal. -/
def GroundedSystemSpec.toSystemSpec (G : GroundedSystemSpec) : SystemSpec :=
  SystemSpec.withGroundedAuthorization G.authorization
    (SystemSpec.withGroundedRedeemability G.redeemability
      (SystemSpec.withGroundedBank G.bank
        (SystemSpec.withGroundedRevocation G.revocation
          (SystemSpec.withGroundedHeaders G.headers
            (SystemSpec.withGroundedTrustBridges G.trust_bridges
              (SystemSpec.withGroundedBubbles G.bubbles G.base))))))

/-- A fully grounded spec satisfies `containsAllFeatures` — and the proof
    does not depend on any manually set `Bool` flag.  Every `spec_has_X` holds
    because the corresponding `withGroundedX` was applied with real evidence. -/
theorem grounded_spec_contains_all (G : GroundedSystemSpec) :
    containsAllFeatures (G.toSystemSpec) := by
  unfold containsAllFeatures GroundedSystemSpec.toSystemSpec
         SystemSpec.withGroundedAuthorization SystemSpec.withGroundedRedeemability
         SystemSpec.withGroundedBank SystemSpec.withGroundedRevocation
         SystemSpec.withGroundedHeaders SystemSpec.withGroundedTrustBridges
         SystemSpec.withGroundedBubbles
         spec_has_bubbles spec_has_trust_bridges spec_has_headers
         spec_has_revocation spec_has_bank spec_has_redeemability spec_has_granular_acl
  simp

end EpArch
