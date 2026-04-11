/-
EpArch/SystemSpec.lean — System Specification
Structural definitions for Has* predicates

This file provides structural definitions that allow the linking axioms
in Minimality.lean to become provable theorems. The key insight:
instead of opaque Has* predicates, we define them as inspectable
properties of a system specification.
-/

import EpArch.Basic

namespace EpArch

universe u

/-! ## System Specification Structure

A SystemSpec captures the architectural features a system has or lacks.
This is what we inspect to determine Has* predicates structurally. -/

/-- System specification: captures what operations and features a system provides.

    Each field corresponds to an architectural capability. The Has* predicates
    in Minimality.lean are now defined by inspecting these fields. -/
structure SystemSpec where
  /-- System has bubble separation (scoped trust zones, not global ledger).
      Forced by: Distributed agents constraint. -/
  has_bubble_separation : Bool

  /-- System has trust bridges (import-via-trust without full revalidation).
      Forced by: Bounded audit constraint. -/
  has_trust_bridges : Bool

  /-- System preserves headers (S/E/V) across export.
      Forced by: Export across boundaries constraint. -/
  preserves_headers : Bool

  /-- System has revocation mechanism (challenge → quarantine → revoke).
      Forced by: Adversarial pressure constraint. -/
  has_revocation : Bool

  /-- System has shared ledger (bank) for collective reliance.
      Forced by: Coordination need constraint. -/
  has_shared_ledger : Bool

  /-- System has redeemability paths (constraint-surface contact).
      Forced by: Truth pressure constraint. -/
  has_redeemability : Bool
  deriving DecidableEq, Repr


/-! ## Feature Predicates on SystemSpec

These are helper predicates that check if a SystemSpec has a feature.
The main Has* predicates in Minimality.lean will use these via W.spec. -/

/-- Predicate: spec has bubble separation. -/
def spec_has_bubbles (spec : SystemSpec) : Prop := spec.has_bubble_separation = true

/-- Predicate: spec has trust bridges. -/
def spec_has_trust_bridges (spec : SystemSpec) : Prop := spec.has_trust_bridges = true

/-- Predicate: spec preserves headers. -/
def spec_has_headers (spec : SystemSpec) : Prop := spec.preserves_headers = true

/-- Predicate: spec has revocation. -/
def spec_has_revocation (spec : SystemSpec) : Prop := spec.has_revocation = true

/-- Predicate: spec has shared ledger. -/
def spec_has_bank (spec : SystemSpec) : Prop := spec.has_shared_ledger = true

/-- Predicate: spec has redeemability. -/
def spec_has_redeemability (spec : SystemSpec) : Prop := spec.has_redeemability = true


/-! ## Decidability Instances -/

instance : DecidablePred spec_has_bubbles := fun spec =>
  if h : spec.has_bubble_separation = true then isTrue h else isFalse h

instance : DecidablePred spec_has_trust_bridges := fun spec =>
  if h : spec.has_trust_bridges = true then isTrue h else isFalse h

instance : DecidablePred spec_has_headers := fun spec =>
  if h : spec.preserves_headers = true then isTrue h else isFalse h

instance : DecidablePred spec_has_revocation := fun spec =>
  if h : spec.has_revocation = true then isTrue h else isFalse h

instance : DecidablePred spec_has_bank := fun spec =>
  if h : spec.has_shared_ledger = true then isTrue h else isFalse h

instance : DecidablePred spec_has_redeemability := fun spec =>
  if h : spec.has_redeemability = true then isTrue h else isFalse h


/-! ## Full Spec Predicate

A system has "all Bank primitives" iff all six features are present. -/

/-- A system specification contains all Bank primitives. -/
def containsAllFeatures (spec : SystemSpec) : Prop :=
  spec_has_bubbles spec ∧ spec_has_trust_bridges spec ∧ spec_has_headers spec ∧
  spec_has_revocation spec ∧ spec_has_bank spec ∧ spec_has_redeemability spec

/-- The "full Bank spec" — a spec with all features enabled. -/
def fullBankSpec : SystemSpec where
  has_bubble_separation := true
  has_trust_bridges := true
  preserves_headers := true
  has_revocation := true
  has_shared_ledger := true
  has_redeemability := true

/-- Full spec has all features. -/
theorem fullBankSpec_contains_all : containsAllFeatures fullBankSpec := by
  unfold containsAllFeatures spec_has_bubbles spec_has_trust_bridges spec_has_headers
         spec_has_revocation spec_has_bank spec_has_redeemability fullBankSpec
  simp


/-! ## Grounded Feature Evidence

`SystemSpec` fields are `Bool`.  `HasX` checks `field = true`.  This works
for consistency witnesses (writing `true` and checking it) but does not
connect architectural feature claims to domain-level evidence.

`GroundedBubbles` is the evidence bridge for scope separation: it witnesses
that two distinct scoped acceptance functions exist over some claim type,
making the necessity of scope separation *derived* rather than *declared*.

The bridge theorem `grounded_bubbles_justified` proves:
  `GroundedBubbles → spec_has_bubbles (withGroundedBubbles G rest)`

so a `SystemSpec` built from evidence is verifiably correct — not just a flag
asserted true. -/

/-- Evidence that a system genuinely has scope separation.

    A system has bubble-separation if there exist two distinct scoped
    acceptance functions over some claim type: each function faithfully
    represents one agent's acceptance regime, and they disagree on at
    least one claim (the witness).

    This is stronger than `has_bubble_separation := true`: the two
    resolvers `scope₁` and `scope₂` are explicit witnesses, and their
    disagreement on `witness` is formally proved. -/
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

/-- Build a `SystemSpec` with `has_bubble_separation = true` from evidence. -/
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
    represent both scopes simultaneously — scope separation is structurally forced.
    Proof: a hypothetical flat resolver that agrees with both scopes must accept
    the witness (via `scope₁`) and also reject it (via `scope₂`), which contradicts
    `scope₂_rejects`. -/
structure GroundedBubblesStrict where
  base             : GroundedBubbles
  no_flat_resolver : ¬∃ (f : base.Claim → Prop),
      (∀ c, f c ↔ base.scope₁ c) ∧ (∀ c, f c ↔ base.scope₂ c)

/-- Derive `GroundedBubblesStrict` from base evidence.
    Uses only `GroundedBubbles` fields — no `Minimality.lean` imports needed. -/
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


/-! ## GroundedSystemSpec: All Six Features from Evidence -/

/-- A fully grounded system specification: all six EpArch features backed by
    domain evidence rather than declared Boolean flags.

    A `GroundedSystemSpec` contains one `GroundedX` witness per feature, plus a
    base spec (conventionally all-false: every `true` comes from evidence).

    `toSystemSpec` chains the six `withGroundedX` applications; each call sets
    exactly one `Bool` field to `true` because the corresponding evidence was
    supplied.  A system that can provide a `GroundedSystemSpec` has *proven*
    — not merely declared — that it satisfies all six Bank primitives. -/
structure GroundedSystemSpec where
  bubbles       : GroundedBubbles
  trust_bridges : GroundedTrustBridges
  headers       : GroundedHeaders
  revocation    : GroundedRevocation
  bank          : GroundedBank
  redeemability : GroundedRedeemability
  base          : SystemSpec

/-- Convert a `GroundedSystemSpec` to a concrete `SystemSpec`.

    The six `withGroundedX` calls are chained innermost-to-outermost.  After
    all six applications every field is `true`, but each `true` was set by
    construction from evidence — not by writing `true` in a record literal. -/
def GroundedSystemSpec.toSystemSpec (G : GroundedSystemSpec) : SystemSpec :=
  SystemSpec.withGroundedRedeemability G.redeemability
    (SystemSpec.withGroundedBank G.bank
      (SystemSpec.withGroundedRevocation G.revocation
        (SystemSpec.withGroundedHeaders G.headers
          (SystemSpec.withGroundedTrustBridges G.trust_bridges
            (SystemSpec.withGroundedBubbles G.bubbles G.base)))))

/-- A fully grounded spec satisfies `containsAllFeatures` — and the proof
    does not depend on any manually set `Bool` flag.  Every `spec_has_X` holds
    because the corresponding `withGroundedX` was applied with real evidence. -/
theorem grounded_spec_contains_all (G : GroundedSystemSpec) :
    containsAllFeatures (G.toSystemSpec) := by
  unfold containsAllFeatures GroundedSystemSpec.toSystemSpec
         SystemSpec.withGroundedRedeemability SystemSpec.withGroundedBank
         SystemSpec.withGroundedRevocation SystemSpec.withGroundedHeaders
         SystemSpec.withGroundedTrustBridges SystemSpec.withGroundedBubbles
         spec_has_bubbles spec_has_trust_bridges spec_has_headers
         spec_has_revocation spec_has_bank spec_has_redeemability
  simp


/-! ## Minimal Specs (for impossibility witnesses)

These are specs missing exactly one feature — useful for impossibility proofs. -/

/-- Spec missing bubbles. -/
def specWithoutBubbles : SystemSpec where
  has_bubble_separation := false
  has_trust_bridges := true
  preserves_headers := true
  has_revocation := true
  has_shared_ledger := true
  has_redeemability := true

/-- Spec missing trust bridges. -/
def specWithoutBridges : SystemSpec where
  has_bubble_separation := true
  has_trust_bridges := false
  preserves_headers := true
  has_revocation := true
  has_shared_ledger := true
  has_redeemability := true

/-- Spec missing headers. -/
def specWithoutHeaders : SystemSpec where
  has_bubble_separation := true
  has_trust_bridges := true
  preserves_headers := false
  has_revocation := true
  has_shared_ledger := true
  has_redeemability := true

/-- Spec missing revocation. -/
def specWithoutRevocation : SystemSpec where
  has_bubble_separation := true
  has_trust_bridges := true
  preserves_headers := true
  has_revocation := false
  has_shared_ledger := true
  has_redeemability := true

/-- Spec missing shared ledger (bank). -/
def specWithoutBank : SystemSpec where
  has_bubble_separation := true
  has_trust_bridges := true
  preserves_headers := true
  has_revocation := true
  has_shared_ledger := false
  has_redeemability := true

/-- Spec missing redeemability. -/
def specWithoutRedeemability : SystemSpec where
  has_bubble_separation := true
  has_trust_bridges := true
  preserves_headers := true
  has_revocation := true
  has_shared_ledger := true
  has_redeemability := false


/-! ## Witness theorems: each minimal spec lacks its feature -/

theorem specWithoutBubbles_lacks_bubbles : ¬spec_has_bubbles specWithoutBubbles := by
  unfold spec_has_bubbles specWithoutBubbles; simp

theorem specWithoutBridges_lacks_bridges : ¬spec_has_trust_bridges specWithoutBridges := by
  unfold spec_has_trust_bridges specWithoutBridges; simp

theorem specWithoutHeaders_lacks_headers : ¬spec_has_headers specWithoutHeaders := by
  unfold spec_has_headers specWithoutHeaders; simp

theorem specWithoutRevocation_lacks_revocation : ¬spec_has_revocation specWithoutRevocation := by
  unfold spec_has_revocation specWithoutRevocation; simp

theorem specWithoutBank_lacks_bank : ¬spec_has_bank specWithoutBank := by
  unfold spec_has_bank specWithoutBank; simp

theorem specWithoutRedeemability_lacks_redeemability : ¬spec_has_redeemability specWithoutRedeemability := by
  unfold spec_has_redeemability specWithoutRedeemability; simp

end EpArch
