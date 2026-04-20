/-
EpArch.WorldBridges — World-to-Structural Bridge Theorems

Connects the W_* world assumption bundles (EpArch.WorldCtx) to the structural
impossibility models (EpArch.Minimality) and the Represents* scenario witnesses
(EpArch.Scenarios).  These are the load-bearing convergence results that sit
above the abstract structural machinery and below the concrete witnesses.

## Headline Theorems

- `grounded_world_and_structure_force_bank_primitives`: the full parameter-explicit
  convergence theorem — uses eight Represents* witnesses plus per-dimension bridge
  hypotheses to constructively derive containsBankPrimitives.
- `bundled_structure_forces_bank_primitives`: the packaged 4-argument form
  using SystemOperationalBundle + WorldBridgeBundle.
- `world_assumptions_force_bank_primitives`: world-conditional variant using
  WorldCtx W_* bundles directly.
- `kernel_world_forces_bank_primitives`: zero-hypothesis corollary.
- `WorldSystemCompat`: bridge structure encoding how world conditions supply the
  three world-adjacent Represents* witnesses and their bridge hypotheses for a
  specific WorkingSystem.
- `world_deriving_bridge`: derives WorldBridgeBundle W from WorldSystemCompat C W
  plus the three W_* witnesses — closes the construction gap noted in Scenarios.lean.

## Dependencies

EpArch.WorldWitness, EpArch.Concrete.Realizer (pulls Concrete.WorkingSystem),
EpArch.Scenarios (pulls Convergence + Minimality).
-/

import EpArch.WorldWitness
import EpArch.Concrete.Realizer
import EpArch.Scenarios

namespace EpArch.WorldBridges

/-! ## World-to-Structural Bridges

These theorems connect the W_* world assumption bundles (EpArch.WorldCtx) to the
structural impossibility models (EpArch.Minimality).  Each bridge shows that any world
satisfying a W_* bundle supplies enough data to construct a matching structural
scenario instance, so the forcing results apply without a separate construction step. -/

/-- Any world satisfying W_bounded_verification constructs a `BoundedVerification`
    instance sufficient to trigger `verification_only_import_incomplete`.

    Packages W's hard claim P and step count k into a minimal `BoundedVerification`
    with constant cost function.  The existential witnesses M, P, and k are returned
    alongside the world's own `RequiresSteps` evidence. -/
theorem w_bounded_forces_incompleteness (C : @EpArch.WorldCtx.{0})
    (W : C.W_bounded_verification) :
    ∃ (P : C.Claim) (k : Nat) (M : BoundedVerification),
      k > 0 ∧
      (∀ w, C.RequiresSteps w P k) ∧
      M.Claim = C.Claim ∧
      ¬∀ c : M.Claim, M.verify_cost c ≤ M.budget := by
  have ⟨P, k, h_pos, h_req⟩ := W.verification_has_cost
  let M : BoundedVerification := ⟨C.Claim, fun _ => k, 0, P, h_pos⟩
  exact ⟨P, k, M, h_pos, h_req, rfl, verification_only_import_incomplete M⟩

/-- Any world satisfying W_lies_possible contains a false claim that is permanently
    trapped in every revocation-free lifecycle over that world's claim type.

    For any step function where every false claim is absorbing, the same false claim
    supplied by W is injectable by every agent (W.unrestricted_utterance) and
    indelible under that step function (monotonic_no_exit).

    The schema parameters `step` and `h_absorb` are universally quantified in the
    conclusion: the result holds for all candidate revocation-free lifecycles, not
    just a specific one supplied as a hypothesis. -/
theorem w_lies_forces_revocation_need (C : @EpArch.WorldCtx.{0})
    (W : C.W_lies_possible) :
    ∃ w P, ¬C.Truth w P ∧ (∀ a, C.Utter a P) ∧
      ∀ (step : C.Claim → C.Claim),
        (∀ w' P', ¬C.Truth w' P' → step P' = P') →
        ∀ n, iter step n P = P := by
  have ⟨w, P, h_false⟩ := W.some_false
  exact ⟨w, P, h_false, fun a => W.unrestricted_utterance a P,
    fun step h_absorb => monotonic_no_exit ⟨C.Claim, P, step, h_absorb w P h_false⟩⟩

/-- Any world satisfying W_partial_observability has a claim that cannot be endorsed
    by any obs-stable closed endorsement system.

    For any endorsement predicate that is obs-stable (same observations → same
    endorsement) and closed (endorsed → true), the underdetermined claim from W
    cannot be endorsed in some world.

    The schema parameters `endorsed`, `obs_stable`, and `closed` are universally
    quantified in the conclusion: the result holds for all candidate closed
    endorsement systems, not just a specific one supplied as a hypothesis. -/
theorem w_partial_obs_forces_redeemability (C : @EpArch.WorldCtx.{0})
    (W : C.W_partial_observability) :
    ∃ P w0,
      ∀ (endorsed : C.World → C.Claim → Prop),
        (∀ P' w0' w1', C.PartialObs w0' w1' → endorsed w0' P' → endorsed w1' P') →
        (∀ w P', endorsed w P' → C.Truth w P') →
        ¬endorsed w0 P := by
  have ⟨P, w0, w1, h_obs, h_bic⟩ := W.obs_underdetermines
  exact ⟨P, w0, fun endorsed obs_stable closed h_end =>
    (h_bic.mp (closed w0 P h_end)) (closed w1 P (obs_stable P w0 w1 h_obs h_end))⟩

/-! ## World-Grounded Convergence -/

/-- A working system is world-aware with respect to WorldCtx C if its structural
    forcing implications are grounded in C's world assumptions (for those that
    have W_* bundle counterparts) and by structural analysis (for the rest).

    Three of the eight StructurallyForced implications are justified by W_* bundles:
    - trust_forcing         ← W_bounded_verification (verification_only_import_incomplete)
    - revocation_forcing    ← W_lies_possible        (monotonic_no_exit)
    - redeemability_forcing ← W_partial_observability (closed_system_unfalsifiable)

    Five are unconditional: scope, headers, bank, authorization, and storage.
    Their forcing is system-internal — a system carrying the corresponding
    `GroundedXStrict` evidence self-certifies the impossibility regardless of
    any world assumption.

    Why authorization is unconditional rather than gated on W_multi_agent_heterogeneous:
    (1) W_multi_agent_heterogeneous is formally incompatible with W_lies_possible
        (proven in WorldCtx.w_lies_multi_agent_incompatible), so it cannot be added
        as a guard here alongside Wl without making this theorem vacuously provable
        from contradictory premises.
    (2) The authorization forcing is self-certifying: GroundedAuthorizationStrict carries
        no_flat_tier, derived from the system's
        own authorization evidence without any world-semantic premise.  The parallel is
        exact: scope forcing is also self-certifying (AgentDisagreement is internal to
        the system), and scope is unconditional for the same reason.

    Storage is also unconditional: no W_* bundle corresponds to bounded storage;
    GroundedStorageStrict self-certifies the impossibility via no_unbounded_accumulation. -/
def WorldAwareSystem (C : @EpArch.WorldCtx.{0}) (W : WorkingSystem) : Prop :=
  (C.W_bounded_verification  → handles_bounded_audit W    → HasTrustBridges W)  ∧
  (C.W_lies_possible         → handles_adversarial W      → HasRevocation W)    ∧
  (C.W_partial_observability → handles_truth_pressure W   → HasRedeemability W) ∧
  (handles_distributed_agents W → HasBubbles W) ∧
  (handles_export W             → HasHeaders W)  ∧
  (handles_coordination W       → HasBank W) ∧
  (handles_multi_agent W        → HasGranularACL W) ∧
  (handles_storage W            → HasStorageManagement W)

/-- A working system satisfying WorldAwareSystem and SatisfiesAllProperties,
    in a world satisfying all three W_* bundles, necessarily contains Bank primitives.

    WorldAwareSystem holds the structural work: it contains the three
    world-conditional capability→feature implications (trust, revocation,
    redeemability) plus the five unconditional ones (scope, headers, bank,
    authorization, storage).  The W_* bundles discharge
    the world-bundle guards in WorldAwareSystem; convergence_structural then
    closes the proof from StructurallyForced + SatisfiesAllProperties.

    All three W_* bundles are consumed: removing any one leaves the corresponding
    guard in WorldAwareSystem undischarged. -/
theorem world_assumptions_force_bank_primitives (C : @EpArch.WorldCtx.{0})
    (Wl : C.W_lies_possible)
    (Wv : C.W_bounded_verification)
    (Wo : C.W_partial_observability)
    (W : WorkingSystem)
    (h_wa : WorldAwareSystem C W)
    (h_sat : SatisfiesAllProperties W) :
    containsBankPrimitives W := by
  -- Name each component of WorldAwareSystem's And-chain for legibility.
  -- Order matches the definition: trust ∧ revocation ∧ redeemability ∧ scope ∧ headers ∧ bank ∧ authorization ∧ storage
  have h_trust_wa   := h_wa.1
  have h_rev_wa     := h_wa.2.1
  have h_redeem_wa  := h_wa.2.2.1
  have h_scope_wa   := h_wa.2.2.2.1
  have h_headers_wa := h_wa.2.2.2.2.1
  have h_bank_wa    := h_wa.2.2.2.2.2.1
  have h_auth_wa    := h_wa.2.2.2.2.2.2.1
  have h_storage_wa := h_wa.2.2.2.2.2.2.2
  have h_sf : StructurallyForced W :=
    { forcing := fun P h => match P with
        | .scope         => h_scope_wa h
        | .trust         => h_trust_wa Wv h
        | .headers       => h_headers_wa h
        | .revocation    => h_rev_wa Wl h
        | .bank          => h_bank_wa h
        | .redeemability => h_redeem_wa Wo h
        | .authorization => h_auth_wa h
        | .storage       => h_storage_wa h
      evidence := {
        scope_consequence         := fun G _h_ev => G.no_flat_resolver
        trust_consequence         := fun G _h_ev => G.bridge_forces_acceptance
        headers_consequence       := fun G _h_ev => G.routing_invariant
        revocation_consequence    := fun G _h_ev => G.has_invalid_revocable_witness
        bank_consequence          := fun G _h_ev => G.has_shared_entry
        redeemability_consequence := fun G _h_ev => G.has_constrained_redeemable_witness
        authorization_consequence := fun G _h_ev => G.no_flat_tier
        storage_consequence       := fun G _h_ev => G.no_unbounded_accumulation } }
  exact (grounded_evidence_consequences W h_sf h_sat).1

/-- Any StructurallyForced system satisfies WorldAwareSystem for any WorldCtx.

    Proof by weakening: StructurallyForced asserts all eight capability→feature
    implications *unconditionally*, while WorldAwareSystem only requires three of
    them *conditionally* (behind W_* hypothesis guards).  Ignoring the W_* guard
    via `fun _ =>` discharges each conditional, reducing WorldAwareSystem to a
    strict weakening of StructurallyForced. -/
theorem structurally_forced_is_world_aware (C : @EpArch.WorldCtx.{0}) (W : WorkingSystem)
    (h_sf : StructurallyForced W) : WorldAwareSystem C W :=
  -- Tuple order must match WorldAwareSystem's And-chain:
  -- (trust) ∧ (revocation) ∧ (redeemability) ∧ (scope) ∧ (headers) ∧ (bank) ∧ (authorization) ∧ (storage)
  ⟨fun _ => h_sf.forcing .trust,
   fun _ => h_sf.forcing .revocation,
   fun _ => h_sf.forcing .redeemability,
   h_sf.forcing .scope,
   h_sf.forcing .headers,
   h_sf.forcing .bank,
   h_sf.forcing .authorization,
   h_sf.forcing .storage⟩

/-- Zero-hypothesis corollary: the concrete working system contains Bank primitives
    with no free assumptions.

    Proof path:
    (1) WitnessCtx (EpArch.WorldWitness) witnesses all three W_* bundles.
    (2) concrete_structurally_forced gives StructurallyForced ConcreteWorkingSystem.
    (3) structurally_forced_is_world_aware converts that to WorldAwareSystem WitnessCtx.
    (4) concrete_satisfies_all_properties gives SatisfiesAllProperties.
    (5) world_assumptions_force_bank_primitives closes the proof.

    The three world assumptions that appear as hypotheses in
    world_assumptions_force_bank_primitives are discharged here by the WitnessCtx
    model, leaving a fully closed theorem. -/
theorem kernel_world_forces_bank_primitives :
    containsBankPrimitives EpArch.ConcreteInstance.ConcreteWorkingSystem :=
  world_assumptions_force_bank_primitives
    EpArch.WorldWitness.WitnessCtx
    EpArch.WorldWitness.holds_W_lies_possible
    EpArch.WorldWitness.holds_W_bounded_verification
    EpArch.WorldWitness.holds_W_partial_observability
    EpArch.ConcreteInstance.ConcreteWorkingSystem
    (structurally_forced_is_world_aware _ _
      EpArch.ConcreteInstance.concrete_structurally_forced)
    EpArch.ConcreteInstance.concrete_satisfies_all_properties


/-- Any working system that carries explicit structural-scenario witnesses for all
    eight EpArch dimensions and satisfies all operational properties necessarily
    contains Bank primitives.

    This theorem replaces `world_assumptions_force_bank_primitives` + `WorldAwareSystem`
    as the headline convergence result.  `WorldAwareSystem` bundles the eight
    capability→feature implications as opaque Prop conjuncts; here each implication
    is unpacked into a named `Represents*` structure (structural data) plus an
    auditable bridge hypothesis (per-dimension forcing evidence):

    | Dimension     | Structure                        | Bridge hypothesis                                    |
    |---------------|----------------------------------|------------------------------------------------------|
    | Scope         | `RepresentsDisagreement`         | flat acceptance function matches both agents         |
    | Trust         | `RepresentsBoundedVerification`  | absent trust, all claims fit within budget           |
    | Headers       | `RepresentsDiscriminatingImport` | absent headers, import is uniform, sound, complete   |
    | Revocation    | `RepresentsMonotonicLifecycle`   | absent revocation, accepted state escapes at n_rev   |
    | Bank          | `RepresentsPrivateCoordination`  | absent ledger, both agents access the same deposit   |
    | Redeemability | `RepresentsClosedEndorsement`    | absent redeemability, endorsed claim is falsifiable  |
    | Authorization | `RepresentsUniformAccess`        | absent granular ACL, a flat predicate represents both the submission and commit tiers |
    | Storage       | `RepresentsBoundedCapacity`      | absent storage management, all active-deposit states stay within budget |

    All eight `ForcingEmbedding` fields are constructed inline from the witnesses —
    none are stated as opaque system-design axioms.  `embedding_to_structurally_forced`
    and `convergence_structural` then close the proof mechanically. -/
theorem grounded_world_and_structure_force_bank_primitives
    (W : WorkingSystem)
    -- Structural scenario witnesses (one per dimension)
    (Rd : RepresentsDisagreement W)
    (Rb : RepresentsBoundedVerification W)
    (Ri : RepresentsDiscriminatingImport W)
    (Rm : RepresentsMonotonicLifecycle W)
    (Rp : RepresentsPrivateCoordination W)
    (Re : RepresentsClosedEndorsement W)
    (Ra : RepresentsUniformAccess W)
    (Rs : RepresentsBoundedCapacity W)
    -- Scope: absent bubbles, a flat acceptance function must cover both agents
    (flat_accept : ¬HasBubbles W → Rd.Claim → Prop)
    (hflat₁ : ∀ h c, flat_accept h c ↔ Rd.accept₁ c)
    (hflat₂ : ∀ h c, flat_accept h c ↔ Rd.accept₂ c)
    -- Trust: absent trust bridges, all claims fit within the verification budget
    (h_trust_all : ¬HasTrustBridges W → ∀ c, Rb.verify_cost c ≤ Rb.budget)
    -- Headers: absent headers, the import function is uniform, sound, and complete
    (f_import : ¬HasHeaders W → Ri.Claim → Bool)
    (h_unif : ∀ h x y, f_import h x = f_import h y)
    (h_sound : ∀ h, f_import h Ri.bad = false)
    (h_complete : ∀ h, f_import h Ri.good = true)
    -- Revocation: absent revocation, the accepted state escapes at step n_rev
    (n_rev : Nat)
    (h_rev_escape : ¬HasRevocation W → iter Rm.step n_rev Rm.accepted ≠ Rm.accepted)
    -- Bank: absent a shared ledger, both agents access the same deposit
    (shared_deposit : ¬HasBank W → Rp.Deposit)
    (h_access₁ : ∀ h, Rp.has_access Rp.a₁ (shared_deposit h))
    (h_access₂ : ∀ h, Rp.has_access Rp.a₂ (shared_deposit h))
    -- Redeemability: absent redeemability, an endorsed claim is externally falsifiable
    (c_re : Re.Claim)
    (h_endorsed : Re.endorsed c_re)
    (h_fals : ¬HasRedeemability W → Re.externally_falsifiable c_re)
    -- Authorization: absent granular ACL, a flat predicate represents both tiers
    (h_no_acl_flat : ¬HasGranularACL W → ∃ f : Ra.Agent → Ra.Claim → Prop,
        (∀ a c, f a c ↔ Ra.can_propose a c) ∧ (∀ a c, f a c ↔ Ra.can_commit a c))
    -- Storage: absent storage management, all active-deposit states stay within budget
    (h_storage_bounded : ¬HasStorageManagement W → ∀ s : Rs.State, Rs.count s ≤ Rs.budget)
    (h_sat : SatisfiesAllProperties W) :
    containsBankPrimitives W := by
  -- Construct h_sf from the eight Represents* scenario witnesses.
  have h_sf : StructurallyForced W := by
    apply embedding_to_structurally_forced
    constructor
    intro P h
    cases P
    · -- scope: disagreement_scope_embed has the exact required type
      exact disagreement_scope_embed W Rd flat_accept hflat₁ hflat₂ h
    · -- trust: absent trust bridges, BridgeTrust is constructible from h_trust_all
      by_cases ht : HasTrustBridges W
      · exact Or.inl ht
      · exact Or.inr ⟨Rb.toVerification, h_trust_all ht⟩
    · -- headers: absent headers, BridgeHeaders is constructible from f_import
      by_cases hh : HasHeaders W
      · exact Or.inl hh
      · exact Or.inr ⟨Ri.toImport, f_import hh, h_unif hh, h_sound hh, h_complete hh⟩
    · -- revocation: absent revocation, BridgeRevocation uses Rm.toLifecycle + h_rev_escape
      by_cases hr : HasRevocation W
      · exact Or.inl hr
      · exact Or.inr ⟨Rm.toLifecycle hr, n_rev, h_rev_escape hr⟩
    · -- bank: private_coordination_bank_embed has the exact required type
      exact private_coordination_bank_embed W Rp shared_deposit h_access₁ h_access₂ h
    · -- redeemability: absent redeemability, BridgeRedeemability uses Re.toClosed
      by_cases hre : HasRedeemability W
      · exact Or.inl hre
      · exact Or.inr ⟨Re.toClosed hre, c_re, h_endorsed, h_fals hre⟩
    · -- authorization: use uniform_access_acl_embed from Scenarios
      exact uniform_access_acl_embed W Ra h_no_acl_flat h
    · -- storage: absent storage management, BridgeStorage is constructible
      by_cases hst : HasStorageManagement W
      · exact Or.inl hst
      · exact Or.inr ⟨Rs.toStorage, h_storage_bounded hst⟩
  -- .1 extracts containsBankPrimitives.
  exact (grounded_evidence_consequences W h_sf h_sat).1

/-- **Headline convergence theorem — bundled form.**

    Any working system carrying an `SystemOperationalBundle` (architectural
    witnesses for scope, headers, bank) and a `WorldBridgeBundle` (world-adjacent
    witnesses for revocation, trust, redeemability), satisfying all operational
    properties, necessarily contains Bank primitives.

    This is the cleanest citable form of the main result.  All 20+ per-dimension
    parameters from `grounded_world_and_structure_force_bank_primitives` are
    absorbed into two named records, symmetrically split by the nature of the
    evidence each carries:

    | Bundle                   | Dimensions                                    |
    |--------------------------|-----------------------------------------------|
    | `SystemOperationalBundle`| scope · headers · bank · authorization · storage |
    | `WorldBridgeBundle`      | revocation · trust · redeemability            |

    **World-agnostic status:** No `WorldCtx` or W_* bundle appears in this
    signature.  The theorem's statement is world-agnostic — no formal world
    precondition is required.  The W_*
    bundles (W_lies_possible, W_bounded_verification, W_partial_observability)
    that characterise the EpArch world semantics are the natural *sources*
    for the `WorldBridgeBundle` data, but they are not formal preconditions
    here — the structural and operational witnesses alone suffice.

    Proof: one-liner unpack of both bundles into
    `grounded_world_and_structure_force_bank_primitives`. -/
theorem bundled_structure_forces_bank_primitives
    (W : WorkingSystem)
    (O : SystemOperationalBundle W)
    (B : WorldBridgeBundle W)
    (h_sat : SatisfiesAllProperties W) :
    containsBankPrimitives W :=
  grounded_world_and_structure_force_bank_primitives W
    O.Rd B.Rb O.Ri B.Rm O.Rp B.Re O.Ra O.Rs
    O.flat_accept O.hflat₁ O.hflat₂
    B.h_trust_all
    O.f_import O.h_unif O.h_sound O.h_complete
    B.n_rev B.h_rev_escape
    O.shared_deposit O.h_access₁ O.h_access₂
    B.c_re B.h_endorsed B.h_fals
    O.h_no_acl_flat
    O.h_storage_bounded
    h_sat

/-! ## WorldSystemCompat — Deriving WorldBridgeBundle from World Conditions

When a system genuinely operates under the EpArch world conditions, the
`WorldBridgeBundle` data should be derivable from the world bundle witnesses
alone rather than supplied as independent explicit parameters.

`WorldSystemCompat C W` is the bridge structure that makes this derivation
possible: it records, for each world-adjacent dimension, how the world
pressure (a `W_*` bundle) supplies the corresponding `Represents*` structural
witness and bridge hypothesis for the specific system `W`.

`world_deriving_bridge` then produces `WorldBridgeBundle W` from a
`WorldSystemCompat C W` plus the three `W_*` witnesses, closing the gap
noted in the `WorldBridgeBundle` design comment. -/

/-- System-world compatibility for the three world-adjacent EpArch dimensions.

    Each field group encodes: given that the world satisfies pressure X (a W_*
    bundle), here is the structural scenario evidence for system W and its bridge
    hypothesis for that dimension.

    This structure is the additive bridge layer that connects `WorldCtx` world
    bundles to `WorldBridgeBundle` structural witnesses without refactoring either.

    **Structural invariant:** `n_rev` is a property of W, shared across all
    W_lies_possible instances; `lifecycle_escape` carries the per-dimension bridge
    hypothesis parameterized over the world witness. -/
structure WorldSystemCompat (C : WorldCtx) (W : WorkingSystem) where
  /-- Revocation dimension: world adversarial pressure supplies the lifecycle witness. -/
  lifecycle        : C.W_lies_possible → RepresentsMonotonicLifecycle W
  /-- The step count at which the accepted state escapes absent revocation.
      Property of W, not of the world bundle. -/
  n_rev            : Nat
  /-- Bridge: absent revocation, the accepted state escapes at step n_rev. -/
  lifecycle_escape : ∀ (wl : C.W_lies_possible),
      ¬HasRevocation W →
      iter (lifecycle wl).step n_rev (lifecycle wl).accepted ≠ (lifecycle wl).accepted
  /-- Trust dimension: bounded verification pressure supplies the verification witness. -/
  verification     : C.W_bounded_verification → RepresentsBoundedVerification W
  /-- Bridge: absent trust bridges, all claims fit within the budget. -/
  trust_all        : ∀ (wv : C.W_bounded_verification),
      ¬HasTrustBridges W → ∀ c, (verification wv).verify_cost c ≤ (verification wv).budget
  /-- Redeemability dimension: partial observability pressure supplies the endorsement witness. -/
  endorsement      : C.W_partial_observability → RepresentsClosedEndorsement W
  /-- Bridge data: for each partial-observability witness, a claim that is endorsed
      and (absent redeemability) externally falsifiable. Carried as a dependent pair
      so the claim type is correctly scoped to the specific endorsement witness. -/
  endorsement_witness : ∀ (wo : C.W_partial_observability),
      Σ' (c : (endorsement wo).Claim),
        (endorsement wo).endorsed c ∧
        (¬HasRedeemability W → (endorsement wo).externally_falsifiable c)

/-- WORLD-DERIVING BRIDGE THEOREM

    Derives `WorldBridgeBundle W` from world bundle witnesses alone, given a
    `WorldSystemCompat C W` recording how C's world conditions bind to W.

    Any system genuinely operating under the three EpArch world conditions
    (lies possible, verification bounded, observation partial) satisfies
    `WorldBridgeBundle` without supplying the bridge witnesses as separate
    explicit parameters.

    **Theorem shape:** WorldSystemCompat C W + three W_* witnesses → WorldBridgeBundle W.
    **Proof strategy:** Extract each Represents* witness and bridge hypothesis
    from the compat fields; destructure endorsement_witness for the dependent
    triple ⟨c_re, h_endorsed, h_fals⟩; assemble the WorldBridgeBundle record. -/
theorem world_deriving_bridge
    (C : WorldCtx)
    (W : WorkingSystem)
    (compat : WorldSystemCompat C W)
    (wl : C.W_lies_possible)
    (wv : C.W_bounded_verification)
    (wo : C.W_partial_observability) :
    WorldBridgeBundle W :=
  -- Destructure the redeemability dependent pair to get c_re and its properties.
  let ⟨c_re, h_endorsed, h_fals⟩ := compat.endorsement_witness wo
  { Rm           := compat.lifecycle wl
    n_rev        := compat.n_rev
    h_rev_escape := compat.lifecycle_escape wl
    Rb           := compat.verification wv
    h_trust_all  := compat.trust_all wv
    Re           := compat.endorsement wo
    c_re         := c_re
    h_endorsed   := h_endorsed
    h_fals       := h_fals }

end EpArch.WorldBridges
