/-
EpArch/Feasibility.lean — Existence Under Constraints / Non-Vacuity Theorems

This module packages existing witnesses into "system class is nonempty"
statements, providing non-vacuity and existence proofs for
the existence-under-constraints claim.

## Purpose

Natural objections to an epistemic systems framework:
- "Are these constraints even consistent? Maybe they're vacuous."
- "Does a system satisfying these properties actually exist?"

This module answers: Yes. The constraint bundles are satisfiable,
working systems exist, and success forces Bank primitives.

## Headline Theorems

- `structural_goals_force_bank_primitives`: StructurallyForced ∧ SatisfiesAllProperties → containsBankPrimitives
- `existence_under_constraints_structural`: ∃ W, StructurallyForced W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W
- `bundled_structure_forces_bank_primitives`: uses SystemOperationalBundle + WorldBridgeBundle

These package non-vacuity + forced primitives into citable results.

## Claim Budget

**Buys:**
- "The constraint+objective package is consistent (nonempty)"
- "There exists at least one working system meeting the success bundle"
- "Success forces Bank primitives" (via Minimality)

**Does NOT buy:**
- "The real world literally is this model"
- "Uniqueness" (many realizations can exist)
- "Abduction/inference from observed O to existence of S"

-/

import EpArch.WorldWitness
import EpArch.Realizer
import EpArch.Minimality
import EpArch.Convergence

namespace EpArch.Feasibility

/-! ## World Constraint Feasibility -/

/-- World constraint bundles are satisfiable (non-vacuity).

    Uses the WitnessCtx from WorldWitness.lean to show that the
    W_* bundles are jointly satisfiable.

    Note: We use `@WorldCtx.{0}` to fix the universe level to match WitnessCtx. -/
theorem world_bundles_feasible :
    ∃ C : @EpArch.WorldCtx.{0},
      Nonempty C.W_lies_possible ∧
      Nonempty C.W_bounded_verification ∧
      Nonempty C.W_partial_observability := by
  refine ⟨EpArch.WorldWitness.WitnessCtx, ?_⟩
  exact EpArch.WorldWitness.all_bundles_satisfiable

/-- Alias for backward compatibility -/
theorem constraints_feasible :
    ∃ C : @EpArch.WorldCtx.{0},
      Nonempty C.W_lies_possible ∧
      Nonempty C.W_bounded_verification ∧
      Nonempty C.W_partial_observability :=
  world_bundles_feasible


/-! ## Commitment Feasibility -/

/-- Commitments are jointly satisfiable (named alias for external reference).

    This re-exports `all_commitments_satisfiable` under a consistent name. -/
theorem commitments_feasible :
    -- Commitment 1: Traction/Authorization split
    (∃ a B P, ConcreteModel.c_certainty a P ∧ ¬ConcreteModel.c_knowledge B P) ∧
    (∃ a B P, ConcreteModel.c_knowledge B P ∧ ¬ConcreteModel.c_certainty a P) ∧
    -- Commitment 2: No global ledger supports both
    (∃ G, ¬(ConcreteModel.c_supports_innovation G ∧ ConcreteModel.c_supports_coordination G)) ∧
    -- Commitment 3: S/E/V factorization exists
    (∃ d : ConcreteModel.CDeposit, d.S > 0 ∧ d.E.length > 0 ∧ d.V.length > 0) ∧
    -- Commitment 4: Consensus without redeemability
    (∃ B d, ConcreteModel.c_consensus B d.claim ∧ ¬ConcreteModel.c_redeemable d) ∧
    -- Commitment 5: Export gating
    True ∧
    -- Commitment 6: Repair loop
    (∃ _d c : ConcreteModel.CChallenge, c.field ∈ ["S", "E", "V", "τ"]) ∧
    -- Commitment 7: Header-stripped loses diagnosability
    (∃ d : ConcreteModel.CDeposit, ConcreteModel.c_header_stripped d ∧ d.E.length = 0) ∧
    -- Commitment 8: Fresh/stale differ
    (∃ d1 d2 t, ConcreteModel.c_fresh d1 t ∧ ConcreteModel.c_stale d2 t) :=
  ConcreteModel.all_commitments_satisfiable

/-- Objective bundle is satisfiable: there exists at least one Realizer.

    The Realizer packages the proof that all core commitments
    are simultaneously satisfiable. -/
theorem objectives_feasible : ∃ _ : EpArch.Realizer, True := by
  exact ⟨EpArch.ConcreteRealizer, trivial⟩


/-! ## System-Level Feasibility -/

/-! ## Joint Feasibility -/

/-- Joint feasibility: world constraints and objectives are both nonempty.

    Kept for backward compatibility. The stronger `existence_under_constraints`
    is the preferred reference. -/
theorem joint_feasible :
    (∃ C : @EpArch.WorldCtx.{0},
      Nonempty C.W_lies_possible ∧
      Nonempty C.W_bounded_verification ∧
      Nonempty C.W_partial_observability) ∧
    (∃ _ : EpArch.Realizer, True) := by
  exact ⟨constraints_feasible, objectives_feasible⟩


/-! ## Structural Convergence -/

/-- Paper-facing name (structural version): success forces Bank primitives
    without depending on WellFormed biconditionals. -/
theorem structural_goals_force_bank_primitives :
    ∀ W : WorkingSystem,
      StructurallyForced W → SatisfiesAllProperties W → containsBankPrimitives W :=
  convergence_structural

/-- Headline theorem (structural version): the concrete model is
    structurally forced, satisfies all properties, and contains Bank
    primitives — without going through WellFormed. -/
theorem existence_under_constraints_structural :
    ∃ W : WorkingSystem,
      StructurallyForced W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W := by
  refine ⟨EpArch.ConcreteInstance.ConcreteWorkingSystem, ?_⟩
  refine ⟨EpArch.ConcreteInstance.concrete_structurally_forced,
          EpArch.ConcreteInstance.concrete_satisfies_all_properties, ?_⟩
  exact convergence_structural EpArch.ConcreteInstance.ConcreteWorkingSystem
    EpArch.ConcreteInstance.concrete_structurally_forced
    EpArch.ConcreteInstance.concrete_satisfies_all_properties

/-- Headline theorem (embedding version): full chain from
    `ForcingEmbedding` through `StructurallyForced` to convergence.
    This is the strongest form — the design judgment is localised
    in `concrete_forcing_embedding`, and the derivation is mechanical. -/
theorem existence_under_constraints_embedding :
    ∃ W : WorkingSystem,
      ForcingEmbedding W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W :=
  ⟨EpArch.ConcreteInstance.ConcreteWorkingSystem,
   EpArch.ConcreteInstance.concrete_forcing_embedding,
   EpArch.ConcreteInstance.concrete_satisfies_all_properties,
   EpArch.ConcreteInstance.concrete_structural_convergence⟩


/-! ## World-to-Structural Bridges

These theorems connect the W_* world assumption bundles (WorldCtx.lean) to the
structural impossibility models (Minimality.lean).  Previously the two sides were
proved independently — the structural models had hand-supplied witnesses, and the
world assumptions had witnesses of their own.  These bridges show that any world
satisfying a W_* bundle supplies enough data to construct a matching structural
scenario instance, so the forcing results apply without a separate construction step.

The constructed instances are the minimal form sufficient to trigger the relevant
impossibility theorem — they package the W bundle's witness values, not a full
semantic import of the world's relational structure. -/

/-- Any world satisfying W_bounded_verification constructs a `BoundedVerification`
    instance sufficient to trigger `verification_only_import_incomplete`.

    The W bundle supplies a hard claim P and step count k > 0.  The constructed M
    packages these into the minimal abstract form: `verify_cost := fun _ => k`
    (a constant, not C.RequiresSteps itself) and `budget := 0`.  The world's
    RequiresSteps field is preserved in the existential witness but is not carried
    into M's cost function.

    The constructed M has:
    - M.Claim = C.Claim  (claim type is the world's claim type, not Unit)
    - M.hard_claim = P   (the actual hard claim from the world assumption)
    - M.verify_cost P = k (the extracted step count, as a constant function)
    - ∀ w, C.RequiresSteps w P k  (world witness, returned alongside M)

    verification_only_import_incomplete then fires on M.
    Consequence: the incompleteness is specifically about the claim P the world
    says is hard — not a synthetic Unit witness. -/
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

    Three of the six StructurallyForced implications are justified by W_* bundles:
    - trust_forcing        ← W_bounded_verification (verification_only_import_incomplete)
    - revocation_forcing   ← W_lies_possible        (monotonic_no_exit)
    - redeemability_forcing ← W_partial_observability (closed_system_unfalsifiable)

    Three are justified by structural impossibility arguments alone and have no
    W_* bundle counterpart (AgentDisagreement, DiscriminatingImport,
    PrivateOnlyStorage) — included here as unconditional hypotheses. -/
def WorldAwareSystem (C : @EpArch.WorldCtx.{0}) (W : WorkingSystem) : Prop :=
  (C.W_bounded_verification  → handles_bounded_audit W    → HasTrustBridges W)  ∧
  (C.W_lies_possible         → handles_adversarial W      → HasRevocation W)    ∧
  (C.W_partial_observability → handles_truth_pressure W   → HasRedeemability W) ∧
  (handles_distributed_agents W → HasBubbles W) ∧
  (handles_export W             → HasHeaders W)  ∧
  (handles_coordination W       → HasBank W)

/-- A working system satisfying WorldAwareSystem and SatisfiesAllProperties,
    in a world satisfying all three W_* bundles, necessarily contains Bank primitives.

    WorldAwareSystem holds the structural work: it contains the three
    world-conditional capability→feature implications (trust, revocation,
    redeemability) plus the three unconditional ones.  The W_* bundles discharge
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
  apply convergence_structural W _ h_sat
  exact { scope_forcing        := h_wa.2.2.2.1
          trust_forcing        := h_wa.1 Wv
          header_forcing       := h_wa.2.2.2.2.1
          revocation_forcing   := h_wa.2.1 Wl
          bank_forcing         := h_wa.2.2.2.2.2
          redeemability_forcing := h_wa.2.2.1 Wo }

/-- Any StructurallyForced system satisfies WorldAwareSystem for any WorldCtx.

    Proof by weakening: StructurallyForced asserts all six capability→feature
    implications *unconditionally*, while WorldAwareSystem only requires three of
    them *conditionally* (behind W_* hypothesis guards).  Ignoring the W_* guard
    via `fun _ =>` discharges each conditional, reducing WorldAwareSystem to a
    strict weakening of StructurallyForced. -/
theorem structurally_forced_is_world_aware (C : @EpArch.WorldCtx.{0}) (W : WorkingSystem)
    (h_sf : StructurallyForced W) : WorldAwareSystem C W :=
  ⟨fun _ => h_sf.trust_forcing,
   fun _ => h_sf.revocation_forcing,
   fun _ => h_sf.redeemability_forcing,
   h_sf.scope_forcing,
   h_sf.header_forcing,
   h_sf.bank_forcing⟩

/-- Zero-hypothesis corollary: the concrete working system contains Bank primitives
    with no free assumptions.

    Proof path:
    (1) WitnessCtx (WorldWitness.lean) witnesses all three W_* bundles.
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
    six EpArch dimensions and satisfies all operational properties necessarily
    contains Bank primitives.

    This theorem replaces `world_assumptions_force_bank_primitives` + `WorldAwareSystem`
    as the headline convergence result.  `WorldAwareSystem` bundles the six
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

    All six `ForcingEmbedding` fields are constructed inline from the witnesses —
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
    (h_sat : SatisfiesAllProperties W) :
    containsBankPrimitives W := by
  apply convergence_structural W _ h_sat
  apply embedding_to_structurally_forced
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- scope_embed: disagreement_scope_embed has the exact required type
    exact disagreement_scope_embed W Rd flat_accept hflat₁ hflat₂
  · -- trust_embed: absent trust bridges, BridgeTrust is constructible from h_trust_all
    intro _
    by_cases h : HasTrustBridges W
    · exact Or.inl h
    · exact Or.inr ⟨Rb.toVerification, h_trust_all h⟩
  · -- header_embed: absent headers, BridgeHeaders is constructible from f_import
    intro _
    by_cases h : HasHeaders W
    · exact Or.inl h
    · exact Or.inr ⟨Ri.toImport, f_import h, h_unif h, h_sound h, h_complete h⟩
  · -- revocation_embed: absent revocation, BridgeRevocation uses Rm.toLifecycle + h_rev_escape
    intro _
    by_cases h : HasRevocation W
    · exact Or.inl h
    · exact Or.inr ⟨Rm.toLifecycle h, n_rev, h_rev_escape h⟩
  · -- bank_embed: private_coordination_bank_embed has the exact required type
    exact private_coordination_bank_embed W Rp shared_deposit h_access₁ h_access₂
  · -- redeemability_embed: absent redeemability, BridgeRedeemability uses Re.toClosed
    intro _
    by_cases h : HasRedeemability W
    · exact Or.inl h
    · exact Or.inr ⟨Re.toClosed h, c_re, h_endorsed, h_fals h⟩

/-- **Headline convergence theorem — bundled form.**

    Any working system carrying an `SystemOperationalBundle` (architectural
    witnesses for scope, headers, bank) and a `WorldBridgeBundle` (world-adjacent
    witnesses for revocation, trust, redeemability), satisfying all operational
    properties, necessarily contains Bank primitives.

    This is the cleanest citable form of the main result.  All 20+ per-dimension
    parameters from `grounded_world_and_structure_force_bank_primitives` are
    absorbed into two named records, symmetrically split by the nature of the
    evidence each carries:

    | Bundle                   | Dimensions                           |
    |--------------------------|--------------------------------------|
    | `SystemOperationalBundle`| scope · headers · bank               |
    | `WorldBridgeBundle`      | revocation · trust · redeemability   |

    **"Any world" status:** No `WorldCtx` or W_* bundle appears in this
    signature.  The theorem holds for *any* world whatsoever.  The W_*
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
    O.Rd B.Rb O.Ri B.Rm O.Rp B.Re
    O.flat_accept O.hflat₁ O.hflat₂
    B.h_trust_all
    O.f_import O.h_unif O.h_sound O.h_complete
    B.n_rev B.h_rev_escape
    O.shared_deposit O.h_access₁ O.h_access₂
    B.c_re B.h_endorsed B.h_fals
    h_sat

end EpArch.Feasibility
