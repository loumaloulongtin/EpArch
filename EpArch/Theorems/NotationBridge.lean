/-
EpArch.Theorems.NotationBridge — Notation Bridge Authorization

Bridges Layer 1 (notation-invariance of redeemability, proved in Dissolutions)
to Layers 2 and 3 of the notation authorization story:
- Layer 2: a single divergence witness defeats pointwise bijection identification
- Layer 3: having the source bijection record instantiates Layer 1 directly
- Gettier case: route mismatch (σ′ ≠ σ) is independent of surface correctness
-/
import EpArch.Theorems.Dissolutions
import EpArch.Theorems.Strip
import EpArch.Theorems.Pathologies

namespace EpArch

open StepSemantics

universe u

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}

/-! ## Notation Bridge Authorization

The existing Layer 1 results (`notation_invariance_of_redeemability`,
`math_practice_is_bubble_distinct`) prove that a coherent bijection already in the
recipient's possession preserves redeemability across relabeling. This section
addresses the case where the recipient does NOT already possess the bijection.

Layer 2 (this file): without the source bijection σ, the recipient cannot identify
which relabeling was used — a single witness of divergence defeats identification.
This mirrors `import_cannot_reconstruct` for the notation domain.

Layer 3 (this file): if σ is carried with the export, `notation_invariance_of_redeemability`
applies directly and authorization transfers without prior notation knowledge.
Layer 3 is exactly Layer 1 with the bridge now available to the recipient by construction. -/

/-- The export packet: a claim together with its source notation bijection.
    Having this record IS having the bridge: σ/σ_inv/left_inv/right_inv are
    structurally present. The `bridge_carried` flag is documentation metadata
    recording the design intent (σ was exported with the claim) but does not
    appear in any proof — if you can construct a `notation_bridge_case`, you
    already have σ. The stripped case (σ not exported) is modelled by
    `improvised_uptake_case`, where only `source.P` is available and the
    recipient must supply an improvised σ′ that may diverge from σ. -/
structure notation_bridge_case where
  P              : PropLike
  σ              : PropLike → PropLike
  σ_inv          : PropLike → PropLike
  left_inv       : ∀ x, σ_inv (σ x) = x
  right_inv      : ∀ x, σ (σ_inv x) = x
  /-- Was σ exported together with the claim? True = full headers; false = stripped. -/
  bridge_carried : Bool

/-- Recipient's interpretation attempt without the bridge.
    Carries the source packet and the recipient's improvised bijection σ′,
    together with an explicit divergence witness.
    The `disagrees` field is the structural invariant encoding V-side defect under
    notation opacity: the improvised route departs from the source's truth-conferring
    structure at `divergence_point` — the one input where σ′ ≠ σ. -/
structure improvised_uptake_case where
  source          : notation_bridge_case (PropLike := PropLike)
  σ_prime         : PropLike → PropLike
  /-- The input at which σ_prime diverges from source.σ. -/
  divergence_point : PropLike
  /-- Structural invariant: σ_prime ≠ source.σ at divergence_point. -/
  disagrees       : σ_prime divergence_point ≠ source.σ divergence_point

/-- Notation-Gettier case: improvised uptake produces a surface match but does not
    track the source authorization route.

    The source is `improvised.source` — routing through the `improvised_uptake_case`
    rather than carrying a separate top-level `source` field ensures by construction
    that the improvised case and the Gettier case share a single coherent source packet.

    Structural invariant: `route_mismatch` records that the improvised bijection is
    not the source bijection, making this a V-side defect under notation opacity —
    not epistemic luck, but a missing bridge. Models the `leanKernelGettierCase`
    pattern: correct outcome, provenance gap. -/
structure notation_gettier_case where
  improvised     : improvised_uptake_case (PropLike := PropLike)
  /-- Recipient accidentally produced the right surface output. -/
  surface_match  : Bool
  /-- Structural invariant: the improvised bijection is not the source bijection.
      The correct output was reached via the wrong interpretive route. -/
  route_mismatch : improvised.σ_prime ≠ improvised.source.σ

/-! ## Layer 2 — Notation Opacity Prevents Authorization

A single divergence witness defeats bijection identification.
Mirrors `import_cannot_reconstruct` (Strip.lean) for the notation domain. -/

/-- NOTATION OPACITY (Layer 2)

    A single divergence witness defeats pointwise identification: if σ′ disagrees
    with σ at `c.divergence_point`, then σ′ cannot equal σ on all inputs.

    **Theorem shape:** ¬(∀ P, σ′ P = σ P), given `c.disagrees`.

    **Proof strategy:** Apply the universal to `c.divergence_point`; this produces
    `c.σ_prime c.divergence_point = c.source.σ c.divergence_point`, which
    `c.disagrees` refutes directly. Structurally identical to `import_cannot_reconstruct`
    (Strip.lean): one witnessed divergence defeats pointwise equality.

    Note: this proves ¬(pointwise equal), not a full authorization-denial theorem.
    The authorization reading is: an improvised bijection that diverges at even one
    point cannot be identified with the source bijection, so uptake via σ′ does not
    track the source authorization route. -/
theorem notation_opacity_prevents_authorization
    (c : improvised_uptake_case (PropLike := PropLike)) :
    ¬ (∀ P, c.σ_prime P = c.source.σ P) :=
  fun h => c.disagrees (h c.divergence_point)

/-! ## Layer 3 — Bridge Record Instantiates Layer 1

Having a `notation_bridge_case` record structurally encodes the bijection σ.
This is what it means for the bridge to be “carried with the export”: the
σ/σ_inv fields are structurally present, so a `NotationRelabeling` assembles
directly and Layer 1 applies. There is no additional proof content beyond
that instantiation. -/

/-- BRIDGE EXPORT INSTANTIATES LAYER 1 (Layer 3)

    A `notation_bridge_case` record structurally encodes the bijection σ.
    Having this record IS having the bridge: the fields σ, σ_inv, left_inv,
    right_inv are present by construction, so a `NotationRelabeling` can be
    assembled directly. `notation_invariance_of_redeemability` then applies.

    **Theorem shape:** redeemability_is_proof_consistency a ↔ (relabeled case),
    where the relabeling is the bijection embedded in c.

    **Proof strategy:** Assemble `⟨c.σ, c.σ_inv, c.left_inv, c.right_inv⟩ : NotationRelabeling`
    and apply the Layer 1 theorem. This is Layer 1 instantiated at the export-packet
    bijection — there is no additional proof content beyond that instantiation.

    Contrast: `notation_opacity_prevents_authorization` (Layer 2) handles the case
    where only `c.P` reaches the recipient without the bijection fields. There the
    `improvised_uptake_case` record carries σ′ ≠ σ, which defeats pointwise equality.
    Here the full `notation_bridge_case` record is available, so Layer 1 applies. -/
theorem bridge_export_enables_authorization
    (c : notation_bridge_case (PropLike := PropLike))
    (a : apriori_case (PropLike := PropLike)) :
    redeemability_is_proof_consistency a ↔
    redeemability_is_proof_consistency (relabel_case ⟨c.σ, c.σ_inv, c.left_inv, c.right_inv⟩ a) :=
  notation_invariance_of_redeemability ⟨c.σ, c.σ_inv, c.left_inv, c.right_inv⟩ a

/-! ## Gettier Case — Accidental Correctness Is Not Authorization

Correct surface output through the wrong interpretive route is not authorized uptake. -/

/-- ROUTE MISMATCH IS INDEPENDENT OF SURFACE MATCH (Gettier theorem)

    σ′ ≠ σ (as functions) even when the improvised uptake surface-matches the
    correct output. The `route_mismatch` field encodes this directly: the improvised
    bijection is not extensionally equal to the source bijection, regardless of
    whether any particular output happened to agree.

    **Theorem shape:** surface_match = true → ¬(σ′ = σ as functions).

    **Proof strategy:** Discard the surface-match premise (it is not needed — route
    mismatch is unconditional); extract `c.route_mismatch`. All structural content
    lives in the record field, not in the proof term.

    Note: this proves ¬(functional equality of σ′ and σ), given `c.route_mismatch`.
    The Gettier reading is: the recipient's route (σ′) is not the source's route (σ),
    so any correct output produced by σ′ is not authorized under the source notation. -/
theorem accidental_correctness_is_not_authorization
    (c : notation_gettier_case (PropLike := PropLike)) :
    c.surface_match = true →
    ¬ (c.improvised.σ_prime = c.improvised.source.σ) :=
  fun _ h_eq => c.route_mismatch h_eq

end EpArch
