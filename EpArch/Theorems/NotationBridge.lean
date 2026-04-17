/-
EpArch.Theorems.NotationBridge — Notation Bridge Authorization

Bridges Layer 1 (notation-invariance of redeemability, proved in Dissolutions)
to Layers 2 and 3 of the notation authorization story:
- Layer 2: notation opacity prevents authorization when the bridge is stripped
- Layer 3: carrying the bridge with the export restores authorization
- Gettier case: accidental surface match is not authorization
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
    Carrying σ is the "full headers" case; absence of σ is stripped notation export.
    The bijection σ/σ_inv witnesses that the source community's notation is internally
    coherent — `left_inv` and `right_inv` encode that σ is genuinely bijective. -/
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
    together with a witness that σ′ disagrees with σ on at least one input.
    The `disagrees` field is the structural invariant encoding V-side defect under
    notation opacity: the improvised route departs from the source's truth-conferring
    structure at the single input `agrees_on`. -/
structure improvised_uptake_case where
  source      : notation_bridge_case (PropLike := PropLike)
  σ_prime     : PropLike → PropLike
  σ_prime_inv : PropLike → PropLike
  /-- A point at which σ_prime diverges from source.σ. -/
  agrees_on   : PropLike
  /-- Structural invariant: σ_prime disagrees with source.σ at agrees_on. -/
  disagrees   : σ_prime agrees_on ≠ source.σ agrees_on

/-- Notation-Gettier case: improvised uptake produces a surface match but does not
    track the source authorization route.

    Structural invariant: `route_mismatch` records that the improvised bijection is
    not the source bijection, making this a V-side defect under notation opacity —
    not epistemic luck, but a missing bridge. Models the `leanKernelGettierCase`
    pattern: correct outcome, provenance gap. -/
structure notation_gettier_case where
  source         : notation_bridge_case (PropLike := PropLike)
  improvised     : improvised_uptake_case (PropLike := PropLike)
  /-- Recipient accidentally produced the right surface output. -/
  surface_match  : Bool
  /-- Structural invariant: the improvised bijection is not the source bijection.
      The correct output was reached via the wrong interpretive route. -/
  route_mismatch : improvised.σ_prime ≠ source.σ

/-! ## Layer 2 — Notation Opacity Prevents Authorization

A single divergence witness defeats bijection identification.
Mirrors `import_cannot_reconstruct` (Strip.lean) for the notation domain. -/

/-- NOTATION OPACITY THEOREM (Layer 2)

    Without the source bijection σ, the recipient cannot identify which relabeling
    was used. A single witness where σ′ ≠ σ defeats the assumption that σ′
    universally agrees with σ.

    **Theorem shape:** ¬(∀ P, σ′ P = σ P), given the single divergence witness
    encoded in `c.disagrees`.

    **Proof strategy:** Apply the universal to `c.agrees_on`; this produces
    `c.σ_prime c.agrees_on = c.source.σ c.agrees_on`, which `c.disagrees` refutes.
    Structurally identical to `import_cannot_reconstruct`: one missing datum
    makes identification impossible. -/
theorem notation_opacity_prevents_authorization
    (c : improvised_uptake_case (PropLike := PropLike)) :
    ¬ (∀ P, c.σ_prime P = c.source.σ P) :=
  fun h => c.disagrees (h c.agrees_on)

/-! ## Layer 3 — Bridge Export Enables Authorization

When σ is carried with the export, `notation_invariance_of_redeemability` applies
directly. Layer 3 reduces to Layer 1 with the bridge now available by construction. -/

/-- BRIDGE EXPORT ENABLES AUTHORIZATION (Layer 3)

    If the notation bijection is carried with the export, the recipient can verify
    σ directly and redeemability transfers without prior notation knowledge.
    Delegates to `notation_invariance_of_redeemability` (Layer 1, Dissolutions.lean):
    once σ is available, the bridge packet is a valid `NotationRelabeling`.

    **Theorem shape:** redeemability_is_proof_consistency a ↔ (relabeled case).

    **Proof strategy:** Construct a `NotationRelabeling` from c's fields and apply
    the Layer 1 theorem directly. The `_h` and `_hP` premises document the
    authorization preconditions (bridge was carried; a.P matches c.P) in the theorem
    statement but are not needed in the proof term — Layer 1 applies unconditionally
    once the NotationRelabeling is assembled. -/
theorem bridge_export_enables_authorization
    (c : notation_bridge_case (PropLike := PropLike))
    (_h : c.bridge_carried = true)
    (a : apriori_case (PropLike := PropLike))
    (_hP : a.P = c.P) :
    redeemability_is_proof_consistency a ↔
    redeemability_is_proof_consistency (relabel_case ⟨c.σ, c.σ_inv, c.left_inv, c.right_inv⟩ a) :=
  notation_invariance_of_redeemability ⟨c.σ, c.σ_inv, c.left_inv, c.right_inv⟩ a

/-! ## Gettier Case — Accidental Correctness Is Not Authorization

Correct surface output through the wrong interpretive route is not authorized uptake. -/

/-- ACCIDENTAL CORRECTNESS IS NOT AUTHORIZATION (Gettier theorem)

    An improvised uptake that surface-matches the correct output is not authorized
    under the source notation. Surface match does not imply route identity.
    Authorization requires the specific σ used at source deposit time — not any σ′
    that happens to agree on one output.

    **Theorem shape:** surface_match = true → ¬(σ′ = σ).

    **Proof strategy:** Extract `route_mismatch` from the record. The surface match
    premise is intentionally dropped — the route mismatch holds independently of
    whether the output happened to be correct. The structural content is in the
    record field `route_mismatch`, not in the proof term. -/
theorem accidental_correctness_is_not_authorization
    (c : notation_gettier_case (PropLike := PropLike)) :
    c.surface_match = true →
    ¬ (c.improvised.σ_prime = c.source.σ) :=
  fun _ h_eq => c.route_mismatch h_eq

end EpArch
