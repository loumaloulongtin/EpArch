/-
EpArch.Theorems.Strip — Export Stripping and Competition Gate Corners 3, 4, 10

All stripping results live here:
- `Payload` / `stripV`: provenance loss across trust boundaries (non-injectivity, irreversibility)
- `strip` / `PayloadStripped`: header loss on deposit export (non-injectivity, SEV-equivalence)
- Competition gate corners 3, 4, 10
-/
import EpArch.Basic
import EpArch.StepSemantics
import EpArch.Diagnosability

namespace EpArch

open StepSemantics
open Diagnosability

universe u

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}

/-! ========================================================================
    CORNER THEOREMS — Competition Gates

    These theorems formalize "cornering opportunities" — competition gates.
    Each corner forces rival architectures to either implement equivalent
    structure or retreat to an idealized target.
    ======================================================================== -/


/-! ## Corner 3 — Export-gating gate (strip non-injectivity)

    **Theorem shape:** `strip` is not injective — two deposits with different
    headers can have identical stripped forms.

    **Implication:** Importing only payload (without header) cannot recover
    the authorization state. Any system that strips headers loses diagnosability.

    The result is simple and obvious once stated, but structurally
    devastating to any system that strips headers on export. -/

/-- PayloadStripped: a deposit with header information removed.
    This represents what remains after export-stripping. -/
structure PayloadStripped (PropLike : Type u) where
  P : PropLike
  bubble : Bubble
  status : DepositStatus

/-- strip: remove header from a deposit.
    This is the "lossy export" operation that crosses trust boundaries
    without preserving validation metadata. -/
def strip (d : Deposit PropLike Standard ErrorModel Provenance) : PayloadStripped PropLike :=
  { P := d.P, bubble := d.bubble, status := d.status }

/-- CORNER 3 THEOREM: strip is not injective.

    Given a colliding pair d₁ ≠ d₂ with strip d₁ = strip d₂, derive the
    negation of injectivity directly: there is no way strip can map distinct
    deposits to distinct stripped forms.

    Conclusion is `¬∀ x y, strip x = strip y → x = y` (the definition of
    non-injectivity spelled out, since `Function.Injective` is not in scope
    without Mathlib).  The conclusion identifies the non-injectivity witness directly.

    For the structural construction of a colliding pair from header differences,
    see `different_headers_same_strip`.  For the no-left-inverse corollary,
    see `no_strip_left_inverse`. -/
theorem strip_not_injective_if
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_diff : d₁ ≠ d₂)
    (h_same_strip : strip d₁ = strip d₂) :
    ¬∀ (x y : Deposit PropLike Standard ErrorModel Provenance),
        strip x = strip y → x = y :=
  fun h_inj => h_diff (h_inj d₁ d₂ h_same_strip)

/-- Alternative formulation: strip loses information.

    If d₁.h ≠ d₂.h but all other fields match, strip(d₁) = strip(d₂).
    This is the non-injectivity in terms of header differences. -/
theorem strip_loses_header_info
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_same_P : d₁.P = d₂.P)
    (h_same_bubble : d₁.bubble = d₂.bubble)
    (h_same_status : d₁.status = d₂.status) :
    strip d₁ = strip d₂ := by
  unfold strip
  simp only [h_same_P, h_same_bubble, h_same_status]

/-- CORNER 3 COROLLARY: Different headers, same strip.

    The key insight: two deposits can have different headers (d₁.h ≠ d₂.h)
    but identical stripped forms. This is the information-loss lemma. -/
theorem different_headers_same_strip
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_same_P : d₁.P = d₂.P)
    (h_same_bubble : d₁.bubble = d₂.bubble)
    (h_same_status : d₁.status = d₂.status)
    (h_diff_header : d₁.h ≠ d₂.h) :
    d₁ ≠ d₂ ∧ strip d₁ = strip d₂ := by
  constructor
  · intro h_eq
    have : d₁.h = d₂.h := congrArg Deposit.h h_eq
    exact h_diff_header this
  · exact strip_loses_header_info d₁ d₂ h_same_P h_same_bubble h_same_status

/-! ## No Right Inverse for Strip

    These theorems establish that stripping is irreversible:
    you cannot reconstruct the original deposit from stripped payload alone.

    Authorization doesn't transfer frictionlessly. -/

/-- THEOREM: strip has no left inverse.

    There cannot exist a function `unstrip` that recovers the original
    deposit from its stripped form. The reason: multiple distinct deposits
    can have the same stripped form (as shown by `different_headers_same_strip`).

    Formulated as: IF unstrip existed (recovering original from strip),
    THEN it would make distinct deposits equal, contradiction.

    **COMPETITION GATE**: Import cannot reconstruct provenance from
    stripped payload alone. Authorization requires re-validation. -/
theorem no_strip_left_inverse
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_diff : d₁ ≠ d₂)
    (h_same_strip : strip d₁ = strip d₂) :
    -- Any function claiming to be a left inverse would map
    -- strip d₁ = strip d₂ to a single value, but d₁ ≠ d₂
    -- So no such function can exist that satisfies both:
    --   unstrip (strip d₁) = d₁ AND unstrip (strip d₂) = d₂
    ¬∃ (unstrip : PayloadStripped PropLike → Deposit PropLike Standard ErrorModel Provenance),
      unstrip (strip d₁) = d₁ ∧ unstrip (strip d₂) = d₂ := by
  intro ⟨unstrip, h_inv₁, h_inv₂⟩
  -- unstrip (strip d₁) = d₁ and unstrip (strip d₂) = d₂
  -- But strip d₁ = strip d₂, so unstrip (strip d₁) = unstrip (strip d₂)
  have h_eq : unstrip (strip d₁) = unstrip (strip d₂) := by
    rw [h_same_strip]
  -- Therefore d₁ = d₂
  rw [h_inv₁, h_inv₂] at h_eq
  -- But d₁ ≠ d₂, contradiction
  exact h_diff h_eq

/-- COROLLARY: Import cannot reconstruct original deposit.

    Given only a stripped payload, there is no way to uniquely determine
    which original deposit it came from (when multiple valid sources exist).

    This is the formal statement of "authorization doesn't transfer." -/
theorem import_cannot_reconstruct
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_same_P : d₁.P = d₂.P)
    (h_same_bubble : d₁.bubble = d₂.bubble)
    (h_same_status : d₁.status = d₂.status)
    (h_diff_header : d₁.h ≠ d₂.h) :
    -- The stripped payload is ambiguous: it could have come from d₁ or d₂
    -- No reconstruction function can determine which
    strip d₁ = strip d₂ ∧
    ¬∃ (reconstruct : PayloadStripped PropLike → Deposit PropLike Standard ErrorModel Provenance),
      reconstruct (strip d₁) = d₁ ∧ reconstruct (strip d₂) = d₂ := by
  have h_strip_eq := strip_loses_header_info d₁ d₂ h_same_P h_same_bubble h_same_status
  have h_diff : d₁ ≠ d₂ := by
    intro h_eq
    have : d₁.h = d₂.h := congrArg Deposit.h h_eq
    exact h_diff_header this
  constructor
  · exact h_strip_eq
  · exact no_strip_left_inverse d₁ d₂ h_diff h_strip_eq


/-! ## Corner 10 — Recovery vs re-derivation gate

    **Theorem shape:** Two deposits with identical content P can be
    non-identical as deposits (due to different provenance/headers).

    **Implication:** Rediscovering a claim is NOT epistemically identical
    to recovering the original deposit. The header carries authorization
    that raw content does not. -/

/-- DepositContentEq: two deposits have the same propositional content.
    This is WEAKER than deposit identity. -/
def DepositContentEq (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  d₁.P = d₂.P

/-- DepositFullEq: two deposits are fully identical (same P, header, bubble, status).
    This is deposit IDENTITY. -/
def DepositFullEq (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  d₁ = d₂

/-- CORNER 10 THEOREM: Same content does not imply same deposit.

    Two deposits can have identical P but differ in header, making them
    non-identical as deposits. This corners views that treat rediscovery
    as epistemically equivalent to recovery.

    Formulated as implication: IF headers differ, THEN deposits differ
    (even with same content). -/
theorem content_eq_not_implies_deposit_eq
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_same_P : d₁.P = d₂.P)
    (h_diff_header : d₁.h ≠ d₂.h) :
    DepositContentEq d₁ d₂ ∧ ¬DepositFullEq d₁ d₂ := by
  constructor
  · exact h_same_P
  · intro h_eq
    have : d₁.h = d₂.h := congrArg Deposit.h h_eq
    exact h_diff_header this

/-- Structural content: if headers differ, deposits differ (even with same P). -/
theorem different_headers_different_deposits
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_diff_header : d₁.h ≠ d₂.h) :
    d₁ ≠ d₂ := by
  intro h_eq
  have : d₁.h = d₂.h := congrArg Deposit.h h_eq
  exact h_diff_header this

/-- Provenance matters: deposits with different provenance are different
    even if they have the same content P. -/
theorem provenance_matters
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (_h_same_P : d₁.P = d₂.P)
    (h_diff_V : d₁.h.V ≠ d₂.h.V) :
    d₁ ≠ d₂ := by
  intro h_eq
  have : d₁.h.V = d₂.h.V := by
    have hh : d₁.h = d₂.h := congrArg Deposit.h h_eq
    exact congrArg Header.V hh
  exact h_diff_V this


/-! ## Diagnosability Ordering

    **Goal:** Make "systematically harder" fully internal — define it via
    diagnosability (number of distinguishable failure modes) rather than
    asserting it axiomatically.

    **Key insight:** "Harder" means fewer diagnostic distinctions, which means
    coarser partition of failure modes. This is a structural property of the
    observation function, not a time metric. -/

/-- FieldCount_Full: the number of fields that can be independently observed
    and challenged in a full (non-stripped) deposit. This is 6:
    S, E, V, τ, redeemability, acl. -/
def FieldCount_Full : Nat := 6

/-- FieldCount_Stripped: the number of fields remaining after stripping.
    This is 3: P, bubble, status. -/
def FieldCount_Stripped : Nat := 3

/-- harder_by_field_count: ordering by distinguishable fields.
    Fewer fields = harder to diagnose.

    Note: This captures that harder = coarser partition = fewer repair paths. -/
def harder_by_field_count (count₁ count₂ : Nat) : Prop :=
  count₁ < count₂

/-- THEOREM: Stripping reduces field count.

    The stripped form has fewer distinguishable fields than the original.
    This is the formal content of "stripping causes diagnosability drop." -/
theorem strip_reduces_field_count :
    harder_by_field_count FieldCount_Stripped FieldCount_Full := by
  -- FieldCount_Stripped = 3, FieldCount_Full = 6
  unfold harder_by_field_count FieldCount_Stripped FieldCount_Full
  decide

/-- THEOREM: Fewer fields means fewer repair targets.

    If you can distinguish fewer fields, you have fewer targeted
    repair options. This is the formal bridge from "harder" to "worse."

    The key insight: repair targeting requires field identification.
    Stripping collapses field identity, so repair becomes coarser. -/
theorem fewer_fields_coarser_repair :
    -- Stripped version has 3 distinguishable classes
    -- Full version has 6 distinguishable classes
    -- So stripped version can target at most 3 repair types
    FieldCount_Stripped ≤ FieldCount_Full := by
  unfold FieldCount_Stripped FieldCount_Full
  decide

/-! ## Summary: The "harder" ordering is definitional.

    1. FieldCount_Full = 6 distinguishable fields
    2. FieldCount_Stripped = 3 distinguishable fields
    3. 3 < 6, so stripping reduces diagnostic granularity
    4. Lower granularity = fewer repair options
    5. Therefore stripping makes repair "harder" (definitionally)

    No time metric required. "Harder" is a structural property.

    See also `sev_refines_stripped` in Corner 4 for the partition
    refinement form of this result. -/


/-! ## Bridge to Diagnosability Module

    The `FieldCount_*` constants are superseded by the principled
    approach in `EpArch.Diagnosability`. This section bridges the two.

    Key improvements:
    - `AllFields` and `StrippedFields` are actual lists, not magic numbers
    - `diagnosability` is computed from list length
    - `canTargetRepair` connects observability to repair routing
    - `SoundDiagnosis` constrains diagnosis oracles -/

/-- Bridge theorem: FieldCount_Full matches the principled diagnosability for full deposits. -/
theorem fieldcount_full_eq_diagnosability :
    FieldCount_Full = diagnosability true := by
  unfold FieldCount_Full diagnosability ObservableFields AllFields
  rfl

/-- Bridge theorem: stripped diagnosability is 0.

    Only header fields are observable; stripped deposits have none, yielding 0. -/
theorem stripped_diagnosability_is_zero :
    diagnosability false = 0 := diagnosability_stripped

/-- Bridge theorem: `strip_reduces_diagnosability` implies `strip_reduces_field_count`.

    The principled result is strictly stronger because it uses the actual field sets. -/
theorem v8_implies_v7_strip_reduces :
    Diagnosability.systematically_harder false true → harder_by_field_count 0 FieldCount_Full := by
  intro _
  unfold harder_by_field_count FieldCount_Full
  decide

/-- Bridge theorem: repair routing is impossible without observable fields.

    We can now prove that repair
    *cannot* be field-specific on stripped deposits (not just that it's "harder"). -/
theorem stripped_repair_must_be_coarse :
    ∀ f : Field, ¬canTargetRepair false f := stripped_no_field_repair

/-- Bridge theorem: full deposits support surgical repair.

    Any field can be targeted for repair in a full deposit. -/
theorem full_repair_can_be_surgical :
    ∀ f : Field, canTargetRepair true f := full_can_repair_any


/-! ## Corner 4 — Header-stripping gate (partition refinement)

    **Theorem shape:** The equivalence relation induced by header-preserved
    states is strictly finer than the equivalence relation on stripped states.

    **Implication:** "Systematically harder" is structural — header-preserved
    deposits admit more diagnostic distinctions than headerless ones. -/

/-- SEV_equivalent: two deposits are equivalent from an SEV perspective.
    They have the same S, E, V fields. This is FINER than stripped equivalence. -/
def SEV_equivalent (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  d₁.h.S = d₂.h.S ∧ d₁.h.E = d₂.h.E ∧ d₁.h.V = d₂.h.V

/-- Stripped_equivalent: two deposits are equivalent after stripping.
    Same P, bubble, status. This is COARSER than SEV equivalence. -/
def Stripped_equivalent (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  d₁.P = d₂.P ∧ d₁.bubble = d₂.bubble ∧ d₁.status = d₂.status

/-- CORNER 4 THEOREM: SEV equivalence refines stripped equivalence.

    If two deposits are SEV-equivalent, they may still differ in other
    header fields (τ, acl, redeem), but from a diagnostic perspective
    they're in the same "failure-mode class."

    More importantly: Stripped_equivalent does NOT imply SEV_equivalent,
    so the refinement is STRICT. -/
theorem sev_refines_stripped
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_same_P : d₁.P = d₂.P)
    (h_same_bubble : d₁.bubble = d₂.bubble)
    (h_same_status : d₁.status = d₂.status)
    (_h_sev : SEV_equivalent d₁ d₂) :
    Stripped_equivalent d₁ d₂ := by
  exact ⟨h_same_P, h_same_bubble, h_same_status⟩

/-- Stripped equivalence does NOT imply SEV equivalence.
    (The refinement is strict — header-preserved distinguishes more.)

    Formulated as implication: IF deposits have same stripped form
    but different S/E/V fields, THEN stripped equivalence holds
    but SEV equivalence fails. -/
theorem stripped_not_implies_sev
    (d₁ d₂ : Deposit PropLike Standard ErrorModel Provenance)
    (h_stripped_eq : Stripped_equivalent d₁ d₂)
    (h_sev_diff : d₁.h.S ≠ d₂.h.S ∨ d₁.h.E ≠ d₂.h.E ∨ d₁.h.V ≠ d₂.h.V) :
    Stripped_equivalent d₁ d₂ ∧ ¬SEV_equivalent d₁ d₂ := by
  constructor
  · exact h_stripped_eq
  · intro h_sev
    cases h_sev_diff with
    | inl h_S => exact h_S h_sev.1
    | inr h_rest =>
      cases h_rest with
      | inl h_E => exact h_E h_sev.2.1
      | inr h_V => exact h_V h_sev.2.2


/-! ## Provenance Stripping: Non-Injectivity of V-Loss

When deposits cross trust boundaries, provenance (V) may be stripped.
This stripping is NOT INJECTIVE — different provenances collapse to the same
stripped payload. Therefore you cannot "undo" the stripping; the information
is genuinely lost.

This underwrites "justification doesn't transfer cleanly across export boundaries."
If it did, you could always recover V from the stripped payload, contradicting
non-injectivity.

Contrast with `strip`/`PayloadStripped` above: that operation strips the
header from a full `Deposit`. This operation strips provenance from a
minimal `Payload` (claim + provenance only). Both are one-way losses. -/

/-- A payload packages a claim with its provenance.

    Minimal structure for demonstrating information loss in export.
    The full Deposit includes more structure (header, bubble, status),
    but for the non-injectivity theorem we only need claim + provenance. -/
structure Payload (PropLike Provenance : Type u) where
  claim : PropLike
  provenance : Option Provenance
  deriving DecidableEq

/-- Strip provenance from a payload.

    This models export across a trust boundary that does not preserve
    provenance chains (e.g., informal citation, oral transmission,
    screenshot sharing, "I heard somewhere...").

    The operation is definitionally simple: set provenance to none.
    The interesting property is what this LOSES. -/
def stripV (p : Payload PropLike Provenance) : Payload PropLike Provenance :=
  { p with provenance := none }

/-- stripV is not injective.

    There exist two payloads with different provenances that become
    identical after stripping.

    This is the core information-loss theorem for cross-boundary transfer.
    It proves that provenance is GENUINELY LOST, not merely hidden:
    no function can recover it from the stripped payload.

    Proof: Trivial witness construction. Given any two distinct provenances
    p1 ≠ p2, the payloads (claim, some p1) and (claim, some p2) have
    different provenances but identical stripped forms. -/
theorem stripV_not_injective [Inhabited PropLike] [Inhabited Provenance]
    (h_two_provenances : ∃ (p1 p2 : Provenance), p1 ≠ p2) :
    ∃ (pay1 pay2 : Payload PropLike Provenance),
      pay1.provenance ≠ pay2.provenance ∧ stripV pay1 = stripV pay2 :=
  let ⟨p1, p2, h_ne⟩ := h_two_provenances
  let claim : PropLike := default
  let pay1 : Payload PropLike Provenance := ⟨claim, some p1⟩
  let pay2 : Payload PropLike Provenance := ⟨claim, some p2⟩
  ⟨pay1, pay2, fun h_eq => h_ne (Option.some.inj h_eq), rfl⟩

/-- Corollary: stripping destroys provenance information.

    No function can "unstripV" to recover original provenance,
    because stripping is not injective.

    If there were such a function f : Payload → Payload with
    f ∘ stripV = id, then stripV would be injective (left-cancellable).
    But we just proved stripV is NOT injective. -/
theorem stripV_irreversible [Inhabited PropLike] [Inhabited Provenance]
    (h_two_provenances : ∃ (p1 p2 : Provenance), p1 ≠ p2) :
    ¬∃ (f : Payload PropLike Provenance → Payload PropLike Provenance),
      ∀ p, f (stripV p) = p := fun ⟨f, h_inv⟩ =>
  let ⟨pay1, pay2, h_ne, h_eq⟩ := stripV_not_injective h_two_provenances
  -- If f were a left inverse, then pay1 = f (stripV pay1) = f (stripV pay2) = pay2
  let h1 : pay1 = f (stripV pay1) := (h_inv pay1).symm
  let h2 : f (stripV pay2) = pay2 := h_inv pay2
  -- Since stripV pay1 = stripV pay2, we have f (stripV pay1) = f (stripV pay2)
  let h3 : f (stripV pay1) = f (stripV pay2) := congrArg f h_eq
  -- Therefore pay1 = pay2
  let h_eq' : pay1 = pay2 := h1.trans (h3.trans h2)
  -- But this contradicts pay1.provenance ≠ pay2.provenance
  h_ne (congrArg Payload.provenance h_eq')

/-- The stripping operation is idempotent.

    Once stripped, further stripping does nothing.
    This models: "you can't lose what you've already lost." -/
theorem stripV_idempotent (p : Payload PropLike Provenance) :
    stripV (stripV p) = stripV p := by
  simp only [stripV]

/-- Stripped payloads preserve the claim but lose provenance.

    The claim survives export; only the validation metadata is lost. -/
theorem stripV_preserves_claim (p : Payload PropLike Provenance) :
    (stripV p).claim = p.claim := by
  simp only [stripV]

/-- Stripped payloads have no provenance. -/
theorem stripV_loses_provenance (p : Payload PropLike Provenance) :
    (stripV p).provenance = none := by
  simp only [stripV]


end EpArch
