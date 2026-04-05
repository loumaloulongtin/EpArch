import EpArch.Basic
import EpArch.Header

/-!
# Diagnosability.lean

This module defines observability and diagnosability in terms of field sets,
replacing hardcoded constants with a principled approach.

## Key Concepts

1. **ObservableFields**: The set of fields that can be inspected in a given
   representation (full deposit vs stripped payload).

2. **Diagnosability**: The cardinality of ObservableFields — how many
   independent failure modes can be distinguished.

3. **systematically_harder**: A partial order on representations based on
   diagnosability. Fewer observable fields = harder to diagnose.

## Design Decisions

- We use `List Field` rather than `Finset` to avoid Mathlib dependency
- "Harder" is definitional: fewer observable fields = coarser partition
- No time/cost claims — only structural availability of diagnostic moves
-/

namespace EpArch.Diagnosability

open EpArch

/-! ## Observable Fields by Representation -/

/-- All fields available in a full deposit with complete header.
    This is the maximum diagnostic granularity. -/
def AllFields : List Field :=
  [.S, .E, .V, .τ, .redeemability, .acl]

/-- Fields observable in a header (S, E, V, τ, acl, redeemability).
    A full deposit exposes all of these. -/
def HeaderFields : List Field :=
  [.S, .E, .V, .τ, .redeemability, .acl]

/-- Fields observable after stripping (only structural fields remain).
    After stripping, we lose S, E, V — only τ, redeemability, acl might remain
    depending on the stripping model.

    Conservative model: stripping removes header entirely, leaving only
    the claim content and status. We model this as empty field set for
    header-specific fields. -/
def StrippedFields : List Field :=
  []  -- No header fields observable after stripping

/-- Fields that survive stripping (structural fields from the deposit itself).
    These are NOT header fields — they're the P, bubble, status fields.
    But since Field only covers header fields, stripped = empty. -/
def StrippedHeaderFields : List Field :=
  []

/-! ## Observability Predicates -/

/-- A field is observable in a full deposit. -/
def observable_in_full (f : Field) : Prop :=
  f ∈ AllFields

/-- A field is observable in a stripped deposit.
    After stripping, no header fields are observable. -/
def observable_in_stripped (f : Field) : Prop :=
  f ∈ StrippedFields

/-- Observable fields given a "has header" flag.
    This is the key bridge between representation and observability. -/
def ObservableFields (has_header : Bool) : List Field :=
  if has_header then AllFields else StrippedFields

/-! ## Diagnosability as Cardinality -/

/-- Diagnosability: the number of fields that can be independently
    inspected and challenged.

    This replaces the hardcoded FieldCount_Full = 6, FieldCount_Stripped = 3
    with a computed value based on the observable field set. -/
def diagnosability (has_header : Bool) : Nat :=
  (ObservableFields has_header).length

/-- Full deposits have diagnosability 6 (all header fields). -/
theorem diagnosability_full : diagnosability true = 6 := by
  unfold diagnosability ObservableFields AllFields
  rfl

/-- Stripped deposits have diagnosability 0 (no header fields). -/
theorem diagnosability_stripped : diagnosability false = 0 := by
  unfold diagnosability ObservableFields StrippedFields
  rfl

/-! ## The "Harder" Ordering -/

/-- systematically_harder: representation r1 is harder to diagnose than r2
    if it has strictly fewer observable fields.

    This is DEFINITIONAL — we're not asserting time/cost claims. -/
def systematically_harder (has_header₁ has_header₂ : Bool) : Prop :=
  diagnosability has_header₁ < diagnosability has_header₂

/-- alternative: harder_or_equal allows ≤ comparison. -/
def harder_or_equal (has_header₁ has_header₂ : Bool) : Prop :=
  diagnosability has_header₁ ≤ diagnosability has_header₂

/-! ## Monotonicity Theorems -/

/-- THEOREM: Stripping reduces diagnosability.

    This is the core result for Commitment #7.
    Stripped deposits have strictly fewer observable fields. -/
theorem strip_reduces_diagnosability :
    systematically_harder false true := by
  unfold systematically_harder diagnosability ObservableFields AllFields StrippedFields
  decide

/-- THEOREM: Stripping never increases diagnosability.

    Weaker version (≤ instead of <) for contexts where we only need monotonicity. -/
theorem strip_monotonic :
    harder_or_equal false true := by
  unfold harder_or_equal diagnosability ObservableFields AllFields StrippedFields
  decide

/-- THEOREM: Observable fields in stripped ⊆ observable fields in full.

    Set-theoretic version of monotonicity. -/
theorem stripped_subset_full :
    ∀ f : Field, observable_in_stripped f → observable_in_full f := by
  intro f h_stripped
  -- StrippedFields = [], so h_stripped : f ∈ [] is False
  unfold observable_in_stripped StrippedFields at h_stripped
  cases h_stripped

/-! ## Bridge to Repair Routing -/

/-- RepairTarget: a field that can be targeted for repair.
    If a field is not observable, it cannot be a repair target. -/
def canTargetRepair (has_header : Bool) (f : Field) : Prop :=
  f ∈ ObservableFields has_header

/-- THEOREM: Stripped deposits cannot target any header field for repair.

    This is the formal content of "coarser repair."
    Without header fields visible, the only option is full revocation. -/
theorem stripped_no_field_repair :
    ∀ f : Field, ¬canTargetRepair false f := by
  intro f h
  unfold canTargetRepair ObservableFields StrippedFields at h
  cases h

/-- THEOREM: Full deposits can target any field for repair.

    With all fields visible, we can do surgical repair. -/
theorem full_can_repair_any :
    ∀ f : Field, canTargetRepair true f := by
  intro f
  unfold canTargetRepair ObservableFields AllFields
  cases f <;> decide

/-! ## Diagnosis Soundness -/

/-- A diagnosis function must return an observable field.
    This is the soundness constraint for any diagnosis oracle.

    We don't define the diagnosis function itself (that's spec-level),
    but we characterize what a sound diagnosis must satisfy. -/
def SoundDiagnosis (has_header : Bool) (diagnose : Unit → Option Field) : Prop :=
  ∀ u, match diagnose u with
    | some f => f ∈ ObservableFields has_header
    | none => True

/-- THEOREM: Any sound diagnosis on stripped deposits must return none.

    If the deposit is stripped, a sound diagnosis cannot return any field
    because no fields are observable. -/
theorem sound_diagnosis_stripped_must_be_none :
    ∀ diagnose : Unit → Option Field,
      SoundDiagnosis false diagnose →
      ∀ u, diagnose u = none := by
  intro diagnose h_sound u
  cases h : diagnose u with
  | none => rfl
  | some f =>
    -- This contradicts soundness since StrippedFields = []
    have h_absurd := h_sound u
    simp only [h] at h_absurd
    unfold ObservableFields StrippedFields at h_absurd
    cases h_absurd

/-! ## Bridge to Repair-Loop Claims

The key connection is between observability and repair routing.
The result "stripping makes repair harder" is structural,
not merely a time/cost assertion. -/

/-- THEOREM: Observable fields exactly match repair targets.

    A field can be targeted for repair iff it can be observed.
    This is the formal content of "no invisible repair." -/
theorem repair_requires_observability :
    ∀ f : Field, ∀ has_header : Bool,
      canTargetRepair has_header f ↔ f ∈ ObservableFields has_header := by
  intro f has_header
  unfold canTargetRepair
  exact Iff.rfl

/-- THEOREM: Repair granularity equals diagnosability.

    The number of distinct repair targets equals the diagnosability.
    This formalizes "coarser partition = fewer repair options." -/
theorem repair_granularity_eq_diagnosability :
    ∀ has_header : Bool,
      (ObservableFields has_header).length = diagnosability has_header := by
  intro has_header
  unfold diagnosability
  rfl

/-- THEOREM: Full deposits have maximal repair granularity.

    All 6 fields can be targeted for repair. -/
theorem full_has_maximal_repair_granularity :
    diagnosability true = 6 := diagnosability_full

/-- THEOREM: Stripped deposits have zero repair granularity.

    No fields can be targeted; only coarse revocation remains. -/
theorem stripped_has_zero_repair_granularity :
    diagnosability false = 0 := diagnosability_stripped

/-! ## Summary

The diagnosability model provides:

1. **Definitional "harder"**: `systematically_harder false true` is a theorem,
   not an axiom. Stripped = 0 observable fields, Full = 6.

2. **Monotonicity**: `stripped_subset_full` proves the set inclusion.

3. **Repair targeting**: `stripped_no_field_repair` shows why stripped
   deposits can only be revoked, not surgically repaired.

4. **Diagnosis soundness**: Any sound diagnosis on stripped deposits
   must return `none` because there are no observable fields.

5. **Repair-loop bridge**: `repair_requires_observability` proves
   that repair routing is exactly constrained by observability.

This uses a principled derivation from the observable field sets,
rather than magic constants like `FieldCount_Full := 6`. -/

end EpArch.Diagnosability
