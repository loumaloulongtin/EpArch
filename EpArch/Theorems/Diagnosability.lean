/-
EpArch.Theorems.Diagnosability — Observable Fields and Diagnosability

Defines observability and diagnosability in terms of field sets:
- ObservableFields (per-representation field lists)
- Diagnosability (cardinality of observable fields)
- systematically_harder (partial order: fewer fields = harder to diagnose)

Uses List Field rather than Finset to avoid Mathlib dependency.
No time/cost claims — only structural availability of diagnostic moves.
-/

import EpArch.Basic
import EpArch.Header

namespace EpArch.Diagnosability

open EpArch

/-! ## Observable Fields by Representation -/

/-- All fields available in a full deposit with complete header.
    This is the maximum diagnostic granularity. -/
def AllFields : List Field :=
  [.S, .E, .V, .τ, .redeemability, .acl]

/-- Fields observable after stripping (only structural fields remain).
    After stripping, we lose S, E, V — only τ, redeemability, acl might remain
    depending on the stripping model.

    Conservative model: stripping removes header entirely, leaving only
    the claim content and status. We model this as empty field set for
    header-specific fields. -/
def StrippedFields : List Field :=
  []  -- No header fields observable after stripping

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

/-! ## Monotonicity Theorems -/

/-- THEOREM: Stripping reduces diagnosability.

    This is the core result for Commitment #7.
    Stripped deposits have strictly fewer observable fields. -/
theorem strip_reduces_diagnosability :
    systematically_harder false true := by
  unfold systematically_harder diagnosability ObservableFields AllFields StrippedFields
  decide

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

end EpArch.Diagnosability
