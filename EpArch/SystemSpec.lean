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
