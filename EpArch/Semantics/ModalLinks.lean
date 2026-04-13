/-
EpArch/Semantics/ModalLinks.lean — Modal Epistemology Conditions

Connects Safety/Sensitivity (modal epistemology) to the S/E/V field
structure. Both conditions reduce operationally to header preservation.

## Contents

- V_independent, V_spoofable, E_covers_counterfactual, E_has_gap
- Safe, Unsafe, Sensitive, Insensitive
- safety_iff_V_independence, sensitivity_iff_E_coverage
- headers_provide_modal_properties, stripped_headers_lose_modal_properties
- safety_sensitivity_coincide, modal_robustness_is_header_preservation

## Relationship to Other Files

- EpArch.Semantics.StepSemantics: Deposit, header_preserved
- EpArch.Concrete.NonVacuity: opens this namespace for concrete instantiation tests
-/

import EpArch.Semantics.StepSemantics

namespace EpArch.ModalLinks

open EpArch.StepSemantics

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}

/-! ## V-Independence: Provenance Not Dependent on Luck

V-independence means the provenance chain doesn't depend on accidental
features that could easily vary. In the threat model, this corresponds
to resistance against V-spoofing attacks. -/

/-- A deposit has V-independence if its header is preserved.

    Operationally: the V-field (provenance) is intact and authentic.
    This means: no successful V-spoofing occurred during acceptance.

    V-independence: the provenance must not depend on lucky features
    that could vary. Since header_preserved is opaque, we use it as
    the foundation. -/
def V_independent (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  -- The deposit's header including V is preserved (not stripped)
  header_preserved d

/-- A deposit is V-spoofable if its header was stripped.

    This is the NEGATION of V-independence: the header is stripped,
    so the V-field (provenance) could have been faked. -/
def V_spoofable (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  ¬header_preserved d

/-- V-spoofable is equivalent to ¬V_independent. -/
theorem V_spoofable_iff_not_independent
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    V_spoofable d ↔ ¬V_independent d := by
  unfold V_spoofable V_independent
  exact Iff.rfl

/-! ## E-Covers-Counterfactual: Error Model Includes Falsehood Scenario

E-covers-counterfactual means the error model includes the scenario
where the claim is false. This corresponds to the E-field being
comprehensive enough to model relevant failure modes. -/

/-- A deposit's E-field covers the counterfactual if header is preserved.

    Operationally: the E-field (error model) is accessible and intact.
    This enables the agent to detect falsehood if it occurs.

    E-covers-counterfactual: the error model must include the scenario
    where P is false. Since header_preserved is opaque, we use it as
    the foundation. -/
def E_covers_counterfactual (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  -- The E-field is accessible (header preserved)
  header_preserved d

/-- E-field gap: the error model is inaccessible (header stripped).

    This is the failure mode: agent can't detect falsehood because
    the E-field is not accessible. -/
def E_has_gap (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  ¬header_preserved d

/-- E_has_gap is equivalent to ¬E_covers_counterfactual. -/
theorem E_has_gap_iff_not_covers
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    E_has_gap d ↔ ¬E_covers_counterfactual d := by
  unfold E_has_gap E_covers_counterfactual
  exact Iff.rfl

/-! ## Safety: Wouldn't Falsely Believe P

Safety in modal epistemology: in nearby worlds where P is false,
the agent wouldn't believe P. In our model, this corresponds to
V-independence: the provenance must not depend on lucky features. -/

/-- Safety for a deposit: agent wouldn't falsely believe P.

    Operationally: the deposit's acceptance was based on genuine V,
    not spoofed provenance that could have been different. -/
def Safe (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  V_independent d

/-- Unsafe: the deposit could have been falsely accepted.

    This happens when V was spoofable — the provenance could have
    been faked, so acceptance doesn't track truth. -/
def Unsafe (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  V_spoofable d

/-- Unsafe ↔ ¬Safe. -/
theorem unsafe_iff_not_safe
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    Unsafe d ↔ ¬Safe d := by
  unfold Unsafe Safe
  exact V_spoofable_iff_not_independent d

/-! ## Sensitivity: Would Notice If P Were False

Sensitivity in modal epistemology: if P were false, the agent would
notice (wouldn't believe P). In our model, this corresponds to
E-coverage: the error model must include the falsehood scenario. -/

/-- Sensitivity for a deposit: agent would notice if P were false.

    Operationally: the deposit's E-field covers counterfactual scenarios,
    so the agent can detect falsehood if it occurs. -/
def Sensitive (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  E_covers_counterfactual d

/-- Insensitive: agent wouldn't notice if P were false.

    This happens when E has gaps — the error model doesn't include
    the falsehood scenario, so detection fails. -/
def Insensitive (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  E_has_gap d

/-- Insensitive ↔ ¬Sensitive. -/
theorem insensitive_iff_not_sensitive
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    Insensitive d ↔ ¬Sensitive d := by
  unfold Insensitive Sensitive
  exact E_has_gap_iff_not_covers d

/-! ## The Modal Links: Safety ↔ V, Sensitivity ↔ E

These are the key theorems connecting modal epistemology to S/E/V fields.
They show that Safety/Sensitivity are not separate conditions but are
captured by the V/E field structure. -/

/-- Safety failure implies V-independence failure.

    If a deposit is Unsafe (could have been falsely accepted),
    then it lacks V-independence (provenance is spoofable).

    This grounds `safety_V_link` from Theorems.lean. -/
theorem safety_V_link
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    Unsafe d → ¬V_independent d := by
  intro h_unsafe
  exact (V_spoofable_iff_not_independent d).mp h_unsafe

/-- V-independence implies Safety.

    If a deposit has V-independence (genuine provenance),
    then it is Safe (wouldn't have been falsely accepted).

    This is the converse: V-independence is SUFFICIENT for Safety. -/
theorem V_independence_implies_safety
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    V_independent d → Safe d := by
  intro h
  exact h

/-- Safety ↔ V-independence (biconditional).

    This is the full characterization: Safety IS V-independence. -/
theorem safety_iff_V_independence
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    Safe d ↔ V_independent d := by
  unfold Safe
  exact Iff.rfl

/-- Sensitivity failure implies E-coverage failure.

    If a deposit is Insensitive (wouldn't notice falsehood),
    then it lacks E-coverage (error model has gaps).

    This grounds `sensitivity_E_link` from Theorems.lean. -/
theorem sensitivity_E_link
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    Insensitive d → ¬E_covers_counterfactual d := by
  intro h_insens
  exact (E_has_gap_iff_not_covers d).mp h_insens

/-- E-coverage implies Sensitivity.

    If a deposit has E-coverage (error model covers counterfactual),
    then it is Sensitive (would notice falsehood).

    This is the converse: E-coverage is SUFFICIENT for Sensitivity. -/
theorem E_coverage_implies_sensitivity
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    E_covers_counterfactual d → Sensitive d := by
  intro h
  exact h

/-- Sensitivity ↔ E-coverage (biconditional).

    This is the full characterization: Sensitivity IS E-coverage. -/
theorem sensitivity_iff_E_coverage
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    Sensitive d ↔ E_covers_counterfactual d := by
  unfold Sensitive
  exact Iff.rfl

/-! ## Connection to Adversarial Model

The Safety/Sensitivity predicates connect to AdversarialBase.lean's
attack model. V-spoofing attacks violate Safety; E-field poisoning
violates Sensitivity. -/

/-- Header preservation provides both Safety and Sensitivity.

    If a deposit has preserved headers, it is both Safe and Sensitive.
    This is the operationalization of why headers matter for modal properties. -/
theorem headers_provide_modal_properties
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (hpres : header_preserved d) :
    Safe d ∧ Sensitive d := by
  constructor
  · exact hpres
  · exact hpres

/-- Stripped headers lose both Safety and Sensitivity.

    If header is not preserved, the deposit is both Unsafe and Insensitive.
    Header stripping breaks modal properties: the V-field (provenance)
    and E-field (error model) are no longer accessible. -/
theorem stripped_headers_lose_modal_properties
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_stripped : ¬header_preserved d) :
    Unsafe d ∧ Insensitive d := by
  constructor
  · exact h_stripped
  · exact h_stripped

/-- Safety and Sensitivity coincide when header_preserved is the foundation.

    This shows that both modal conditions reduce to the same structural
    property: header preservation. This is a feature, not a bug—it shows
    that S/E/V factorization captures BOTH modal conditions uniformly. -/
theorem safety_sensitivity_coincide
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    Safe d ↔ Sensitive d := by
  unfold Safe Sensitive V_independent E_covers_counterfactual
  exact Iff.rfl

/-- The unified modal condition: header preservation captures both.

    This theorem shows that `header_preserved` is THE operational
    condition for modal robustness. Both Safety and Sensitivity
    reduce to it. -/
theorem modal_robustness_is_header_preservation
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    (Safe d ∧ Sensitive d) ↔ header_preserved d := by
  constructor
  · intro ⟨h_safe, _⟩
    exact h_safe
  · intro h
    exact ⟨h, h⟩

/-! ## Summary: Modal Conditions Are S/E/V Conditions

The key results of this section:

1. `safety_iff_V_independence`: Safety ↔ V-independence ↔ header_preserved
   - Safe deposits have genuine provenance (header preserved)
   - Unsafe deposits have stripped headers (V spoofable)

2. `sensitivity_iff_E_coverage`: Sensitivity ↔ E-coverage ↔ header_preserved
   - Sensitive deposits have accessible error models (header preserved)
   - Insensitive deposits have stripped headers (E inaccessible)

3. `headers_provide_modal_properties`: header_preserved → Safe ∧ Sensitive
   - This is WHY headers matter: they preserve modal structure

4. `stripped_headers_lose_modal_properties`: ¬header_preserved → Unsafe ∧ Insensitive
   - This is WHY stripping is an attack: it breaks modal properties

5. `safety_sensitivity_coincide`: Safe ↔ Sensitive
   - Both modal conditions reduce to header preservation

These results establish that Safety/Sensitivity conditions are captured
by S/E/V field structure. The routing works as follows:
- `safety_V_link` is a theorem (not an axiom)
- `sensitivity_E_link` is a theorem (not an axiom)
- Both modal conditions reduce to header preservation

The modal epistemology literature's Safety/Sensitivity conditions are
subsumed by S/E/V field structure.
-/

end EpArch.ModalLinks
