/-
EpArch.Header — Header and Deposit

Defines the validation header (S, E, V, τ, acl, redeemability) and the
Deposit record that packages a claim with its full metadata. Also contains
the Observational Completeness theorems: two deposits agreeing on all named
fields are provably identical, leaving no hidden degrees of freedom.

The S/E/V factorization enables field-localized diagnosis: knowing
WHICH of the three independent fields failed tells you whether the problem
is a standards failure (S), a detection miss (E), or a provenance weakness (V).
-/

import EpArch.Basic

namespace EpArch

universe u

/-! ## Redeemability Reference -/

/-- RedeemabilityRef: a pointer to a constraint surface.
    Grounds the deposit in an external reality check that is
    independent of consensus within the bubble. -/
abbrev RedeemabilityRef := ConstraintSurface


/-! ## Header Structure -/

/-- A structured validation header (S, E, V).

    - S: Standard / threshold / protocol class
         "What counts as passing?"

    - E: Error model / threat model / uncertainty class
         "What failure modes were considered?"

    - V: Provenance / source chain / independence class
         "Where did this come from? Are sources independent?"

    This factorization is what enables field-localized diagnosis and repair. -/
structure Header (Standard ErrorModel Provenance : Type u) where
  S : Standard
  E : ErrorModel
  V : Provenance
  τ : Time            -- currentness marker / TTL-style
  acl : ACL
  redeem : RedeemabilityRef


/-! ## Deposit Record -/

/-- Deposit record — the fundamental unit of Bank state.

    A deposit is not just a claim P but P together with all the
    metadata that makes it diagnosable, challengeable, and repairable:
    - P: the claim itself
    - h: the validation header (S, E, V, τ, acl, redeemability)
    - bubble: the scoped authorization zone it lives in
    - status: current lifecycle stage (Candidate → Deposited → Quarantined → Revoked) -/
structure Deposit (PropLike Standard ErrorModel Provenance : Type u) where
  P      : PropLike
  h      : Header Standard ErrorModel Provenance
  bubble : Bubble
  status : DepositStatus


/-! ## Challenge Record -/

/-- A structured challenge carries a suspected field.

    This is the key to field-localized repair:
    "The deposit failed — but WHERE did it fail?"

    A well-formed challenge identifies:
    - Which claim P is being challenged
    - What the reason/evidence is
    - Which field is suspected to be broken -/
structure Challenge (PropLike Reason Evidence : Type u) where
  P : PropLike
  reason : Reason
  evidence : Evidence
  suspected : Field


/-! ## Header Predicates -/

/-- Predicate: deposit has its header preserved (not stripped in transmission). -/
opaque header_preserved {P S E V : Type u} : Deposit P S E V → Prop

/-- Predicate: deposit has had its header stripped (bare claim only).

    Definitional: stripped = not preserved. This makes mutual exclusion
    a theorem rather than an axiom. -/
def header_stripped {P S E V : Type u} (d : Deposit P S E V) : Prop :=
  ¬header_preserved d

/-- Header preservation and stripping are mutually exclusive.

    Follows directly from the definition `header_stripped := ¬header_preserved`;
    no separate axiom is needed. -/
theorem header_exclusive {P S E V : Type u} (d : Deposit P S E V) :
    ¬(header_preserved d ∧ header_stripped d) := by
  intro ⟨h_pres, h_strip⟩
  exact h_strip h_pres


/-! ========================================================================
    OBSERVATIONAL COMPLETENESS — Type-definitional closure

    Two deposits agreeing on all named fields are identical. This is a
    metatheoretic closure result: any proposed new deposit field either
    (1) affects observable behavior — but then it must be determined by
        the existing named fields, making it a refinement (compatible), or
    (2) does not affect any observable behavior — making it operationally
        inert and unnecessary.

    No incompatible extension can arise from a missing field. The only
    productive attack surface is the constraint enumeration: finding a
    new world or agent constraint that forces a primitive none of the
    existing fields can express.
    ======================================================================== -/

/-- HEADER EXTENSIONALITY: two headers agreeing on all six fields are equal.

    Header has exactly six fields: S, E, V, τ, acl, redeem. The type
    definition is the completeness proof — there is no room for a hidden
    seventh field. -/
theorem header_ext {S E V : Type u}
    (h₁ h₂ : Header S E V)
    (hS : h₁.S = h₂.S)
    (hE : h₁.E = h₂.E)
    (hV : h₁.V = h₂.V)
    (hτ : h₁.τ = h₂.τ)
    (hacl : h₁.acl = h₂.acl)
    (hredeem : h₁.redeem = h₂.redeem) :
    h₁ = h₂ := by
  cases h₁; cases h₂
  subst hS; subst hE; subst hV; subst hτ; subst hacl
  simp_all

/-- DEPOSIT EXTENSIONALITY: two deposits agreeing on all four fields are equal.

    Combined with header extensionality, two deposits agreeing on P, S, E, V,
    τ, acl, redeem, bubble, and status are identical. No unnamed fields exist. -/
theorem deposit_ext {PL S E V : Type u}
    (d₁ d₂ : Deposit PL S E V)
    (hP : d₁.P = d₂.P)
    (hh : d₁.h = d₂.h)
    (hbubble : d₁.bubble = d₂.bubble)
    (hstatus : d₁.status = d₂.status) :
    d₁ = d₂ := by
  cases d₁; cases d₂
  subst hP; subst hh; subst hbubble; subst hstatus
  rfl

/-- OBSERVATIONAL COMPLETENESS: every predicate over deposits is fully
    determined by the nine named fields.

    If two deposits agree on all fields, any predicate holding of one holds
    of the other. Follows from deposit extensionality by substitution. -/
theorem observational_completeness {PL S E V : Type u}
    (d₁ d₂ : Deposit PL S E V)
    (hP : d₁.P = d₂.P)
    (hh : d₁.h = d₂.h)
    (hbubble : d₁.bubble = d₂.bubble)
    (hstatus : d₁.status = d₂.status)
    (Pred : Deposit PL S E V → Prop)
    (h_pred : Pred d₁) :
    Pred d₂ := by
  have h_eq := deposit_ext d₁ d₂ hP hh hbubble hstatus
  rw [← h_eq]
  exact h_pred

/-- FULL FIELD OBSERVATIONAL COMPLETENESS: same as `observational_completeness`
    but takes all nine primitive fields individually rather than a pre-composed
    header. Two deposits agreeing on P, S, E, V, τ, acl, redeem, bubble, and
    status are identical and indistinguishable by any predicate. -/
theorem observational_completeness_full {PL S E V : Type u}
    (d₁ d₂ : Deposit PL S E V)
    (hP : d₁.P = d₂.P)
    (hS : d₁.h.S = d₂.h.S)
    (hE : d₁.h.E = d₂.h.E)
    (hV : d₁.h.V = d₂.h.V)
    (hτ : d₁.h.τ = d₂.h.τ)
    (hacl : d₁.h.acl = d₂.h.acl)
    (hredeem : d₁.h.redeem = d₂.h.redeem)
    (hbubble : d₁.bubble = d₂.bubble)
    (hstatus : d₁.status = d₂.status)
    (Pred : Deposit PL S E V → Prop)
    (h_pred : Pred d₁) :
    Pred d₂ := by
  have hh := header_ext d₁.h d₂.h hS hE hV hτ hacl hredeem
  exact observational_completeness d₁ d₂ hP hh hbubble hstatus Pred h_pred

end EpArch
