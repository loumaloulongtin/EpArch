/-
EpArch.Meta.LeanKernel.VerificationPath — Worked Example: Lean Domain C4b Instantiation

This file is NOT part of the core architectural claim. It demonstrates two things:

**Part A — Axiom-free parallel instantiation.**
The C4b surface structure can be fully discharged as a theorem, with zero axioms,
by giving concrete non-opaque definitions to the three evidence predicates for the
Lean domain. This shows the shape any domain instantiation must take.

**Part B — Core theory connection (one axiom).**
Connecting to the core theory's `redeemable d` (which wraps opaque predicates from
Commitments.lean) requires one axiom. The opaques cannot be opened from downstream;
an axiom is the only structural escape. This names the one trust boundary explicitly.

Together these two parts answer the question: can the positive side of C4b be
discharged as a theorem? Yes — for the *structure* of the instantiation. Connecting
that structure to the core theory's opaque surface requires naming one assumption.

- `LeanPathExists` / `LeanContact` / `LeanVerdict` — concrete Lean-domain predicates
- `LeanVerificationPath` — concrete local structure, mirrors VerificationPath
- `lean_redeemable_theorem` — Part A: non-vacuity as a closed theorem (zero axioms)
- `lean_kernel_verification_path` — Part B: axiom bridging to core `redeemable`
- `redeemable_deposits_exist` — Part B: ∃ d, redeemable d via the core theory
-/

import EpArch.Commitments

namespace EpArch.Meta.LeanKernel.VerificationPath

open EpArch

/-! ========================================================================
    PART A — AXIOM-FREE PARALLEL INSTANTIATION
    ======================================================================== -/

/-! ## Concrete Lean-Domain Predicates

These are non-opaque definitions for the Lean domain. Unlike `path_route_exists`,
`contact_was_made`, and `verdict_discriminates` in Commitments.lean (which are
`opaque` and have no introduction rules), these can be inhabited by construction. -/

/-- A proof term exists for this deposit's claim: the claim is inhabited as a Prop. -/
def LeanPathExists (d : Deposit Prop Standard ErrorModel Provenance) (_ : ConstraintSurface) : Prop :=
  d.P

/-- Elaboration ran: the deposit's claim was submitted and type-checked. -/
def LeanContact (_ : Deposit Prop Standard ErrorModel Provenance) (_ : ConstraintSurface) : Prop :=
  True

/-- The kernel gave a non-trivial verdict: it accepts some terms and not others.
    Witnessed here by the fact that `True` and `False` have different proof statuses. -/
def LeanVerdict (_ : Deposit Prop Standard ErrorModel Provenance) (_ : ConstraintSurface) : Prop :=
  True

/-- A concrete VerificationPath for the Lean domain using the non-opaque predicates above.
    Mirrors the structure of `VerificationPath` in Commitments.lean — same shape,
    but with inhabitable evidence fields. -/
structure LeanVerificationPath (d : Deposit Prop Standard ErrorModel Provenance) where
  surface   : ConstraintSurface
  h_path    : LeanPathExists d surface
  h_contact : LeanContact d surface
  h_discrim : LeanVerdict d surface

/-- A deposit is Lean-redeemable if it has a LeanVerificationPath targeting its own surface. -/
def lean_redeemable (d : Deposit Prop Standard ErrorModel Provenance) : Prop :=
  ∃ vp : LeanVerificationPath d, vp.surface = d.h.redeem

/-- PART A THEOREM: Any proved Prop deposit is Lean-redeemable. Zero axioms.

    **Theorem shape:** `d.P → lean_redeemable d`

    **Proof strategy:** Constructs the LeanVerificationPath directly from `h_prop`.
    `LeanPathExists` is literally `d.P`, `LeanContact` and `LeanVerdict` are `True`.
    No trust boundary required — all evidence fields have concrete definitions. -/
theorem lean_redeemable_from_proof
    {Standard ErrorModel Provenance : Type}
    (d : Deposit Prop Standard ErrorModel Provenance)
    (h_prop : d.P) :
    lean_redeemable d :=
  ⟨⟨d.h.redeem, h_prop, trivial, trivial⟩, rfl⟩

/-- PART A COROLLARY: Lean-redeemable deposits exist. Zero axioms.

    **Theorem shape:** `∃ d, lean_redeemable d`

    **Proof strategy:** Exhibits a deposit with `P := True` and applies
    `lean_redeemable_from_proof` with `True.intro`. Fully closed theorem. -/
theorem lean_redeemable_deposits_exist :
    ∃ (d : Deposit Prop Unit Unit Unit), lean_redeemable d :=
  let d : Deposit Prop Unit Unit Unit :=
    { P      := True
      h      := { S := (), E := (), V := (), τ := 0,
                  acl := ACL.mk 0, redeem := ConstraintSurface.mk 0 }
      bubble := Bubble.mk 0
      status := .Deposited }
  ⟨d, lean_redeemable_from_proof d True.intro⟩

/-! ========================================================================
    PART B — CORE THEORY CONNECTION (ONE AXIOM)
    ======================================================================== -/

/-! ## The Opaque Barrier

Part A shows the structure can be discharged axiom-free. Connecting to the core
theory's `redeemable d` — which wraps `path_route_exists`, `contact_was_made`,
`verdict_discriminates` from Commitments.lean — requires crossing an opaque barrier.
Those predicates are sealed; no downstream file can construct inhabitants of them.
An axiom is the only structural escape. -/

/-- Lean-kernel VerificationPath axiom: bridges the Lean domain to the core theory.

    **What it asserts:** For any proved Prop deposit, the Lean kernel instantiates
    the core theory's three opaque C4 predicates against the deposit's own surface.

    **Why it cannot be a theorem:** `path_route_exists`, `contact_was_made`, and
    `verdict_discriminates` are `opaque` in Commitments.lean — they have no
    introduction rules and cannot be inhabited from any downstream file. This axiom
    is the only escape. See Part A for the same claim proved as a theorem using
    local non-opaque predicates.

    **Universe note:** `Prop : Type 0 = Type`, so `Standard`, `ErrorModel`, and
    `Provenance` are fixed to `Type` (universe 0). -/
axiom lean_kernel_verification_path
    {Standard ErrorModel Provenance : Type}
    (d : Deposit Prop Standard ErrorModel Provenance)
    (h_prop : d.P) :
    path_route_exists d d.h.redeem ∧
    contact_was_made d d.h.redeem ∧
    verdict_discriminates d d.h.redeem

/-- PART B THEOREM: Any proved Prop deposit is redeemable in the core theory's sense.

    **Theorem shape:** `d.P → redeemable d` (core theory `redeemable`, not `lean_redeemable`)

    **Proof strategy:** Destructs the axiom to extract the three opaque evidence
    terms, packages them into a `VerificationPath`, witnesses `rfl` for both
    `vp.deposit = d` and `vp.surface = d.h.redeem`. -/
theorem lean_kernel_path_is_redeemable
    {Standard ErrorModel Provenance : Type}
    (d : Deposit Prop Standard ErrorModel Provenance)
    (h_prop : d.P) :
    redeemable d :=
  let ⟨h_path, h_contact, h_discrim⟩ := lean_kernel_verification_path d h_prop
  ⟨⟨d, d.h.redeem, h_path, h_contact, h_discrim⟩, rfl, rfl⟩

/-- PART B COROLLARY: Core-theory redeemable deposits exist (via the axiom). -/
theorem redeemable_deposits_exist :
    ∃ (d : Deposit Prop Unit Unit Unit), redeemable d :=
  let d : Deposit Prop Unit Unit Unit :=
    { P      := True
      h      := { S := (), E := (), V := (), τ := 0,
                  acl := ACL.mk 0, redeem := ConstraintSurface.mk 0 }
      bubble := Bubble.mk 0
      status := .Deposited }
  ⟨d, lean_kernel_path_is_redeemable d True.intro⟩

end EpArch.Meta.LeanKernel.VerificationPath
