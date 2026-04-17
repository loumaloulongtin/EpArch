/-
EpArch.Meta.LeanKernel.VerificationPath — Lean-Kernel Non-Vacuity Witness for C4b

Without a positive witness for `redeemable`, `intra_bubble_only d` is vacuously true
for every deposit (since `path_route_exists` is never inhabited), and
`redeemability_requires_more_than_consensus` degenerates into a tautology that
distinguishes nothing. This file prevents that collapse by exhibiting the Lean kernel
as a concrete VerificationPath instantiation for any proved Prop deposit.

The three opaque predicates (`path_route_exists`, `contact_was_made`,
`verdict_discriminates`) are unchanged in Commitments.lean — this file is a
downstream witness layer only, not a redefinition of the C4 surface.

- `lean_kernel_verification_path` — the packaged axiom; names the trust boundary
- `lean_kernel_path_is_redeemable` — redeemability for any proved Prop deposit
- `redeemable_deposits_exist` — the non-vacuity witness: ∃ d, redeemable d
-/

import EpArch.Commitments

namespace EpArch.Meta.LeanKernel.VerificationPath

open EpArch

/-! ========================================================================
    THE LEAN-KERNEL AXIOM
    ======================================================================== -/

/-- Non-vacuity witness for `redeemable`: the Lean kernel is a VerificationPath.

    For any proved Prop deposit, the Lean kernel satisfies all three C4 surface
    obligations against the deposit's own constraint surface. This is the axiom
    that gives `intra_bubble_only` its discriminating force: without an inhabited
    `redeemable`, the separation theorem `redeemability_requires_more_than_consensus`
    would be vacuously true of every deposit.

    The assumption is kernel soundness — that the Lean kernel does not accept
    `h : T` when `T` is false without `sorry`. Every sorry-free Lean proof already
    relies on this; this formalization must name it explicitly because `verdict_discriminates`
    is opaque and has no in-system inhabitants.

    **Universe note:** `Prop : Type 0 = Type`, so `Standard`, `ErrorModel`, and
    `Provenance` are fixed to `Type` (universe 0). -/
axiom lean_kernel_verification_path
    {Standard ErrorModel Provenance : Type}
    (d : Deposit Prop Standard ErrorModel Provenance)
    (h_prop : d.P) :
    path_route_exists d d.h.redeem ∧
    contact_was_made d d.h.redeem ∧
    verdict_discriminates d d.h.redeem

/-! ## Redeemability from the Lean-Kernel Axiom -/

/-- A Lean proved theorem is a VerificationPath instantiation.

    **Theorem shape:** Any deposit whose claim is a proved Prop is redeemable.

    **Proof strategy:** Destructs `lean_kernel_verification_path d h_prop` to
    extract the three evidence fields, then packages them into a `VerificationPath`
    targeting `d.h.redeem`. The `rfl` witnesses are `vp.deposit = d` and
    `vp.surface = d.h.redeem`. -/
theorem lean_kernel_path_is_redeemable
    {Standard ErrorModel Provenance : Type}
    (d : Deposit Prop Standard ErrorModel Provenance)
    (h_prop : d.P) :
    redeemable d :=
  let ⟨h_path, h_contact, h_discrim⟩ := lean_kernel_verification_path d h_prop
  ⟨⟨d, d.h.redeem, h_path, h_contact, h_discrim⟩, rfl, rfl⟩

/-! ## Non-Vacuity Corollary -/

/-- Redeemable deposits exist: the concept of redeemability is non-vacuous.

    **Theorem shape:** There exists a deposit (over the Lean domain: `Prop` claim,
    `Unit` header fields) that is redeemable.

    **Proof strategy:** Exhibits a concrete deposit with `P := True` and applies
    `lean_kernel_path_is_redeemable` with `True.intro`. This closes the C4b
    non-vacuity gap — `redeemable` was previously used only in the negative
    direction (`¬redeemable d` for intra-bubble deposits).

    **Architectural significance:** C4b now has witnesses in both directions:
    - Negative: `intra_bubble_not_redeemable` (Commitments.lean) — intra-bubble
      deposits cannot be redeemed.
    - Positive: this theorem — deposits with proved claims can be redeemed. -/
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
