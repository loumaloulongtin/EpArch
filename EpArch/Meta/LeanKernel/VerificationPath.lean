/-
EpArch.Meta.LeanKernel.VerificationPath — Lean-Kernel C4 Non-Vacuity Witness

Closes the non-vacuity gap in Commitment 4b: `redeemable d` is proved false for
intra-bubble deposits in Commitments.lean, but `∃ d, redeemable d` was never
exhibited. This file supplies the witness via a single named axiom.

## Design

The three opaque predicates (`path_route_exists`, `contact_was_made`,
`verdict_discriminates`) are NOT rewritten. They remain generic hooks in
Commitments.lean, open to instantiation for any domain (medical, legal, empirical
science, etc.). This file is a *downstream witness layer only* — it does not
mutate the C4 surface.

The Lean kernel constitutes a VerificationPath instantiation for any deposit
whose claim is a proved Prop:
- `path_route_exists d d.h.redeem` — a proof term exists (Curry-Howard route).
- `contact_was_made d d.h.redeem` — elaboration ran; the kernel was invoked.
- `verdict_discriminates d d.h.redeem` — the kernel is a non-trivial oracle;
  it rejects `h : T` when T is false (no sorry). This is kernel soundness —
  the assumption every sorry-free Lean proof already relies on implicitly.
  This formalization just has to name it explicitly. Lean4Lean (digama0) is
  an active project that offers a hopeful path toward a formal proof of this,
  but remains incomplete.

## Axiom accounting

| | Before | After |
|---|---|---|
| `#print axioms` entries for C4 theorems | 3 (opaques, unlabeled) | 1 (named, packaged) |
| `∃ d, redeemable d` provable | No | Yes |
| Commitments.lean changed | — | No — untouched |

## Exported items

- `lean_kernel_verification_path` — the single packaged axiom
- `lean_kernel_path_is_redeemable` — redeemability from the axiom
- `redeemable_deposits_exist` — non-vacuity corollary: ∃ d, redeemable d
-/

import EpArch.Commitments

namespace EpArch.Meta.LeanKernel.VerificationPath

open EpArch

/-! ========================================================================
    THE LEAN-KERNEL AXIOM
    ======================================================================== -/

/-- Lean-kernel VerificationPath witness.

    For any deposit whose claim is a proved Prop, the Lean kernel constitutes
    a VerificationPath against the deposit's own constraint surface: a proof
    term exists (route), elaboration ran (contact), and the kernel discriminated
    the verdict (it does not accept all terms).

    This packages all three C4 evidence obligations for the Lean domain into one
    named trust boundary. The three opaque predicates in Commitments.lean remain
    unchanged — this axiom is a downstream instantiation, not a redefinition.

    **Universe note:** `Prop : Type 0 = Type`, so `Standard`, `ErrorModel`, and
    `Provenance` are all fixed to `Type` (universe 0) to match the `PropLike = Prop`
    instantiation of `Deposit`.

    **Trust boundary:** kernel soundness (`verdict_discriminates`) is the assumption
    underlying every sorry-free Lean proof — this formalization is unusual only in
    having to state it explicitly. Lean4Lean (digama0) is an active project that
    aims to prove Lean's kernel sound within Lean itself, offering a hopeful path
    toward discharging this axiom. That work is incomplete, and discharging this
    axiom would additionally require bridging `verdict_discriminates` (opaque in
    `Commitments.lean`) to whatever Lean4Lean establishes.

    **Axiom footprint:** 1 named axiom, replacing 3 unlabeled opaque instances
    in `#print axioms` output for any theorem that uses `redeemable`. -/
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
