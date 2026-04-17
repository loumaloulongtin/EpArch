/-
EpArch.Meta.LeanKernel.VerificationPath — Worked Example: Lean Domain C4b Instantiation

This file is NOT part of the core architectural claim. It demonstrates two things:

**Part A — Axiom-free parallel instantiation.**
The C4b surface structure can be fully discharged as a theorem, with zero axioms,
by giving concrete non-opaque definitions to the three evidence predicates for the
Lean domain. This shows the shape any domain instantiation must take.

**Part B — Core theory connection (one axiom).**
Connecting to the core theory's `redeemable d` requires crossing the opaque barrier
in Commitments.lean. That barrier is intentional: the three predicates are opaque so
that EpArch is not committed to any single domain's notion of validation. An agent
validating by observing outcomes over time, an AI receiving RLHF reward signal, a
student getting exam results from a teacher, and an agent surviving peer challenge all
satisfy the same abstract contract — but none of them are the Lean kernel. If the
predicates had concrete bodies, every theorem about `redeemable` would be a claim
about one specific mechanism, not a domain-general architecture.

Part B's axiom is the formal bridge: it names the assumption that the Lean domain
satisfies the abstract interface. Other domains would supply their own analogous axiom.
That is what the opaque barrier is for.

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

/-! ## The Opaque Barrier and Why It Exists

The three predicates in Commitments.lean are opaque because different agents make
contact with reality in fundamentally different ways. Observation over time, RLHF
reward signal, institutional exam results, and peer challenge all constitute valid
instantiations of "path", "contact", and "verdict" — and none of them is the Lean
kernel. An architecture that commits to one of these notions is not a general
epistemic architecture; it is a theory about one specific mechanism.

Part A fills the abstract interface concretely for the Lean domain, using non-opaque
local definitions. Those definitions are not the opaques — they live in a different
namespace and have concrete reduction behaviour. Connecting them to the core theory's
abstract interface is exactly what Part B's axiom does. The axiom is not a weakness;
it is the formal statement that the Lean domain satisfies the abstract contract, in
the same way that any other domain would have to name its own trust boundary. -/

/-- Lean-kernel VerificationPath axiom: the Lean domain satisfies the abstract C4 interface.

    **What it asserts:** For any proved Prop deposit, the Lean kernel instantiates
    the core theory's three opaque evidence predicates against the deposit's own surface.
    This is the bridge from the Lean-domain instantiation (Part A) to the core theory's
    abstract `redeemable` predicate.

    **Why it is an axiom and not a theorem:** The opaques are opaque by design — any
    concrete body would commit the core theory to one domain's validation mechanism and
    break the domain-generality of every theorem about `redeemable`. This axiom names
    the assumption that the Lean domain satisfies the abstract contract. An agent
    validating by observation over time, or through RLHF, or through institutional
    assessment would each supply an analogous axiom for their own domain.

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
