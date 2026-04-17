/-
EpArch.Meta.LeanKernel.VerificationPath — Worked Example: Lean Domain C4b Instantiation

This file is NOT part of the core architectural claim. It demonstrates two things:

**Part A — Axiom-free parallel instantiation.**
The C4b surface structure can be fully discharged as a theorem, with zero axioms,
by giving concrete non-opaque definitions to the three evidence predicates for the
Lean domain. This shows the shape any domain instantiation must take.

**Part B — Core theory connection (one axiom).**
Connecting to the core theory's `redeemable d` requires crossing the opaque barrier
in Commitments.lean. That barrier is intentional: `vindication_evidence` is opaque
because its realization varies across domains, across subsystems within a domain,
and even across deposits within the same system. A single concrete body would not
just commit the architecture to one domain — it would assert a uniform implementation
of route, contact, and verdict for every deposit, which is false in any realistic
system. Even within Lean alone, fresh elaboration, cache reuse, and proof-object
replay are genuinely different realizations of the same interface for different deposits.

Part B's axiom is the formal bridge: it names the assumption that Lean elaboration
(not Lean caching, not proof-object replay — this specific mechanism) satisfies the
abstract interface for this class of deposits. Other domains and other mechanisms
within a domain would each supply their own analogous statement.

- `LeanPathExists` / `LeanContact` / `LeanVerdict` — concrete Lean-domain predicates
- `LeanVerificationPath` — concrete local structure, mirrors VerificationPath
- `lean_redeemable_deposits_exist` — Part A: non-vacuity as a closed theorem (zero axioms)
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

Non-opaque definitions inhabitable by construction — unlike `vindication_evidence`
(the sealed opaque in Commitments.lean) that each domain must satisfy from the outside. -/

/-- A proof term exists for this deposit's claim: the claim is inhabited as a Prop. -/
def LeanPathExists (d : Deposit Prop Standard ErrorModel Provenance) (_ : ConstraintSurface) : Prop :=
  d.P

/-- Elaboration ran: the deposit's claim was submitted and type-checked. -/
def LeanContact (_ : Deposit Prop Standard ErrorModel Provenance) (_ : ConstraintSurface) : Prop :=
  True

/-- The kernel gave a non-trivial verdict: it accepts some terms and not others. -/
def LeanVerdict (_ : Deposit Prop Standard ErrorModel Provenance) (_ : ConstraintSurface) : Prop :=
  True

/-- Lean-domain analogue of `VerificationPath`: same shape, inhabitable evidence fields. -/
structure LeanVerificationPath (d : Deposit Prop Standard ErrorModel Provenance) where
  surface   : ConstraintSurface
  h_path    : LeanPathExists d surface
  h_contact : LeanContact d surface
  h_discrim : LeanVerdict d surface

/-- A deposit is Lean-redeemable if it has a LeanVerificationPath targeting its own surface. -/
def lean_redeemable (d : Deposit Prop Standard ErrorModel Provenance) : Prop :=
  ∃ vp : LeanVerificationPath d, vp.surface = d.h.redeem

/-- Any proved Prop deposit is Lean-redeemable.

    **Theorem shape:** `d.P → lean_redeemable d`

    **Proof strategy:** Constructs `LeanVerificationPath` directly from `h_prop`;
    `LeanPathExists` unfolds to `d.P`, `LeanContact` and `LeanVerdict` are `True`. -/
theorem lean_redeemable_from_proof
    {Standard ErrorModel Provenance : Type}
    (d : Deposit Prop Standard ErrorModel Provenance)
    (h_prop : d.P) :
    lean_redeemable d :=
  ⟨⟨d.h.redeem, h_prop, trivial, trivial⟩, rfl⟩

/-- Lean-redeemable deposits exist. -/
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

/-! ## Connecting to the Core Theory

Part A filled the abstract C4 interface with concrete Lean-domain definitions.
Part B's axiom bridges those definitions to the core theory's sealed opaque (`vindication_evidence`) —
the step that cannot be a theorem, for the reasons given in the file header. -/

/-- The Lean domain satisfies the abstract C4 interface.

    **What it asserts:** For any proved Prop deposit, the Lean kernel satisfies
    all three vindication-role predicates against the deposit's own constraint surface
    (via the opaque `vindication_evidence` in Commitments.lean).

    **Why an axiom:** The opaque `vindication_evidence` in Commitments.lean is sealed
    by design; any concrete body would fix one domain's validation mechanism as the
    architecture's own. This axiom names the Lean domain's trust boundary. Other domains
    supply their own.

    **Universe note:** `Prop : Type 0 = Type`, so `Standard`, `ErrorModel`, and
    `Provenance` are fixed to `Type` (universe 0). -/
axiom lean_kernel_verification_path
    {Standard ErrorModel Provenance : Type}
    (d : Deposit Prop Standard ErrorModel Provenance)
    (h_prop : d.P) :
    path_route_exists d d.h.redeem ∧
    contact_was_made d d.h.redeem ∧
    verdict_discriminates d d.h.redeem

/-- Any proved Prop deposit is redeemable in the core theory's sense.

    **Theorem shape:** `d.P → redeemable d` (core `redeemable`, not `lean_redeemable`)

    **Proof strategy:** Destructs the axiom, packages the three evidence terms
    into a `VerificationPath`, witnesses `vp.deposit = d` and `vp.surface = d.h.redeem`
    by `rfl`. -/
theorem lean_kernel_path_is_redeemable
    {Standard ErrorModel Provenance : Type}
    (d : Deposit Prop Standard ErrorModel Provenance)
    (h_prop : d.P) :
    redeemable d :=
  let ⟨h_path, h_contact, h_discrim⟩ := lean_kernel_verification_path d h_prop
  ⟨⟨d, d.h.redeem, h_path, h_contact, h_discrim⟩, rfl, rfl⟩

/-- Core-theory redeemable deposits exist (via the axiom).
    Same deposit witness as `lean_redeemable_deposits_exist` — the bridge changes
    which redeemability predicate is targeted, not the example. -/
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
