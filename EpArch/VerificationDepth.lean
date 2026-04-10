/-
EpArch/VerificationDepth.lean — Kernel-grounded verification depth

## What this file shows

`W_bounded_verification` is not an empirical assumption about the world.
It follows from the structural properties of the verification relation
itself, as witnessed by the `DepthClaim` proposition family.

`DepthClaim n` is a depth-indexed proposition family — one `step` constructor
per level.  `bounded_verify`, the budget-d checker defined here, traverses
exactly n recursive steps to decide a claim of depth n.  A budget-d verifier
rejects `DepthClaim (d+1)`, which is true — making any fixed budget incomplete.

## Architecture connection

1. The bounded verify story (§2 of Minimality.lean): ABSTRACT.
   "Some claims exceed the budget" is a structural scenario.

2. This file: CONSTRUCTIVE.
   The `DepthClaim` family witnesses that such claims exist within the
   kernel itself, not just as a hypothetical scenario.  `BoundedVerification`
   is not merely well-typed — it has a canonical kernel inhabitant for every
   budget d.

3. `DepthWorldCtx`: a `WorldCtx` instantiation where `VerifyWithin` is
   grounded in structural depth.  Within this context, `W_bounded_verification`
   is provable by construction — no world assumption needed beyond faithfully
   modelling the depth relation.

## The endorsement cycle

An endorsement of `DepthClaim n` — a claim asserting that `DepthClaim n`
has been validated — has structural depth n+1 (it wraps the original).
Budget-n verifiers cannot check their own endorsements:
`bounded_verify n (n+1) = false`.  This is the kernel-level shadow of the
forcing argument for trust bridges and redeemability.
-/

import EpArch.WorldCtx

namespace EpArch

/-! ## §2c. Kernel Verification Depth

The DepthClaim family provides a concrete witness that some true propositions
have verification cost that cannot be reduced below their structural depth.
The forcing argument of §2 (bounded audit → trust bridges) applies to this
family without any coverage assumption — the cost is intrinsic to the type. -/

/-- A proposition family where `DepthClaim n` has a unique canonical proof
    of structural depth n: one `step` constructor per level.
    The kernel must traverse all n constructors to type-check a proof term. -/
inductive DepthClaim : Nat → Prop where
  | base : DepthClaim 0
  | step : DepthClaim n → DepthClaim (n + 1)

/-- Every `DepthClaim n` is provable.  The canonical proof has n constructors. -/
theorem depth_claim_provable (n : Nat) : DepthClaim n := by
  induction n with
  | zero      => exact .base
  | succ n ih => exact .step ih

/-- A budget-d decision procedure: accepts "claim of depth n" iff n ≤ d.
    Recurses on both depth and budget; `bounded_verify_incomplete` shows
    every fixed budget misses some true claim in the family. -/
def bounded_verify : Nat → Nat → Bool
  | _,     0     => true
  | 0,     _ + 1 => false
  | d + 1, n + 1 => bounded_verify d n

/-- A budget-d verifier correctly accepts any claim with depth ≤ d. -/
theorem bounded_verify_sound {d n : Nat} (h : n ≤ d) :
    bounded_verify d n = true := by
  induction n generalizing d with
  | zero      => cases d <;> simp [bounded_verify]
  | succ n ih =>
    cases d with
    | zero      => exact absurd h (Nat.not_le_of_gt (Nat.succ_pos n))
    | succ d    => simp [bounded_verify]; exact ih (Nat.le_of_succ_le_succ h)

/-- A budget-d verifier rejects the true claim `DepthClaim (d+1)`. -/
theorem bounded_verify_incomplete (d : Nat) :
    bounded_verify d (d + 1) = false := by
  induction d with
  | zero      => simp [bounded_verify]
  | succ d ih => simp [bounded_verify]; exact ih

/-- For any fixed budget d, there is a true claim that the budget-d verifier
    rejects.  No finite budget covers the full claim space. -/
theorem no_budget_is_sufficient (d : Nat) :
    ∃ n : Nat, DepthClaim n ∧ bounded_verify d n = false :=
  ⟨d + 1, depth_claim_provable (d + 1), bounded_verify_incomplete d⟩

/-! ### Connection to BoundedVerification

`BoundedVerification` in Minimality.lean is the structural scenario abstraction
that sits above this layer.  The `DepthClaim` family witnesses it: for any
budget d, `depth_bounded_verification d` supplies the required instance with
`Claim := Nat`, `verify_cost := id`, `budget := d`, `hard_claim := d+1`.
`depth_claim_provable` confirms `DepthClaim (d+1)` is genuinely true, so the
rejection by `bounded_verify_incomplete` is a real incompleteness, not a
vacuous one.  That bridge lives in Minimality.lean's direction, not here. -/
/-- An endorsement of a depth-n claim has depth n+1 — one more constructor
    wrapping the original.  Budget-n verifiers cannot verify their own
    endorsements: `bounded_verify n (n+1) = false`. -/
theorem endorser_cannot_self_verify (n : Nat) :
    bounded_verify n (n + 1) = false :=
  bounded_verify_incomplete n

/-! ### DepthWorldCtx: W_bounded_verification by construction

A concrete `WorldCtx` where `VerifyWithin w n t` holds iff `n ≤ t` —
the structural depth of the claim equals the number of steps required.
Within this context, `W_bounded_verification` is provable by construction,
not assumed. -/

/-- A `WorldCtx` grounded in kernel depth.
    - Claims are `Nat` (n represents DepthClaim n).
    - `VerifyWithin _ n t ↔ n ≤ t`: depth-n claim verified in t steps iff t ≥ n.
    - `RequiresSteps _ n k`: claim n requires k steps (holds when k ≤ n).
    Declared `abbrev` so field accesses reduce automatically in proofs. -/
abbrev DepthWorldCtx : WorldCtx where
  World             := Unit
  Agent             := Unit
  Claim             := Nat
  Obs               := Unit
  Truth             := fun _ n => DepthClaim n
  Utter             := fun _ _ => True
  obs               := fun _ => ()
  VerifyWithin      := fun _ n t => n ≤ t
  effectiveTime     := fun _ => 0
  world_inhabited   := ⟨()⟩
  agent_inhabited   := ⟨()⟩
  claim_inhabited   := ⟨0⟩

/-- In `DepthWorldCtx`, claim n requires at least k steps iff k ≤ n. -/
theorem DepthWorldCtx_requires_steps (n k : Nat) :
    (∀ w : DepthWorldCtx.World, DepthWorldCtx.RequiresSteps w n k) ↔ k ≤ n := by
  simp only [WorldCtx.RequiresSteps]
  constructor
  · intro h
    -- split on n < k ∨ k ≤ n; right case is the goal; left case contradicts h
    exact (Nat.lt_or_ge n k).elim
      (fun hlt => absurd (Nat.le_refl n) (h () n hlt))
      id
  · intro hkn _ t htk hnt
    -- t < k ≤ n ≤ t gives t < t via Nat.lt_of_lt_of_le
    exact absurd hnt (Nat.not_le_of_gt (Nat.lt_of_lt_of_le htk hkn))

/-- `DepthWorldCtx` satisfies `W_bounded_verification` by construction:
    claim `1` requires at least `1` step in every world.
    No empirical world assumption is needed — the cost is structural. -/
theorem depth_world_satisfies_bounded_verification :
    Nonempty DepthWorldCtx.W_bounded_verification :=
  ⟨{ verification_has_cost :=
      ⟨1, 1, Nat.succ_pos 0,
        -- RequiresSteps () 1 1 : ∀ t, t < 1 → ¬(1 ≤ t)
        -- ht : t < 1 and hv : 1 ≤ t  →  t < 1 and 1 ≤ t  →  t < t
        fun _ t ht hv =>
          absurd (Nat.lt_of_lt_of_le ht hv) (Nat.lt_irrefl t)⟩ }⟩

/-- For any budget d, `DepthWorldCtx` contains a claim that requires more
    than d steps — the `W_bounded_verification` witness is uniform across
    all budgets, not just the singleton witness above. -/
theorem depth_world_exceeds_any_budget (d : Nat) :
    ∀ w : DepthWorldCtx.World, DepthWorldCtx.RequiresSteps w (d + 1) (d + 1) :=
  -- RequiresSteps () (d+1) (d+1) : ∀ t, t < d+1 → ¬(d+1 ≤ t)
  -- ht : t < d+1 and hv : d+1 ≤ t  →  t < d+1 and d+1 ≤ t  →  t < t
  fun _ t ht hv =>
    absurd (Nat.lt_of_lt_of_le ht hv) (Nat.lt_irrefl t)

end EpArch
