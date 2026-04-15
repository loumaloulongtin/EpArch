/-
EpArch.Meta.Modular — Machine-Certified Modularity Meta-Theorem

Answers the question: "Is EpArch modular on its six operational constraints —
can you drop any constraint and have the remaining forcing theorems still hold?"

Scope: this file covers the six constraints in EpArch.Minimality only.
Health-goal modularity (∀-transport of SafeWithdrawal, ReliableExport, etc.)
is proved separately in EpArch.Meta.TheoremTransport and EpArch.Meta.Tier4Transport.

This file provides two pieces:

  (1) `PartialWellFormed W S` — a biconditional-subset type parameterized by a subset S of
      the six constraints. You only supply the biconditionals for the constraints
      you care about; the rest are not required.

  (2) `projection_valid S W` — the named target predicate: the conjunction of six
      guarded forcing implications, each guarded by "S selects this constraint."

  (3) `modular` — the universally-quantified meta-theorem:

        ∀ (S : ConstraintSubset) (W : WorkingSystem),
          PartialWellFormed W S → projection_valid S W

## Relationship to PartialWellFormed

  `PartialWellFormed W allConstraints` — all six biconditionals required,
  the strongest subset — is the natural replacement for the former `WellFormed`
  predicate (which has been removed).  Every existing `WellFormed`-gated proof
  can be re-stated as `PartialWellFormed W allConstraints`.

## What This Proves

  - You can remove constraint X by setting S.X := false.
  - `PartialWellFormed W S` with S.X = false requires nothing about X.
  - `modular` returns a guarded implication `false = true → ...` for X, which
    is vacuously true — the forcing theorem for X is not claimed.
  - The forcing theorems for all other constraints in S remain valid.

  This is a machine-certified proof, not a structural observation.
-/

import EpArch.Minimality

namespace EpArch.Meta.Modular

open EpArch

-- `ConstraintSubset`, `allConstraints`, `noConstraints`, and `PartialWellFormed`
-- are defined in `EpArch.Minimality` (visible here via `open EpArch`).
-- `partial_no_constraints` is stated here as the first result that builds on them.

/-! ## Trivial instance: empty subset -/

/-- `PartialWellFormed W noConstraints` holds for every system. -/
theorem partial_no_constraints (W : WorkingSystem) : PartialWellFormed W noConstraints :=
  { wf_distributed    := fun h => absurd h (by decide)
    wf_bounded_audit  := fun h => absurd h (by decide)
    wf_export         := fun h => absurd h (by decide)
    wf_adversarial    := fun h => absurd h (by decide)
    wf_coordination   := fun h => absurd h (by decide)
    wf_truth_pressure := fun h => absurd h (by decide)
    wf_multi_agent    := fun h => absurd h (by decide) }


/-! ## The Modularity Target Predicate -/

/-- `projection_valid S W` — the named target of the modularity meta-theorem.

    For each constraint X in S (i.e., S.X = true), asserts that W satisfies
    the forcing implication for X. Constraints outside S are not claimed.

    This is a real exported definition, not just descriptive wording, so that
    downstream code (e.g. configuration engines, product-profile checkers) can
    reference the target by name. -/
def projection_valid (S : ConstraintSubset) (W : WorkingSystem) : Prop :=
  (S.distributed    = true → handles_distributed_agents W → HasBubbles W) ∧
  (S.bounded_audit  = true → handles_bounded_audit W → HasTrustBridges W) ∧
  (S.export_across  = true → handles_export W → HasHeaders W) ∧
  (S.adversarial    = true → handles_adversarial W → HasRevocation W) ∧
  (S.coordination   = true → handles_coordination W → HasBank W) ∧
  (S.truth_pressure = true → handles_truth_pressure W → HasRedeemability W) ∧
  (S.multi_agent    = true → handles_multi_agent W → HasGranularACL W)


/-! ## The Modularity Meta-Theorem -/

/-- **`modular` — the EpArch constraint-modularity meta-theorem.**

    For any subset S of the seven constraints, any system with `PartialWellFormed W S`
    satisfies `projection_valid S W`: the forcing theorem holds for each constraint
    in S, and no claim is made about constraints outside S.

    Usage:
    - To drop constraint X: set S.X := false. The X-conjunct in `projection_valid`
      becomes `false = true → ...`, which is vacuously true.
    - The remaining conjuncts are live forcing implications backed by the
      biconditionals in `PartialWellFormed W S`. -/
theorem modular (S : ConstraintSubset) (W : WorkingSystem)
    (pwf : PartialWellFormed W S) : projection_valid S W :=
  ⟨fun hd h => (pwf.wf_distributed    hd).mp h,
   fun hb h => (pwf.wf_bounded_audit   hb).mp h,
   fun he h => (pwf.wf_export          he).mp h,
   fun ha h => (pwf.wf_adversarial     ha).mp h,
   fun hc h => (pwf.wf_coordination    hc).mp h,
   fun ht h => (pwf.wf_truth_pressure  ht).mp h,
   fun hm h => (pwf.wf_multi_agent     hm).mp h⟩


/-! ## PartialGroundedSpec — Minimal User-Facing Compliance API

A product developer filling in a `PartialGroundedSpec S` is writing their
EpArch compliance certificate.  The workflow:

  1. Choose `S : ConstraintSubset` — the EpArch pressures your product faces.
  2. Fill in the active `GroundedX` fields with domain-typed evidence.
  3. `lake build` — if it compiles, `partial_modular S pgs` certifies that
     every constraint in S is structurally satisfied.  No flag-bags, no sorry.

Inactive constraints (S.X = false) require only `fun h => absurd h (by decide)`.

### Mapping

| S field          | Constraint              | Required evidence          |
|------------------|-------------------------|----------------------------|
| `distributed`    | Distributed agents      | `GroundedBubbles`          |
| `bounded_audit`  | Bounded audit           | `GroundedTrustBridges`     |
| `export_across`  | Export across bounds    | `GroundedHeaders`          |
| `adversarial`    | Adversarial pressure    | `GroundedRevocation`       |
| `coordination`   | Coordination need       | `GroundedBank`             |
| `truth_pressure` | Truth pressure          | `GroundedRedeemability`    | -/

/-- The compliance form: evidence for each EpArch constraint in S.

    For `S.X = true`  → the field type is `true = true → GroundedX`;
                         the user must supply a real `GroundedX` value.
    For `S.X = false` → the field type is `false = true → GroundedX = False → GroundedX`;
                         vacuously inhabited; no obligation.

    Example fill-in (app with distributed agents and adversarial pressure only):
    ```lean
    def MyConstraints : ConstraintSubset :=
      { distributed := true, adversarial := true,
        bounded_audit := false, export_across := false,
        coordination := false, truth_pressure := false }

    def MySpec : PartialGroundedSpec MyConstraints where
      bubbles       := fun _ => MyGroundedBubbles    -- real domain evidence
      revocation    := fun _ => MyGroundedRevocation -- real domain evidence
      trust_bridges := fun h => absurd h (by decide)
      headers       := fun h => absurd h (by decide)
      bank          := fun h => absurd h (by decide)
      redeemability := fun h => absurd h (by decide)

    -- If this compiles, your design is EpArch-compliant for MyConstraints:
    #check (partial_modular MyConstraints MySpec)
    ``` -/
structure PartialGroundedSpec (S : ConstraintSubset) where
  /-- Scope separation evidence (required iff S.distributed = true) -/
  bubbles       : S.distributed    = true → GroundedBubbles
  /-- Trust bridge evidence (required iff S.bounded_audit = true) -/
  trust_bridges : S.bounded_audit  = true → GroundedTrustBridges
  /-- Header preservation evidence (required iff S.export_across = true) -/
  headers       : S.export_across  = true → GroundedHeaders
  /-- Revocation evidence (required iff S.adversarial = true) -/
  revocation    : S.adversarial    = true → GroundedRevocation
  /-- Shared ledger evidence (required iff S.coordination = true) -/
  bank          : S.coordination   = true → GroundedBank
  /-- Redeemability evidence (required iff S.truth_pressure = true) -/
  redeemability : S.truth_pressure = true → GroundedRedeemability
  /-- Authorization evidence (required iff S.multi_agent = true) -/
  authorization : S.multi_agent    = true → GroundedAuthorization


/-- Build a `WorkingSystem` from partial evidence.

    Active constraints (S.X = true) set the corresponding spec flag and
    evidence field from the supplied `GroundedX` value.
    Inactive constraints leave both `false`/`none`. -/
def PartialGroundedSpec.toWorkingSystem (S : ConstraintSubset)
    (pgs : PartialGroundedSpec S) : WorkingSystem where
  spec := {
    has_bubble_separation :=
      if h : S.distributed    = true then let _ev := pgs.bubbles h;       true else false
    has_trust_bridges     :=
      if h : S.bounded_audit  = true then let _ev := pgs.trust_bridges h; true else false
    preserves_headers     :=
      if h : S.export_across  = true then let _ev := pgs.headers h;       true else false
    has_revocation        :=
      if h : S.adversarial    = true then let _ev := pgs.revocation h;    true else false
    has_shared_ledger     :=
      if h : S.coordination   = true then let _ev := pgs.bank h;          true else false
    has_redeemability     :=
      if h : S.truth_pressure = true then let _ev := pgs.redeemability h; true else false
    has_granular_acl      :=
      if h : S.multi_agent    = true then let _ev := pgs.authorization h; true else false
  }
  bubbles_ev       := if h : S.distributed    = true then some (pgs.bubbles h).toStrict       else none
  bridges_ev       := if h : S.bounded_audit  = true then some (pgs.trust_bridges h).toStrict else none
  headers_ev       := if h : S.export_across  = true then some (pgs.headers h).toStrict       else none
  revocation_ev    := if h : S.adversarial    = true then some (pgs.revocation h).toStrict    else none
  bank_ev          := if h : S.coordination   = true then some (pgs.bank h).toStrict          else none
  redeemability_ev := if h : S.truth_pressure = true then some (pgs.redeemability h).toStrict else none
  authorization_ev := if h : S.multi_agent    = true then some (pgs.authorization h).toStrict else none


/-- A `WorkingSystem` built by `toWorkingSystem` satisfies `PartialWellFormed W S`.

    Active constraints supply grounded evidence for the live biconditionals;
    inactive constraints pass vacuously. -/
theorem partial_grounded_is_partial_wellformed (S : ConstraintSubset)
    (pgs : PartialGroundedSpec S) :
    PartialWellFormed (PartialGroundedSpec.toWorkingSystem S pgs) S := {
  wf_distributed    := fun h => by
    simp [handles_distributed_agents, HasBubbles, PartialGroundedSpec.toWorkingSystem, h,
          Option.isSome]
  wf_bounded_audit  := fun h => by
    simp [handles_bounded_audit, HasTrustBridges, PartialGroundedSpec.toWorkingSystem, h,
          Option.isSome]
  wf_export         := fun h => by
    simp [handles_export, HasHeaders, PartialGroundedSpec.toWorkingSystem, h, Option.isSome]
  wf_adversarial    := fun h => by
    simp [handles_adversarial, HasRevocation, PartialGroundedSpec.toWorkingSystem, h,
          Option.isSome]
  wf_coordination   := fun h => by
    simp [handles_coordination, HasBank, PartialGroundedSpec.toWorkingSystem, h, Option.isSome]
  wf_truth_pressure := fun h => by
    simp [handles_truth_pressure, HasRedeemability, PartialGroundedSpec.toWorkingSystem, h,
          Option.isSome]
  wf_multi_agent    := fun h => by
    simp [handles_multi_agent, HasGranularACL, PartialGroundedSpec.toWorkingSystem, h,
          Option.isSome] }


/-- EpArch compliance for a partial constraint profile.

    Given `pgs : PartialGroundedSpec S`, certifies that the system built from `pgs`
    satisfies `projection_valid S W`: the forcing implication holds for every
    constraint in S. -/
theorem partial_modular (S : ConstraintSubset) (pgs : PartialGroundedSpec S) :
    projection_valid S (PartialGroundedSpec.toWorkingSystem S pgs) :=
  modular S _ (partial_grounded_is_partial_wellformed S pgs)

end EpArch.Meta.Modular
