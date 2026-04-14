/-
EpArch.Theorems.Cases.Standard — Standard Case: S-Field Failure

Structures and theorems for the relational S-failure mode:
- StandardClearance: deposit_standard vs required_threshold, with soundness bridge
- ProvenanceMode / VProvenance: genuine provenance witness (V sound)
- Threat / EAdequacy: typed error-model adequacy witness (E sound)
- StandardCase: V and E are both sound; S alone fails
- canonical_standard_case: the peanut-allergy example
- canonical_lenient_clearance: same deposit standard, weaker threshold — passes
- standard_failure_is_relational: same deposit, different outcomes per agent
- RelationalClearanceSplit / field-exclusion theorems: V and E positively certified

The key asymmetry with Gettier and FakeBarn:
- Gettier (V-failure): deposit defective regardless of who reads it
- FakeBarn (E-failure): deposit defective regardless of who reads it
- Standard (S-failure): deposit is accurate; fails only relative to THIS agent's threshold

For the absolute (non-relational) S-failure variant, see VacuousStandard.lean.
-/
import EpArch.Basic
import EpArch.Semantics.StepSemantics

namespace EpArch

open StepSemantics

universe u

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}

/-! ### Standard Case: S-Field Failure (Threshold Mismatch)

    S is a property of the claim — stamped at certification time, truthful,
    and fixed. The friend's claim "no peanuts used as an ingredient" carries
    `S = ingredient_check`. That is what the claim says. It is accurate.

    The failure is relational: the deposit's S doesn't satisfy the consuming
    agent's required threshold. The allergic agent needs `S ≥ cross_contamination_check`.
    The same deposit, same S, same E (no detection gap), same V (genuine provenance).
    E and V are both sound — the only mismatch is in S.

    This is the one case where the deposit is not structurally defective:
    - Gettier (V-failure): the deposit is defective regardless of who reads it
    - Fake Barn (E-failure): the deposit is defective regardless of who reads it
    - Standard (S-failure): the deposit is accurate; the standard it carries
      doesn't clear THIS agent's acceptance threshold

    The repair is field-local to S: obtain a new certification under a stricter
    standard. V and E do not need to change.

    Proxy: `StandardClearance.clears = false` represents the threshold mismatch.
    The `deposit_standard` and `required_threshold` fields are left abstract
    (typed by the `Standard` parameter) — EpArch records that they differ but
    does not model the ordering on Standard values; that lives in the agent
    implementation.
-/

/-- Standard clearance: does the deposit's S satisfy the agent's required threshold?

    Both fields are typed by the same `Standard` parameter.  The real semantic
    content is `threshold_met : Prop` — whether the deposit standard satisfies the
    agent's threshold.  EpArch records that the relation holds or fails; the
    ordering on Standard values lives in the consuming agent, outside EpArch's scope.
    `clears : Bool` is an executable mirror with a soundness bridge. -/
structure StandardClearance (Standard : Type u) where
  /-- The standard actually applied when the deposit was certified.
      This is the S field's content — truthful, stamped at certification. -/
  deposit_standard   : Standard
  /-- The minimum standard this agent requires to accept withdrawal. -/
  required_threshold : Standard
  /-- The real semantic content: does deposit_standard satisfy required_threshold?
      EpArch records that this relation holds or fails; the ordering
      lives in the consuming agent's implementation. -/
  threshold_met      : Prop
  /-- Executable mirror of threshold_met for computable contexts. -/
  clears             : Bool
  /-- Sound bridge: the Bool is honest about the Prop. -/
  clears_sound       : clears = true ↔ threshold_met

/-- Provenance mode: how the certifying source connects to the truth-maker.
    Only `.direct_inspection` counts as genuinely tracking.  The `tracks_genuine`
    Bool in `VProvenance` must be honest about `mode = .direct_inspection`;
    the bridge requires a concrete enum comparison. -/
inductive ProvenanceMode where
  | direct_inspection  -- source directly verified the claim
  | hearsay            -- source only received it from another party
  | coincidental       -- source's certification is coincidental to the truth-maker
  deriving DecidableEq, Repr

/-- V-provenance witness: genuine provenance for the Standard case.

    The claim genuinely traces to the certifying source without coincidence,
    in contrast to the Gettier case (V-failure).  `genuinely_tracks` is derived
    from `mode = .direct_inspection`; the `tracks_sound` bridge requires a
    concrete enum comparison. -/
structure VProvenance where
  /-- Who certified this claim (e.g., "the cook", "the supplier") -/
  certifying_source : String
  /-- How the source connects to the truth-maker — the data backing V. -/
  mode              : ProvenanceMode
  /-- Executable mirror: reflects `mode = .direct_inspection`. -/
  tracks_genuine    : Bool
  /-- Sound bridge: the Bool must honestly reflect the provenance-mode comparison. -/
  tracks_sound      : tracks_genuine = true ↔ mode = .direct_inspection

/-- V-provenance genuinely tracks the truth-maker iff the mode is direct inspection.
    Derived from `mode`.
    `@[reducible]` makes this transparent to `decide` and definitional reduction. -/
@[reducible] def VProvenance.genuinely_tracks (v : VProvenance) : Prop := v.mode = .direct_inspection

/-- Typed threat categories for the error model.
    Membership proofs use `List.Mem` witnesses, giving genuine decidable evidence. -/
inductive Threat where
  | ingredient_contamination  -- e.g., peanut traces via shared equipment
  | cross_contact             -- e.g., packaging shared with allergen products
  | fake_barn_facade          -- deceptive replica in environment
  | known_liar_testimony      -- testimony from a documented unreliable source
  deriving DecidableEq, Repr

/-- Error-model adequacy witness for the Standard case: all nearby relevant threats
    for this claim are covered.  `no_relevant_gap` derives from
    `relevant_threat ∈ modeled_threats` via `adequacy_sound`. -/
structure EAdequacy where
  /-- The threat this case is exposed to — what E must cover. -/
  relevant_threat     : Threat
  /-- Failure modes the error model accounts for (typed list). -/
  modeled_threats     : List Threat
  /-- Executable mirror: reflects `relevant_threat ∈ modeled_threats`. -/
  no_nearby_unmodeled : Bool
  /-- Sound bridge: the Bool must honestly reflect the membership fact. -/
  adequacy_sound      : no_nearby_unmodeled = true ↔ relevant_threat ∈ modeled_threats

/-- E is adequate iff the relevant threat is on the modeled list.
    Derived from concrete data.
    `@[reducible]` makes this transparent to `decide` and definitional reduction. -/
@[reducible] def EAdequacy.no_relevant_gap (e : EAdequacy) : Prop :=
  e.relevant_threat ∈ e.modeled_threats

/-- Standard Case structure.

    A Standard case has:
    - Genuine provenance (`v_provenance`): the cook really did certify this
    - Adequate error model (`e_adequacy`): no unmodeled threat gap
    - A StandardClearance whose `threshold_met` is ¬Prop (not just Bool = false)

    The canonical instance: peanut allergy.
    - v_provenance: cook certified, tracks_genuine = true
    - e_adequacy: ingredient_contamination modeled, no nearby gaps
    - S = ingredient_check; required = cross_contamination_check
    - threshold_met = False (ingredient_check does not satisfy cross_contamination_check)
    - clearance_fails = ¬False -/
structure StandardCase (Standard : Type u) where
  claim        : PropLike
  /-- V-field witness: provenance is genuine — not a coincidence -/
  v_provenance : VProvenance
  /-- E-field witness: error model has no relevant gap -/
  e_adequacy   : EAdequacy
  /-- The S-level clearance check — carries deposit_standard, required_threshold,
      threshold_met : Prop, clears : Bool, and soundness bridge -/
  s_clearance  : StandardClearance Standard
  /-- S fails: the threshold relation is not met (Prop-level, not Bool) -/
  clearance_fails : ¬s_clearance.threshold_met

/-- S-field inadequacy: the threshold relation is not met (Prop-level). -/
def case_S_inadequate (sc : StandardCase Standard (PropLike := PropLike)) : Prop :=
  ¬sc.s_clearance.threshold_met

/-- IsStandardCase: a genuine S-failure case iff:
    1. V passes (genuine provenance: tracks_genuine = true)
    2. E passes (no nearby unmodeled threat: no_nearby_unmodeled = true)
    3. S fails (threshold relation not met: ¬threshold_met)

    The asymmetry with Gettier and FakeBarn is intentional: the deposit
    is structurally sound but insufficient for this agent. -/
def IsStandardCase (sc : StandardCase Standard (PropLike := PropLike)) : Prop :=
  sc.v_provenance.genuinely_tracks ∧
  sc.e_adequacy.no_relevant_gap ∧
  ¬sc.s_clearance.threshold_met

/-- Standard cases route to S-failure.

    - `v_provenance`: the cook genuinely certified it (tracks_genuine = true)
    - `e_adequacy`: ingredient contamination is modeled, no nearby gap
    - `deposit_standard` and `required_threshold` are left abstract (two distinct
      Standard values supplied by the caller — the architecture doesn't model the ordering)
    - `threshold_met = False`: the ingredient-check standard does not satisfy the allergy
      threshold (expressed as ⊥ since EpArch doesn't model the Standard ordering)
    - `clearance_fails = False.elim`: witnesses `¬False` -/
def canonical_standard_case (P : PropLike) (ingredient_check cross_contamination_check : Standard) :
    StandardCase Standard (PropLike := PropLike) :=
  { claim := P,
    v_provenance := {
      certifying_source := "cook",
      mode              := .direct_inspection,
      tracks_genuine    := true,
      tracks_sound      := ⟨fun _ => rfl, fun _ => rfl⟩ },
    e_adequacy := {
      relevant_threat     := .ingredient_contamination,
      modeled_threats     := [.ingredient_contamination],
      no_nearby_unmodeled := true,
      adequacy_sound      := by decide },
    s_clearance := {
      deposit_standard   := ingredient_check,
      required_threshold := cross_contamination_check,
      threshold_met      := False,
      clears             := false,
      clears_sound       := ⟨Bool.noConfusion, False.elim⟩ },
    clearance_fails := False.elim }

/-- Canonical Standard case satisfies IsStandardCase. -/
theorem canonical_standard_case_is_standard (P : PropLike)
    (ingredient_check cross_contamination_check : Standard) :
    IsStandardCase (canonical_standard_case (Standard := Standard) P
      ingredient_check cross_contamination_check) :=
  ⟨rfl, List.Mem.head _, False.elim⟩

/-- S-failure is field-local: the failure routes to Field.S.

    When V and E are both fine and only S fails, the failure localises to
    Field.S — not Field.E or Field.V. This demonstrates field independence:
    the deposit's provenance and error model are structurally unaffected.

    Proof: Bool case-split on `s_clearance.clears`, then the `clears_sound`
    bridge connects the Bool outcome to the Prop `¬threshold_met`. -/
theorem standard_failure_targets_S (sc : StandardCase Standard (PropLike := PropLike)) :
    IsStandardCase sc → sc.s_clearance.clears = false := by
  intro ⟨_, _, h_fails⟩
  cases h_eq : sc.s_clearance.clears with
  | false => rfl
  | true => exact absurd (sc.s_clearance.clears_sound.mp h_eq) h_fails

/-- CANONICAL lenient clearance: same deposit standard, lower threshold — clears.

    The disliking-peanuts agent is satisfied by ingredient_check — the exact
    same S stamped on the deposit. `threshold_met = True` (trivially met);
    `clears = true`; `clears_sound` bridges them.

    This is a StandardClearance, not a StandardCase. StandardCase requires
    `¬threshold_met`; a passing clearance has `threshold_met = True`. -/
def canonical_lenient_clearance (ingredient_check : Standard) :
    StandardClearance Standard :=
  { deposit_standard   := ingredient_check,
    required_threshold := ingredient_check,
    threshold_met      := True,
    clears             := true,
    clears_sound       := ⟨fun _ => trivial, fun _ => rfl⟩ }

/-- S-failure is relational: same deposit standard, different outcomes per agent.

    The allergic agent's case fails (`¬threshold_met` = `¬False` is trivially the
    failure structure, held as a Prop — not Bool.not_false).
    The disliking agent's clearance passes (`clears = true`, `threshold_met = True`).
    Same claim. Same V. Same E. Same deposit_standard. Only required_threshold differs.

    This is what distinguishes S-failure from V-failure (Gettier) and E-failure
    (fake barn): those are deposit defects independent of who reads the deposit.
    S-failure is relational — it depends on the consuming agent's threshold. -/
theorem standard_failure_is_relational
    (P : PropLike) (ingredient_check cross_contamination_check : Standard) :
    let strict  := canonical_standard_case (Standard := Standard) P
                     ingredient_check cross_contamination_check
    let lenient := canonical_lenient_clearance (Standard := Standard) ingredient_check
    case_S_inadequate strict ∧ lenient.threshold_met :=
  ⟨False.elim, trivial⟩

/-! ### Generic S-Failure Profile and Field-Exclusion Theorems

The generic contract: an S-failure has V and E positively certified.
These theorems make the taxonomy non-trivially structural — they show that
S-failure and V/E-failure are orthogonal conditions, not just different labels. -/

/-- A relational S-failure split: two clearances on the same deposit standard
    where one consumer's threshold is unmet and another's is met.

    Implementation note: `deposit_standard` is abstract — EpArch does not model the
    ordering on Standard values.  `threshold_met` and its negation are the semantic
    content.  Same deposit, same stamped S, different consuming agent outcomes. -/
def RelationalClearanceSplit {Standard : Type u} (strict lenient : StandardClearance Standard) : Prop :=
  strict.deposit_standard = lenient.deposit_standard ∧
  ¬strict.threshold_met ∧
  lenient.threshold_met

/-- Generic construction: given same deposit standard and opposite threshold outcomes,
    conclude a relational split.  The canonical allergy pair is an instance;
    this theorem applies to any clearing structure. -/
theorem same_deposit_standard_split_yields_relational_S_failure {Standard : Type u}
    (strict lenient : StandardClearance Standard)
    (h_same  : strict.deposit_standard = lenient.deposit_standard)
    (h_fail  : ¬strict.threshold_met)
    (h_pass  : lenient.threshold_met) :
    RelationalClearanceSplit strict lenient :=
  ⟨h_same, h_fail, h_pass⟩

/-- The canonical allergy pair constitutes a relational split.
    Proof: applies the generic theorem to the allergy/lenient constructors. -/
theorem canonical_allergy_is_relational_split
    (P : PropLike) (ingredient_check cross_contamination_check : Standard) :
    RelationalClearanceSplit
      (canonical_standard_case (Standard := Standard) P
        ingredient_check cross_contamination_check).s_clearance
      (canonical_lenient_clearance (Standard := Standard) ingredient_check) :=
  same_deposit_standard_split_yields_relational_S_failure _ _ rfl False.elim trivial

/-- In an S-failure, V is positively certified: the failure does not route through V.
    V-failure (¬genuinely_tracks) and S-failure (genuinely_tracks ∧ ¬threshold_met)
    have incompatible V conditions — they are mutually exclusive failure modes. -/
theorem s_failure_v_is_sound (sc : StandardCase Standard (PropLike := PropLike))
    (h : IsStandardCase sc) :
    sc.v_provenance.genuinely_tracks :=
  h.1

/-- In an S-failure, E is positively certified: the failure does not route through E.
    E-failure (¬no_relevant_gap) and S-failure (no_relevant_gap ∧ ¬threshold_met)
    have incompatible E conditions — they are mutually exclusive failure modes. -/
theorem s_failure_e_is_sound (sc : StandardCase Standard (PropLike := PropLike))
    (h : IsStandardCase sc) :
    sc.e_adequacy.no_relevant_gap :=
  h.2.1

end EpArch
