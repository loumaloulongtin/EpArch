/-
EpArch.Theorems.Cases — Classic Epistemology Diagnoses

Structural case types and theorems for the three SEV failure modes:
- Gettier case: V-independence failure (provenance doesn't track truth-maker)
- Fake Barn case: E-field failure (unmodeled environmental threat)
- Standard case: S-field failure (threshold mismatch, relational and vacuous forms)
- Lottery / Confabulation: type errors (Ladder ≠ Bank)
-/
import EpArch.Basic
import EpArch.StepSemantics

namespace EpArch

open StepSemantics

universe u

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}

/-! ## Classic Epistemology Diagnoses -/

/-! ### Gettier Case: V-Independence Failure

    The V-independence concept ("truth-maker not connected to provenance")
    is intentionally schematic — philosophy can remain schematic while Lean
    supplies conditional, non-unique proxies.

    This proxy encodes the intended failure pattern without committing to a
    specific causal or modal apparatus (which would be research-level work).

    Proxy interpretation: `VIndependence.tracks = false` means the provenance
    doesn't connect to the truth-maker. Theorem: GettierInstance → ¬Tracks.

    Future work: Richer semantics via causal graphs or modal structures.
-/

/-- Truth-maker: the fact in the world that makes P true. -/
structure TruthMaker where
  /-- The actual ground of truth (e.g., "Smith has 10 coins") -/
  ground : PropLike

/-- Provenance chain: the evidence/justification path.
    Abstract type—represents the agent's epistemic route to the claim. -/
structure ProvenanceChain where
  /-- The evidential basis (e.g., "Jones has 10 coins and will get job") -/
  basis : PropLike

/-- Independence relation: does the provenance chain track the truth-maker?

    When `tracks` is false, the truth is accidental relative to the evidence. -/
structure VIndependence where
  truth_maker : TruthMaker (PropLike := PropLike)
  provenance : ProvenanceChain (PropLike := PropLike)
  /-- Does the provenance causally/evidentially connect to the truth-maker? -/
  tracks : Bool

/-- Gettier case structure.

    A Gettier case has:
    - True proposition (the claim happens to be correct)
    - Valid-looking header (the agent has apparent justification)
    - V-independence failure (the evidence chain doesn't track truth)

    We explicitly represent the truth-maker/provenance disconnect,
    not just a Bool flag. -/
structure GettierCase where
  claim : PropLike
  S_passes : Bool  -- Standard/threshold satisfied
  E_passes : Bool  -- Error model adequate
  /-- The V-independence structure showing truth-maker/provenance disconnect -/
  v_independence : VIndependence (PropLike := PropLike)
  /-- Structural evidence: truth-maker ground and provenance basis are distinct -/
  ground_distinct : v_independence.truth_maker.ground ≠ v_independence.provenance.basis
  /-- Structural certification: provenance tracks = false is mandatory for a
      genuine Gettier case.  Required at construction time. -/
  tracks_false_certified : v_independence.tracks = false

/-- V fails when provenance doesn't track truth-maker. -/
def V_fails (g : GettierCase (PropLike := PropLike)) : Bool :=
  !g.v_independence.tracks

/-- The claim is true (in the proxy encoding, S passing represents truth). -/
def case_is_true (g : GettierCase (PropLike := PropLike)) : Prop :=
  g.S_passes = true

/-- The header looks valid when S and E both pass. -/
def case_header_valid (g : GettierCase (PropLike := PropLike)) : Prop :=
  g.S_passes = true ∧ g.E_passes = true

/-- V-independence fails when provenance doesn't track truth-maker.

    Structurally encoded via VIndependence.tracks = false. -/
def case_V_independence_fails (g : GettierCase (PropLike := PropLike)) : Prop :=
  V_fails g = true

/-- CANONICAL Gettier case: S and E pass, but provenance doesn't track truth.

    Smith/Jones example:
    - truth_maker: Smith has 10 coins, Smith gets job
    - provenance: Jones has 10 coins, Jones expected to get job
    - tracks = false: provenance doesn't connect to actual truth-maker -/
def canonical_gettier (P : PropLike) (truth_ground evidence_basis : PropLike)
    (h_ground : truth_ground ≠ evidence_basis) :
    GettierCase (PropLike := PropLike) :=
  { claim := P,
    S_passes := true,
    E_passes := true,
    v_independence := {
      truth_maker := ⟨truth_ground⟩,
      provenance := ⟨evidence_basis⟩,
      tracks := false  -- The key Gettier feature: evidence doesn't track truth
    },
    ground_distinct := h_ground,
    tracks_false_certified := rfl }

/-- IsGettierCase: A case is a genuine Gettier case iff:
    1. S passes (meets threshold)
    2. E passes (error model adequate)
    3. V fails (provenance doesn't track truth-maker)

    The definitional characterization: "The Gettier intuition tracks
    V-independence failure: the evidence chain doesn't causally connect
    to the truth-maker."

    With explicit VIndependence structure, V-failure means
    provenance.tracks = false. A case is only a "Gettier case" when this
    disconnect exists. -/
def IsGettierCase (g : GettierCase (PropLike := PropLike)) : Prop :=
  g.S_passes = true ∧ g.E_passes = true ∧ g.v_independence.tracks = false

/-- Gettier cases route to V-failure.

    Unconditional: the conclusion follows directly from the structural
    `tracks_false_certified` field — `IsGettierCase g` is not needed.
    The structural invariant is certified at construction time. -/
theorem gettier_is_V_failure (g : GettierCase (PropLike := PropLike)) :
    case_V_independence_fails g :=
  by simp only [case_V_independence_fails, V_fails, g.tracks_false_certified, Bool.not_false]

/-- Canonical Gettier case satisfies IsGettierCase. -/
theorem canonical_gettier_is_gettier (P truth_ground evidence_basis : PropLike)
    (h_ground : truth_ground ≠ evidence_basis) :
    IsGettierCase (canonical_gettier P truth_ground evidence_basis h_ground) := by
  unfold IsGettierCase canonical_gettier
  exact ⟨rfl, rfl, rfl⟩

/-- Canonical Gettier case also satisfies the legacy conditions. -/
theorem canonical_gettier_conditions (P truth_ground evidence_basis : PropLike)
    (h_ground : truth_ground ≠ evidence_basis) :
    let g := canonical_gettier P truth_ground evidence_basis h_ground
    case_is_true g ∧ case_header_valid g ∧ case_V_independence_fails g := by
  simp [canonical_gettier, case_is_true, case_header_valid, case_V_independence_fails, V_fails]

/-- Gettier case: truth-maker and provenance are structurally distinct grounds.
    Directly accesses the `ground_distinct` structural field added in Pass 6. -/
theorem gettier_ground_disconnected (g : GettierCase (PropLike := PropLike)) :
    g.v_independence.truth_maker.ground ≠ g.v_independence.provenance.basis :=
  g.ground_distinct

/-! ### Fake Barn Case: E-Field Failure (Unmodeled Environmental Threat)

    The E-coverage concept ("nearby failure modes") is intentionally
    schematic. We don't need full modal semantics—just a threat-coverage relation.

    This proxy treats "nearby" as a parameterized set selector (by region,
    context class, etc.) rather than solving modal metaphysics.

    Proxy interpretation: `ErrorModelCoverage.unmodeled_threats.any nearby` means
    the error model has coverage gaps. Theorem: FakeBarnInstance → ¬Coverage.

    Future work: Modal structures for "nearby possible worlds".
-/

/-- A failure mode that could defeat the claim. -/
structure FailureMode where
  /-- Description of the threat (e.g., "deceptive replica in environment") -/
  threat : String
  /-- Is this failure mode "nearby" (modally close / plausible)? -/
  nearby : Bool

/-- Error model coverage: which failure modes are included?

    An error model is adequate if it includes all nearby failure modes. -/
structure ErrorModelCoverage where
  /-- Failure modes the agent's error model considers -/
  modeled_threats : List FailureMode
  /-- Failure modes present in the environment but not modeled -/
  unmodeled_threats : List FailureMode

/-- E-field fails when nearby threats are unmodeled. -/
def E_coverage_fails (cov : ErrorModelCoverage) : Bool :=
  cov.unmodeled_threats.any (·.nearby)

/-- Fake Barn case structure.

    The "Fake Barn County" case:
    - Agent sees a real barn, correctly identifies it
    - But is surrounded by fake barns (unmodeled environmental threat)
    - Error model E didn't include "nearby deceptive replicas"

    We explicitly represent the unmodeled nearby failure mode,
    not just a Bool flag. -/
structure FakeBarnCase where
  /-- The agent's claim (e.g., "that's a barn") -/
  claim : PropLike
  /-- S-field passes (meets threshold) -/
  S_passes : Bool
  /-- Error model coverage showing unmodeled nearby threats -/
  e_coverage : ErrorModelCoverage
  /-- V-field passes (genuine provenance) -/
  V_passes : Bool
  /-- Structural certification: the error model coverage definitionally fails -/
  e_certified : E_coverage_fails e_coverage = true

/-- E-field fails when error model has unmodeled nearby threats. -/
def E_fails (fb : FakeBarnCase (PropLike := PropLike)) : Bool :=
  E_coverage_fails fb.e_coverage

/-- E-field is inadequate when error model has unmodeled nearby threats. -/
def barn_case_E_inadequate (fb : FakeBarnCase (PropLike := PropLike)) : Prop :=
  E_fails fb = true

/-- CANONICAL Fake Barn case: S and V pass, but nearby threat unmodeled.

    Fake Barn County example:
    - modeled_threats: [] (agent just uses "looks like a barn")
    - unmodeled_threats: [{threat: "facades in region", nearby: true}]
    - E_coverage_fails = true because nearby threat is unmodeled -/
def canonical_fake_barn (P : PropLike) : FakeBarnCase (PropLike := PropLike) :=
  { claim := P,
    S_passes := true,
    e_coverage := {
      modeled_threats := [],
      unmodeled_threats := [⟨"deceptive facades in region", true⟩]  -- nearby = true
    },
    V_passes := true,
    e_certified := rfl }

/-- IsFakeBarnCase: A case is a genuine Fake Barn case iff:
    1. S passes (meets threshold)
    2. V passes (genuine provenance)
    3. E fails (unmodeled nearby threats exist)

    The definitional characterization: E failed to include the nearby failure mode. -/
def IsFakeBarnCase (fb : FakeBarnCase (PropLike := PropLike)) : Prop :=
  fb.S_passes = true ∧ fb.V_passes = true ∧ E_coverage_fails fb.e_coverage = true

/-- Fake Barn cases route to E-failure.

    Unconditional: `IsFakeBarnCase fb` is not needed — the conclusion follows
    directly from the structural `e_certified` field.  The field is certified
    at construction time; `fake_barn_profile_yields_E_failure` is its alias. -/
theorem fake_barn_is_E_failure (fb : FakeBarnCase (PropLike := PropLike)) :
    barn_case_E_inadequate fb :=
  fb.e_certified

/-- Canonical Fake Barn case satisfies IsFakeBarnCase. -/
theorem canonical_fake_barn_is_fake_barn (P : PropLike) :
    IsFakeBarnCase (canonical_fake_barn P) :=
  ⟨rfl, rfl, rfl⟩

/-- Fake Barn profile: the structural `e_certified` field directly certifies
    E-coverage failure. The field is proved at construction time. -/
theorem fake_barn_profile_yields_E_failure (fb : FakeBarnCase (PropLike := PropLike)) :
    barn_case_E_inadequate fb :=
  fb.e_certified


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

/-- Boolean mirror: S clearance fails (for executable use). -/
def S_fails (sc : StandardCase Standard (PropLike := PropLike)) : Bool :=
  !sc.s_clearance.clears

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

/-- S-field inadequacy: the threshold relation is not met (Prop-level). -/
def case_S_inadequate (sc : StandardCase Standard (PropLike := PropLike)) : Prop :=
  ¬sc.s_clearance.threshold_met

/-- Standard cases route to S-failure.

    When V and E are both sound, a withdrawal block localises to Field.S.
    Proof: extracts `¬threshold_met` from the IsStandardCase bundle via pattern
    matching — a genuine Prop negation, not Bool.not_false. -/
theorem standard_case_is_S_failure (sc : StandardCase Standard (PropLike := PropLike)) :
    IsStandardCase sc → case_S_inadequate sc :=
  fun ⟨_, _, h_fails⟩ => h_fails

/-- CANONICAL Standard case: peanut allergy / ingredient-check vs cross-contamination.

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
    IsStandardCase sc → S_fails sc = true := by
  intro ⟨_, _, h_fails⟩
  simp only [S_fails]
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

/-- Data-backed form of `s_failure_v_is_sound` + `s_failure_e_is_sound`.
    Surfaces the concrete evidence: `mode = .direct_inspection` (not `True`)
    and `relevant_threat ∈ modeled_threats` (a real `List.Mem` witness, not `True`).
    These are stronger conclusions because the evidence structure is identified. -/
theorem s_failure_v_mode_and_e_threat
    (sc : StandardCase Standard (PropLike := PropLike))
    (h : IsStandardCase sc) :
    sc.v_provenance.mode = .direct_inspection ∧
    sc.e_adequacy.relevant_threat ∈ sc.e_adequacy.modeled_threats :=
  ⟨h.1, h.2.1⟩

/-- In a relational S-failure, V and E data are symmetric across both consumers;
    only the threshold differs.  Data-backed form: conclusions are concrete
    (`mode = .direct_inspection`, `threat ∈ modeled_threats`), not `True`. -/
theorem relational_S_requires_matching_VE_data
    (sc : StandardCase Standard (PropLike := PropLike))
    (lenient_clearance : StandardClearance Standard)
    (h : IsStandardCase sc)
    (h_same   : sc.s_clearance.deposit_standard = lenient_clearance.deposit_standard)
    (h_lenient : lenient_clearance.threshold_met) :
    sc.v_provenance.mode = .direct_inspection ∧
    sc.e_adequacy.relevant_threat ∈ sc.e_adequacy.modeled_threats ∧
    sc.s_clearance.deposit_standard = lenient_clearance.deposit_standard ∧
    ¬sc.s_clearance.threshold_met ∧ lenient_clearance.threshold_met :=
  ⟨h.1, h.2.1, h_same, h.2.2, h_lenient⟩


/-! ### Vacuous Standard Case: S Voided by E + V Interaction

    A second kind of S-failure, distinct from the relational (allergy) case.

    Setup — the known-liar cook:
    - V: provenance genuinely traces to the cook. V is accurate and honest.
    - E: our error model explicitly documents "cook is a known liar."
          E is sound — we have the threat modeled correctly.
    - S: "the cook said it." Standard = source testimony.

    E and V are both *correct*. Their correct content jointly witnesses that
    S = "trust the cook's testimony" carries a structural void — the two
    fields E and V together exhibit the pattern `VacuousStandardCase` describes.
    This is a demonstration of field independence, not a prescription
    for what any consuming agent should decide.

    This is the architectural content of "E + V ≠ S":
    - E being sound does not make S sound.
    - V being accurate does not make S sound.
    - The three fields are genuinely independent.
    S can be the broken field while E and V are doing their jobs perfectly.

    Contrast with the allergy case (relational S-failure):
    - Relational: what makes the deposit pass or fail differs per consuming agent.
    - Absolute/void: the two structural conditions are present in the fields
      regardless of which agent inspects the deposit. How agents respond
      to `S_is_vacuous` is outside EpArch's scope.

    Repair in both cases localizes to S: the field structure tells you *where*
    to look, not what the agent must do.
-/

/-- Tags that document why a source is considered unreliable.
    A source is unreliable iff it carries `documented_liar` or `audited_unreliable`;
    membership in the tag list enables a real `List.Mem` witness below. -/
inductive ReliabilityTag where
  | documented_liar     -- source explicitly known to be deceptive
  | audited_unreliable  -- source independently audited as unreliable
  | plausible           -- no documented reliability issues
  deriving DecidableEq, Repr

/-- Source reliability record.
    `is_unreliable` derives from `tags`: it holds iff
    `documented_liar ∈ tags ∨ audited_unreliable ∈ tags`. `unreliability_sound`
    bridges the Bool mirror. -/
structure SourceReliability where
  source_id             : String
  /-- Reliability tags recorded for this source in the error model. -/
  tags                  : List ReliabilityTag
  /-- Executable mirror: reflects tag-based unreliability. -/
  documented_unreliable : Bool
  /-- Sound bridge: the Bool must honestly reflect `documented_liar ∈ tags ∨ …`. -/
  unreliability_sound   : documented_unreliable = true ↔
                            .documented_liar ∈ tags ∨ .audited_unreliable ∈ tags

/-- A source is unreliable iff it carries a documented or audited tag.
    Derived from the tag list.
    `@[reducible]` makes this transparent to `decide` and definitional reduction. -/
@[reducible] def SourceReliability.is_unreliable (sr : SourceReliability) : Prop :=
  .documented_liar ∈ sr.tags ∨ .audited_unreliable ∈ sr.tags

/-- Testimony mode: does the standard have an independent verification path,
    or does it rely solely on the source's word? -/
inductive TestimonyMode where
  | sole_source   -- only testimony, no independent verification path
  | corroborated  -- testimony supplemented by independent evidence
  deriving DecidableEq, Repr

/-- Vacuous Standard Case.

    S is grounded in testimony from a source that E explicitly documents as
    unreliable, while V accurately traces the claim to that same source.

    Both E and V are structurally correct — the void is in S.
    `testimony_only` derives from `testimony_mode = .sole_source`;
    `testimony_sound` bridges the mode comparison. -/
structure VacuousStandardCase where
  claim  : PropLike
  /-- The source whose testimony grounds the deposit.
      V is honest: the claim genuinely came from this source. -/
  source : SourceReliability
  /-- E documents this source as unreliable — E is sound.
      Required cert: guarantees `is_unreliable` holds via `unreliability_sound`. -/
  e_documents_unreliability : source.documented_unreliable = true
  /-- How the standard was grounded — the data backing the testimony condition. -/
  testimony_mode             : TestimonyMode
  /-- Executable mirror: reflects `testimony_mode = .sole_source`. -/
  s_is_source_testimony_only : Bool
  /-- Sound bridge: the Bool must honestly reflect the mode comparison. -/
  testimony_sound            : s_is_source_testimony_only = true ↔ testimony_mode = .sole_source
  /-- Structural cert: S is testimony-only at construction time. -/
  s_testimony_certified      : s_is_source_testimony_only = true

/-- S is testimony-only iff the testimony mode is `sole_source`.
    Derived from the mode.
    `@[reducible]` makes this transparent to `decide` and definitional reduction. -/
@[reducible] def VacuousStandardCase.testimony_only
    (vc : VacuousStandardCase (PropLike := PropLike)) : Prop :=
  vc.testimony_mode = .sole_source

/-- S is vacuous when it is grounded solely in testimony from a documented unreliable source.

    Both conditions are required: the standard must be testimony-only AND the
    source must be documented unreliable. Either condition alone is insufficient — a
    documented unreliable source could still be confirmed by independent evidence (S
    would then not be testimony-only), and testimony-only from a reliable source is the
    ordinary case. The void arises from the intersection. -/
def S_is_vacuous (vc : VacuousStandardCase (PropLike := PropLike)) : Prop :=
  vc.testimony_only ∧ vc.source.is_unreliable

/-- Vacuous standard routes to S-failure — absolute, not relational.

    Proof: both conditions are certified structural fields; no case analysis needed. -/
theorem vacuous_standard_is_S_failure (vc : VacuousStandardCase (PropLike := PropLike)) :
    S_is_vacuous vc :=
  ⟨vc.testimony_sound.mp vc.s_testimony_certified,
    vc.source.unreliability_sound.mp vc.e_documents_unreliability⟩

/-- Generic: for any `VacuousStandardCase`, testimony-only S over a documented-unreliable
    source yields void S.  The proof uses the Prop fields directly — the soundness bridges
    (`testimony_sound`, `unreliability_sound`) extract the Prop content from the Bool certs.
    Canonical instances apply this theorem rather than re-proving via construction. -/
theorem testimony_only_plus_unreliable_source_yields_void_S
    (vc : VacuousStandardCase (PropLike := PropLike))
    (h_testimony  : vc.testimony_only)
    (h_unreliable : vc.source.is_unreliable) :
    S_is_vacuous vc :=
  ⟨h_testimony, h_unreliable⟩

/-- CANONICAL vacuous case: the known-liar cook. -/
def canonical_liar_cook_case (P : PropLike) : VacuousStandardCase (PropLike := PropLike) :=
  { claim  := P,
    source := { source_id           := "cook",
                tags                := [.documented_liar],
                documented_unreliable := true,
                unreliability_sound := by decide },
    e_documents_unreliability  := rfl,
    testimony_mode             := .sole_source,
    s_is_source_testimony_only := true,
    testimony_sound            := ⟨fun _ => rfl, fun _ => rfl⟩,
    s_testimony_certified      := rfl }

/-- The canonical liar-cook case yields void S, as an instance of the generic theorem. -/
theorem canonical_liar_cook_is_void (P : PropLike) :
    S_is_vacuous (canonical_liar_cook_case P) :=
  testimony_only_plus_unreliable_source_yields_void_S _ rfl
    (Or.inl (List.Mem.head _))

/-- Absolute vs relational S-failure: two kinds of S-void.

    Relational (allergy): `¬threshold_met` is the Prop-level failure structure;
    the lenient agent has `threshold_met = True`. Same deposit, different agents.

    Absolute (known liar): E + V together witness that S is void regardless of
    which agent inspects the deposit.

    Both repair by targeting Field.S. -/
theorem absolute_vs_relational_S_failure
    (P : PropLike) (ingredient_check cross_contamination_check : Standard) :
    let relational := canonical_standard_case (Standard := Standard) P
                        ingredient_check cross_contamination_check
    let absolute   := canonical_liar_cook_case (PropLike := PropLike) P
    case_S_inadequate relational ∧ S_is_vacuous absolute :=
  ⟨False.elim, ⟨rfl, Or.inl (List.Mem.head _)⟩⟩


/-! ## Lottery Problem -/

/-- Lottery situation: agent has high credence but no deposit.

    The classic case: "I believe my lottery ticket will lose" (99.9999%)
    but this credence alone doesn't authorize withdrawal as knowledge. -/
structure LotterySituation where
  /-- The proposition being considered (e.g., "ticket loses") -/
  proposition : PropLike
  /-- Credence level (0-100) -/
  credence_level : Nat
  /-- Whether there's an authorized deposit for this proposition -/
  has_deposit : Bool

/-- High credence: credence level above threshold (say, 95). -/
def high_credence (s : LotterySituation (PropLike := PropLike)) : Prop :=
  s.credence_level ≥ 95

/-- No deposit: the proposition has no authorized deposit in the agent's bank. -/
def no_deposit (s : LotterySituation (PropLike := PropLike)) : Prop :=
  s.has_deposit = false

/-- Type error: a situation exhibits category confusion between ladder and bank.

    In the banking metaphor: having credence (ladder-state) but no deposit (bank-state)
    and conflating the two. The type error IS the situation, not just acting on it.

    "You can't withdraw from a bank that never accepted a deposit." -/
structure TypeError where
  /-- High credence exists (ladder-state) -/
  has_ladder_state : Prop
  /-- No authorization exists (bank-state) -/
  lacks_bank_state : Prop
  /-- Evidence of ladder state -/
  ladder_evidence : has_ladder_state
  /-- Evidence of missing bank state -/
  bank_evidence : lacks_bank_state

/-- Theorem: Lottery problem is a type error.

    The lottery holder has high credence (ladder-state) but no validated deposit
    (bank-state). Probability yields credence, not authorization.
    You can't withdraw from a bank that never accepted a deposit.
    This is a category confusion between certainty (ladder) and knowledge (bank).

    The lottery situation IS a type error: it exhibits the structural pattern of
    having ladder-state (high credence) while lacking bank-state (no deposit).
    The type error is IDENTIFIED BY the combination, not caused by acting on it. -/
theorem LotteryIsTypeError (s : LotterySituation (PropLike := PropLike)) :
    high_credence s → no_deposit s → TypeError := by
  intro h_credence h_no_deposit
  exact ⟨high_credence s, no_deposit s, h_credence, h_no_deposit⟩


/-! ## Confabulation as Type Error -/

/-- Confabulation case: an agent produces a fluent claim with no grounding.

    This is the original neuropsychological referent: a patient with a memory gap
    generates a confident, coherent narrative that is unconnected to any stored
    episodic trace. The language system produces traction; the memory system
    provides no deposit. Classic instance: split-brain left-hemisphere confabulation
    of causes for right-hemisphere-directed actions.

    The structure is agent-agnostic by construction. Generative AI hallucination is
    a direct instantiation of the same type error in a different substrate:
    - fluency_traction = model emits with high confidence (Ladder-side)
    - has_grounding    = traceable constraint-surface contact exists (Bank-side)

    Renamed instantiation of LotterySituation:
    - fluency_traction replaces credence_level (Ladder side)
    - has_grounding    replaces has_deposit    (Bank side)

    "hallucination is the lottery problem instantiated in generative systems" -/
structure ConfabulationCase where
  /-- The claim being produced -/
  claim             : PropLike
  /-- Agent generates with high confidence (Ladder-side traction) -/
  fluency_traction  : Bool
  /-- A traceable constraint-surface contact exists (Bank-side grounding) -/
  has_grounding     : Bool

def high_fluency (c : ConfabulationCase (PropLike := PropLike)) : Prop := c.fluency_traction = true
def ungrounded   (c : ConfabulationCase (PropLike := PropLike)) : Prop := c.has_grounding = false

/-- Theorem: Confabulation is a type error.

    High fluency-traction with no grounding is the identical architectural type error
    as the lottery problem: Ladder-state (fluency) conflated with Bank-state (grounding).
    The failure is not accuracy failure but category confusion — the system accepted
    an output in a slot requiring Bank without Bank contact.

    Direct instantiation of LotteryIsTypeError with fluency/grounding fields. -/
theorem confabulation_is_type_error (c : ConfabulationCase (PropLike := PropLike)) :
    high_fluency c → ungrounded c → TypeError := by
  intro h_fluency h_ungrounded
  exact ⟨high_fluency c, ungrounded c, h_fluency, h_ungrounded⟩


/-! ### Structural Step-Grounded Forms

These theorems provide the genuine operational content for the lottery and
confabulation patterns.  `Step.withdraw` requires `isDeposited` as a hard
precondition; without a deposit the withdrawal transition is simply
uninhabited.  This is structurally stronger than `LotteryIsTypeError`: the
operational machinery itself is blocked, not just categorically mislabelled. -/

/-- Without an authorized deposit, no withdrawal Step can fire.
    `Step.withdraw` carries `h_deposited : isDeposited s d_idx` as a
    precondition; `h` provides `¬isDeposited`, so the Step is uninhabited. -/
theorem lottery_no_deposit_blocks_withdraw
    (s : SystemState PropLike Standard ErrorModel Provenance) (d_idx : Nat)
    (h : ¬isDeposited s d_idx) :
    ¬∃ (s' : SystemState PropLike Standard ErrorModel Provenance) (a : Agent) (B : Bubble),
      Step (Reason := Reason) (Evidence := Evidence) s (.Withdraw a B d_idx) s' := by
  intro ⟨_, _, _, h_step⟩
  cases h_step
  exact absurd ‹isDeposited s d_idx› h



end EpArch
