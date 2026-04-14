/-
EpArch.Theorems.Cases.VacuousStandard — Vacuous Standard Case: S Voided by E + V Interaction

Structures and theorems for the absolute (non-relational) S-failure mode:
- ReliabilityTag / SourceReliability: typed source-reliability witness
- TestimonyMode / VacuousStandardCase: S grounded in testimony from a documented-unreliable source
- vacuous_standard_is_S_failure: unconditional; structural fields certified at construction
- canonical_liar_cook_case: the "known-liar cook" canonical example
- absolute_vs_relational_S_failure: contrasts the two kinds of S-failure

Setup — the known-liar cook:
- V: provenance genuinely traces to the cook. V is accurate and honest.
- E: our error model explicitly documents "cook is a known liar." E is sound.
- S: "the cook said it." Standard = source testimony.

E and V are both *correct*. Their correct content jointly witnesses that S carries
a structural void. This demonstrates field independence: S can be broken while E and V
are doing their jobs perfectly.

Contrast with Standard.lean (relational S-failure):
- Relational: what makes the deposit pass or fail differs per consuming agent.
- Absolute/void: the two structural conditions are present in the fields
  regardless of which agent inspects the deposit.

Repair in both cases localizes to S.
-/
import EpArch.Basic
import EpArch.Semantics.StepSemantics
import EpArch.Theorems.Cases.Standard

namespace EpArch

open StepSemantics

universe u

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}

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

end EpArch
