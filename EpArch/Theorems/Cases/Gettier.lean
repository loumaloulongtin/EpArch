/-
EpArch.Theorems.Cases.Gettier — Gettier Case: V-Independence Failure

Structures and theorems for the Gettier SEV failure mode:
- TruthMaker / ProvenanceChain / VIndependence: the V-disconnect proxy
- GettierCase: structural invariant (tracks_false_certified required at construction)
- gettier_is_V_failure: unconditional; certified at construction time
- canonical_gettier: the Smith/Jones canonical example

Proxy interpretation: `VIndependence.tracks = false` means provenance does not
connect to the truth-maker.  Theorem: GettierInstance → ¬Tracks.

Future work: Richer semantics via causal graphs or modal structures.
-/
import EpArch.Basic
import EpArch.Semantics.StepSemantics

namespace EpArch

open StepSemantics

universe u

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}

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

end EpArch
