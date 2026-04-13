/-
EpArch/RevisionSafety.lean — Revision Safety Meta-Theorems

This module provides meta-theorems guaranteeing that:
1. Adding constraints doesn't invalidate existing implications
2. Extensions preserve the revision gate via forgetful projection
3. Compatible extensions don't silently drift semantics

## Key Properties

RevisionGate is the competition-gate predicate capturing the architectural core claim.
Compatible requires semantic preservation via commuting laws, not mere type equality.

## Purpose

Answer: "If I adopt this architecture and it's later incomplete, do I get stuck?"

Prove: Adding constraints / extending the world does NOT collapse already-proved
revision-gate results, as long as extensions preserve the core interface.

-/

import EpArch.Basic
import EpArch.WorldCtx
import EpArch.LTS

namespace EpArch.RevisionSafety

universe u

/-! ## Premise Strengthening (Assumption Monotonicity)

If `A → Claim` then `(A ∧ B) → Claim`.

This is trivially true but worth stating explicitly:
adding extra constraints cannot invalidate implication theorems,
it only narrows their applicability.
-/

/-- Premise strengthening: adding constraints preserves implications.

    If a claim follows from assumption A, it also follows from A ∧ B.
    This is the fundamental revision-safety property. -/
theorem premise_strengthening {A B Claim : Prop} :
    (A → Claim) → ((A ∧ B) → Claim) := by
  intro h_impl ⟨h_A, _⟩
  exact h_impl h_A

/-- Premise strengthening for dependent props.

    More general version for type-indexed claims. -/
theorem premise_strengthening_dep {α : Type u} {A B : α → Prop} {Claim : Prop} :
    (∀ x, A x → Claim) → (∀ x, A x ∧ B x → Claim) := by
  intro h_impl x ⟨h_A, _⟩
  exact h_impl x h_A

/-- Chained strengthening: can add multiple constraints. -/
theorem premise_chain {A B C Claim : Prop} :
    (A → Claim) → ((A ∧ B ∧ C) → Claim) := by
  intro h_impl ⟨h_A, _, _⟩
  exact h_impl h_A


/-! ## Core Signature

The core signature defines what operations matter for revision-gate claims.
-/

/--
## Core Primitives (Single Canonical Definition)

This is the **ONLY** canonical list of primitives that `Compatible` must commute.
Any extension claiming compatibility must preserve these semantics exactly.

### Frozen Core Surface

This is the revision-gate core surface. All primitives listed here are load-bearing
for the formalization's core architectural claims. Extensions must preserve all of them.

**Primitive Types (CoreSig):**
1. `Agent` — Economic actors
2. `Claim` — Propositions / audit targets
3. `Bubble` — Truth-containing bounded regions
4. `Time` — Verification cost / duration
5. `Deposit` — Epistemic claims with governance status
6. `Header` — Minimal verifiable commitment

**World Primitives (from WorldCtx):**
1. `truth` — Bubble truth relation (B ⊢ d)
2. `obs` — Observability predicate
3. `verifyWithin` — Time-bounded verification
4. `effectiveTime` — Resource capacity at bubble (for bounded verification)

**Bank Primitives (submission/revision cycle):**
5. `deposit_header` — Extract header from deposit
6. `submit` — Submit a deposit for acceptance (Candidate → Validated path)
7. `revise` — Revise a deposit in response to challenge (Repair_B semantics)

**Capability Predicates:**
8. `hasRevision` — Revision capability (bubble can process revisions)
9. `selfCorrects` — Self-correction property (system health)

**Compatibility Contract:**
Extensions must provide commuting diagrams for 8 of 9 CoreOps
(all except deposit_header, which has no Header projection in Compatible).
See `Compatible` structure for the precise formulation.
-/
abbrev CorePrims : List String :=
  ["truth", "obs", "verifyWithin", "effectiveTime",
   "deposit_header", "submit", "revise",
   "hasRevision", "selfCorrects"]

/-- Core signature: the type structure of core models. -/
structure CoreSig where
  /-- Agent type -/
  Agent : Type u
  /-- Claim/Proposition type -/
  Claim : Type u
  /-- Bubble type -/
  Bubble : Type u
  /-- Time type -/
  Time : Type u
  /-- Deposit type -/
  Deposit : Type u
  /-- Header type -/
  Header : Type u

/-- Core operations: the semantic content of core models.

    These operations constitute the frozen core surface.
    Any Compatible extension must preserve all of them via commuting laws. -/
structure CoreOps (Sig : CoreSig) where
  /-- Deposit → Header projection -/
  deposit_header : Sig.Deposit → Sig.Header

  -- World primitives (from WorldCtx)
  /-- Truth in bubble: B ⊢ d -/
  truth : Sig.Bubble → Sig.Deposit → Prop
  /-- Observability: d is externally checkable -/
  obs : Sig.Deposit → Prop
  /-- Verify within time: can check d in B within τ -/
  verifyWithin : Sig.Bubble → Sig.Deposit → Sig.Time → Prop
  /-- Resource capacity at bubble (effectiveTime from WorldCtx) -/
  effectiveTime : Sig.Bubble → Sig.Time

  -- Bank primitives (submission/revision cycle)
  /-- Submit: deposit enters acceptance pipeline (Candidate → validation path) -/
  submit : Sig.Agent → Sig.Bubble → Sig.Deposit → Prop
  /-- Revise: deposit is revised in response to challenge -/
  revise : Sig.Bubble → Sig.Deposit → Sig.Deposit → Prop

  -- Capability predicates
  /-- Has revision capability -/
  hasRevision : Sig.Bubble → Prop
  /-- Can self-correct -/
  selfCorrects : Sig.Bubble → Prop

/-- A core model: signature + operations + non-triviality. -/
structure CoreModel where
  sig : CoreSig
  ops : CoreOps sig
  /-- Non-triviality: at least one bubble exists -/
  hasBubble : Nonempty sig.Bubble


/-! ## RevisionGate

RevisionGate is a real predicate, not `True`.
A model satisfies the revision gate if it satisfies the core architectural invariant.
-/

/-- RevisionGate: the competition-gate predicate.

    A model satisfies the revision gate if selfCorrects B → hasRevision B for all bubbles.
    (Header projection and non-triviality are structural guarantees of CoreModel.) -/
def RevisionGate (M : CoreModel) : Prop :=
  -- Competition Gate: revision is necessary for self-correction
  ∀ B : M.sig.Bubble, M.ops.selfCorrects B → M.ops.hasRevision B


/-! ## Compatible Extensions

Compatible is not mere type equality.
It requires semantic preservation: operations commute with projection.
-/

/-- Extended signature: adds extra structure to core. -/
structure ExtSig extends CoreSig where
  /-- Extra agent state -/
  AgentExtra : Type u
  /-- Extra world state -/
  WorldExtra : Type u

/-- Extended operations: includes extra-state operations. -/
structure ExtOps (ESig : ExtSig) extends CoreOps ESig.toCoreSig where
  /-- Extra: get agent's extra state -/
  getAgentExtra : ESig.Agent → ESig.AgentExtra
  /-- Extra: get world's extra state -/
  getWorldExtra : ESig.WorldExtra

/-- Extended model: full extension with operations and non-triviality. -/
structure ExtModel where
  sig : ExtSig
  ops : ExtOps sig
  hasBubble : Nonempty sig.Bubble

/-- Forgetful projection on signatures: ExtSig → CoreSig. -/
def forgetSig (E : ExtSig) : CoreSig where
  Agent := E.Agent
  Claim := E.Claim
  Bubble := E.Bubble
  Time := E.Time
  Deposit := E.Deposit
  Header := E.Header

/-- Forgetful projection on models: ExtModel → CoreModel.

    Forgets the extra structure, preserving only core primitives. -/
def forget (E : ExtModel) : CoreModel where
  sig := forgetSig E.sig
  ops := {
    deposit_header := E.ops.deposit_header
    truth := E.ops.truth
    obs := E.ops.obs
    verifyWithin := E.ops.verifyWithin
    effectiveTime := E.ops.effectiveTime
    submit := E.ops.submit
    revise := E.ops.revise
    hasRevision := E.ops.hasRevision
    selfCorrects := E.ops.selfCorrects
  }
  hasBubble := E.hasBubble

/-- Compatibility witness: semantic preservation between E and C.

    Compatible requires that core operations commute
    with explicit projection maps, not just type equality.

    The projection maps relate extended types to core types:
    - πBubble : E.Bubble → C.Bubble
    - πDeposit : E.Deposit → C.Deposit
    - πAgent : E.Agent → C.Agent
    - πTime : E.Time → C.Time

    The commuting laws ensure operations behave the same when projected.
    8 of the 9 core operations must commute (deposit_header is excluded;
    no Header projection is needed). -/
structure Compatible (E : ExtModel) (C : CoreModel) where
  /-- Projection on Bubble -/
  πBubble : E.sig.Bubble → C.sig.Bubble
  /-- Projection on Deposit -/
  πDeposit : E.sig.Deposit → C.sig.Deposit
  /-- Projection on Time -/
  πTime : E.sig.Time → C.sig.Time
  /-- Projection on Agent -/
  πAgent : E.sig.Agent → C.sig.Agent

  -- World primitive commuting laws
  /-- Commuting law: truth relation commutes with projection -/
  truth_comm : ∀ (B : E.sig.Bubble) (d : E.sig.Deposit),
    E.ops.truth B d ↔ C.ops.truth (πBubble B) (πDeposit d)
  /-- Commuting law: observation predicate commutes with projection -/
  obs_comm : ∀ (d : E.sig.Deposit),
    E.ops.obs d ↔ C.ops.obs (πDeposit d)
  /-- Commuting law: verification commutes with projection -/
  verifyWithin_comm : ∀ (B : E.sig.Bubble) (d : E.sig.Deposit) (t : E.sig.Time),
    E.ops.verifyWithin B d t ↔ C.ops.verifyWithin (πBubble B) (πDeposit d) (πTime t)
  /-- Commuting law: effectiveTime commutes with projection -/
  effectiveTime_comm : ∀ (B : E.sig.Bubble),
    πTime (E.ops.effectiveTime B) = C.ops.effectiveTime (πBubble B)

  -- Bank primitive commuting laws
  /-- Commuting law: submit commutes with projection -/
  submit_comm : ∀ (a : E.sig.Agent) (B : E.sig.Bubble) (d : E.sig.Deposit),
    E.ops.submit a B d ↔ C.ops.submit (πAgent a) (πBubble B) (πDeposit d)
  /-- Commuting law: revise commutes with projection -/
  revise_comm : ∀ (B : E.sig.Bubble) (d d' : E.sig.Deposit),
    E.ops.revise B d d' ↔ C.ops.revise (πBubble B) (πDeposit d) (πDeposit d')

  -- Capability predicate commuting laws
  /-- Commuting law: hasRevision commutes with projection -/
  hasRevision_comm : ∀ (B : E.sig.Bubble),
    E.ops.hasRevision B ↔ C.ops.hasRevision (πBubble B)
  /-- Commuting law: selfCorrects commutes with projection -/
  selfCorrects_comm : ∀ (B : E.sig.Bubble),
    E.ops.selfCorrects B ↔ C.ops.selfCorrects (πBubble B)


/-! ## Transport Theorem

If E is compatible with C, and C satisfies the revision gate,
then the forgetful projection of E also satisfies the revision gate.

The proof uses the commuting laws to transfer the competition gate property.
-/

/-- Transport: Compatible extensions preserve the revision gate.

    This is a real proof using commuting laws, not trivial record equality.

    The proof works by:
    1. Given: C satisfies competition gate (selfCorrects → hasRevision)
    2. Want: forget E satisfies competition gate
    3. Use commuting laws to transfer the property

    The key insight: RevisionGate (forget E) unfolds to a statement about
    E.ops.selfCorrects and E.ops.hasRevision. The commuting laws let us
    transfer these to C, apply C's revision gate property, and transfer back. -/
theorem transport_core (E : ExtModel) (C : CoreModel) (h : Compatible E C) :
    RevisionGate C → RevisionGate (forget E) := by
  intro h_gate_C
  -- RevisionGate (forget E) means: ∀ B, (forget E).ops.selfCorrects B → (forget E).ops.hasRevision B
  -- By definition of forget: (forget E).ops.selfCorrects = E.ops.selfCorrects
  unfold RevisionGate
  intro B_E h_sc_E
  -- h_sc_E : E.ops.selfCorrects B_E
  -- Need: E.ops.hasRevision B_E

  -- Step 1: Transfer to C using commuting laws
  have h_sc_C : C.ops.selfCorrects (h.πBubble B_E) := h.selfCorrects_comm B_E |>.mp h_sc_E

  -- Step 2: Apply revision-gate property of C
  have h_hr_C : C.ops.hasRevision (h.πBubble B_E) := h_gate_C (h.πBubble B_E) h_sc_C

  -- Step 3: Transfer back using hasRevision_comm
  exact h.hasRevision_comm B_E |>.mpr h_hr_C


/-! ## Safe Extensions

A revision-safe extension combines compatibility with consistency.
-/

/-- Revision-safe extension: compatible and consistent. -/
structure RevisionSafeExtension (C : CoreModel) where
  ext : ExtModel
  compat : Compatible ext C
  /-- Consistency: extension has a model (non-triviality witnessed by hasBubble) -/
  consistent : True  -- Already witnessed by ext.hasBubble

/-- Safe extensions preserve all revision gate results. -/
theorem safe_extension_preserves (C : CoreModel) (R : RevisionSafeExtension C) :
    RevisionGate C → RevisionGate (forget R.ext) :=
  transport_core R.ext C R.compat


/-! ## Refinement Preservation

Safety properties are preserved under refinement.
This is proved in LTS.lean using trace semantics.
-/

/-- Refinement relation for CoreModels via LTS semantics.

    R refines C if R has fewer behaviors than C (trace inclusion).
    This is expressed via an LTS.Refinement between their operational semantics. -/
structure RefinesWith (R C : CoreModel) where
  /-- State type for both LTSs -/
  StateType : Type u
  /-- Action type for both LTSs -/
  ActionType : Type u
  /-- LTS for the core model -/
  core_lts : LTS.LTS StateType ActionType
  /-- LTS for the refined model -/
  refined_lts : LTS.LTS StateType ActionType
  /-- Refinement witness -/
  refinement : LTS.Refinement core_lts refined_lts

/-- Safety properties are preserved under refinement.

    **KEY THEOREM**: Proved using LTS.safety_preserved_under_refinement.

    If C satisfies a safety property (invariant under transitions) and R refines C,
    then R satisfies the same property (pulled back via the refinement map). -/
theorem safety_preserved_under_contract_refinement {R C : CoreModel}
    (h_refines : RefinesWith R C)
    {Safety : h_refines.StateType → Prop}
    (h_invariant : LTS.IsInvariant h_refines.core_lts Safety) :
    LTS.IsInvariant h_refines.refined_lts (Safety ∘ h_refines.refinement.φ) :=
  LTS.safety_preserved_under_refinement h_refines.refinement h_invariant


/-! ## Acceptance Tests

These examples demonstrate that Compatible is a REAL constraint:
- Good extensions: preserve operations, commuting laws hold
- Bad extensions: change operations, CANNOT provide Compatible witness

This is the key diagnostic: the contract blocks semantic-breaking extensions.
-/

section AcceptanceTests

variable (C : CoreModel)

/-- **GOOD Extension**: Add extra state, preserve operations.

    This extension adds WorldExtra but copies all ops from C.
    Compatible holds because all commuting laws are Iff.refl. -/
def goodExtension (WorldExtra : Type) [Inhabited WorldExtra] : ExtModel where
  sig := {
    Agent := C.sig.Agent
    Claim := C.sig.Claim
    Bubble := C.sig.Bubble
    Time := C.sig.Time
    Deposit := C.sig.Deposit
    Header := C.sig.Header
    AgentExtra := Unit
    WorldExtra := WorldExtra
  }
  ops := {
    deposit_header := C.ops.deposit_header
    truth := C.ops.truth
    obs := C.ops.obs
    verifyWithin := C.ops.verifyWithin
    effectiveTime := C.ops.effectiveTime
    submit := C.ops.submit
    revise := C.ops.revise
    hasRevision := C.ops.hasRevision
    selfCorrects := C.ops.selfCorrects  -- PRESERVED
    getAgentExtra := fun _ => ()
    getWorldExtra := default
  }
  hasBubble := C.hasBubble

/-- Good extension passes Compatible: all commuting laws hold. -/
theorem goodExtension_compatible (WorldExtra : Type) [Inhabited WorldExtra] :
    Compatible (goodExtension C WorldExtra) C where
  πBubble := id
  πDeposit := id
  πTime := id
  πAgent := id
  truth_comm := fun _ _ => Iff.refl _
  obs_comm := fun _ => Iff.refl _
  verifyWithin_comm := fun _ _ _ => Iff.refl _
  effectiveTime_comm := fun _ => rfl
  submit_comm := fun _ _ _ => Iff.refl _
  revise_comm := fun _ _ _ => Iff.refl _
  hasRevision_comm := fun _ => Iff.refl _
  selfCorrects_comm := fun _ => Iff.refl _  -- ✓ Works because ops unchanged

/-- **BAD Extension**: Change selfCorrects semantics.

    This extension modifies selfCorrects to always return True.
    This BREAKS the competition gate: selfCorrects B holds even when hasRevision B doesn't.

    CRITICAL: This extension CANNOT satisfy Compatible with any C where
    C.ops.selfCorrects is not constantly True. The selfCorrects_comm law fails! -/
def badExtension : ExtModel where
  sig := {
    Agent := C.sig.Agent
    Claim := C.sig.Claim
    Bubble := C.sig.Bubble
    Time := C.sig.Time
    Deposit := C.sig.Deposit
    Header := C.sig.Header
    AgentExtra := Unit
    WorldExtra := Unit
  }
  ops := {
    deposit_header := C.ops.deposit_header
    truth := C.ops.truth
    obs := C.ops.obs
    verifyWithin := C.ops.verifyWithin
    effectiveTime := C.ops.effectiveTime
    submit := C.ops.submit
    revise := C.ops.revise
    hasRevision := C.ops.hasRevision
    selfCorrects := fun _ => True  -- ⚠️ CHANGED: always True!
    getAgentExtra := fun _ => ()
    getWorldExtra := ()
  }
  hasBubble := C.hasBubble

/-- Bad extension FAILS Compatible (diagnostic).

    To demonstrate, we show that IF Compatible held, we'd have a contradiction
    for any C with a bubble where selfCorrects doesn't hold.

    The key insight: Compatible requires selfCorrects_comm to hold FOR ALL bubbles.
    For badExtension, selfCorrects is always True.
    So selfCorrects_comm requires: True ↔ C.ops.selfCorrects (πBubble B)
    This means C.ops.selfCorrects (πBubble B) must be True for ALL B.

    But if C has ANY bubble B' where selfCorrects doesn't hold, and πBubble maps
    some B to B', then we get a contradiction.

    This is the KEY DIAGNOSTIC: semantic-breaking extensions are blocked. -/
theorem badExtension_incompatible_witness
    (h_compat : Compatible (badExtension C) C)
    (B : C.sig.Bubble) (h_not_sc : ¬ C.ops.selfCorrects B)
    (h_surj : ∃ B', h_compat.πBubble B' = B) : False := by
  -- Find a B' that maps to B
  match h_surj with
  | ⟨B', h_eq⟩ =>
    -- badExtension always says selfCorrects is True
    have h_bad_sc : (badExtension C).ops.selfCorrects B' := True.intro
    -- By selfCorrects_comm: True ↔ C.selfCorrects (πBubble B')
    have h_comm := h_compat.selfCorrects_comm B'
    have h_sc_π : C.ops.selfCorrects (h_compat.πBubble B') := h_comm.mp h_bad_sc
    -- But πBubble B' = B, so C.selfCorrects B
    rw [h_eq] at h_sc_π
    exact h_not_sc h_sc_π

/-- Corollary: If πBubble is surjective and C has a non-self-correcting bubble,
    badExtension is incompatible.

    For the common case where πBubble = id (identity), surjectivity is trivial. -/
theorem badExtension_incompatible_if_id
    (h_compat : Compatible (badExtension C) C)
    (h_π_id : ∀ B, h_compat.πBubble B = B)
    (B : C.sig.Bubble) (h_not_sc : ¬ C.ops.selfCorrects B) : False :=
  badExtension_incompatible_witness C h_compat B h_not_sc ⟨B, h_π_id B⟩

end AcceptanceTests


/-! ## Summary: Revision Safety Guarantees

1. **Premise Strengthening**: `premise_strengthening`
   - Adding assumptions never breaks existing implications

2. **RevisionGate**: NOT `True` — real predicate on CoreModel
   - Competition gate must hold

3. **Compatible**: NOT type equality — semantic commuting laws
   - Operations must commute with projection maps
   - **Acceptance tests prove**: bad extensions FAIL Compatible

4. **Transport**: `transport_core`
   - Compatible extensions preserve the revision gate
   - **Real proof**: uses commuting laws, not record equality

5. **Safe Extension**: `safe_extension_preserves`
   - Revision-safe extensions preserve the revision gate

6. **Refinement**: `safety_preserved_under_contract_refinement`
   - Safety properties preserved under trace refinement

These guarantees answer: "Will later constraints break this?" with a Lean theorem.
-/


end EpArch.RevisionSafety
