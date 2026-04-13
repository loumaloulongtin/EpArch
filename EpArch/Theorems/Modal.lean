/-
EpArch.Theorems.Modal — Modal Condition Subsumption

Safety and sensitivity conditions from modal epistemology, shown to reduce to
V/E field structure via WorldCtx-parameterized case structures.

Canonical forms: SafetyCaseCtx, SensitivityCaseCtx, GettierCaseCtx.
Concrete witnesses: toyCtx four-world model.
-/
import EpArch.Basic
import EpArch.WorldCtx
import EpArch.Theorems.Headers

namespace EpArch

universe u

variable {PropLike Standard ErrorModel Provenance Reason Evidence : Type u}

/-! ## Modal Condition Subsumption

Safety and sensitivity conditions from modal epistemology,
shown to be special cases of V/E field structure.

The canonical forms here are `SafetyCaseCtx` and `SensitivityCaseCtx`: they carry
genuinely universally-quantified predicates over world-relative truth.  The predicates
`v_independent` and `e_covers` are obs-bounded — they quantify over observationally
equivalent worlds rather than all worlds — which gives genuine modus-tollens structure
to `safety_ctx_V_link` and `sensitivity_ctx_E_link` below. -/



/-- Gettier case parameterized over a WorldCtx.
    Carries a structural provenance-disconnection predicate: in any world where P is
    true that is observationally indistinguishable from the actual world,
    that world must differ from the actual world — truth and observation come apart. -/
structure GettierCaseCtx (C : WorldCtx) where
  /-- The actual world (where the Gettier situation obtains) -/
  world         : C.World
  /-- The claim in question -/
  P             : C.Claim
  /-- S-field: claim passes acceptance threshold -/
  S_passes      : Bool
  /-- Structural cert: S clears the threshold in this Gettier case.
      A `GettierCaseCtx` presupposes that S and E both pass (the claim satisfies
      all classical knowledge conditions except V); the epistemic failure is in V alone. -/
  s_passes_cert : S_passes = true
  /-- E-field: error model is locally adequate -/
  E_passes      : Bool
  /-- Structural cert: E is locally adequate in this Gettier case. -/
  e_passes_cert : E_passes = true
  /-- Provenance disconnection: any world where P is true that is obs-equivalent
      to the actual world must differ from the actual world. -/
  provenance_disconnected :
    ∀ w', C.Truth w' P → C.obs w' = C.obs world → w' ≠ world

/-- A system is in a Gettier-profile situation when
    the claim is false in the actual world but true in an obs-equivalent world.
    S and E pass by structural cert; the Gettier condition is the provenance gap alone. -/
def IsGettierCtx (C : WorldCtx) (g : GettierCaseCtx C) : Prop :=
  ¬C.Truth g.world g.P ∧
  ∃ w', C.Truth w' g.P ∧ C.obs w' = C.obs g.world

/-- A Gettier-profile situation exhibits a provenance gap:
    the world where P holds is observationally equivalent to but distinct from
    the actual world.  This uses `provenance_disconnected` — not trivial: constructing
    a `GettierCaseCtx` at `LeanKernelCtx` requires `Bool.noConfusion` to
    prove the field. -/
theorem gettier_ctx_exhibits_provenance_gap (C : WorldCtx) (g : GettierCaseCtx C)
    (h : IsGettierCtx C g) :
    ∃ w', C.Truth w' g.P ∧ C.obs w' = C.obs g.world ∧ w' ≠ g.world := by
  let ⟨_, w', h_truth, h_obs⟩ := h
  exact ⟨w', h_truth, h_obs, g.provenance_disconnected w' h_truth h_obs⟩

/-- Gettier profile (WorldCtx level) yields V-failure: the provenance gap witnesses
    a world where truth and observation come apart.
    This is the canonical statement of the Gettier result using the structural
    WorldCtx-parameterized infrastructure defined above. -/
theorem gettier_profile_yields_V_failure (C : WorldCtx) (g : GettierCaseCtx C)
    (h : IsGettierCtx C g) :
    ∃ w', C.Truth w' g.P ∧ C.obs w' = C.obs g.world ∧ w' ≠ g.world :=
  gettier_ctx_exhibits_provenance_gap C g h

/-- Safety case parameterized over a WorldCtx.
    `obs_aligned` says the actual world and the deposit world are observationally
    co-accessible.  `v_independent` is obs-bounded: truth of P co-varies in all
    obs-equivalent worlds — not rigidly across all worlds. -/
structure SafetyCaseCtx (C : WorldCtx) where
  /-- The actual world -/
  world         : C.World
  /-- The claim being evaluated -/
  P             : C.Claim
  /-- The world from which evidence was gathered -/
  deposit_world : C.World
  /-- Observational alignment: the actual world is obs-equivalent to the deposit world.
      V-independence is only meaningful relative to observable context; obs-alignment
      certifies the two worlds are epistemically co-accessible. -/
  obs_aligned   : C.obs world = C.obs deposit_world
  /-- V-independence: truth of P co-varies with deposit_world in all obs-equivalent worlds.
      Replaces the rigid "P has the same truth in ALL worlds" with the obs-bounded form. -/
  v_independent : ∀ w', C.obs w' = C.obs deposit_world → (C.Truth w' P ↔ C.Truth deposit_world P)

/-- Safety (modal): actual world and deposit world agree on P's truth. -/
def SafetyCtx (C : WorldCtx) (sc : SafetyCaseCtx C) : Prop :=
  C.Truth sc.world sc.P ↔ C.Truth sc.deposit_world sc.P

/-- V-independence (structural): truth of P co-varies with deposit_world in obs-equivalent worlds. -/
def V_indepCtx (C : WorldCtx) (sc : SafetyCaseCtx C) : Prop :=
  ∀ w', C.obs w' = C.obs sc.deposit_world → (C.Truth w' sc.P ↔ C.Truth sc.deposit_world sc.P)

/-- Safety failure implies V-independence failure.
    Proof instantiates `v_independent` at `sc.world` with `sc.obs_aligned` — modus
    tollens that genuinely uses `obs_aligned`; not reducible to `exact h`. -/
theorem safety_ctx_V_link (C : WorldCtx) (sc : SafetyCaseCtx C) :
    ¬SafetyCtx C sc → ¬V_indepCtx C sc := by
  intro h_safety h_vind
  exact h_safety (h_vind sc.world sc.obs_aligned)

/-- Sensitivity case parameterized over a WorldCtx.
    `cf_obs_aligned` says the actual world and counterfactual are obs-equivalent
    (nearby).  `e_covers` is obs-bounded: falsity of P co-varies in obs-equivalent
    worlds only — not globally. -/
structure SensitivityCaseCtx (C : WorldCtx) where
  /-- The actual world -/
  world          : C.World
  /-- The claim being evaluated -/
  P              : C.Claim
  /-- The nearest counterfactual (where P is false) -/
  counterfactual : C.World
  /-- Observational alignment: actual world and counterfactual are obs-equivalent.
      Sensitivity concerns nearby worlds; obs-alignment captures nearness. -/
  cf_obs_aligned : C.obs world = C.obs counterfactual
  /-- E-coverage: falsity of P co-varies with counterfactual in all obs-equivalent worlds.
      Replaces the rigid global-covariation form with the obs-bounded form. -/
  e_covers : ∀ w', C.obs w' = C.obs counterfactual → ((¬C.Truth w' P) ↔ (¬C.Truth counterfactual P))

/-- Sensitivity (modal): falsity of P is consistent between actual and counterfactual. -/
def SensitivityCtx (C : WorldCtx) (sc : SensitivityCaseCtx C) : Prop :=
  ¬C.Truth sc.world sc.P ↔ ¬C.Truth sc.counterfactual sc.P

/-- E-covers-counterfactual (structural): falsity of P co-varies in obs-equivalent worlds. -/
def E_counterfactualCtx (C : WorldCtx) (sc : SensitivityCaseCtx C) : Prop :=
  ∀ w', C.obs w' = C.obs sc.counterfactual → ((¬C.Truth w' sc.P) ↔ (¬C.Truth sc.counterfactual sc.P))

/-- Sensitivity failure implies E-coverage gap.
    Proof instantiates `e_covers` at `sc.world` with `sc.cf_obs_aligned` — analogous
    to `safety_ctx_V_link`; uses `cf_obs_aligned` genuinely. -/
theorem sensitivity_ctx_E_link (C : WorldCtx) (sc : SensitivityCaseCtx C) :
    ¬SensitivityCtx C sc → ¬E_counterfactualCtx C sc := by
  intro h_sens h_ecov
  exact h_sens (h_ecov sc.world sc.cf_obs_aligned)


/-! ## Toy WorldCtx: Concrete Safety / Sensitivity Witnesses

A minimal four-world concrete instantiation of `WorldCtx`.  Purpose: give
`SafetyCaseCtx` and `SensitivityCaseCtx` inhabited non-trivial examples so
that `safety_ctx_V_link` and `sensitivity_ctx_E_link` are demonstrated at a
specific model, not just abstract theorems.

World layout (2×2):
- `w0`, `w1` → obs-class 0, P is **True**   (the "actual" cluster)
- `w2`, `w3` → obs-class 1, P is **False**  (the "counterfactual" cluster)

This structure means obs-equivalence preserves P-truth within each class.
Safety case uses `(world = w0, deposit_world = w1)`: same class, `obs_aligned = rfl`.
`v_independent` is proved by a 4-way case split — discarding obs-1 worlds via
`absurd h (by decide)`.  `Iff.rfl` closes the obs-0 cases because both worlds
have the same `toyTruth` value.

Sensitivity case uses `(world = w2, counterfactual = w3)`: symmetric. -/

private inductive ToyWorld | w0 | w1 | w2 | w3 deriving DecidableEq, Repr

/-- Obs map: w0/w1 → 0 (actual cluster); w2/w3 → 1 (counterfactual cluster). -/
private def toyObs : ToyWorld → Fin 2
  | .w0 | .w1 => 0
  | .w2 | .w3 => 1

/-- Truth: P is True in the actual cluster (obs 0) and False in the counterfactual cluster (obs 1). -/
private def toyTruth : ToyWorld → Unit → Prop
  | .w0 | .w1 => fun _ => True
  | .w2 | .w3 => fun _ => False

/-- The concrete four-world WorldCtx.
    `@[reducible]` makes field accesses (`toyCtx.obs`, `toyCtx.Truth`, etc.) transparent
    so that proofs like `absurd h (by decide)` can reduce through the struct. -/
@[reducible] def toyCtx : WorldCtx :=
  { World          := ToyWorld,
    Agent          := Unit,
    Claim          := Unit,
    Obs            := Fin 2,
    Truth          := toyTruth,
    Utter          := fun _ _ => True,
    obs            := toyObs,
    VerifyWithin   := fun _ _ _ => True,
    effectiveTime  := fun _ => 0,
    world_inhabited := ⟨.w0⟩,
    agent_inhabited := ⟨()⟩,
    claim_inhabited := ⟨()⟩ }

/-- Concrete safety case: `world = w0`, `deposit_world = w1` (distinct, same obs-class).
    `obs_aligned = rfl` (both map to 0).
    `v_independent`: proved by a 4-way case split on `ToyWorld`, discarding obs-1
    worlds via `absurd h (by decide)` and closing obs-0 cases via `Iff.rfl`. -/
def toySafetyCase : SafetyCaseCtx toyCtx :=
  { world         := .w0,
    P             := (),
    deposit_world := .w1,
    obs_aligned   := rfl,
    v_independent := fun w' h =>
      match w' with
      | .w0 => Iff.rfl
      | .w1 => Iff.rfl
      | .w2 => absurd h (by decide)
      | .w3 => absurd h (by decide) }

/-- Safety holds for the toy safety case: V-independence implies agreement on P.
    Proof: apply `v_independent` at `world = w0` with `obs_aligned = rfl`. -/
theorem toy_safety_holds : SafetyCtx toyCtx toySafetyCase :=
  toySafetyCase.v_independent .w0 rfl

/-- Concrete sensitivity case: `world = w2`, `counterfactual = w3` (distinct, same obs-class 1).
    `cf_obs_aligned = rfl`.  `e_covers`: 4-way case split symmetric to `v_independent`. -/
def toySensitivityCase : SensitivityCaseCtx toyCtx :=
  { world          := .w2,
    P              := (),
    counterfactual := .w3,
    cf_obs_aligned := rfl,
    e_covers := fun w' h =>
      match w' with
      | .w0 => absurd h (by decide)
      | .w1 => absurd h (by decide)
      | .w2 => Iff.rfl
      | .w3 => Iff.rfl }

/-- Sensitivity holds for the toy sensitivity case: E-coverage implies agreement on ¬P.
    Proof: apply `e_covers` at `world = w2` with `cf_obs_aligned = rfl`. -/
theorem toy_sensitivity_holds : SensitivityCtx toyCtx toySensitivityCase :=
  toySensitivityCase.e_covers .w2 rfl



end EpArch
