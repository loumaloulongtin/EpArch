/-
EpArch/Meta/Tier4Transport.lean — Tier 4 Transport Closure

Closes the DOCS/MODULARITY.md Tier 4 gap by showing that the three remaining
theorem clusters in the main library (Theorems.lean, Commitments.lean) are
transport-safe by established mechanisms.

## The Three Clusters

### Cluster A — CommitmentsCtx-parameterized theorems

These are theorems of shape `(C : CommitmentsCtx ...) → ... → Claim`.
Adding more commitments to a context never invalidates theorems proved under
the sub-context — this follows from `premise_strengthening` in
`RevisionSafety.lean`, which is already proved.

We package this as `commitments_transport` and `commitments_transport_pack`.

### Cluster B — Standalone structural theorems

Theorems `SEVFactorization`, `TemporalValidity`, `monolithic_not_injective`,
`header_stripping_harder` carry no world, commitment, or ops hypothesis.
They are universally valid — no transport mechanism is needed.

We package this as `structural_theorems_unconditional`.

### Cluster C — Concrete bank = CoreModel bridge

Shows that the concrete EpArch bank types form a valid `CoreModel`
instantiation (`ConcreteBankModel`). This makes the transport machinery from
`Meta/TheoremTransport.lean` apply to the concrete operational layer:
any compatible extension of the bank preserves health goals.

## Coverage Table

| Cluster | Mechanism | Theorem |
|---|---|---|
| CommitmentsCtx-parameterized | `premise_strengthening` projection | `commitments_transport_pack` |
| Standalone structural | Unconditional (no transport needed) | `structural_theorems_unconditional` |
| Concrete bank bridge | `ConcreteBankModel` : CoreModel | `ConcreteBankModel`, `concrete_bank_vacuous_pf` |
| Compatible bank extension | `transport_self_correction` | `concrete_bank_transport` |
| Full Tier 4 pack | All three combined | `tier4_transport_pack` |

-/

import EpArch.Commitments
import EpArch.Meta.TheoremTransport

namespace EpArch.Meta.Tier4Transport

open RevisionSafety
open EpArch.Meta.TheoremTransport

variable {PropLike Standard ErrorModel Provenance : Type}


/-! ## §1  Cluster A: CommitmentsCtx Transport -/

/-- An extended CommitmentsCtx: the original four fields plus one additional
    architectural commitment (proof-relevant). -/
structure ExtCommitmentsCtx
    (PropLike Standard ErrorModel Provenance : Type u) (Extra : Prop)
    extends CommitmentsCtx PropLike Standard ErrorModel Provenance where
  /-- The extra commitment -/
  extra : Extra

/-- Generic CommitmentsCtx transport:
    any predicate proved under CommitmentsCtx survives extension. -/
theorem commitments_transport
    {Claim : Prop}
    {Extra : Prop}
    (h_proof : CommitmentsCtx PropLike Standard ErrorModel Provenance → Claim)
    (E : ExtCommitmentsCtx PropLike Standard ErrorModel Provenance Extra) :
    Claim :=
  h_proof E.toCommitmentsCtx

/-- CommitmentsCtx transport pack — all four canonical forward theorems survive
    extension to any larger context. -/
theorem commitments_transport_pack
    {Extra : Prop}
    (E : ExtCommitmentsCtx PropLike Standard ErrorModel Provenance Extra) :
    (∀ (a : Agent) (B : Bubble) (P : Claim),
        ∃ (_ : certainty_L a P), ¬knowledge_B B P) ∧
    (∀ (a : Agent) (B : Bubble) (P : Claim),
        ∃ (_ : knowledge_B B P), ¬certainty_L a P) ∧
    (∀ G : GlobalLedger, supports_innovation G → ¬supports_coordination G) ∧
    (∀ (B : Bubble) (d : Deposit PropLike Standard ErrorModel Provenance),
        ∃ (_ : consensus B d.P), ¬redeemable d) :=
  ⟨fun a B P => certainty_insufficient_for_authorization E.toCommitmentsCtx a B P,
   fun a B P => authorization_insufficient_for_certainty E.toCommitmentsCtx a B P,
   fun G => innovation_excludes_coordination E.toCommitmentsCtx G,
   fun B d => redeemability_requires_more_than_consensus E.toCommitmentsCtx B d⟩


/-! ## §2  Cluster B: Standalone Structural Theorems -/

/-- Structural theorems are transport-vacuous: they hold in every sub-bundle.

    (1) SEV factorization
    (2) Temporal validity
    (3) Monolithic non-injectivity
    (4) Header-stripped diagnosability is lower -/
theorem structural_theorems_unconditional :
    (∀ (d : Deposit PropLike Standard ErrorModel Provenance),
        ∃ (s : Standard) (e : ErrorModel) (v : Provenance),
          d.h.S = s ∧ d.h.E = e ∧ d.h.V = v) ∧
    (∀ (d1 d2 : Deposit PropLike Standard ErrorModel Provenance),
        refreshed d1 → unrefreshed d2 → ¬performs_equivalently d1 d2) ∧
    (¬∀ f1 f2 : FailureField, FailMonolithic f1 = FailMonolithic f2 → f1 = f2) ∧
    systematically_harder header_preserved_diagnosability header_stripped_diagnosability :=
  ⟨SEVFactorization, TemporalValidity, monolithic_not_injective, header_stripping_harder⟩


/-! ## §3  Cluster C: Concrete Bank = CoreModel Bridge -/

/-- `ConcreteBankModel`: a `CoreModel` whose signature uses the concrete EpArch
    bank types and whose operations are supplied as parameters.

    The caller provides world-layer and bank-layer predicates
    (e.g. from WorldCtx.Truth or StepSemantics.Step).
    `deposit_header` is fixed as the structural projection `d.h`. -/
noncomputable def ConcreteBankModel
    (truth_pred    : Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop)
    (obs_pred      : Deposit PropLike Standard ErrorModel Provenance → Prop)
    (verify_pred   : Bubble → Deposit PropLike Standard ErrorModel Provenance → Time → Prop)
    (etime         : Bubble → Time)
    (submit_pred   : Agent → Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop)
    (revise_pred   : Bubble → Deposit PropLike Standard ErrorModel Provenance →
                     Deposit PropLike Standard ErrorModel Provenance → Prop)
    (hasRev_pred   : Bubble → Prop)
    (selfCorr_pred : Bubble → Prop)
    : CoreModel where
  sig := {
    Agent   := EpArch.Agent
    Claim   := PropLike
    Bubble  := EpArch.Bubble
    Time    := EpArch.Time
    Deposit := EpArch.Deposit PropLike Standard ErrorModel Provenance
    Header  := EpArch.Header Standard ErrorModel Provenance
  }
  ops := {
    deposit_header := fun d => d.h
    truth          := truth_pred
    obs            := obs_pred
    verifyWithin   := verify_pred
    effectiveTime  := etime
    submit         := submit_pred
    revise         := revise_pred
    hasRevision    := hasRev_pred
    selfCorrects   := selfCorr_pred
  }
  hasBubble := ⟨default⟩

/-- `ConcreteBankModel` with `selfCorrects := fun _ => False` is PaperFacing.
    The competition gate holds vacuously since the premise is always False. -/
theorem concrete_bank_vacuous_pf
    (truth_pred  : Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop)
    (obs_pred    : Deposit PropLike Standard ErrorModel Provenance → Prop)
    (verify_pred : Bubble → Deposit PropLike Standard ErrorModel Provenance → Time → Prop)
    (etime       : Bubble → Time)
    (submit_pred : Agent → Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop)
    (revise_pred : Bubble → Deposit PropLike Standard ErrorModel Provenance →
                   Deposit PropLike Standard ErrorModel Provenance → Prop)
    (hasRev_pred : Bubble → Prop) :
    PaperFacing (ConcreteBankModel truth_pred obs_pred verify_pred etime
                   submit_pred revise_pred hasRev_pred (fun _ => False)) :=
  fun _B h_sc => h_sc.elim

/-- Compatible extensions of `ConcreteBankModel` preserve `PaperFacing`.
    Direct application of `transport_self_correction`. -/
theorem concrete_bank_transport
    (truth_pred    : Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop)
    (obs_pred      : Deposit PropLike Standard ErrorModel Provenance → Prop)
    (verify_pred   : Bubble → Deposit PropLike Standard ErrorModel Provenance → Time → Prop)
    (etime         : Bubble → Time)
    (submit_pred   : Agent → Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop)
    (revise_pred   : Bubble → Deposit PropLike Standard ErrorModel Provenance →
                     Deposit PropLike Standard ErrorModel Provenance → Prop)
    (hasRev_pred   : Bubble → Prop)
    (selfCorr_pred : Bubble → Prop)
    (E : ExtModel)
    (h_compat : Compatible E
        (ConcreteBankModel truth_pred obs_pred verify_pred etime
           submit_pred revise_pred hasRev_pred selfCorr_pred))
    (h_pf : PaperFacing
        (ConcreteBankModel truth_pred obs_pred verify_pred etime
           submit_pred revise_pred hasRev_pred selfCorr_pred)) :
    PaperFacing (forget E) :=
  transport_self_correction E _ h_compat h_pf

/-- Vacuous concrete bank extension: specialises `concrete_bank_transport` to
    the base case where `selfCorrects` is always False. -/
theorem concrete_bank_vacuous_transport
    (truth_pred  : Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop)
    (obs_pred    : Deposit PropLike Standard ErrorModel Provenance → Prop)
    (verify_pred : Bubble → Deposit PropLike Standard ErrorModel Provenance → Time → Prop)
    (etime       : Bubble → Time)
    (submit_pred : Agent → Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop)
    (revise_pred : Bubble → Deposit PropLike Standard ErrorModel Provenance →
                   Deposit PropLike Standard ErrorModel Provenance → Prop)
    (hasRev_pred : Bubble → Prop)
    (E : ExtModel)
    (h_compat : Compatible E
        (ConcreteBankModel truth_pred obs_pred verify_pred etime
           submit_pred revise_pred hasRev_pred (fun _ => False))) :
    PaperFacing (forget E) :=
  transport_self_correction E _
    h_compat
    (concrete_bank_vacuous_pf truth_pred obs_pred verify_pred etime
       submit_pred revise_pred hasRev_pred)


/-! ## §4  Full Tier 4 Certification -/

/-- `tier4_transport_pack` — complete Tier 4 transport certification.

    Packages all three cluster mechanisms:
    (1) CommitmentsCtx: four canonical forward theorems survive commitment extension.
    (2) Structural: SEVFactorization holds unconditionally.
    (3) Bank bridge: compatible extensions of the concrete bank are PaperFacing. -/
theorem tier4_transport_pack
    {Extra : Prop}
    (CE : ExtCommitmentsCtx PropLike Standard ErrorModel Provenance Extra)
    (truth_pred  : Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop)
    (obs_pred    : Deposit PropLike Standard ErrorModel Provenance → Prop)
    (verify_pred : Bubble → Deposit PropLike Standard ErrorModel Provenance → Time → Prop)
    (etime       : Bubble → Time)
    (submit_pred : Agent → Bubble → Deposit PropLike Standard ErrorModel Provenance → Prop)
    (revise_pred : Bubble → Deposit PropLike Standard ErrorModel Provenance →
                   Deposit PropLike Standard ErrorModel Provenance → Prop)
    (hasRev_pred : Bubble → Prop)
    (E_bank      : ExtModel)
    (h_compat    : Compatible E_bank
        (ConcreteBankModel truth_pred obs_pred verify_pred etime
           submit_pred revise_pred hasRev_pred (fun _ => False))) :
    -- (1) CommitmentsCtx: certainty ≠ authorization survives extension
    (∀ (a : Agent) (B : Bubble) (P : Claim),
        ∃ (_ : certainty_L a P), ¬knowledge_B B P) ∧
    -- (2) Structural: SEV factorization holds unconditionally
    (∀ (d : Deposit PropLike Standard ErrorModel Provenance),
        ∃ (s : Standard) (e : ErrorModel) (v : Provenance),
          d.h.S = s ∧ d.h.E = e ∧ d.h.V = v) ∧
    -- (3) Bank bridge: compatible extensions are PaperFacing
    PaperFacing (forget E_bank) :=
  ⟨fun a B P => certainty_insufficient_for_authorization CE.toCommitmentsCtx a B P,
   SEVFactorization,
   concrete_bank_vacuous_transport truth_pred obs_pred verify_pred etime
     submit_pred revise_pred hasRev_pred E_bank h_compat⟩

end EpArch.Meta.Tier4Transport