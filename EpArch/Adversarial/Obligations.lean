/-
EpArch.Adversarial.Obligations — Obligation Theorems for Adversarial Claims

This module converts adversarial axioms into conditional obligation theorems.
Instead of asserting mechanism claims as axioms, we prove them conditional
on explicit world assumption bundles.

## What Are Obligation Theorems?

Rather than asserting "attacks are possible" as axioms (which would be
unjustified claims about the world), we prove:

  "IF the world has property W, THEN mechanism M is required."

This makes every adversarial claim conditional on explicit, falsifiable
assumptions. The high-level W_* bundles (W_lies_possible, etc.) are defined
in EpArch.WorldCtx; finer-grained attack-specific bundles are defined locally.
EpArch.WorldWitness proves these bundles are satisfiable (non-vacuous).

## Naming Convention

- `X_of_W` = conditional theorem version (proved here)
- `W_X` = minimal assumption bundle for `X_of_W` (defined locally or in EpArch.WorldCtx)
- All W_* bundles use vocabulary from EpArch.Adversarial.Base directly —
  no local shadow types duplicating Base vocabulary.
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank
import EpArch.WorldCtx
import EpArch.Adversarial.Base

namespace EpArch.AdversarialObligations

open EpArch.WorldCtx

universe u

variable {PropLike Standard ErrorModel Provenance : Type u}


/-! ## Verification Path

    PathExists names the abstract structure of a provenance verification path.
    Used in V-spoofing and consultation-suppression theorems. -/

/-- PathExists: there is a verification path to the constraint surface.

    A path exists when:
    1. The provenance chain is intact (V not spoofed)
    2. The chain leads to a constraint surface contact
    3. The contact can be verified within available resources -/
structure PathExists (d : Deposit PropLike Standard ErrorModel Provenance) where
  provenance_intact : Bool
  reaches_constraint : Bool
  verifiable : Bool

def has_path (p : PathExists d) : Prop :=
  p.provenance_intact ∧ p.reaches_constraint ∧ p.verifiable


/-! ## W_spoofedV: V spoofing and consultation suppression block the verification path -/

/-- World assumption: either V spoofing or consultation suppression blocks the
    verification path.

    Uses Base opaques `V_spoof` and `consultation_suppressed` directly — no
    shadow Bool-field types. The two mechanisms are distinct (V_spoof injects
    false provenance; consultation_suppressed blocks real validators) but both
    close the path to the constraint surface.

    Matches `FullStackAttack.attack_succeeds` clause 2: (V_spoofed ∨ consultation_blocked). -/
structure W_spoofedV where
  /-- Spoofed provenance blocks any intact provenance path -/
  spoof_blocks_path : ∀ (d : Deposit PropLike Standard ErrorModel Provenance)
    (p : PathExists d), EpArch.V_spoof d → ¬has_path p
  /-- Consultation suppression also blocks the provenance path -/
  suppression_blocks_path : ∀ (a : EpArch.Agent)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (p : PathExists d), EpArch.consultation_suppressed a → ¬has_path p

/-- Obligation theorem: V spoofing or consultation suppression blocks the path.

    **Proof strategy:** genuine `rcases` dispatching each mechanism to its W field,
    matching `FullStackAttack.attack_succeeds` clause 2 exactly. -/
theorem spoofed_V_blocks_path_of_W
    (W : W_spoofedV (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (a : EpArch.Agent) (p : PathExists d) :
    (EpArch.V_spoof d ∨ EpArch.consultation_suppressed a) → ¬has_path p := by
  intro h
  cases h with
  | inl h_spoof => exact W.spoof_blocks_path d p h_spoof
  | inr h_supp  => exact W.suppression_blocks_path a d p h_supp


/-! ## W_ddos: DDoS attack causes verification collapse -/

/-- World assumption: each DDoS vector causes verification collapse.

    One field per `DDoSVector` constructor, using Base opaques throughout.
    Replaces the shadow `DDoSState`/`CollapsedState` types that duplicated
    Base vocabulary with disconnected Bool-field structures. -/
structure W_ddos where
  /-- Ladder overload: traction forms before V can be checked → verification collapses -/
  ladder_collapses : ∀ (a : EpArch.Agent),
    EpArch.ladder_overloaded a → EpArch.verification_collapsed a
  /-- V-channel exhaustion: provenance checking too costly → verification collapses -/
  V_exhaustion_collapses : ∀ (a : EpArch.Agent),
    EpArch.V_channel_exhausted a → EpArch.verification_collapsed a
  /-- E-field poisoning: ubiquitous noise makes everything uncertain → verification collapses -/
  E_poisoning_collapses : ∀ (a : EpArch.Agent),
    EpArch.E_field_poisoned a → EpArch.verification_collapsed a
  /-- Denial triggering: generalized distrust blocks all external import → verification collapses -/
  denial_collapses : ∀ (a : EpArch.Agent),
    EpArch.denial_triggered a → EpArch.verification_collapsed a

/-- Obligation theorem: any DDoS vector causes verification collapse.

    **Proof strategy:** genuine 4-way `rcases` dispatching each `DDoSVector` branch
    to its per-vector W field. Each branch requires a distinct W field — no single
    field covers all four cases. -/
theorem ddos_causes_verification_collapse_of_W
    (W : W_ddos)
    (a : EpArch.Agent) :
    (EpArch.ladder_overloaded a ∨ EpArch.V_channel_exhausted a ∨
     EpArch.E_field_poisoned a ∨ EpArch.denial_triggered a) →
    EpArch.verification_collapsed a := by
  intro h
  cases h with
  | inl h_ladder => exact W.ladder_collapses a h_ladder
  | inr h =>
    cases h with
    | inl h_V => exact W.V_exhaustion_collapses a h_V
    | inr h =>
      cases h with
      | inl h_E     => exact W.E_poisoning_collapses a h_E
      | inr h_denial => exact W.denial_collapses a h_denial


/-! ## W_collapse_centralization: Verification collapse causes trust centralization -/

/-- World assumption: verification collapse triggers trust centralization (delegation).

    Uses Base opaques `verification_collapsed` and `trust_centralized` directly.
    Replaces the shadow `CollapsedState`/`CentralizedState` types.

    **Implication:** exhausted agents seek a single "trusted" authority — behavioral
    path of least resistance under verification failure. -/
structure W_collapse_centralization where
  /-- Exhaustion triggers delegation: verification failure → centralized trust -/
  exhaustion_triggers_delegation : ∀ (a : EpArch.Agent),
    EpArch.verification_collapsed a → EpArch.trust_centralized a

/-- Obligation theorem: verification collapse causes trust centralization. -/
theorem collapse_causes_centralization_of_W
    (W : W_collapse_centralization)
    (a : EpArch.Agent) :
    EpArch.verification_collapsed a → EpArch.trust_centralized a :=
  W.exhaustion_triggers_delegation a


/-! ## W_lies_scale: Export cost asymmetry -/

/-- World assumption: export costs strictly less than defense.

    Grounded concretely: `c_export_cost = 1 < c_verify_cost d` for any deposit
    with `d.V.length ≥ 1`. See `EpArch.Adversarial.Concrete.concrete_W_lies_scale`
    for the proved instance that discharges this bundle without axioms. -/
structure W_lies_scale where
  /-- Concrete publication cost (steps) -/
  export_cost : Nat
  /-- Concrete verification cost (steps) -/
  defense_cost : Nat
  /-- Asymmetry holds: publication is strictly cheaper than verification -/
  asymmetry_holds : export_cost < defense_cost

/-- Obligation theorem: lies scale — export costs strictly less than defense costs. -/
theorem lies_scale_of_W (W : W_lies_scale) :
    W.export_cost < W.defense_cost :=
  W.asymmetry_holds


/-! ## W_rolex_ddos: Structural equivalence of individual and population attacks -/

/-- Structural equivalence: same exploit pattern at different scales.

    Both Rolex scam and propaganda DDoS exploit bounded audit:
    - Rolex: τ compression blocks individual verification
    - DDoS: channel flooding blocks population verification

    The structure is: overwhelm verification capacity → force acceptance/delegation. -/
structure ExploitStructure where
  overwhelms_verification : Bool
  forces_suboptimal_acceptance : Bool

def same_structure (e1 e2 : ExploitStructure) : Prop :=
  e1.overwhelms_verification = e2.overwhelms_verification ∧
  e1.forces_suboptimal_acceptance = e2.forces_suboptimal_acceptance

/-- World assumption: individual-scale and population-scale attacks share exploit structure.

    Both overwhelm verification capacity and force suboptimal acceptance. -/
structure W_rolex_ddos where
  /-- Individual-scale attack structure -/
  rolex_structure : ExploitStructure
  /-- Population-scale attack structure -/
  ddos_structure : ExploitStructure
  /-- Both overwhelm verification -/
  both_overwhelm : rolex_structure.overwhelms_verification ∧ ddos_structure.overwhelms_verification
  /-- Both force suboptimal acceptance -/
  both_force : rolex_structure.forces_suboptimal_acceptance ∧ ddos_structure.forces_suboptimal_acceptance

/-- Obligation theorem: Rolex-DDoS structural equivalence (conditional version). -/
theorem rolex_ddos_structural_equivalence_of_W (W : W_rolex_ddos) :
    same_structure W.rolex_structure W.ddos_structure := by
  constructor
  · have ⟨h1, h2⟩ := W.both_overwhelm
    simp [h1, h2]
  · have ⟨h1, h2⟩ := W.both_force
    simp [h1, h2]


/-! ## Full Chain: DDoS → Collapse → Centralization -/

/-- Combined world assumptions for full DDoS chain. -/
structure W_ddos_full extends W_ddos, W_collapse_centralization

/-- Obligation theorem: Full DDoS chain — any DDoS vector reaches trust centralization.

    **Proof strategy:** Composes `ddos_causes_verification_collapse_of_W` and
    `collapse_causes_centralization_of_W` sequentially. -/
theorem ddos_to_centralization_of_W
    (W : W_ddos_full)
    (a : EpArch.Agent) :
    (EpArch.ladder_overloaded a ∨ EpArch.V_channel_exhausted a ∨
     EpArch.E_field_poisoned a ∨ EpArch.denial_triggered a) →
    EpArch.trust_centralized a := by
  intro h
  have h_collapsed := ddos_causes_verification_collapse_of_W W.toW_ddos a h
  exact collapse_causes_centralization_of_W W.toW_collapse_centralization a h_collapsed


/-! ## Boundary Condition Countermeasures

These theorems show when attacks fail — the defense conditions.

Key insight: the exploit's power is feasibility control, not counterfeit
perfection. Wherever independent validation is cheap and reachable inside
the decision window, this attack class fails.
-/

/-! ### W_cheap_validator: Cheap validator blocks V-failure attack -/

/-- World assumption: a reachable cheap validator enables verification despite
    V spoofing or consultation suppression.

    Uses Base opaques `cheap_validator_reachable`, `V_spoof`, and
    `consultation_suppressed` directly. -/
structure W_cheap_validator where
  /-- Cheap validator enables check: V spoofing and consultation suppression both fail -/
  cheap_validator_enables_check : ∀ (a : EpArch.Agent) (τ : EpArch.Time)
    (d : Deposit PropLike Standard ErrorModel Provenance),
    EpArch.cheap_validator_reachable a τ →
    ¬(EpArch.V_spoof d ∨ EpArch.consultation_suppressed a)

/-- Obligation theorem: cheap validator blocks the V attack. -/
theorem cheap_validator_blocks_V_attack_of_W
    (W : W_cheap_validator (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (a : EpArch.Agent) (τ : EpArch.Time)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    EpArch.cheap_validator_reachable a τ →
    ¬(EpArch.V_spoof d ∨ EpArch.consultation_suppressed a) :=
  W.cheap_validator_enables_check a τ d


/-! ### W_trust_bridge: Trust bridge blocks V-failure attack -/

/-- World assumption: a pre-established trust bridge provides an alternative
    verification path, defeating V spoofing and consultation suppression.

    Uses Base opaques `trust_bridge_on_hand`, `V_spoof`, and
    `consultation_suppressed` directly. -/
structure W_trust_bridge where
  /-- Trust bridge enables check: V spoofing and consultation suppression both fail -/
  trust_bridge_enables_check : ∀ (a : EpArch.Agent)
    (d : Deposit PropLike Standard ErrorModel Provenance),
    EpArch.trust_bridge_on_hand a →
    ¬(EpArch.V_spoof d ∨ EpArch.consultation_suppressed a)

/-- Obligation theorem: trust bridge blocks the V attack. -/
theorem trust_bridge_blocks_V_attack_of_W
    (W : W_trust_bridge (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (a : EpArch.Agent)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    EpArch.trust_bridge_on_hand a →
    ¬(EpArch.V_spoof d ∨ EpArch.consultation_suppressed a) :=
  W.trust_bridge_enables_check a d


/-! ### W_reversibility: Reversibility neutralizes τ compression -/

/-- World assumption: if a deposit is reversible, τ compression cannot force
    irreversible commitment.

    Uses Base opaques `transaction_reversible` and `τ_compress` directly.
    Reversibility closes the attack vector: even with a compressed decision
    window, the victim can verify and undo after the fact. -/
structure W_reversibility where
  /-- Reversibility prevents τ compression from being effective -/
  reversibility_neutralizes : ∀ (t_orig t_compressed : EpArch.Time)
    (d : Deposit PropLike Standard ErrorModel Provenance),
    EpArch.transaction_reversible d → ¬EpArch.τ_compress t_orig t_compressed

/-- Obligation theorem: reversibility neutralizes τ compression. -/
theorem reversibility_neutralizes_τ_of_W
    (W : W_reversibility (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (t_orig t_compressed : EpArch.Time)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    EpArch.transaction_reversible d → ¬EpArch.τ_compress t_orig t_compressed :=
  W.reversibility_neutralizes t_orig t_compressed d


/-! ### W_E_inclusion: E-field threat modeling closes expertise gap -/

/-- World assumption: if an agent's E-field models the attack pattern,
    the expertise gap cannot be exploited.

    Uses Base opaques `E_includes_threat` and `expertise_gap` directly. -/
structure W_E_inclusion where
  /-- E-field threat modeling closes the expertise gap -/
  E_modeling_closes_gap : ∀ (a : EpArch.Agent),
    EpArch.E_includes_threat a → ¬EpArch.expertise_gap a

/-- Obligation theorem: E-field inclusion closes the expertise gap. -/
theorem E_inclusion_closes_expertise_gap_of_W
    (W : W_E_inclusion)
    (a : EpArch.Agent) :
    EpArch.E_includes_threat a → ¬EpArch.expertise_gap a :=
  W.E_modeling_closes_gap a


/-! ### W_cheap_constraint: Cheaply testable constraint blocks V spoof -/

/-- World assumption: if the constraint surface is cheaply testable, a real
    redeemability check happens within τ, exposing V spoofing and defeating
    consultation suppression.

    Uses Base opaques `constraint_cheaply_testable`, `V_spoof`, and
    `consultation_suppressed` directly. -/
structure W_cheap_constraint where
  /-- Cheap testing exposes spoofed V and defeats consultation suppression -/
  cheap_test_exposes_spoof : ∀ (a : EpArch.Agent)
    (d : Deposit PropLike Standard ErrorModel Provenance),
    EpArch.constraint_cheaply_testable d →
    ¬(EpArch.V_spoof d ∨ EpArch.consultation_suppressed a)

/-- Obligation theorem: cheaply testable constraint blocks V spoof. -/
theorem cheap_constraint_blocks_V_spoof_of_W
    (W : W_cheap_constraint (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (a : EpArch.Agent)
    (d : Deposit PropLike Standard ErrorModel Provenance) :
    EpArch.constraint_cheaply_testable d →
    ¬(EpArch.V_spoof d ∨ EpArch.consultation_suppressed a) :=
  W.cheap_test_exposes_spoof a d


/-! ## Axiom-to-Obligation Summary (Attack Vectors)

| Obligation Theorem | World Bundle |
|---|---|
| `spoofed_V_blocks_path_of_W` | `W_spoofedV` |
| `ddos_causes_verification_collapse_of_W` | `W_ddos` |
| `collapse_causes_centralization_of_W` | `W_collapse_centralization` |
| `lies_scale_of_W` | `W_lies_scale` |
| `rolex_ddos_structural_equivalence_of_W` | `W_rolex_ddos` |
| `ddos_to_centralization_of_W` | `W_ddos_full` |

-/


/-! ## Axiom-to-Obligation Summary (Boundary Conditions)

| Obligation Theorem | World Bundle |
|---|---|
| `cheap_validator_blocks_V_attack_of_W` | `W_cheap_validator` |
| `trust_bridge_blocks_V_attack_of_W` | `W_trust_bridge` |
| `reversibility_neutralizes_τ_of_W` | `W_reversibility` |
| `E_inclusion_closes_expertise_gap_of_W` | `W_E_inclusion` |
| `cheap_constraint_blocks_V_spoof_of_W` | `W_cheap_constraint` |

-/


end EpArch.AdversarialObligations
