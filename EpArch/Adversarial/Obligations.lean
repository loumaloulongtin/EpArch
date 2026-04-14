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

## Obligation Theorem Targets

See the two summary tables at the end of this file for the full list
of attack-vector and boundary-condition obligation theorems.

## Naming Convention

- `X` = original definition (in EpArch.Adversarial.Base)
- `X_of_W` = conditional theorem version (proved here)
- `W_X` = minimal assumption bundle for `X_of_W` (defined in EpArch.WorldCtx or locally)

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


/-! ## World Assumption Bundles for Adversarial Claims -/

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

/-- V_Spoofed: the verification field was fabricated.

    When V is spoofed:
    - Provenance chain is fabricated at source
    - Chain is broken (no valid path to constraint surface) -/
structure V_Spoofed_State (d : Deposit PropLike Standard ErrorModel Provenance) where
  fabricated : Bool
  chain_broken : Bool

def is_V_spoofed (v : V_Spoofed_State d) : Prop :=
  v.fabricated ∧ v.chain_broken


/-! ## W_spoofedV: World assumptions for spoofed-V blocking path -/

/-- World assumptions for the spoofed-V-blocks-path claim.

    Assumption: If V is fabricated and chain is broken, no path can exist.
    This is structural: a broken chain cannot be traversed.

    This converts the axiom `spoofed_V_blocks_path` into an explicit assumption. -/
structure W_spoofedV where
  /-- Broken provenance chain implies no path to constraint surface -/
  broken_chain_no_path : ∀ (d : Deposit PropLike Standard ErrorModel Provenance)
    (v : V_Spoofed_State d) (p : PathExists d),
    v.chain_broken → ¬p.provenance_intact

/-- Obligation theorem: Spoofed V blocks path (conditional version).

    Conditional version: this holds UNDER the assumption that broken chains block paths. -/
theorem spoofed_V_blocks_path_of_W
    (W : W_spoofedV (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (v : V_Spoofed_State d) (p : PathExists d) :
    is_V_spoofed v → ¬has_path p := by
  intro ⟨_, h_broken⟩
  intro ⟨h_intact, _, _⟩
  have h_no_intact := W.broken_chain_no_path d v p h_broken
  exact h_no_intact h_intact


/-! ## W_ddos: World assumptions for DDoS causing verification collapse -/

/-- Verification capacity model.

    An agent has finite verification capacity per time unit.
    When incoming volume exceeds capacity, verification collapses. -/
structure VerificationCapacity where
  capacity_per_unit : Nat
  incoming_volume : Nat
  is_overwhelmed : Bool := incoming_volume > capacity_per_unit

/-- DDoS attack state: multiple vectors can overwhelm verification. -/
structure DDoSState (a : Agent) where
  ladder_load : Nat       -- candidate items flooding ladder
  V_channel_load : Nat    -- provenance check requests
  E_field_noise : Nat     -- error signal noise level
  denial_pressure : Nat   -- distrust induction pressure
  capacity : VerificationCapacity

/-- Any vector overwhelmed implies at least one attack succeeding. -/
def some_vector_overwhelmed (s : DDoSState a) : Prop :=
  s.ladder_load > s.capacity.capacity_per_unit ∨
  s.V_channel_load > s.capacity.capacity_per_unit ∨
  s.E_field_noise > s.capacity.capacity_per_unit ∨
  s.denial_pressure > s.capacity.capacity_per_unit

/-- Verification collapsed state. -/
structure CollapsedState (a : Agent) where
  cannot_verify : Bool
  delegating : Bool

def is_collapsed (c : CollapsedState a) : Prop :=
  c.cannot_verify

/-- World assumptions for DDoS-causes-collapse claim.

    Assumption: When any vector overwhelms capacity, verification collapses.
    This is resource-theoretic: finite capacity + excess demand = failure. -/
structure W_ddos where
  /-- Overwhelmed capacity implies verification failure -/
  overwhelm_causes_collapse : ∀ (a : Agent) (s : DDoSState a) (c : CollapsedState a),
    some_vector_overwhelmed s → is_collapsed c

/-- Obligation theorem: DDoS causes verification collapse (conditional version).

    Conditional version: this holds UNDER the assumption that overwhelmed capacity
    implies collapse. -/
theorem ddos_causes_verification_collapse_of_W
    (W : W_ddos)
    (a : Agent) (s : DDoSState a) (c : CollapsedState a) :
    some_vector_overwhelmed s → is_collapsed c := by
  exact W.overwhelm_causes_collapse a s c


/-! ## W_collapse_centralization: Collapse leads to trust centralization -/

/-- Trust centralization state: agent delegates to single authority. -/
structure CentralizedState (a : Agent) where
  delegates_to_single : Bool
  authority : Agent

def is_centralized (t : CentralizedState a) : Prop :=
  t.delegates_to_single

/-- World assumptions for collapse-causes-centralization.

    Assumption: When verification collapses, agents seek a single trusted authority.
    This is behavioral: exhaustion → path of least resistance → delegation. -/
structure W_collapse_centralization where
  /-- Verification collapse triggers delegation behavior -/
  exhaustion_triggers_delegation : ∀ (a : Agent) (c : CollapsedState a) (t : CentralizedState a),
    is_collapsed c → is_centralized t

/-- Obligation theorem: Collapse causes centralization (conditional version).

    Conditional version: this holds UNDER the behavioral assumption about exhaustion. -/
theorem collapse_causes_centralization_of_W
    (W : W_collapse_centralization)
    (a : Agent) (c : CollapsedState a) (t : CentralizedState a) :
    is_collapsed c → is_centralized t := by
  exact W.exhaustion_triggers_delegation a c t


/-! ## W_lies_scale: Export cost asymmetry -/

/-- Cost model for export vs defense.

    Export (lying): creating and publishing a false claim
    Defense (verification): checking incoming claims for validity -/
structure CostModel where
  export_cost : Nat        -- cost to publish a claim
  defense_cost : Nat       -- cost to verify a claim
  asymmetric : Bool := export_cost < defense_cost

/-- World assumptions for lies-scale claim.

    Assumption: Export is structurally cheaper than defense.
    This is information-theoretic: creation < verification in general. -/
structure W_lies_scale where
  /-- The cost model exhibits asymmetry -/
  costs : CostModel
  /-- Export is cheaper than defense -/
  asymmetry_holds : costs.export_cost < costs.defense_cost

/-- Obligation theorem: Lies scale (conditional version).

    Conditional version: this holds UNDER a world where the cost asymmetry exists. -/
theorem lies_scale_of_W (W : W_lies_scale) :
    W.costs.export_cost < W.costs.defense_cost :=
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

/-- World assumptions for Rolex-DDoS equivalence.

    Assumption: Consultation blocking (individual) and channel overwhelming (population)
    produce structurally equivalent exploits. -/
structure W_rolex_ddos where
  /-- Individual-scale attack structure -/
  rolex_structure : ExploitStructure
  /-- Population-scale attack structure -/
  ddos_structure : ExploitStructure
  /-- Both overwhelm verification -/
  both_overwhelm : rolex_structure.overwhelms_verification ∧ ddos_structure.overwhelms_verification
  /-- Both force suboptimal acceptance -/
  both_force : rolex_structure.forces_suboptimal_acceptance ∧ ddos_structure.forces_suboptimal_acceptance

/-- Obligation theorem: Rolex-DDoS structural equivalence (conditional version).

    Conditional version: this holds UNDER a world where both attacks share structure. -/
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

/-- Obligation theorem: Full DDoS chain (conditional version).

    Composes the two conditional theorems for DDoS → collapse → centralization. -/
theorem ddos_to_centralization_of_W
    (W : W_ddos_full)
    (a : Agent) (s : DDoSState a) (c : CollapsedState a) (t : CentralizedState a) :
    some_vector_overwhelmed s → is_centralized t := by
  intro h_overwhelm
  have h_collapsed := ddos_causes_verification_collapse_of_W W.toW_ddos a s c h_overwhelm
  exact collapse_causes_centralization_of_W W.toW_collapse_centralization a c t h_collapsed


/-! ## Axiom-to-Obligation Summary (Attack Vectors)

| Original Axiom | Obligation Theorem | World Bundle |
|----------------|-------------------|--------------|
| `spoofed_V_blocks_path` | `spoofed_V_blocks_path_of_W` | `W_spoofedV` |
| `ddos_causes_verification_collapse` | `ddos_causes_verification_collapse_of_W` | `W_ddos` |
| `collapse_causes_centralization` | `collapse_causes_centralization_of_W` | `W_collapse_centralization` |
| `lies_scale` | `lies_scale_of_W` | `W_lies_scale` |
| `rolex_ddos_structural_equivalence` | `rolex_ddos_structural_equivalence_of_W` | `W_rolex_ddos` |
| `ddos_to_centralization` | `ddos_to_centralization_of_W` | `W_ddos_full` |

-/


/-! ## Boundary Condition Countermeasures

These theorems show when attacks fail — the defense conditions.

Key insight: the exploit's power is feasibility control, not counterfeit
perfection. Wherever independent validation is cheap and reachable inside
the decision window, this attack class fails.
-/


/-! ### W_cheap_validator: Cheap validator blocks V-failure attack -/

/-- Cheap validator available: can verify within time budget τ. -/
structure CheapValidatorAvailable (a : Agent) (τ : Time) where
  validator_exists : Bool
  cost_within_budget : Bool
  reachable_in_time : Bool

def has_cheap_validator (cv : CheapValidatorAvailable a τ) : Prop :=
  cv.validator_exists ∧ cv.cost_within_budget ∧ cv.reachable_in_time

/-- Attack state: V was spoofed or consultation was blocked. -/
structure VAttackState where
  V_spoofed : Bool
  consultation_blocked : Bool

def V_attack_succeeded (v : VAttackState) : Prop :=
  v.V_spoofed ∨ v.consultation_blocked

/-- World assumptions for cheap-validator defense.

    Assumption: If a cheap validator is reachable within τ, the agent can
    successfully verify, so neither V spoofing nor consultation blocking works. -/
structure W_cheap_validator where
  /-- Cheap validator enables verification despite attack attempts -/
  cheap_validator_enables_check : ∀ (a : Agent) (τ : Time)
    (cv : CheapValidatorAvailable a τ) (v : VAttackState),
    has_cheap_validator cv → ¬V_attack_succeeded v

/-- Obligation theorem: Cheap validator blocks V attack (conditional version).

    Conditional version: cheap validator reachable within τ disables the attack. -/
theorem cheap_validator_blocks_V_attack_of_W
    (W : W_cheap_validator)
    (a : Agent) (τ : Time)
    (cv : CheapValidatorAvailable a τ) (v : VAttackState) :
    has_cheap_validator cv → ¬V_attack_succeeded v :=
  W.cheap_validator_enables_check a τ cv v


/-! ### W_trust_bridge: Trust bridge blocks V-failure attack -/

/-- Trust bridge available: pre-established trust relationship. -/
structure TrustBridgeAvailable (a : Agent) where
  bridge_exists : Bool
  provides_expertise : Bool

def has_trust_bridge (tb : TrustBridgeAvailable a) : Prop :=
  tb.bridge_exists ∧ tb.provides_expertise

/-- World assumptions for trust-bridge defense.

    Assumption: A pre-established trust bridge provides an alternative
    verification path that bypasses consultation blocking and detects spoofing. -/
structure W_trust_bridge where
  /-- Trust bridge enables verification despite attack attempts -/
  trust_bridge_enables_check : ∀ (a : Agent)
    (tb : TrustBridgeAvailable a) (v : VAttackState),
    has_trust_bridge tb → ¬V_attack_succeeded v

/-- Obligation theorem: Trust bridge blocks V attack (conditional version).

    Conditional version: trust bridge provides an alternative verification path. -/
theorem trust_bridge_blocks_V_attack_of_W
    (W : W_trust_bridge)
    (a : Agent)
    (tb : TrustBridgeAvailable a) (v : VAttackState) :
    has_trust_bridge tb → ¬V_attack_succeeded v :=
  W.trust_bridge_enables_check a tb v


/-! ### W_reversibility: Reversibility neutralizes τ compression -/

/-- Transaction reversibility: can undo after verification. -/
structure TransactionReversible (d : Deposit PropLike Standard ErrorModel Provenance) where
  can_reverse : Bool
  reversal_available : Bool

def is_reversible (tr : TransactionReversible d) : Prop :=
  tr.can_reverse ∧ tr.reversal_available

/-- τ compression attack state. -/
structure τCompressionState where
  τ_compressed : Bool
  decision_forced : Bool

def τ_attack_effective (tc : τCompressionState) : Prop :=
  tc.τ_compressed ∧ tc.decision_forced

/-- World assumptions for reversibility defense.

    Assumption: If transaction is reversible, τ compression loses force—
    the victim can verify after commitment and reverse if failed. -/
structure W_reversibility where
  /-- Reversibility neutralizes urgency -/
  reversibility_neutralizes : ∀ (d : Deposit PropLike Standard ErrorModel Provenance)
    (tr : TransactionReversible d) (tc : τCompressionState),
    is_reversible tr → ¬τ_attack_effective tc

/-- Obligation theorem: Reversibility neutralizes τ (conditional version).

    Conditional version: if reversible, τ compression loses force. -/
theorem reversibility_neutralizes_τ_of_W
    (W : W_reversibility (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (tr : TransactionReversible d) (tc : τCompressionState) :
    is_reversible tr → ¬τ_attack_effective tc :=
  W.reversibility_neutralizes d tr tc


/-! ### W_E_inclusion: E-field threat modeling closes expertise gap -/

/-- E-field includes threat model for this attack pattern. -/
structure EFieldIncludesThreat (a : Agent) where
  threat_modeled : Bool
  countermeasures_known : Bool

def E_includes_threat (ef : EFieldIncludesThreat a) : Prop :=
  ef.threat_modeled ∧ ef.countermeasures_known

/-- Expertise gap attack state. -/
structure ExpertiseGapState (a : Agent) where
  gap_exists : Bool
  exploited : Bool

def expertise_gap_exploited (eg : ExpertiseGapState a) : Prop :=
  eg.gap_exists ∧ eg.exploited

/-- World assumptions for E-field inclusion defense.

    Assumption: If the agent's E-field models this threat pattern,
    the expertise gap cannot be exploited. -/
structure W_E_inclusion where
  /-- E-field modeling closes the gap -/
  E_modeling_closes_gap : ∀ (a : Agent)
    (ef : EFieldIncludesThreat a) (eg : ExpertiseGapState a),
    E_includes_threat ef → ¬expertise_gap_exploited eg

/-- Obligation theorem: E-field inclusion closes expertise gap (conditional version).

    Conditional version: if E-field models threat, the expertise gap is closed. -/
theorem E_inclusion_closes_expertise_gap_of_W
    (W : W_E_inclusion)
    (a : Agent)
    (ef : EFieldIncludesThreat a) (eg : ExpertiseGapState a) :
    E_includes_threat ef → ¬expertise_gap_exploited eg :=
  W.E_modeling_closes_gap a ef eg


/-! ### W_cheap_constraint: Cheaply testable constraint blocks V spoof -/

/-- Constraint surface is cheaply testable. -/
structure ConstraintCheapTest (d : Deposit PropLike Standard ErrorModel Provenance) where
  test_available : Bool
  cost_acceptable : Bool
  within_τ : Bool

def constraint_cheaply_testable (ct : ConstraintCheapTest d) : Prop :=
  ct.test_available ∧ ct.cost_acceptable ∧ ct.within_τ

/-- World assumptions for cheap constraint test defense.

    Assumption: If constraint surface is cheaply testable, real redeemability
    check happens within τ, exposing any spoofed V. -/
structure W_cheap_constraint where
  /-- Cheap testing exposes spoofed V -/
  cheap_test_exposes_spoof : ∀ (d : Deposit PropLike Standard ErrorModel Provenance)
    (ct : ConstraintCheapTest d) (v : VAttackState),
    constraint_cheaply_testable ct → ¬V_attack_succeeded v

/-- Obligation theorem: Cheap constraint test blocks V spoof (conditional version).

    Conditional version: a quick redeemability test exposes spoofed V. -/
theorem cheap_constraint_blocks_V_spoof_of_W
    (W : W_cheap_constraint (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (ct : ConstraintCheapTest d) (v : VAttackState) :
    constraint_cheaply_testable ct → ¬V_attack_succeeded v :=
  W.cheap_test_exposes_spoof d ct v


/-! ## Axiom-to-Obligation Summary (Boundary Conditions)

| Original Axiom | Obligation Theorem | World Bundle |
|----------------|-------------------|--------------|
| `cheap_validator_blocks_V_attack` | `cheap_validator_blocks_V_attack_of_W` | `W_cheap_validator` |
| `trust_bridge_blocks_V_attack` | `trust_bridge_blocks_V_attack_of_W` | `W_trust_bridge` |
| `reversibility_neutralizes_τ` | `reversibility_neutralizes_τ_of_W` | `W_reversibility` |
| `E_inclusion_closes_expertise_gap` | `E_inclusion_closes_expertise_gap_of_W` | `W_E_inclusion` |
| `cheap_constraint_blocks_V_spoof` | `cheap_constraint_blocks_V_spoof_of_W` | `W_cheap_constraint` |

-/


end EpArch.AdversarialObligations
