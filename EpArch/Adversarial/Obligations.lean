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

/-- PathExists: evidence that a verification path exists for deposit d.

    Carries two kernel-verifiable proof obligations:
    - `ttl_valid`: the deposit's verification window is open (d.h.τ > 0)
    - `status_live`: the deposit is not revoked (can still be inspected and challenged)

    **Why only two fields — why not "V is non-empty"?**

    `d.h.V : Provenance` is a bare type variable. EpArch is a schema, not a
    data model: the architecture deliberately does not prescribe what provenance
    looks like. In one bubble it might be `List String`, in another `Set AgentId`,
    in another a Merkle root. Because `Provenance` carries no typeclass structure
    at the abstract layer, there is nothing to inspect — you cannot write
    `d.h.V.length > 0` without knowing `Provenance` is a `List`.

    **The real goal of PathExists is not to certify source richness.**

    It is to show what happens *if* V is not empty — i.e., *given* that an agent
    has supplied valid provenance (the W bundle hypothesis), the path is either
    intact (ttl_valid ∧ status_live) or destroyed by the attack (¬PathExists d).
    The W bundles carry the provenance assumption; PathExists carries the
    consequence. V-spoofing and consultation suppression block the path not by
    emptying V per se, but by making the deposit untrustworthy in a way that
    forces its revocation or prevents it from ever reaching Deposited status.

    **If you are modeling agents and want to say more about provenance:**
    Add a typeclass to `Provenance` in `Header.lean` (e.g., a `nonempty_V` predicate
    or `[DecidableEq Provenance]` + a cardinality function) and add a corresponding
    field here. That change propagates through every downstream signature that
    parameterizes over `Provenance`. The modular architecture (Meta/Config.lean,
    ClusterRegistry) supports registering a richer PathExists cluster alongside
    this one without touching the existing proof surface. -/
structure PathExists (d : Deposit PropLike Standard ErrorModel Provenance) : Prop where
  /-- Deposit TTL is positive: the verification window is open (kernel-verified) -/
  ttl_valid   : d.h.τ > 0
  /-- Deposit is not revoked: it can still be inspected and challenged (kernel-verified) -/
  status_live : d.status ≠ DepositStatus.Revoked


/-! ## W_spoofedV: V spoofing and consultation suppression block the verification path -/

/-- World assumption: either V spoofing or consultation suppression blocks the
    verification path entirely.

    Uses Base opaques `V_spoof` and `consultation_suppressed` directly — no
    shadow Bool-field types. The two mechanisms are distinct (V_spoof injects
    false provenance; consultation_suppressed blocks real validators) but both
    eliminate the path: V_spoof → ¬PathExists d (the spoofed deposit cannot
    remain non-revoked once the spoof is acted on); consultation_suppressed
    similarly closes every path.

    Matches `FullStackAttack.attack_succeeds` clause 2: (V_spoofed ∨ consultation_blocked). -/
structure W_spoofedV where
  /-- Spoofed provenance blocks the verification path: deposit cannot remain non-revoked -/
  spoof_blocks_path : ∀ (d : Deposit PropLike Standard ErrorModel Provenance),
    EpArch.V_spoof d → ¬PathExists d
  /-- Consultation suppression also blocks the verification path -/
  suppression_blocks_path : ∀ (a : EpArch.Agent)
    (d : Deposit PropLike Standard ErrorModel Provenance),
    EpArch.consultation_suppressed a → ¬PathExists d

/-- Obligation theorem: V spoofing or consultation suppression blocks any verification path.

    **Theorem shape:** If V is spoofed OR consultation is suppressed, then no PathExists
    witness can exist for deposit d: the attack hypothesis contradicts any path evidence.

    **Proof strategy:** `intro h p` introduces the disjunction and the path evidence, then
    `cases h` dispatches to `spoof_blocks_path` or `suppression_blocks_path`, each of
    which has type `→ ¬PathExists d` and is applied to the path evidence `p`. -/
theorem spoofed_V_blocks_path_of_W
    (W : W_spoofedV (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (a : EpArch.Agent) (p : PathExists d) :
    (EpArch.V_spoof d ∨ EpArch.consultation_suppressed a) → False := by
  intro h
  cases h with
  | inl h_spoof => exact W.spoof_blocks_path d h_spoof p
  | inr h_supp  => exact W.suppression_blocks_path a d h_supp p


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

/-! ### W_cheap_validator: Cheap validator maintains path despite V-failure -/

/-- World assumption: a reachable cheap validator preserves a valid verification
    path regardless of V spoofing or consultation suppression.

    The attack (W_spoofedV) says every path is blocked. The countermeasure says
    the cheap validator keeps at least one path open — the attacker has not won.

    Field uses `cheap_validator_reachable a d.h.τ` — the validator's time budget is
    tied to the deposit's own TTL window. `cheap_validator_reachable` is grounded
    as `d.h.τ > 0` (see Base.lean), so `h_cv : d.h.τ > 0` directly discharges
    `ttl_valid` in PathExists. The `h_s` precondition certifies non-revoked status,
    discharging `status_live`. -/
structure W_cheap_validator where
  /-- Cheap validator enables path: validator reachable within deposit window, deposit not revoked -/
  cheap_validator_enables_path : ∀ (a : EpArch.Agent)
    (d : Deposit PropLike Standard ErrorModel Provenance),
    EpArch.cheap_validator_reachable a d.h.τ →
    d.status ≠ DepositStatus.Revoked →
    PathExists d

/-- Obligation theorem: cheap validator maintains a valid verification path.

    **Proof strategy:** `cheap_validator_reachable a d.h.τ` is definitionally
    `d.h.τ > 0`, which the W field uses directly. Result: PathExists d with
    ttl_valid = h_cv and status_live = h_s. -/
theorem cheap_validator_maintains_path_of_W
    (W : W_cheap_validator (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (a : EpArch.Agent)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_s : d.status ≠ DepositStatus.Revoked) :
    EpArch.cheap_validator_reachable a d.h.τ →
    PathExists d :=
  fun h_cv => W.cheap_validator_enables_path a d h_cv h_s


/-! ### W_trust_bridge: Trust bridge maintains path despite V-failure -/

/-- World assumption: a pre-established trust bridge provides an alternative
    verification path, maintaining access despite V spoofing or consultation
    suppression.

    The bridge does not prevent V_spoof from occurring — it opens an
    alternative route so the attack cannot close off all paths.
    `trust_bridge_on_hand` remains opaque (an agent property with no
    abstract grounding on the Nat-indexed Agent type). -/
structure W_trust_bridge where
  /-- Trust bridge enables path: deposit non-expired and non-revoked -/
  trust_bridge_enables_path : ∀ (a : EpArch.Agent)
    (d : Deposit PropLike Standard ErrorModel Provenance),
    EpArch.trust_bridge_on_hand a →
    d.h.τ > 0 →
    d.status ≠ DepositStatus.Revoked →
    PathExists d

/-- Obligation theorem: trust bridge maintains a valid verification path. -/
theorem trust_bridge_maintains_path_of_W
    (W : W_trust_bridge (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (a : EpArch.Agent)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_τ : d.h.τ > 0)
    (h_s : d.status ≠ DepositStatus.Revoked) :
    EpArch.trust_bridge_on_hand a →
    PathExists d :=
  fun h_tb => W.trust_bridge_enables_path a d h_tb h_τ h_s


/-! ### W_reversibility: Reversibility maintains path after τ compression -/

/-- World assumption: if a deposit is reversible, τ compression cannot close
    all verification paths — the victim retains a recovery path even after
    the decision window has been compressed.

    The attack (τ_compress) shortens the window, not the recovery capability.
    Reversibility means the post-compress state still has a path for verify-and-undo.
    `transaction_reversible d` is grounded as `d.h.τ > 0` (Base.lean), directly
    discharging `ttl_valid` in PathExists. The `h_s` precondition certifies
    non-revoked status. -/
structure W_reversibility where
  /-- Reversibility keeps a path open even after τ compression, provided deposit not revoked -/
  reversibility_survives_τ_compress : ∀ (t_orig t_compressed : EpArch.Time)
    (d : Deposit PropLike Standard ErrorModel Provenance),
    EpArch.transaction_reversible d →
    EpArch.τ_compress t_orig t_compressed →
    d.status ≠ DepositStatus.Revoked →
    PathExists d

/-- Obligation theorem: reversibility maintains a path after τ compression. -/
theorem reversibility_maintains_path_after_τ_compress_of_W
    (W : W_reversibility (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (t_orig t_compressed : EpArch.Time)
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_s : d.status ≠ DepositStatus.Revoked) :
    EpArch.transaction_reversible d →
    EpArch.τ_compress t_orig t_compressed →
    PathExists d :=
  fun h_rev h_compress => W.reversibility_survives_τ_compress t_orig t_compressed d h_rev h_compress h_s


/-! ### W_E_inclusion: E-field threat modeling prevents verification collapse -/

/-- World assumption: if an agent's E-field models the attack pattern,
    verification collapse is prevented — the expertise gap exists but is
    not exploitable.

    The attack exploits a gap between what the victim checks and what matters.
    When E models the threat, the agent recognizes and resists the substitution
    before V collapse occurs.
    Uses Base opaques `E_includes_threat` and `verification_collapsed` directly. -/
structure W_E_inclusion where
  /-- E-field threat modeling prevents verification collapse -/
  E_modeling_prevents_collapse : ∀ (a : EpArch.Agent),
    EpArch.E_includes_threat a → ¬EpArch.verification_collapsed a

/-- Obligation theorem: E-field inclusion prevents verification collapse. -/
theorem E_inclusion_prevents_collapse_of_W
    (W : W_E_inclusion)
    (a : EpArch.Agent) :
    EpArch.E_includes_threat a → ¬EpArch.verification_collapsed a :=
  W.E_modeling_prevents_collapse a


/-! ### W_cheap_constraint: Cheaply testable constraint maintains path despite V spoof -/

/-- World assumption: if the constraint surface is cheaply testable, a real
    redeemability check happens within τ, maintaining a valid path regardless
    of V spoofing or consultation suppression.

    `constraint_cheaply_testable d` is grounded as `d.h.τ > 0` (Base.lean),
    directly discharging `ttl_valid` in PathExists. The `h_s` precondition
    certifies non-revoked status, discharging `status_live`. Together, both
    PathExists fields are derived from the preconditions — no hand-set Bools. -/
structure W_cheap_constraint where
  /-- Cheap testing enables path: TTL positive (via grounded constraint_cheaply_testable), deposit not revoked -/
  cheap_test_enables_path : ∀ (d : Deposit PropLike Standard ErrorModel Provenance),
    EpArch.constraint_cheaply_testable d →
    d.status ≠ DepositStatus.Revoked →
    PathExists d

/-- Obligation theorem: cheaply testable constraint maintains a valid verification path. -/
theorem cheap_constraint_maintains_path_of_W
    (W : W_cheap_constraint (PropLike := PropLike) (Standard := Standard)
         (ErrorModel := ErrorModel) (Provenance := Provenance))
    (d : Deposit PropLike Standard ErrorModel Provenance)
    (h_s : d.status ≠ DepositStatus.Revoked) :
    EpArch.constraint_cheaply_testable d →
    PathExists d :=
  fun h_ct => W.cheap_test_enables_path d h_ct h_s


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

| Obligation Theorem | World Bundle | Effect asserted |
|---|---|---|
| `cheap_validator_maintains_path_of_W` | `W_cheap_validator` | `PathExists d` (ttl_valid + status_live) |
| `trust_bridge_maintains_path_of_W` | `W_trust_bridge` | `PathExists d` (ttl_valid + status_live) |
| `reversibility_maintains_path_after_τ_compress_of_W` | `W_reversibility` | `PathExists d` survives τ compress |
| `E_inclusion_prevents_collapse_of_W` | `W_E_inclusion` | `¬verification_collapsed` |
| `cheap_constraint_maintains_path_of_W` | `W_cheap_constraint` | `PathExists d` (ttl_valid + status_live) |

-/


end EpArch.AdversarialObligations
