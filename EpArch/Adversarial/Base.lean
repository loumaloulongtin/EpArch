/-
EpArch.Adversarial.Base — Adversarial Base Types and Structures

This module contains the TYPE-LEVEL definitions for adversarial modeling:
- Attack primitives (opaques)
- Attack structures and attack-success predicate
- `is_lie_iff` biconditional

"Adversarial" here means any source of epistemic failure — lies, omissions,
misobservations, forgeries. Attack structures formalize the space of possible
failures so that the obligation theorems can prove which mechanisms are forced.
Obligation theorems live in EpArch.Adversarial.Obligations; `is_lie_iff` is the
only structural theorem co-located here.
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank
import EpArch.Commitments

namespace EpArch

universe u

variable {PropLike Standard ErrorModel Provenance : Type u}

/-! ## Attack Primitives -/

/-- τ compression: compressed time is strictly less than the original window.
    Concretely: the attacker succeeds when t_compressed < t_orig. -/
def τ_compress (t_orig t_compressed : Time) : Prop := t_compressed < t_orig

/-- V spoofing: attacker injects fake provenance header. -/
opaque V_spoof : Deposit PropLike Standard ErrorModel Provenance → Prop

/-- Proxy cue amplification: attacker amplifies cheap-to-process cues. -/
opaque amplify_cues : Deposit PropLike Standard ErrorModel Provenance → Prop

/-- Consultation suppression: attacker blocks access to validators. -/
opaque consultation_suppressed : Agent → Prop

/-- Expertise gap: victim cannot distinguish surface from deep checks. -/
opaque expertise_gap : Agent → Prop


/-! ## Attack Structures -/

/-- Full-stack attack: coordinated attack on multiple primitives.

    A full-stack attack coordinates τ compression, V spoofing,
    cue amplification, consultation blocking, and expertise exploitation. -/
structure FullStackAttack where
  target : Agent
  deposit : Deposit PropLike Standard ErrorModel Provenance
  τ_compressed : Bool
  V_spoofed : Bool
  cues_amplified : Bool
  consultation_blocked : Bool
  expertise_exploited : Bool

/-- Attack succeeds: victim accepts the pseudo-deposit.

    Attack succeeds when ALL of:
    1. τ was compressed (decision window too short for verification)
    2. V-verification failed: EITHER V was spoofed (fake provenance)
       OR consultation was blocked (real validators unreachable)
    3. Proxy cues amplified (cheap signals substituted for expensive checks)
    4. Expertise gap exploited (victim can't distinguish surface/deep)

    The disjunction in (2) captures two distinct attack mechanisms:
    - V spoofing: provides false provenance signal
    - Consultation suppression: blocks true provenance signal
    Both prevent proper V-checking, but through different mechanisms. -/
def attack_succeeds (a : FullStackAttack (PropLike := PropLike)
    (Standard := Standard) (ErrorModel := ErrorModel) (Provenance := Provenance)) : Prop :=
  a.τ_compressed ∧
  (a.V_spoofed ∨ a.consultation_blocked) ∧
  a.cues_amplified ∧
  a.expertise_exploited


/-! ## Pseudo-Deposit -/

/-- Pseudo-deposit: deposit that passed Promote_B on spoofed inputs.

    The deposit is Committed in the victim's bubble, but:
    - V was forged (no valid provenance path)
    - S was displaced to cheap proxies
    - Later redeemability will fail

    Operationally: a pseudo-deposit has V_spoofed = true in its attack context. -/
structure PseudoDeposit where
  deposit : Deposit PropLike Standard ErrorModel Provenance
  V_was_spoofed : Bool
  S_displaced_to_proxies : Bool

/-- A deposit is a pseudo-deposit if V was spoofed during acceptance. -/
def is_pseudo_deposit (pd : PseudoDeposit (PropLike := PropLike)
    (Standard := Standard) (ErrorModel := ErrorModel) (Provenance := Provenance)) : Prop :=
  pd.V_was_spoofed = true


/-! ## DDoS / Bandwidth Exhaustion -/

/-- Audit channel: the pathway through which verification happens. -/
opaque AuditChannel : Type

/-- Channel capacity: how much verification can be processed. -/
opaque channel_capacity : AuditChannel → Nat

/-- Attack volume: how much the attacker is pushing through. -/
opaque attack_volume : AuditChannel → Nat

/-- Channel is overwhelmed when attack_volume > channel_capacity. -/
def channel_overwhelmed (c : AuditChannel) : Prop :=
  attack_volume c > channel_capacity c

/-- DDoS attack structure: propaganda as bandwidth exhaustion.

    Propaganda as bandwidth exhaustion:
    - High volume of claims
    - Multi-channel diversity
    - Continuous flooding
    - Victory: victim retreats to attacker-influenced bubble -/
structure DDoSAttack where
  channels : List AuditChannel
  volume_per_channel : Nat
  is_continuous : Bool


/-! ## DDoS Attack Vectors -/

/-- DDoS attack vector types. -/
inductive DDoSVector where
  | LadderOverload      -- Flood candidate-belief stage with high-salience items
  | VChannelExhaustion  -- Make provenance checking too costly/slow
  | EFieldPoisoning     -- Inject noise so error signals become ubiquitous
  | DenialTriggering    -- Induce generalized distrust blocking all external import
  deriving DecidableEq, Repr

/-- Ladder overload: traction forms before V can be checked.

    High-salience flooding causes the candidate-belief stage to commit
    before provenance verification can complete. -/
opaque ladder_overloaded : Agent → Prop

/-- V-channel exhaustion: provenance checking too costly.

    Provenance checking is made too costly or slow to keep pace with incoming claims. -/
opaque V_channel_exhausted : Agent → Prop

/-- E-field poisoning: everything feels uncertain.

    Noise is injected so error signals become ubiquitous, making
    everything feel uncertain. -/
opaque E_field_poisoned : Agent → Prop

/-- Denial triggered: generalized distrust blocks all external import.

    Generalized distrust is induced ('nothing is trustworthy'),
    blocking all external import. -/
opaque denial_triggered : Agent → Prop

/-- Verification collapse: every audit channel available to agent a is overwhelmed.

    STRUCTURAL definition — not a world assumption. When this holds, no audit
    capacity remains for per-deposit verification steps; the agent cannot
    schedule a verification step before its mandatory decision deadline.

    Two sub-conditions are jointly required:
    - `channels ≠ []`: there must be channels that are overwhelmed, not merely
      an absence of channels (an agent with no channels is not in a collapsed
      state — it never had verification capacity to lose).
    - `∀ c, c ∈ channels → channel_overwhelmed c`: every channel satisfies
      `attack_volume c > channel_capacity c` — no capacity remains for
      any individual verification step.

    The consequence chain (τ exhaustion → `¬PathExists`) is closed by
    the `h_exhausts_tau` hypothesis supplied to `rolex_ddos_share_path_failure_structure`
    and `collapsed_to_path_failure` (purely structural theorem). -/
def verification_collapsed (a : Agent) (channels : List AuditChannel) : Prop :=
  channels ≠ [] ∧ ∀ c, c ∈ channels → channel_overwhelmed c

/-- Trust centralization: agent delegates to single "trusted" authority. -/
opaque trust_centralized : Agent → Prop

/-! ## Boundary Conditions (When Attacks Fail) -/

/-- Cheap validator reachable: the agent's time budget is positive (d.h.τ > 0 when τ = d.h.τ),
    meaning a real V-check can be completed within the remaining window.
    Grounded as a def: τ > 0 is the concrete condition — a validator is reachable iff
    the verification window is still open. -/
def cheap_validator_reachable (_a : Agent) (τ : Time) : Prop := τ > 0

/-- Trust bridge on-hand: victim has pre-established expertise access. -/
opaque trust_bridge_on_hand : Agent → Prop

/-- Transaction reversible: deposit has remaining TTL (d.h.τ > 0).
    A deposit with positive TTL can still be verified and undone before commitment. -/
def transaction_reversible (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  d.h.τ > 0

/-- E-field includes threat: victim models this attack pattern. -/
opaque E_includes_threat : Agent → Prop

/-- Constraint surface cheaply testable: the deposit's TTL is positive (d.h.τ > 0),
    meaning a quick redeemability check can complete before expiry.
    Grounded as a def: TTL positivity is the concrete condition — the constraint
    surface is reachable iff the verification window is still open. -/
def constraint_cheaply_testable (d : Deposit PropLike Standard ErrorModel Provenance) : Prop :=
  d.h.τ > 0


/-! ## Attack Hierarchy -/

/-- Attack levels from primitive to scaled.

    Level 0: Lie (fabricate claim + header; attempt export)
    Level 1: Proxy spoofing (exploit similarity)
    Level 2: τ compression (block verification via urgency)
    Level 3: V spoofing (synthetic provenance)
    Level 4: DDoS (overwhelm verification capacity) -/
inductive AttackLevel where
  | Lie           -- Level 0: primitive false deposit
  | ProxySpoof    -- Level 1: exploit similarity
  | τCompress     -- Level 2: urgency-block verification
  | VSpoof        -- Level 3: synthetic provenance
  | DDoS          -- Level 4: population-scale bandwidth attack
  deriving DecidableEq, Repr

/-- Higher levels are the lie plus optimization under constraints. -/
def attack_level_num : AttackLevel → Nat
  | .Lie => 0
  | .ProxySpoof => 1
  | .τCompress => 2
  | .VSpoof => 3
  | .DDoS => 4

/-- Attack sophistication is defined as the attack level number.
    This makes sophistication ordering definitional (no axiom needed). -/
abbrev attack_sophistication : AttackLevel → Nat := attack_level_num

/-! ## Lying as Structural Inevitability -/

/-- A lie in model terms: attempted deposit with fabricated V and severed redeemability. -/
structure Lie where
  claim : PropLike
  fabricated_V : Bool
  severed_redeemability : Bool
  τ_abuse : Bool  -- "accept now, don't check"

/-- A lie has fabricated provenance AND severed redeemability. -/
def is_lie (l : Lie (PropLike := PropLike)) : Prop :=
  l.fabricated_V ∧ l.severed_redeemability

/-- is_lie is a biconditional: a lie is exactly fabricated provenance AND severed redeemability.
    Both sides are definitionally equal — `is_lie` unfolds directly to the conjunction. -/
theorem is_lie_iff (l : Lie (PropLike := PropLike)) :
    is_lie l ↔ l.fabricated_V ∧ l.severed_redeemability := Iff.rfl

/-- Costs for lying scale analysis. -/
opaque export_cost : Nat
opaque import_defense_cost : Nat


/-! ## Proxy Withdrawal / Similarity Substitution -/

/-- Proxy substitution: replacing target claim P with similar claim Q.

    The danger: adversarial environments select for proxies that pass
    cheap checks while failing expensive ones. -/
structure ProxySubstitution where
  target_P : PropLike                   -- what we actually need
  proxy_Q : PropLike                    -- what we're checking instead
  Q_is_true : Bool        -- is Q itself factually correct?
  transfer_valid : Bool   -- does Q actually license P?

/-- Constructive proxying: Q really is equivalent in relevant dimensions. -/
def constructive_proxy (ps : ProxySubstitution (PropLike := PropLike)) : Prop :=
  ps.transfer_valid

/-- Adversarial proxying: Q is true but does not license P— transfer fails. -/
def adversarial_proxy (ps : ProxySubstitution (PropLike := PropLike)) : Prop :=
  ps.Q_is_true ∧ ¬ps.transfer_valid

/-- Domain examples of proxy substitution failures. -/
inductive ProxyFailureDomain where
  | Medication   -- "this drug is like that drug"
  | Expertise    -- "this expert is like that expert"
  | Trends       -- "this graph looks like last year's"
  | Sources      -- "this outlet is generally reliable"
  | Retail       -- "this product looks equivalent"
  deriving DecidableEq, Repr


end EpArch
