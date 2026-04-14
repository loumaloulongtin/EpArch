/-
EpArch.Adversarial.Base — Adversarial Base Types and Structures

This module contains the TYPE-LEVEL definitions for adversarial modeling:
- Attack primitives (opaques)
- Attack structures
- Domain configurations

NO AXIOMS HERE. Obligation theorems live in EpArch.Adversarial.Obligations;
structural theorems (identity/unfolding proofs) are co-located here.

## What is "Adversarial" in EpArch?

"Adversarial" doesn't mean malicious intent — it means the model accounts
for ANY source of epistemic failure: lies, omissions, misobservations,
forgeries.  Attack structures formalize the SPACE of possible failures
so that obligation theorems can prove which mechanisms are forced.

See EpArch.Adversarial.Obligations for the conditional obligation theorems
that use these types.
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank
import EpArch.Commitments

namespace EpArch

universe u

variable {PropLike Standard ErrorModel Provenance : Type u}

/-! ## Attack Primitives -/

/-- τ compression: attacker forces short decision window. -/
opaque τ_compress : Time → Time → Prop  -- (original, compressed)

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

/-- Pseudo-deposit: deposit that passed Accept_B on spoofed inputs.

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
opaque AuditChannel : Type u

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

/-- Verification collapse: agent can no longer perform adequate V-checks. -/
opaque verification_collapsed : Agent → Prop

/-- Trust centralization: agent delegates to single "trusted" authority. -/
opaque trust_centralized : Agent → Prop

/-- Predicted signature table for DDoS effects. -/
structure DDoSSignature where
  signature : String
  measurable_proxy : String
  prediction : String

def ddos_signatures : List DDoSSignature := [
  ⟨"Verification collapse", "Trace density drop",
   "Fraction of claims with checkable provenance drops under overload"⟩,
  ⟨"Trust centralization", "Authority concentration index",
   "Top-N source share rises after collapse"⟩,
  ⟨"Denial dominance", "Challenge response type ratio",
   "Field-local repairs decay; meta-deflections rise"⟩,
  ⟨"Repair loop failure", "Resolution rate decay",
   "Headerless disputes show lower resolution rates"⟩
]


/-! ## Boundary Conditions (When Attacks Fail) -/

/-- Cheap validator reachable: victim can complete real V within τ. -/
opaque cheap_validator_reachable : Agent → Time → Prop

/-- Trust bridge on-hand: victim has pre-established expertise access. -/
opaque trust_bridge_on_hand : Agent → Prop

/-- Transaction reversible: redeemability check before commitment. -/
opaque transaction_reversible : Deposit PropLike Standard ErrorModel Provenance → Prop

/-- E-field includes threat: victim models this attack pattern. -/
opaque E_includes_threat : Agent → Prop

/-- Constraint surface cheaply testable: quick redeemability possible. -/
opaque constraint_cheaply_testable : Deposit PropLike Standard ErrorModel Provenance → Prop


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

/-- Attack sophistication is monotonic in attack level (now definitional). -/
theorem sophistication_monotonic (l1 l2 : AttackLevel) :
    attack_level_num l1 < attack_level_num l2 →
    attack_sophistication l1 < attack_sophistication l2 := id


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

/-- Why social systems need architecture, not virtue.
    The existence of lies is independent of norms — lies are structurally possible
    whenever the Lie type is inhabited, regardless of social conventions.
    (Tautology: is_lie → is_lie) -/
theorem sincerity_norms_irrelevant :
    ∀ (l : Lie (PropLike := PropLike)), is_lie l → is_lie l := fun _ h => h

/-- Architectural observation: norms cannot prevent lie *construction*,
    only lie *acceptance*. Defense is necessarily receive-side.
    (Unfolding: is_lie unpacks to its conjuncts) -/
theorem lies_structurally_possible (l : Lie (PropLike := PropLike)) (h : is_lie l) :
    l.fabricated_V ∧ l.severed_redeemability := h

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

/-- Predicted failure signature: "truthful but mislicensed". -/
def truthful_but_mislicensed (ps : ProxySubstitution (PropLike := PropLike)) : Prop :=
  ps.Q_is_true ∧ ¬ps.transfer_valid

/-- Adversarial proxy always yields truthful-but-mislicensed failure. -/
theorem adversarial_proxy_signature (ps : ProxySubstitution (PropLike := PropLike)) :
    adversarial_proxy ps → truthful_but_mislicensed ps := by
  intro h
  exact h

/-- Domain examples of proxy substitution failures. -/
inductive ProxyFailureDomain where
  | Medication   -- "this drug is like that drug"
  | Expertise    -- "this expert is like that expert"
  | Trends       -- "this graph looks like last year's"
  | Sources      -- "this outlet is generally reliable"
  | Retail       -- "this product looks equivalent"
  deriving DecidableEq, Repr


/-! ## Network Isomorphism -/

/-- Network primitive mappings. -/
structure NetworkMapping where
  epistemic_primitive : String
  network_primitive : String
  shared_mechanism : String

/-- The isomorphism table. -/
def network_isomorphism_table : List NetworkMapping := [
  ⟨"Bubble boundary", "Network segmentation", "Scoped trust zones"⟩,
  ⟨"Deposit", "Signed artifact", "Trusted record"⟩,
  ⟨"Withdrawal", "Consumption", "Reliance on trusted data"⟩,
  ⟨"Export", "Cross-domain trust", "Boundary crossing"⟩,
  ⟨"Provenance (V)", "Certificates/audit logs", "Source tracking"⟩,
  ⟨"Error model (E)", "Threat model", "Failure enumeration"⟩,
  ⟨"Standard (S)", "Security policy", "Acceptance criteria"⟩,
  ⟨"Hygiene", "Patch management", "Ongoing maintenance"⟩,
  ⟨"Counterfeit deposit", "Supply-chain attack", "Trusted path exploited"⟩
]

/-- Transfer status: what ports cleanly vs needs modification. -/
inductive TransferStatus where
  | TransfersClearly  -- shared constraint → direct mapping
  | TransfersWithTwist -- epistemic adds survival/discovery pressure
  | DoesNotTransfer   -- no network analog (traction gradation)
  deriving DecidableEq, Repr

/-- Asymmetry boundary: epistemic systems face extra forcing constraints. -/
structure AsymmetryBoundary where
  extra_constraint : String
  why_networks_lack : String
  consequence : String

def epistemic_asymmetries : List AsymmetryBoundary := [
  ⟨"Survival under τ", "Networks don't face predation deadlines", "Must act on credit-certainty sometimes"⟩,
  ⟨"Discovery pressure", "Networks maintain known artifacts", "Must explore before validation exists"⟩
]


/-! ## Convergent Domain Configurations -/

/-- Primitive configurations for specific domains. -/
structure DomainConfig where
  domain : String
  S_config : String
  E_config : String
  V_config : String
  τ_config : String
  ACL_config : String
  Redeem_config : String

def convergent_domain_configs : List DomainConfig := [
  ⟨"Network Security",
   "Security policy/compliance", "Threat model", "Certificates/audit logs",
   "Key/cert expiry", "Firewall rules", "Penetration tests"⟩,
  ⟨"Supply Chains",
   "Quality standards (ISO, FDA)", "Component failure modes", "Chain-of-custody docs",
   "Shelf life, batch validity", "Authorized supplier lists", "Incoming inspection"⟩,
  ⟨"Legal Systems",
   "Rules of evidence", "Witness reliability, forensic error", "Chain of custody",
   "Statutes of limitation", "Standing, jurisdiction", "Cross-examination, appeals"⟩,
  ⟨"Science",
   "Methodological standards", "Known confounders", "Independent replication",
   "Replication recency", "Peer review gatekeeping", "Replication studies"⟩
]

end EpArch
