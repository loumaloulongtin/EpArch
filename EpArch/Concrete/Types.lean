/-
EpArch.Concrete.Types — Concrete Type Definitions

Ground-level concrete types for the EpArch non-vacuity witness:
  CProp = String, CStandard = Nat, CErrorModel/CProvenance = List String.
No imports required — all types are ground Lean 4 types.

Part of the EpArch.Concrete module family.
-/
namespace EpArch.ConcreteModel

/-! ## Concrete Types -/

/-- Concrete propositions are just strings. -/
abbrev CProp := String

/-- Concrete standard: threshold for acceptance (0-100). -/
abbrev CStandard := Nat

/-- Concrete error model: set of known failure modes. -/
abbrev CErrorModel := List String

/-- Concrete provenance: chain of sources. -/
abbrev CProvenance := List String

/-- Concrete time: natural number (ticks). -/
abbrev CTime := Nat

/-- Concrete constraint surface: what the claim is testable against. -/
structure CConstraintSurface where
  domain : String
  test_procedure : String
deriving DecidableEq, Repr, Inhabited

/-- Concrete deposit with all header fields. -/
structure CDeposit where
  claim : CProp
  S : CStandard           -- acceptance threshold
  E : CErrorModel         -- known failure modes
  V : CProvenance         -- source chain
  τ : CTime               -- time-to-live
  cs : CConstraintSurface -- redeemability reference
deriving Repr, DecidableEq, Inhabited

/-- Concrete bubble: a list of deposits with a scope identifier. -/
structure CBubble where
  id : String
  deposits : List CDeposit
  deriving Repr

/-- Concrete agent: has beliefs (ladder state) and confidence levels. -/
structure CAgent where
  id : String
  beliefs : List CProp           -- what they're certain of
  confidence : CProp → Nat       -- confidence level per claim

/-- Concrete global ledger (for commitment 2). -/
structure CGlobalLedger where
  all_deposits : List CDeposit
  acceptance_threshold : Nat
  deriving Repr


/-! ## Lifecycle States -/

/-- Deposit lifecycle status.
    Candidate → Validated → Deposited → (Aging/Stale/Revoked) -/
inductive CDepositStatus
  | Candidate   -- Proposed but not yet validated
  | Validated   -- Passed S/E/V checks, awaiting acceptance
  | Deposited   -- Accepted into bubble, withdrawable
  | Aging       -- Still valid but approaching τ expiry
  | Stale       -- τ expired, needs refresh
  | Revoked     -- Withdrawn due to challenge or error
  | Unknown     -- Status cannot be determined
  deriving DecidableEq, Repr

/-- Deposit with explicit lifecycle status. -/
structure CDepositWithStatus where
  deposit : CDeposit
  status : CDepositStatus
  accepted_at : CTime      -- When it entered Deposited
  last_refreshed : CTime   -- Last τ update
  deriving Repr

/-- Compute status from deposit and current time. -/
def compute_status (d : CDeposit) (current_time : CTime) : CDepositStatus :=
  if d.τ = 0 then .Revoked
  else if d.τ ≤ current_time then .Stale
  else if d.τ ≤ current_time + 10 then .Aging  -- Within 10 ticks of expiry
  else if d.V.length = 0 then .Candidate       -- No provenance yet
  else .Deposited


/-! ## Access Control List (ACL) -/

/-- ACL entry: who can withdraw what from where. -/
structure CACLEntry where
  agent_id : String
  bubble_id : String
  claim_pattern : String  -- "*" for all, or specific claim
  permission : String     -- "read", "withdraw", "export"
  deriving Repr

/-- ACL for a bubble. -/
structure CACL where
  entries : List CACLEntry
  deriving Repr

/-- Check if agent has permission for action on claim in bubble. -/
def c_has_permission (acl : CACL) (agent : CAgent) (bubble : CBubble)
    (claim : CProp) (action : String) : Prop :=
  ∃ e, e ∈ acl.entries ∧
    (e.agent_id = agent.id ∨ e.agent_id = "*") ∧
    (e.bubble_id = bubble.id ∨ e.bubble_id = "*") ∧
    (e.claim_pattern = claim ∨ e.claim_pattern = "*") ∧
    e.permission = action

/-- Withdrawal requires: ACL permission + deposit is Current + bank consulted. -/
def c_can_withdraw (acl : CACL) (agent : CAgent) (bubble : CBubble)
    (d : CDeposit) (current_time : CTime) : Prop :=
  c_has_permission acl agent bubble d.claim "withdraw" ∧
  compute_status d current_time = .Deposited ∧
  d ∈ bubble.deposits


/-! ## Export/Import Protocols -/

/-- Trust bridge authorization mode.
    Both paths require an accountable party: byAgent names it directly;
    byToken names it indirectly as the holder of a credential (email domain,
    badge, JWT, crypto key — any token the bridge's check function accepts). -/
inductive CTrustBridgeAuth where
  | byAgent (a : CAgent)             -- named party; gate checks presenter identity
  | byToken (token_ok : ByteArray → Bool) -- credential check; gate applies token_ok to auth_token; presenter anonymous
-- NO deriving Repr (function field in byToken)

/-- Trust bridge: authorization for a cross-bubble claim transfer.
    auth selects the gate check (.byAgent: named presenter checked by identity;
    .byToken: predicate applied to auth_token — any credential the deployer chooses).
    scope is a deployer annotation recording which claim categories this bridge is
    intended to cover; `c_valid_export` does not inspect it — enforcement is
    agent-layer policy above the formal model. [] conventionally means all claims. -/
structure CTrustBridge where
  auth  : CTrustBridgeAuth  -- which gate check applies
  scope : List String       -- deployer annotation: intended claim categories; not enforced by c_valid_export
-- NO deriving Repr (auth may contain function)

/-- Export request: moving a deposit across bubble boundaries. -/
structure CExportRequest where
  deposit                : CDeposit
  source                 : CBubble
  target                 : CBubble
  presenting_agent       : CAgent           -- the agent asserting the transfer (used by byAgent path)
  via_trust_bridge       : Option CTrustBridge
  revalidated            : Bool
  auth_token             : Option ByteArray -- credential for byToken path (any bytes the bridge's token_ok accepts); none on agent path

/-- Header mutation on export: V gets extended with export metadata. -/
def mutate_header_for_export (d : CDeposit) (source : CBubble) : CDeposit :=
  { d with V := d.V ++ [s!"exported from {source.id}"] }

/-- Export is valid if: revalidated OR the trust bridge gate passes.
    byAgent:  presenting agent's id matches the bridge's authorized agent.
    byToken:  req.auth_token is Some tok and token_ok tok returns true. -/
def c_valid_export (req : CExportRequest) : Bool :=
  req.revalidated ||
  req.via_trust_bridge.any (fun tb =>
    match tb.auth with
    | .byAgent a       => a.id == req.presenting_agent.id
    | .byToken ok => req.auth_token.any ok)

/-- Import a deposit: creates new deposit with mutated header. -/
def c_import_deposit (req : CExportRequest) : Option CDeposit :=
  if c_valid_export req then
    some (mutate_header_for_export req.deposit req.source)
  else
    none


/-! ## Predicates on Concrete Types -/

/-- Certainty (Ladder): agent believes P with high confidence. -/
def c_certainty (a : CAgent) (P : CProp) : Prop :=
  P ∈ a.beliefs ∧ a.confidence P ≥ 70

/-- Knowledge (Bank): P has a valid deposit in bubble B. -/
def c_knowledge (B : CBubble) (P : CProp) : Prop :=
  ∃ d, d ∈ B.deposits ∧ d.claim = P ∧ d.τ > 0

/-- Consensus: multiple deposits agree on P in bubble B. -/
def c_consensus (B : CBubble) (P : CProp) : Prop :=
  (B.deposits.filter (fun d => d.claim = P)).length ≥ 2

/-- Deposit is redeemable: has valid constraint surface and path. -/
def c_redeemable (d : CDeposit) : Prop :=
  d.cs.domain ≠ "" ∧ d.cs.test_procedure ≠ "" ∧ d.V.length > 0

/-- Header preserved: S, E, V are all non-trivial. -/
def c_header_preserved (d : CDeposit) : Prop :=
  d.S > 0 ∧ d.E.length > 0 ∧ d.V.length > 0

/-- Header stripped: missing essential header fields. -/
def c_header_stripped (d : CDeposit) : Prop :=
  d.S = 0 ∨ d.E.length = 0 ∨ d.V.length = 0

/-- Deposit is fresh (not stale). -/
def c_fresh (d : CDeposit) (current_time : CTime) : Prop :=
  d.τ > current_time

/-- Deposit is stale. -/
def c_stale (d : CDeposit) (current_time : CTime) : Prop :=
  d.τ ≤ current_time


/-! ## Concrete Audit Channel

    Models finite V-verification throughput as a Nat capacity/volume pair.
    This is the concrete substrate for the DDoS channel-collapse proofs in
    EpArch.Adversarial.Concrete: when volume > capacity, c_process_V returns [],
    making the deposit's V field empty and letting the V gate fire. -/

/-- Concrete audit channel: capacity is the per-round V-check budget;
    volume is the per-round demand. The gap between them is what DDoS exploits. -/
structure CAuditChannel where
  capacity : Nat   -- max V-checks per round
  volume   : Nat   -- V-checks demanded per round
  deriving Repr, DecidableEq, Inhabited

/-- The threshold condition for V-channel collapse: once demand exceeds capacity,
    c_process_V cannot service all pending provenance checks and returns []. -/
def c_channel_overwhelmed (cc : CAuditChannel) : Prop :=
  cc.volume > cc.capacity

/-- Route a provenance chain through a channel.
    Returns the full chain when the channel's capacity covers it; returns the empty
    list otherwise.  An empty result is the concrete observable outcome of DDoS
    V-channel exhaustion: the channel never delivered the provenance check result. -/
def c_process_V (cc : CAuditChannel) (sources : CProvenance) : CProvenance :=
  if sources.length ≤ cc.capacity then sources else []


/-! ## Concrete Cost Model

    Step-counting model for the export-cost asymmetry argument.
    Publishing a claim = 1 step; verifying provenance = V.length + 1 steps minimum.
    The cost inequality is proved from definitions by omega — not an axiom. -/

/-- Concrete export cost: publishing a claim takes 1 computational step.
    Export is structurally cheap: one submission regardless of claim size. -/
def c_export_cost : Nat := 1

/-- Concrete verification cost: checking a provenance chain takes one step per
    source plus one kernel check. A deposit with V chain of length n costs n + 1 steps. -/
def c_verify_cost (d : CDeposit) : Nat := d.V.length + 1

/-- For any deposit with at least one provenance source, export costs strictly less
    than verification. Proved by `Nat.succ_lt_succ h` — no assumption required. -/
theorem c_export_cost_lt_verify_cost (d : CDeposit) (h : 0 < d.V.length) :
    c_export_cost < c_verify_cost d :=
  Nat.succ_lt_succ h


end EpArch.ConcreteModel
