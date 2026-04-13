/-
EpArch/Concrete/Types.lean — Concrete Type Definitions

Ground-level concrete types for the EpArch non-vacuity witness:
  CProp = String, CStandard = Nat, CErrorModel/CProvenance = List String.
No imports required — all types are ground Lean 4 types.

Part of: EpArch/Concrete/ split of ConcreteLedgerModel.lean
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

/-- Trust bridge: explicit trust relationship between bubbles. -/
structure CTrustBridge where
  source_bubble : String
  target_bubble : String
  accountability : String    -- Who is responsible if export fails
  scope : List String        -- What claims are covered
  deriving Repr

/-- Export request: moving a deposit across bubble boundaries. -/
structure CExportRequest where
  deposit : CDeposit
  source : CBubble
  target : CBubble
  via_trust_bridge : Option CTrustBridge
  revalidated : Bool
  deriving Repr

/-- Header mutation on export: V gets extended with export metadata. -/
def mutate_header_for_export (d : CDeposit) (source : CBubble) : CDeposit :=
  { d with V := d.V ++ [s!"exported from {source.id}"] }

/-- Export is valid if: revalidated OR trust bridge exists. -/
def c_valid_export (req : CExportRequest) : Bool :=
  req.revalidated ||
  (req.via_trust_bridge.isSome &&
   req.via_trust_bridge.any (fun tb => tb.source_bubble == req.source.id))

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



end EpArch.ConcreteModel
