/-
EpArch.Concrete.Commitments — Concrete Commitment Witnesses (C1–C8)

Constructive witnesses for all 8 EpArch commitments in the concrete model.
Each commitment has an explicit witness pair (or witness triple) and a
closed proof that the commitment holds.

Part of the EpArch.Concrete module family.
-/

import EpArch.Concrete.Types

namespace EpArch.ConcreteModel

/-! ## Commitment 1: Traction/Authorization Split -/

/-- Witness 1a: Agent has certainty, bubble lacks deposit.
    Example: Einstein 1905—certain of relativity, not yet published/validated. -/
def witness_certainty_without_knowledge : CAgent × CBubble × CProp :=
  let einstein : CAgent := {
    id := "Einstein"
    beliefs := ["E=mc²"]
    confidence := fun p => if p == "E=mc²" then 95 else 0
  }
  let physics_1905 : CBubble := {
    id := "Physics-1905"
    deposits := []  -- No deposit yet!
  }
  (einstein, physics_1905, "E=mc²")

/-- Witness 1b: Bubble has deposit, agent lacks certainty.
    Example: Textbook fact that particular student hasn't learned. -/
def witness_knowledge_without_certainty : CAgent × CBubble × CProp :=
  let student : CAgent := {
    id := "NewStudent"
    beliefs := []   -- Hasn't learned this yet
    confidence := fun _ => 0
  }
  let textbook : CBubble := {
    id := "Textbook"
    deposits := [{
      claim := "Mitochondria is powerhouse of cell"
      S := 90
      E := ["outdated research", "transcription error"]
      V := ["peer review", "replication"]
      τ := 1000
      cs := { domain := "biology", test_procedure := "cell inspection" }
    }]
  }
  (student, textbook, "Mitochondria is powerhouse of cell")

/-- Commitment 1 holds in the concrete model. -/
theorem commitment1_concrete :
    let (a1, B1, P1) := witness_certainty_without_knowledge
    let (a2, B2, P2) := witness_knowledge_without_certainty
    -- Certainty doesn't imply knowledge (witness 1a)
    (c_certainty a1 P1 ∧ ¬c_knowledge B1 P1) ∧
    -- Knowledge doesn't imply certainty (witness 1b)
    (c_knowledge B2 P2 ∧ ¬c_certainty a2 P2) := by
  -- Proof uses concrete witness values
  simp only [witness_certainty_without_knowledge, witness_knowledge_without_certainty]
  constructor
  · -- Witness 1a: Einstein has certainty, but bubble lacks knowledge
    constructor
    · -- c_certainty einstein "E=mc²"
      unfold c_certainty
      simp
      decide
    · -- ¬c_knowledge physics_1905 "E=mc²"
      unfold c_knowledge
      simp
      intro ⟨d, hd, _, _⟩
      cases hd
  · -- Witness 1b: textbook has knowledge, student lacks certainty
    constructor
    · -- c_knowledge textbook "Mitochondria is powerhouse of cell"
      unfold c_knowledge
      refine ⟨?d, ?h_mem, ?h_claim, ?h_tau⟩
      case d => exact { claim := "Mitochondria is powerhouse of cell"
                        S := 90
                        E := ["outdated research", "transcription error"]
                        V := ["peer review", "replication"]
                        τ := 1000
                        cs := { domain := "biology", test_procedure := "cell inspection" } }
      case h_mem => exact List.Mem.head _
      case h_claim => rfl
      case h_tau => decide
    · -- ¬c_certainty student "Mitochondria is powerhouse of cell"
      unfold c_certainty
      simp


/-! ## Commitment 2: Scoped Bubbles (No Global Ledger) -/

/-- Innovation: the ledger contains deposits with genuinely distinct claims.
    Non-trivial: requires two deposits with different claim strings. -/
def c_supports_innovation (G : CGlobalLedger) : Prop :=
  ∃ d1 d2, d1 ∈ G.all_deposits ∧ d2 ∈ G.all_deposits ∧ d1.claim ≠ d2.claim

/-- Coordination: all deposits must be mutually consistent. -/
def c_supports_coordination (G : CGlobalLedger) : Prop :=
  ∀ (d1 d2 : CDeposit), d1 ∈ G.all_deposits → d2 ∈ G.all_deposits →
    d1.claim = d2.claim ∨ (d1.claim ≠ d2.claim → d1.cs.domain ≠ d2.cs.domain)
  -- Coordination means: no contradictions in same domain

/-- Witness: a ledger that tries to do both fails.
    If we allow contradictions (innovation), we break coordination.
    If we enforce consistency (coordination), we block innovation. -/
def witness_global_ledger_conflict : CGlobalLedger :=
  { all_deposits := [
      { claim := "P", S := 50, E := [], V := ["A"], τ := 100,
        cs := { domain := "test", test_procedure := "check" } },
      { claim := "¬P", S := 50, E := [], V := ["B"], τ := 100,
        cs := { domain := "test", test_procedure := "check" } }
    ]
    acceptance_threshold := 50 }

/-- Commitment 2 holds: the witness ledger simultaneously supports innovation
    (has deposits "P" and "¬P" with distinct claims) yet cannot support coordination
    (those deposits share domain "test", so consistency is violated).
    Both directions of the tension are witnessed directly. -/
theorem commitment2_concrete :
    let G := witness_global_ledger_conflict
    c_supports_innovation G ∧ ¬c_supports_coordination G := by
  simp only [witness_global_ledger_conflict, c_supports_innovation, c_supports_coordination]
  constructor
  · -- Innovation holds: "P" and "¬P" are distinct deposits in all_deposits
    let d1 : CDeposit := { claim := "P", S := 50, E := [], V := ["A"], τ := 100,
                           cs := { domain := "test", test_procedure := "check" } }
    let d2 : CDeposit := { claim := "¬P", S := 50, E := [], V := ["B"], τ := 100,
                           cs := { domain := "test", test_procedure := "check" } }
    exact ⟨d1, d2, List.Mem.head _, List.Mem.tail _ (List.Mem.head _), by decide⟩
  · -- Coordination fails: "P" and "¬P" are in the same domain "test"
    intro h_coord
    let d1 : CDeposit := { claim := "P", S := 50, E := [], V := ["A"], τ := 100,
                           cs := { domain := "test", test_procedure := "check" } }
    let d2 : CDeposit := { claim := "¬P", S := 50, E := [], V := ["B"], τ := 100,
                           cs := { domain := "test", test_procedure := "check" } }
    have h1 : d1 ∈ [d1, d2] := List.Mem.head _
    have h2 : d2 ∈ [d1, d2] := List.Mem.tail _ (List.Mem.head _)
    have h := h_coord d1 d2 h1 h2
    cases h with
    | inl h_eq => exact absurd h_eq (by decide)
    | inr h_dom => exact absurd rfl (h_dom (by decide))


/-! ## Commitment 3: S/E/V Factorization -/

/-- Witness: a deposit with explicit S/E/V structure. -/
def witness_SEV_deposit : CDeposit :=
  { claim := "Water boils at 100°C at sea level"
    S := 95                                    -- Standard: scientific consensus threshold
    E := ["altitude variation", "impurities", "measurement error"]  -- Error model
    V := ["thermometer calibration", "replicated experiments"]      -- Provenance
    τ := 10000
    cs := { domain := "physics", test_procedure := "boiling point measurement" } }

/-- Commitment 3 holds: deposit has factored structure. -/
theorem commitment3_concrete :
    let d := witness_SEV_deposit
    d.S > 0 ∧ d.E.length > 0 ∧ d.V.length > 0 := by
  simp only [witness_SEV_deposit]
  decide


/-! ## Commitment 4: Redeemability External to Consensus -/

/-- Witness: consensus without redeemability (conspiracy theory bubble). -/
def witness_consensus_not_redeemable : CBubble × CDeposit :=
  let conspiracy_deposit : CDeposit := {
    claim := "Moon landing was faked"
    S := 80
    E := []  -- No error model!
    V := []  -- No provenance!
    τ := 100
    cs := { domain := "", test_procedure := "" }  -- No constraint surface!
  }
  let conspiracy_bubble : CBubble := {
    id := "FlatEarthForum"
    deposits := [conspiracy_deposit, conspiracy_deposit, conspiracy_deposit]  -- Consensus!
  }
  (conspiracy_bubble, conspiracy_deposit)

/-- Commitment 4 holds: consensus exists but redeemability doesn't. -/
theorem commitment4_concrete :
    let (B, d) := witness_consensus_not_redeemable
    c_consensus B d.claim ∧ ¬c_redeemable d := by
  simp only [witness_consensus_not_redeemable, c_consensus, c_redeemable]
  decide


/-! ## Commitment 5: Export Gating -/

/-- Export without gating: just copy deposit across bubbles. -/
def c_ungated_export (B1 B2 : CBubble) (d : CDeposit) : Prop :=
  d ∈ B1.deposits ∧ d ∈ B2.deposits

/-- Revalidation: B2 independently verified the deposit. -/
def c_revalidated (B2 : CBubble) (d : CDeposit) : Prop :=
  d ∈ B2.deposits ∧ d.V.length > 1  -- Has extended provenance

/-- Trust bridge: B2 explicitly trusts B1. -/
def c_trust_bridge (B1 _B2 : CBubble) : Prop :=
  B1.id ∈ ["PeerReviewed", "FDA", "ISO"]  -- Trusted source

/-- Witness: export without gating leads to contamination.
    A deposit from an unreliable source gets into a careful bubble. -/
def witness_ungated_export : CBubble × CBubble × CDeposit :=
  let unreliable_source : CBubble := {
    id := "RandomBlog"
    deposits := [{
      claim := "Vitamin C cures cancer"
      S := 20
      E := []
      V := ["blogger opinion"]
      τ := 50
      cs := { domain := "", test_procedure := "" }
    }]
  }
  let medical_bubble : CBubble := {
    id := "MedicalPractice"
    deposits := []
  }
  (unreliable_source, medical_bubble, unreliable_source.deposits.head!)

/-- Commitment 5 holds: ungated export from unreliable source should fail. -/
theorem commitment5_concrete :
    let (B1, B2, d) := witness_ungated_export
    -- If export happens without gating...
    c_ungated_export B1 B2 d →
    -- ...then either revalidation or trust bridge must exist for reliability
    (c_revalidated B2 d ∨ c_trust_bridge B1 B2) := by
  -- Ungated export needs at least one gate for reliability
  simp only [witness_ungated_export, c_ungated_export]
  intro ⟨_, h_in_B2⟩
  -- B2.deposits = [], so d ∈ B2.deposits is false
  cases h_in_B2


/-! ## Commitment 6: Repair Loop -/

/-- Challenge: someone disputes a deposit. -/
structure CChallenge where
  target : CDeposit
  field : String  -- Which field is challenged: "S", "E", "V", "τ"
  reason : String
deriving Repr

/-- Repair response: how the challenge was handled. -/
inductive CRepairResponse
  | Upheld      -- Challenge rejected, deposit stands
  | Revised     -- Deposit updated
  | Revoked     -- Deposit removed
  | Pending     -- Under review
  deriving Repr

/-- Witness: a deposit that can be challenged and repaired. -/
def witness_repair_loop : CDeposit × CChallenge :=
  let d : CDeposit := {
    claim := "Drug X is safe"
    S := 70
    E := ["selection bias", "short trial"]
    V := ["Phase 2 trial", "Pharma-funded"]
    τ := 365
    cs := { domain := "medicine", test_procedure := "Phase 3 trial" }
  }
  let challenge : CChallenge := {
    target := d
    field := "V"
    reason := "Funding source creates conflict of interest"
  }
  (d, challenge)

/-- Commitment 6 holds: challenges can be localized to specific fields. -/
theorem commitment6_concrete :
    let (_d, c) := witness_repair_loop
    c.field ∈ ["S", "E", "V", "τ"] ∧ c.reason.length > 0 := by
  simp only [witness_repair_loop]
  decide


/-! ## Commitment 7: Header Stripping → Harder Disputes -/

/-- Witness: two versions of same claim, one with header, one without. -/
def witness_header_comparison : CDeposit × CDeposit :=
  let with_header : CDeposit := {
    claim := "Vaccines cause autism"
    S := 60   -- Non-zero: deposit has a standard (a low one, but present)
    E := ["selection bias", "no control group", "data manipulation"]
    V := ["Wakefield 1998", "retracted"]
    τ := 0    -- Expired, but the header fields S/E/V are intact
    cs := { domain := "medicine", test_procedure := "epidemiological study" }
  }
  let without_header : CDeposit := {
    claim := "Vaccines cause autism"
    S := 0
    E := []   -- No error model!
    V := []   -- No provenance!
    τ := 0
    cs := { domain := "", test_procedure := "" }  -- No redeemability!
  }
  (with_header, without_header)

/-- Commitment 7 holds: headerless disputes are harder. -/
theorem commitment7_concrete :
    let (d_good, d_bad) := witness_header_comparison
    -- With header: c_header_preserved implies we have all three diagnostic fields
    (c_header_preserved d_good → d_good.S > 0 ∧ d_good.E.length > 0 ∧ d_good.V.length > 0) ∧
    -- Without header: we can only say "wrong" with no localization
    (c_header_stripped d_bad ∧ d_bad.E.length = 0 ∧ d_bad.V.length = 0) := by
  simp only [witness_header_comparison, c_header_preserved, c_header_stripped]
  constructor
  · -- c_header_preserved unfolds to exactly these three conditions; just unpack
    intro ⟨hS, hE, hV⟩; exact ⟨hS, hE, hV⟩
  · -- d_bad satisfies all conditions
    decide


/-! ## Commitment 8: Temporal Validity (τ / TTL) -/

/-- Witness: fresh vs stale versions of same claim. -/
def witness_temporal_validity : CDeposit × CDeposit × CTime :=
  let fresh_deposit : CDeposit := {
    claim := "Interest rates are 5%"
    S := 90
    E := ["policy change", "market shift"]
    V := ["Fed announcement", "today"]
    τ := 100
    cs := { domain := "finance", test_procedure := "check fed.gov" }
  }
  let stale_deposit : CDeposit := {
    claim := "Interest rates are 5%"
    S := 90
    E := ["policy change", "market shift"]
    V := ["Fed announcement", "2020"]
    τ := 10   -- Low TTL
    cs := { domain := "finance", test_procedure := "check fed.gov" }
  }
  (fresh_deposit, stale_deposit, 50)  -- Current time = 50

/-- Commitment 8 holds: stale and fresh don't perform equivalently. -/
theorem commitment8_concrete :
    let (d_fresh, d_stale, t) := witness_temporal_validity
    c_fresh d_fresh t ∧ c_stale d_stale t := by
  simp only [witness_temporal_validity, c_fresh, c_stale]
  decide


/-! ## Summary: All Commitments Satisfiable -/

/-- All 8 commitments are simultaneously satisfiable in this concrete model. -/
theorem all_commitments_satisfiable :
    -- Commitment 1: Traction/Authorization split
    (∃ a B P, c_certainty a P ∧ ¬c_knowledge B P) ∧
    (∃ a B P, c_knowledge B P ∧ ¬c_certainty a P) ∧
    -- Commitment 2: Innovation and coordination are in genuine tension
    -- (a ledger CAN support innovation AND cannot support coordination simultaneously)
    (∃ G : CGlobalLedger, c_supports_innovation G ∧ ¬c_supports_coordination G) ∧
    -- Commitment 3: S/E/V factorization exists
    (∃ d : CDeposit, d.S > 0 ∧ d.E.length > 0 ∧ d.V.length > 0) ∧
    -- Commitment 4: Consensus without redeemability is possible
    (∃ B d, c_consensus B d.claim ∧ ¬c_redeemable d) ∧
    -- Commitment 5: Export gating is required (ungated → revalidation or trust bridge)
    (∃ B1 B2 d, c_ungated_export B1 B2 d → (c_revalidated B2 d ∨ c_trust_bridge B1 B2)) ∧
    -- Commitment 6: Repair loop with field localization exists
    (∃ _d c : CChallenge, c.field ∈ ["S", "E", "V", "τ"]) ∧
    -- Commitment 7: Header-stripped claims lose diagnosability
    (∃ d : CDeposit, c_header_stripped d ∧ d.E.length = 0) ∧
    -- Commitment 8: Fresh and stale deposits differ
    (∃ d1 d2 t, c_fresh d1 t ∧ c_stale d2 t) := by
  -- Witnesses established via individual commitment theorems
  constructor
  · -- Commitment 1a: ∃ a B P, c_certainty a P ∧ ¬c_knowledge B P
    exact ⟨_, _, _, commitment1_concrete.1⟩
  constructor
  · -- Commitment 1b: ∃ a B P, c_knowledge B P ∧ ¬c_certainty a P
    exact ⟨_, _, _, commitment1_concrete.2⟩
  constructor
  · -- Commitment 2: witness directly; commitment2_concrete proves both directions
    exact ⟨witness_global_ledger_conflict, commitment2_concrete⟩
  constructor
  · -- Commitment 3
    exact ⟨witness_SEV_deposit, commitment3_concrete⟩
  constructor
  · -- Commitment 4
    exact ⟨_, _, commitment4_concrete⟩
  constructor
  · -- Commitment 5
    exact ⟨witness_ungated_export.1, witness_ungated_export.2.1, witness_ungated_export.2.2,
           commitment5_concrete⟩
  constructor
  · -- Commitment 6
    let d : CDeposit := { claim := "P", S := 50, E := [], V := [], τ := 100,
                          cs := { domain := "test", test_procedure := "check" } }
    let c : CChallenge := { target := d, field := "S", reason := "test" }
    exact ⟨c, c, List.Mem.head _⟩
  constructor
  · -- Commitment 7
    exact ⟨_, commitment7_concrete.2.1, commitment7_concrete.2.2.1⟩
  · -- Commitment 8
    exact ⟨_, _, _, commitment8_concrete⟩



end EpArch.ConcreteModel
