/-
EpArch.ConditionalPredictions — Conditional Structural Predictions

Typed structural theorems establishing the model's conditional predictions:
results of the form "under structural conditions X, outcome Y holds" where X
is stated over architectural predicates (not empirical premises). Each theorem
is proved within the current kernel. The conditions themselves — agent psychology
bridges, bubble admission policies — are named opaques: the explicit unconditional
presuppositions. The predictions earn their place here, but they are waiting for an
agent model to correlate them: richer psychology or simulation machinery would let
the conditional premises be derived rather than supplied.

- Conditional Prediction 1 (Cult/Intelligence): Conditions: `import_gated` (bubble
  admission policy blocks disconfirming deposits, named opaque) + `structural_e_closure`
  (no deposit in current state has a header, derived def) + `h_bank_sealed` (named
  bridge field: import gating → Bank signal ignored). Under these conditions,
  `cult_produces_entrenchment` is proved. `structural_e_closure` is a derived def;
  `e_closure_blocks_field_check` is proved from `field_checkable_iff_header` — not an
  assumed invariant. `traction_sealed_under_control` is a proved conjunction.
- Conditional Prediction 2 (CT Non-Transfer): Condition: `ct_transfer_case` carries
  two B2-side deposits — `b2_stripped` (what arrives after import) and `b2_full` (the
  idealized full-header counterpart). Under the case structure, `ct_does_not_transfer`
  proves bubble separation + diagnosability collapse (6→0) + strip-indistinguishability
  with no reconstruction. Proof discharges via `import_cannot_reconstruct`.
- Conditional Prediction 3 (Sharing ≠ Belief): export (sharing) and certainty (belief)
  are structurally independent. Proved bundling of `testimony_is_export` and
  `certainty_not_exportable`; this one has minimal conditioning — it generalizes well.

Prediction 4 (audited entities / blast radius scaling) requires multi-agent reliance
semantics outside the current kernel scope. Its mechanism and falsifier are preserved
in DOCS/THEOREMS.md under "Deferred predictions".
-/

import EpArch.Basic
import EpArch.Header
import EpArch.Bank
import EpArch.Theorems.Pathologies
import EpArch.Theorems.Strip
import EpArch.Theorems.Diagnosability

namespace EpArch

open Diagnosability StepSemantics

universe u

variable {PropLike Standard ErrorModel Provenance : Type u}

/-! ========================================================================
    CONDITIONAL PREDICTION 1 — Intelligence Does Not Protect Against Cults

    Intuition says: intelligent people (high S-quality) should see through
    manipulation and resist cult recruitment.

    Conditional model result: S-quality is orthogonal to cult susceptibility
    when two structural conditions hold simultaneously:
    (1) `import_gated` — the bubble's admission policy blocks disconfirming
        deposits from reaching the agent (import side);
    (2) `structural_e_closure` — every deposit in the relevant state lacks
        a header, so no E-targeted challenge can be grounded (revision side).
    Together they seal the Bank correction pathway. Entrenchment follows from
    Certainty — regardless of S-quality — given the named bridge `h_bank_sealed`.

    The structural half (import gating + E-closure → `bank_signal_structurally_sealed`)
    is proved unconditionally. The psychology-coupling half — that structural sealing
    forces `ignores_bank_signal` — is the one explicit named conditional (the bridge
    field `h_bank_sealed`). An agent model that derived this from agent-internal
    dynamics would turn this into an unconditional result.
    ======================================================================== -/

/-! ## Conditional Prediction 1 Predicates and Bridge -/

/-- Import channel gating: the bubble's admission policy for agent a on claim P
    blocks disconfirming deposits from outside the approved provenance chains.
    Operationally, the bubble's Bank.Accept function acts as a whitelist filter;
    grounding this fully requires a richer policy model of Bank.Accept.
    Named opaque: this is the import-side trust boundary. -/
opaque import_gated (a : Agent) (B : Bubble) (P : Claim) : Prop

/-- Structural E-field closure: every deposit index in state s lacks a header.
    When this holds, `depositHasHeader s d_idx` is false for all indices, so
    `field_checkable s d_idx f` is false for every deposit and every field —
    no E-targeted challenge can be grounded in header inspection. -/
def structural_e_closure
    (s : SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  ∀ (d_idx : Nat), ¬depositHasHeader s d_idx

/-- E-closure implies no field is checkable.

    **Theorem shape:** `structural_e_closure s → ¬field_checkable s d_idx f`.

    **Proof strategy:** `field_checkable_iff_header` establishes that
    `field_checkable s d_idx f ↔ depositHasHeader s d_idx`. Given a proof of
    `field_checkable`, extract `depositHasHeader` via `.mp`, then refute it
    with `h d_idx` from `structural_e_closure`. Proved from library machinery
    — not an assumed invariant. -/
theorem e_closure_blocks_field_check
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (d_idx : Nat) (f : Field)
    (h : structural_e_closure s) :
    ¬field_checkable s d_idx f :=
  fun hf => h d_idx ((field_checkable_iff_header s d_idx f).mp hf)

/-- Structural Bank-signal seal: import gated AND E-field closed in state s.
    Together these block both correction modes:
    - import gating: no disconfirming deposit can enter B from outside
    - E-closure: no existing deposit in s can be challenged on any field
    This is the structural shadow of `ignores_bank_signal`. -/
def bank_signal_structurally_sealed
    (a : Agent) (B : Bubble) (P : Claim)
    (s : SystemState PropLike Standard ErrorModel Provenance) : Prop :=
  import_gated a B P ∧ structural_e_closure s

/-! ## Conditional Prediction 1 Structure -/

/-- A cult case: an agent in a bubble where the import channel is gated.

    The case carries two named components:
    - `h_import_gated` — the opaque import-gating condition (architectural, named)
    - `h_bank_sealed` — the one explicit named trust boundary: import gating →
      Bank signal ignored. The premise is `import_gated` (an architectural fact
      about the bubble's admission policy), not an anonymous `Bool = true`.

    The E-closure structural evidence is established separately by
    `traction_sealed_under_control` (a proved theorem); it is not duplicated here
    because entrenchment follows from import gating alone via `h_bank_sealed`. -/
structure cult_case where
  agent  : Agent
  bubble : Bubble
  claim  : Claim
  /-- Import channel gated: the bubble's admission policy blocks disconfirming
      deposits for this agent on this claim. -/
  h_import_gated : import_gated agent bubble claim
  /-- Named trust boundary: import gating → Bank signal ignored.
      The structural-to-psychological bridge: when the import channel is gated,
      the agent does not correct their Bank signal for this claim. The one
      named undeduced step in P1, replacing the anonymous Bool-keyed
      `traction_sealed` from the old design. The premise `import_gated` is an
      architectural fact (opaque), not a `Bool = true` equality. -/
  h_bank_sealed : import_gated agent bubble claim → ignores_bank_signal agent claim

/-! ## Conditional Prediction 1 Theorems -/

/-- PREDICTION 1 THEOREM: Import gating + E-closure seals the Bank signal.

    **Theorem shape:** `bank_signal_structurally_sealed c.agent c.bubble c.claim s`.

    **Progress over prior design:** This is a PROVED conjunction of
    `c.h_import_gated` and `h_eclosed` — not an extraction of a packed record
    invariant. `h_eclosed` is a real structural premise about the current state;
    the E-closure side is supported by `e_closure_blocks_field_check` (proved
    from the diagnosability machinery). -/
theorem traction_sealed_under_control (c : cult_case)
    (s : SystemState PropLike Standard ErrorModel Provenance)
    (h_eclosed : structural_e_closure s) :
    bank_signal_structurally_sealed c.agent c.bubble c.claim s :=
  ⟨c.h_import_gated, h_eclosed⟩

/-- PREDICTION 1 COROLLARY: Intelligence (Certainty) does not protect against
    Entrenchment in a cult context.

    **Theorem shape:** cult context + Certainty → Entrenched.

    **The formal prediction:** Being at the top Ladder stage does not prevent
    Entrenchment when the import channel is gated. Import gating seals the Bank
    signal (via `c.h_bank_sealed`); sealing plus Certainty yields Entrenchment
    regardless of S-quality.

    **Proof chain:**
    1. `c.h_import_gated` — the opaque architectural premise (import-gated)
    2. `c.h_bank_sealed c.h_import_gated` — named bridge: import-gated → ignores signal
    3. `⟨h_cert, ·⟩` — packs `certainty_L` + `ignores_bank_signal` → `Entrenched`

    E-closure structural evidence is established by `traction_sealed_under_control`;
    it is architecturally relevant but not required for this implication step.
    The one named trust boundary (`h_bank_sealed`) carries an architectural premise
    (`import_gated`), not an anonymous `Bool = true` equality. -/
theorem cult_produces_entrenchment (c : cult_case)
    (h_cert : certainty_L c.agent c.claim) :
    Entrenched c.agent c.claim :=
  ⟨h_cert, c.h_bank_sealed c.h_import_gated⟩


/-! ========================================================================
    CONDITIONAL PREDICTION 2 — Critical Thinking Does Not Transfer Across Domains

    Intuition says: critical thinking is a general skill; high S in one
    domain should carry over to a new domain.

    Conditional model result: under the `ct_transfer_case` structural conditions
    (two distinct bubbles, an actual stripped import, an idealized full-header
    counterpart), the diagnosability collapse and the import barrier are provable
    from library theorems. The conditioning here is light: the case structure
    names the deposits explicitly rather than quantifying over all agents and
    bubbles. An agent-model extension would identify which agents are susceptible
    to assuming CT transfer (e.g., agents whose S-estimate is anchored to B1
    performance) — the structural half is already closed.
    ======================================================================== -/

/-! ## Conditional Prediction 2 Structure -/

/-- A CT transfer case: the same agent expressing domain competence across two
    distinct bubbles. B1 is the home domain (where the E-field and full diagnostic
    headers were built); B2 is the new domain where the agent arrives.

    The case carries two B2-side deposits that together witness the
    information-loss event that formal CT non-transfer rests on:
    - `b2_stripped` is what actually arrives after import — same claim and
      lifecycle status as the home deposit, but the domain E-field is absent
      (the header was stripped when crossing the bubble boundary).
    - `b2_full` is the idealized counterpart: what CT transfer would require —
      a B2 deposit carrying the home domain's full header metadata.
    Their headers differ (`headers_differ`) but their stripped forms coincide
    (proved by `ct_does_not_transfer`). B2 cannot tell these apart from the
    payload alone, which is the formal content of "E-field must be built per
    domain, not carried over by import." -/
structure ct_transfer_case where
  agent             : Agent
  B1                : Bubble   -- home domain: established E-field, full headers
  B2                : Bubble   -- new domain: no domain E-field yet
  bubble_separation : B1 ≠ B2
  /-- The actual import in B2: arrived with the domain E-field absent. -/
  b2_stripped       : Deposit PropLike Standard ErrorModel Provenance
  b2_stripped_in_B2 : b2_stripped.bubble = B2
  /-- The idealized full-header counterpart in B2: same P, bubble, status but
      carrying the home domain's E-field — what CT transfer would look like. -/
  b2_full           : Deposit PropLike Standard ErrorModel Provenance
  b2_full_in_B2     : b2_full.bubble = B2
  same_P            : b2_stripped.P      = b2_full.P
  same_status       : b2_stripped.status = b2_full.status
  /-- The E-field does not survive the crossing: stripped header ≠ full header. -/
  headers_differ    : b2_stripped.h ≠    b2_full.h

/-! ## Conditional Prediction 2 Theorems -/

/-- PREDICTION 2 THEOREM: CT does not transfer — diagnosability is bubble-scoped
    and the import barrier is structurally irreversible.

    **Theorem shape:** For the specific deposits in this case:
    (1) B1 ≠ B2 — the two domains are genuinely distinct (from `c.bubble_separation`);
    (2) diagnosability with full header = 6 — home domain competence is real;
    (3) diagnosability without header = 0 — new domain starts blind;
    (4) `c.b2_stripped` and `c.b2_full` are indistinguishable by `strip`,
        and no reconstruction function can recover which header arrived —
        B2 cannot reconstitute the home E-field from the import payload alone.

    **Proof strategy:** Components (1)–(3) discharge to `c.bubble_separation`,
    `diagnosability_full`, and `diagnosability_stripped`. Component (4) discharges
    to `import_cannot_reconstruct` applied to `c.b2_stripped` and `c.b2_full`:
    same P (`c.same_P`), same bubble (both B2, via `c.b2_stripped_in_B2` and
    `c.b2_full_in_B2`), same status (`c.same_status`), different headers
    (`c.headers_differ`). The case structure — not just abstract header-boolean
    facts — drives the proof. -/
theorem ct_does_not_transfer (c : ct_transfer_case (PropLike := PropLike)
    (Standard := Standard) (ErrorModel := ErrorModel) (Provenance := Provenance)) :
    c.B1 ≠ c.B2 ∧
    diagnosability true = 6 ∧
    diagnosability false = 0 ∧
    strip c.b2_stripped = strip c.b2_full ∧
    ¬∃ (f : PayloadStripped PropLike → Deposit PropLike Standard ErrorModel Provenance),
        f (strip c.b2_stripped) = c.b2_stripped ∧ f (strip c.b2_full) = c.b2_full :=
  ⟨c.bubble_separation,
   diagnosability_full,
   diagnosability_stripped,
   import_cannot_reconstruct c.b2_stripped c.b2_full
     c.same_P
     (c.b2_stripped_in_B2.trans c.b2_full_in_B2.symm)
     c.same_status
     c.headers_differ⟩


/-! ========================================================================
    CONDITIONAL PREDICTION 3 — Sharing ≠ Belief

    Intuition says: people share what they believe; sharing tracks belief.

    Model result: sharing (export) and believing (deposit/certainty) are
    structurally independent — proved from the Pathologies library, minimal
    conditioning. This is the strongest of the three predictions: no agent
    model is needed to derive it. Export and certainty operate on separate
    architectural channels (bubble-to-bubble deposit operations vs. private
    Ladder stages); neither implies the other by construction.
    ======================================================================== -/

/-- PREDICTION 3 THEOREM: Sharing ≠ Belief — the export gate and the Ladder gate
    are architecturally independent.

    **Theorem shape:** Any testimony case t is either trust-import or
    revalidation (the export protocol proceeds regardless of Ladder state);
    AND a value_case at mere_certainty is not exportable (Ladder certainty
    carries no coordination value).

    **Proof strategy:** Two-part conjunction:
    - Direction 1 (sharing ≠ requiring belief): `testimony_is_export t` — the
      testimony/export operation fires at any Ladder stage; the export gate does
      not inspect certainty_L.
    - Direction 2 (belief ≠ sharing): `certainty_not_exportable v h_cert` — a
      value_case at mere_certainty carries no coordination value and is blocked
      from export. Proved by `certainty_not_exportable` from Pathologies. -/
theorem sharing_neq_belief
    (t : testimony_case (PropLike := PropLike))
    (v : value_case (PropLike := PropLike))
    (h_cert : is_mere_certainty v) :
    (trust_import t ∨ revalidation t) ∧ ¬exportable v :=
  ⟨testimony_is_export t, certainty_not_exportable v h_cert⟩

/-- PREDICTION 3 POSITIVE DIRECTION: Deposits are exportable with positive
    coordination value — the export gate fires precisely when authorization
    state (deposit) is present, not when mere traction is present.

    Proof: Direct delegation to `deposit_exportability`. -/
theorem deposit_exports_with_value (v : value_case (PropLike := PropLike)) :
    is_deposit v → exportable v ∧ coordination_value v > 0 :=
  deposit_exportability v

end EpArch
