/-
EpArch.Predictions — Non-Trivial Typed Predictions

Formally typed theorems encoding the model's three structural predictions.
Each prediction is a proved theorem (not a string record): the model's
machinery is used directly to close the gap between intuition and prediction.

- Prediction 1 (Cult/Intelligence): import_channel_controlled ∧ E_field_closed →
  ignores_bank_signal; certainty does not protect against Entrenchment when both
  conditions hold. New predicates: `import_channel_controlled`, `E_field_closed`.
- Prediction 2 (CT Non-Transfer): `ct_transfer_case` carries two B2-side deposits —
  `b2_stripped` (what actually arrives after import) and `b2_full` (the idealized
  full-header counterpart). `ct_does_not_transfer` proves bubble separation + the
  diagnosability collapse (6→0) + that `b2_stripped` and `b2_full` are
  indistinguishable by `strip` with no reconstruction possible — all from the case
  structure. Proof discharges via `import_cannot_reconstruct`.
- Prediction 3 (Sharing ≠ Belief): export (sharing) and certainty (belief) are
  structurally independent. Bundling theorem over `testimony_is_export` and
  `certainty_not_exportable`.

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

open Diagnosability

universe u

variable {PropLike Standard ErrorModel Provenance : Type u}

/-! ========================================================================
    PREDICTION 1 — Intelligence Does Not Protect Against Cults

    Intuition says: intelligent people (high S-quality) should see through
    manipulation and resist cult recruitment.

    Model says: S-quality (reasoning standard) is orthogonal to cult
    susceptibility when two structural conditions hold — import channel
    control and E-field closure. Both together seal the Bank signal pathway,
    making the agent's Ladder traction impervious to disconfirmation
    regardless of their reasoning quality.
    ======================================================================== -/

/-! ## Prediction 1 Structures and Predicates -/

/-- A cult case captures an agent whose import channel is ACL-controlled
    and whose E-field is closed to disconfirmation.

    These are the two structural conditions sufficient for Prediction 1:
    together they seal the Bank signal pathway, making the agent's traction
    on the claim independent of their reasoning standard (S-quality).

    The structural invariant `traction_sealed` requires any well-formed
    cult_case to certify at construction that both conditions together
    imply `ignores_bank_signal` — the formal assertion that the Bank
    doorbell cannot ring for this agent on this claim. -/
structure cult_case where
  agent  : Agent
  bubble : Bubble
  claim  : Claim
  /-- Is the import channel ACL-controlled (only approved deposits enter)? -/
  channel_controlled : Bool
  /-- Is the E-field closed (disconfirmation cannot succeed via challenge)? -/
  e_field_closed : Bool
  /-- Structural invariant: channel control + E-field closure seals the Bank
      signal pathway. The agent cannot receive disconfirming deposits (channel
      gated) and cannot have existing deposits challenged (E closed). Therefore
      the Ladder cannot be updated from the Bank side — `ignores_bank_signal`
      holds regardless of how high the agent's S-quality is. -/
  traction_sealed :
    channel_controlled = true → e_field_closed = true → ignores_bank_signal agent claim

/-- Import channel is ACL-controlled: only pre-approved deposits enter
    the agent's bubble. Disconfirming deposits from outside the approved
    set cannot reach the ledger. -/
def import_channel_controlled (c : cult_case) : Prop :=
  c.channel_controlled = true

/-- E-field is closed: challenges against existing deposits in this bubble
    cannot succeed. The error model admits no disconfirming outcomes. -/
def E_field_closed (c : cult_case) : Prop :=
  c.e_field_closed = true

/-! ## Prediction 1 Theorems -/

/-- PREDICTION 1 THEOREM: Channel control + E-closure seals the Bank signal.

    When both structural conditions hold, the agent's Bank signal channel
    for the claim is sealed: `ignores_bank_signal` holds.

    Proof: Extracts the `traction_sealed` structural invariant from the
    cult_case record. The invariant is required at construction, so any
    well-formed cult_case with both conditions true certifies the result. -/
theorem traction_sealed_under_control (c : cult_case) :
    import_channel_controlled c → E_field_closed c →
    ignores_bank_signal c.agent c.claim :=
  c.traction_sealed

/-- PREDICTION 1 COROLLARY: Intelligence (Certainty) does not protect against
    Entrenchment in a cult context.

    **Theorem shape:** cult context (both conditions) + Certainty → Entrenched.

    **The formal prediction:** Being at the top Ladder stage — the model of
    intelligence/rationality — does not prevent Entrenchment when import
    channels are controlled and the E-field is closed. Entrenchment requires
    only Certainty + ignores_bank_signal; the cult structure supplies the
    second condition independently of S-quality.

    **Proof strategy:** `cult_produces_entrenchment` packs `h_cert` (Certainty)
    and `traction_sealed_under_control c h_chan h_eclosed` (sealed signal) into
    the `Entrenched` constructor `⟨certainty_L, ignores_bank_signal⟩`. -/
theorem cult_produces_entrenchment (c : cult_case)
    (h_chan   : import_channel_controlled c)
    (h_eclosed : E_field_closed c)
    (h_cert  : certainty_L c.agent c.claim) :
    Entrenched c.agent c.claim :=
  ⟨h_cert, traction_sealed_under_control c h_chan h_eclosed⟩


/-! ========================================================================
    PREDICTION 2 — Critical Thinking Does Not Transfer Across Domains

    Intuition says: critical thinking is a general skill; high S in one
    domain should carry over to a new domain.

    Model says: S-quality is grounded in the agent's home bubble (B1)
    where an established E-field (domain error model) makes challenges and
    diagnosis possible. In a new domain (B2) the agent has no E-field yet,
    so diagnosability collapses to zero — regardless of how high S is in B1.
    Import cannot bridge the gap: stripping removes the E-field component.
    ======================================================================== -/

/-! ## Prediction 2 Structure -/

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

/-! ## Prediction 2 Theorems -/

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
    PREDICTION 3 — Sharing ≠ Belief

    Intuition says: people share what they believe; sharing tracks belief.

    Model says: sharing (export) and believing (deposit/certainty) are
    distinct operations on separate architectural channels. Export is a
    bubble-to-bubble operation on deposits; certainty is a private Ladder
    stage. Neither implies the other:
    - You can export without being at Certainty (social sharing without belief).
    - You can be at Certainty without having an exportable deposit (mere traction,
      no authorization value).
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
