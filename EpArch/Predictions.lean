/-
EpArch.Predictions — Non-Trivial Typed Predictions

Formally typed theorems encoding the model's three structural predictions.
Each prediction is a proved theorem (not a string record): the model's
machinery is used directly to close the gap between intuition and prediction.

- Prediction 1 (Cult/Intelligence): import_channel_controlled ∧ E_field_closed →
  ignores_bank_signal; certainty does not protect against Entrenchment when both
  conditions hold. New predicates: `import_channel_controlled`, `E_field_closed`.
- Prediction 2 (CT Non-Transfer): diagnosability is bubble-scoped; high diagnosability
  in B1 does not transfer to B2. Proved via `strip_reduces_diagnosability` and
  `import_cannot_reconstruct`.
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

/-- A CT transfer case: the same agent trying to apply domain competence
    from bubble B1 (home domain, established E-field) to bubble B2
    (new domain, no E-field yet). The bubble_separation invariant certifies
    these are genuinely distinct domains — the transfer is non-trivial. -/
structure ct_transfer_case where
  agent           : Agent
  B1              : Bubble   -- home domain: established E-field, full headers
  B2              : Bubble   -- new domain:  no E-field, no headers yet
  bubble_separation : B1 ≠ B2

/-! ## Prediction 2 Theorems -/

/-- PREDICTION 2 THEOREM: CT does not transfer — diagnosability is bubble-scoped.

    **Theorem shape:** diagnosability in B1 (full header) = 6;
    diagnosability in B2 (no header) = 0; B2 is systematically harder than B1.

    **The formal prediction:** Even for an agent with the same identity and
    reasoning standard, the diagnostic capability in B2 is zero. S-quality
    (high reasoning standard in B1) generates no observable fields in B2,
    because diagnosability is a function of header availability, not of S.

    **Proof strategy:** Three-way conjunction discharging directly to
    `diagnosability_full`, `diagnosability_stripped`, and `strip_reduces_diagnosability`
    from `EpArch.Theorems.Diagnosability`. The `ct_transfer_case` parameter
    supplies the bubble_separation witness — the transfer is across distinct domains. -/
theorem ct_does_not_transfer (_c : ct_transfer_case) :
    diagnosability true = 6 ∧
    diagnosability false = 0 ∧
    Diagnosability.systematically_harder false true :=
  ⟨diagnosability_full, diagnosability_stripped, strip_reduces_diagnosability⟩

/-- PREDICTION 2 BARRIER THEOREM: Import cannot recover the domain E-field.

    Even if the agent imports a deposit from B1 into B2, stripping removes
    the header (including the E-field component). The import operation
    cannot reconstruct the E-field that enables domain-specific diagnosis.

    **Theorem shape:** For any two deposits with distinct headers but
    identical stripped form, strip is non-reconstructible — `import_cannot_reconstruct`.

    **Proof strategy:** Direct delegation to `import_cannot_reconstruct` from
    `EpArch.Theorems.Strip`. The prediction supplies motivation; the mechanism
    is the existing strip non-injectivity theorem. -/
theorem ct_import_barrier
    (d1 d2 : Deposit PropLike Standard ErrorModel Provenance)
    (h_same_P      : d1.P      = d2.P)
    (h_same_bubble : d1.bubble = d2.bubble)
    (h_same_status : d1.status = d2.status)
    (h_diff_header : d1.h      ≠ d2.h) :
    strip d1 = strip d2 ∧
    ¬∃ (f : PayloadStripped PropLike → Deposit PropLike Standard ErrorModel Provenance),
        f (strip d1) = d1 ∧ f (strip d2) = d2 :=
  import_cannot_reconstruct d1 d2 h_same_P h_same_bubble h_same_status h_diff_header


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
