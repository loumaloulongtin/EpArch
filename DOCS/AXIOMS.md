# Axiom Declarations

The formalization contains **zero `axiom` declarations**.

> **Note:** “zero global axioms” does not mean “zero assumptions in an absolute sense.”
> EpArch works with explicit base commitments and context-bundled conditions where appropriate;
> those boundaries are made explicit rather than hidden.
> That is intentional: the framework does not claim terminal epistemic closure,
> and PRP rules out eliminating every assumption boundary altogether.

This document records the current assumption boundary and how the prior axiom surface was resolved.

---

## Current Assumption Boundary

### CommitmentsCtx — All Commitments Now Proved

**File:** `EpArch/Commitments.lean`

`CommitmentsCtx` is now an **empty structure** — all 8 architectural commitments have
been derived as standalone theorems.  No hypothesis fields remain.

C1 (Traction/Authorization Split) was the last remaining field.  It is now expressed
by two mechanism-grounded named theorems:

| Theorem | Direction | Mechanism | Witness structure |
|---------|-----------|-----------|-------------------|
| `innovation_allows_traction_without_authorization` | `certainty_L ⊄ knowledge_B` | Innovation / pre-authorization exploration | `PreAuthTractionWitness` |
| `caveated_authorization_does_not_force_certainty` | `knowledge_B ⊄ certainty_L` | Header burden (stale τ / unredeemable) | `BurdensomeAuthWitness` |

Neither theorem makes a universal `∀ a B P` claim; each is scoped to its named
scenario witness.  This eliminates the single black-box `traction_auth_split` hypothesis
and replaces it with two structurally grounded, independently falsiﬁable theorems.

**C2 is no longer a hypothesis.** `no_global_ledger` was removed from `CommitmentsCtx`
and replaced by the proved theorem `WorldCtx.no_ledger_tradeoff` (EpArch CAP Theorem)
in `WorldCtx.lean`. It is derived from `W_partial_observability` and `obs_based`;
see §Proved Theorems below.

**C4b is no longer a hypothesis.** `consensus_not_sufficient` was removed from
`CommitmentsCtx` and replaced by the proved theorem
`redeemability_requires_more_than_consensus` in `Commitments.lean`. It is derived
from `intra_bubble_only` (structural predicate: ∀ cs, ¬path_route_exists d cs)
and the definitional gap between `consensus` (intra-bubble, formally `True`) and
`redeemable` (requires opaque external evidence: `path_route_exists`, `contact_was_made`,
`verdict_discriminates`); see §Proved Theorems below.

**C7b is no longer a hypothesis.** `header_asymmetry` was removed from `CommitmentsCtx`.
The diagnosability / hardness result (`header_stripping_harder`,
`metadata_stripping_strictly_enlarges`) is proved via the admissible completion-space
model: stripping removes all (S, E, V) admissibility constraints, strictly enlarging
the completion space, which is the structural ground for the score ordering 0 < 3.

`sticky` and `proxy_battles` are **defined predicates** (not opaque), derived from
event-level export witnesses — **no type-universe nontriviality premise needed**:

- **`dispute_about B d`** — some other bubble B2 has exported a counter-deposit d'
  to B covering the same claim as d but disagreeing on ≥ 1 header field (S, E, or V).
  Since d' has the *same type parameters* as d, `⟨d'.h.S, d'.h.E, d'.h.V⟩` is a
  same-type `Completion` witness: **`dispute_about_to_alternative`** proves
  `has_alternative_completion d` directly from the dispute.

- **`cross_axis_dispute_about B d`** — B receives two counter-deposits from
  (possibly different) bubbles: dS disagreeing on the S-axis and dE on the E-axis.
  This directly witnesses the two fault-axis completions needed for `proxy_battles`;
  **`cross_axis_to_dispute_about`** projects it to `dispute_about`.

- **`sticky B P d`** holds when `dispute_about B d` and the header is stripped:
  d'.h provides the alternative completion; no `has_cross_field_alternatives` needed.

- **`proxy_battles B P d`** holds when `cross_axis_dispute_about B d` and the header
  is stripped: dS and dE directly supply the S-blaming and E-blaming completions.

`header_stripping_produces_pathology` takes `dispute_about B d` and
`cross_axis_dispute_about B d`; the former `has_cross_field_alternatives d`
premise is **entirely eliminated** — the type-universe nontriviality condition
is replaced by the event-level export structure.

`dispute B P` is a **defined predicate**: it holds when bubble B exports
deposit d1 to bubble B2, B2 exports deposit d2 back to B, both for claim P, but
d1 and d2 disagree on at least one header field (S, E, or V).  This cross-bubble
export conflict is the structural origin of dispute: two bubbles hold incompatible
evidence for the same claim and are both pushing to export it.  For the pathology
theorems, the more targeted `dispute_about B d` and `cross_axis_dispute_about B d`
are used (see above).

Forward theorems (`innovation_allows_traction_without_authorization`,
`caveated_authorization_does_not_force_certainty`, `no_universal_ledger`,
`redeemability_requires_more_than_consensus`, `header_stripping_produces_pathology`,
and their contradiction companions) are all proved standalone theorems — none
are conditioned on `(C : CommitmentsCtx ...)` fields, as CommitmentsCtx is empty.

### Opaque Domain Primitives

Opaque constants (`opaque foo : T`) are uninterpreted domain predicates.
They are not `axiom` declarations but are underspecified by design —
their intended interpretation is given in comments, not derived.

Key opaque primitives:

| Primitive | File | Role |
|-----------|------|------|
| `agentTraction` | Basic.lean | Agent's private traction assignment (Claim → LadderStage); hook for psychology/cognition |
| `ignores_bank_signal` | Basic.lean | Whether agent's review channel is closed (separate from `certainty_L`) |
| `header_preserved` | Header.lean | Deposit has header intact (vs. stripped in transmission); `header_stripped` is a def: `¬header_preserved` |
| `path_route_exists` / `contact_was_made` / `verdict_discriminates` | Commitments.lean | Opaque evidence predicates for VerificationPath (C4: redeemability external to consensus) |
| `pushback` | Commitments.lean | Agent-level contestation of a deposit; used in C6 repair-loop machinery |
| `withdraw` / `exportDep` / `TrustBridge` / `Revalidate` / `RepairAction` | Bank.lean | Abstract behavioral hooks (withdrawal reliance, cross-bubble export, trust bridge, revalidation, repair action type) |
| AdversarialBase.lean opaques | AdversarialBase.lean | 21 opaques constituting the adversarial model: attack channel (`AuditChannel`, `channel_capacity`, `attack_volume`), DDoS state (`ladder_overloaded`, `V_channel_exhausted`, etc.), countermeasures (`cheap_validator_reachable`, `trust_bridge_on_hand`, etc.), cost primitives (`export_cost`, `import_defense_cost`) — see §Adversarial Model in THEOREMS.md |

Note: `reliance_level` and `blast_radius` are **`def`s** (not opaques), grounded in `DepositDynamics` struct fields (`dd.relying_agents` and `dd.cascade_agents` respectively). The behavioral theorems `success_driven_bypass` and `blast_radius_scales_with_reliance` are proved over these defs.

Note: `certainty_L`, `hasDeposit`, and `deposited` are now **`def`s**, not opaques:

Note: `certainty_L`, `hasDeposit`, and `deposited` are now **`def`s**, not opaques:
- `certainty_L a P := ladder_stage a P = .Certainty` (Basic.lean)
- `deposited B d := d.status = .Deposited ∧ d.bubble = B` (Bank.lean)
- `hasDeposit B P := ∃ S E V d, d.status = .Deposited ∧ d.bubble = B ∧ d.P = P` (Bank.lean)

All theorems that use these primitives state their dependence explicitly via
`(C : WorldCtx)` or direct premises.

---

## Resolution of Former Axioms

### Bank Operators (formerly 18 axioms → 0)

The lifecycle operators (`Validate_B`, `Accept_B`, `Challenge_B`, `Repair_B`,
`Revoke_B`, `Restore_B`, `Export_B_C`, `Import_C`, `repair`, `τ_refresh`,
`deprecate`) and their status postcondition theorems are now concrete
guarded struct-update definitions. Each operator is grounded in
`StepSemantics.lean` and witnessed by `ConcreteLedgerModel.lean`.

`knowledge_B` is a `def` (= `hasDeposit`); `KnowledgeIffDeposited` proved by `Iff.rfl`.
`deposited` and `hasDeposit` are now **`def`s** grounded in `DepositStatus` fields (not opaque):
`deposited B d := d.status = .Deposited ∧ d.bubble = B`;
`hasDeposit B P := ∃ S E V d, d.status = .Deposited ∧ d.bubble = B ∧ d.P = P`.
Two behavioral theorems over concrete definitions
(`success_driven_bypass` over `reliance_level`; `blast_radius_scales_with_reliance` over `blast_radius`)
ground the reliance/cascade surface in `DepositDynamics` fields.

### Structural Commitments (formerly up to 12 axioms → 0)

All 8 commitments are now **proved**. `CommitmentsCtx` is fully empty. The table below records each commitment and how it was discharged:

| Commitment | Resolution |
|------------|------------|
| C3 (`SEVFactorization`) | Proved by rfl |
| C5 (`ExportGating`) | Proved from LTS export constructors |
| C6b (`NoSelfCorrectionWithoutRevision`) | Proved from StepSemantics |
| C8 (`TemporalValidity`) | Proved from header τ definition |
| C2 (`NoGlobalLedger`) | **Proved** as `WorldCtx.no_ledger_tradeoff` (EpArch CAP Theorem) from `W_partial_observability` + `obs_based` in `WorldCtx.lean` |
| C4b (`ConsensusNotSufficient`) | **Proved** as `redeemability_requires_more_than_consensus` from `intra_bubble_only` + definitional gap between `consensus` (`True`) and `redeemable` (opaque external evidence) in `Commitments.lean` |
| C7b (`HeaderStrippingHarder`) | **Proved** via admissible completion-space model: `metadata_stripping_strictly_enlarges` establishes strict inclusion admissible_full ⊂ admissible_stripped; `header_stripping_harder` is its numeric corollary (0 < 3 fields). `dispute_about B d` — an incoming same-type counter-deposit d' disagreeing on ≥1 header field — directly witnesses `has_alternative_completion d` via `dispute_about_to_alternative` (no type-universe condition). `cross_axis_dispute_about B d` — two counter-deposits dS, dE blaming S and E respectively — directly witnesses both axes for `proxy_battles`. `sticky B P d` (admissible-space multiplicity) proved by `stripped_dispute_is_sticky` from `dispute_about B d` alone; `proxy_battles B P d` (cross-axis underdetermination) proved by `stripped_dispute_has_proxy_battles` from `cross_axis_dispute_about B d` alone. **`has_cross_field_alternatives` premise entirely eliminated** — replaced by event-level export structure. `header_stripping_produces_pathology` takes `dispute_about` + `cross_axis_dispute_about`; zero opaque or type-universe hypotheses. |
| C1 (`TractionAuthSplit`) | **Proved** as two mechanism-grounded theorems: `innovation_allows_traction_without_authorization` (`PreAuthTractionWitness`) + `caveated_authorization_does_not_force_certainty` (`BurdensomeAuthWitness`). `CommitmentsCtx` is now an **empty structure**. |

### Invariants (formerly 5 axioms → 0)

| Former Axiom | Resolution |
|--------------|------------|
| `no_deposit_without_redeemability` | Removed: universally-quantified form was inconsistent. Intent expressed by `redeemable` predicate. |
| `no_withdrawal_without_acl` | Replaced by `grounded_no_withdrawal_without_acl`, proved from `StepSemantics.Step.withdraw`. |
| `no_export_without_gate` | Replaced by `grounded_no_export_without_gate`, proved from `StepSemantics.Step.export`. |
| `deposit_kind` | Now a definition in `Commitments.lean`. |
| `worldstate_requires_finite_τ` | Proved from the `deposit_kind` definition. |

---

## Axiom-Free Modules

No `axiom` declarations appear anywhere in the codebase. All modules introduce
only theorems, definitions, and opaque constants.

| Module | Role |
|--------|------|
| `Basic.lean` | Core types |
| `Header.lean` | S/E/V header structure |
| `Bank.lean` | Bank substrate (concrete operators; `deposited`/`hasDeposit`/`knowledge_B`/`reliance_level`/`blast_radius` are defs; opaque: `withdraw`, `exportDep`, `TrustBridge`, `Revalidate`, `RepairAction`) |
| `Commitments.lean` | Structural commitments (all 8 proved; CommitmentsCtx is empty) |
| `Invariants.lean` | Grounded operational invariants |
| `StepSemantics.lean` | Concrete step semantics |
| `Theorems.lean` | Derived theorems |
| `ConcreteLedgerModel.lean` | Constructive concrete model |
| All others | Theorem-bearing or definitional surfaces only |
