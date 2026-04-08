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

### CommitmentsCtx — Structural Commitment as a Hypothesis Bundle

**File:** `EpArch/Commitments.lean`

One structural commitment remains as a field of `CommitmentsCtx` (modelled on `WorldCtx`).
It is not an `axiom` declaration; it is a hypothesis appearing explicitly in theorem
signatures:

    theorem T (C : CommitmentsCtx PropLike Standard ErrorModel Provenance) ...

| Field | Commitment | Plain reading |
|-------|------------|---------------|
| `traction_auth_split` | C1: certainty_L ⊥ knowledge_B (neither implies the other) | An agent can be certain of P without any bank deposit for P, and a bank deposit can exist without the agent being certain. Feeling sure and being authorized are different kinds of things. |

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
`sticky` and `proxy_battles` are **defined predicates** (not opaque), derived
from `has_cross_field_alternatives d`: `sticky B P d` holds when the stripped
admissible space contains ≥2 incompatible completions (no unique localization);
`proxy_battles B P d` holds when completions implicating distinct fault axes (S vs E)
both survive (cross-field underdetermination).  All three pathologies are proved by
`header_stripping_produces_pathology` from `h_cross` alone — no opaque hypotheses.

`dispute B P` is also now a **defined predicate**: it holds when bubble B exports
deposit d1 to bubble B2, B2 exports deposit d2 back to B, both for claim P, but
d1 and d2 disagree on at least one header field (S, E, or V).  This cross-bubble
export conflict is the structural origin of dispute: two bubbles hold incompatible
evidence for the same claim and are both pushing to export it.

Forward theorems (`certainty_insufficient_for_authorization`, `no_universal_ledger`,
`redeemability_requires_more_than_consensus`, `header_stripping_produces_pathology`,
and their contradiction companions) are conditioned on `(C : CommitmentsCtx ...)` for
C1 only; C2, C4b, C7b are now proved.

### Opaque Domain Primitives

Opaque constants (`opaque foo : T`) are uninterpreted domain predicates.
They are not `axiom` declarations but are underspecified by design —
their intended interpretation is given in comments, not derived.

Key opaque primitives:

| Primitive | File | Role |
|-----------|------|------|
| `certainty_L` | Basic.lean | Agent-side certainty (Ladder top) |
| `hasDeposit` / `deposited` | Bank.lean | Deposit membership predicates |

All theorems that use these primitives state their dependence explicitly via
`(C : CommitmentsCtx ...)`, `(C : WorldCtx)`, or direct premises.

---

## Resolution of Former Axioms

### Bank Operators (formerly 18 axioms → 0)

The lifecycle operators (`Validate_B`, `Accept_B`, `Challenge_B`, `Repair_B`,
`Revoke_B`, `Restore_B`, `Export_B_C`, `Import_C`, `repair`, `τ_refresh`,
`deprecate`) and their status postcondition theorems are now concrete
guarded struct-update definitions. Each operator is grounded in
`StepSemantics.lean` and witnessed by `ConcreteLedgerModel.lean`.

`knowledge_B` is now a `def` (= `hasDeposit`); `KnowledgeIffDeposited` is
proved as a theorem by `Iff.rfl`. Two behavioral theorems over concrete definitions
(`success_driven_bypass` over `reliance_level`; `blast_radius_scales_with_reliance` over `blast_radius`)
ground the reliance/cascade surface in `DepositDynamics` fields.

### Structural Commitments (formerly up to 12 axioms → 0)

Three commitments remain as fields of `CommitmentsCtx`. C2 is now proved. The others were discharged as theorems:

| Commitment | Resolution |
|------------|------------|
| C3 (`SEVFactorization`) | Proved by rfl |
| C5 (`ExportGating`) | Proved from LTS export constructors |
| C6b (`NoSelfCorrectionWithoutRevision`) | Proved from StepSemantics |
| C8 (`TemporalValidity`) | Proved from header τ definition |
| C2 (`NoGlobalLedger`) | **Proved** as `WorldCtx.no_ledger_tradeoff` (EpArch CAP Theorem) from `W_partial_observability` + `obs_based` in `WorldCtx.lean` |
| C4b (`ConsensusNotSufficient`) | **Proved** as `redeemability_requires_more_than_consensus` from `intra_bubble_only` + definitional gap between `consensus` (`True`) and `redeemable` (opaque external evidence) in `Commitments.lean` |
| C7b (`HeaderStrippingHarder`) | **Proved** via admissible completion-space model: `metadata_stripping_strictly_enlarges` establishes strict inclusion admissible_full ⊂ admissible_stripped; `header_stripping_harder` is its numeric corollary (0 < 3 fields). `sticky` and `proxy_battles` are **defined** from `has_cross_field_alternatives`: admissible-space multiplicity and cross-field underdetermination respectively; proved by `stripped_dispute_is_sticky` and `stripped_dispute_has_proxy_battles`. `dispute B P` is **defined** as a cross-bubble export conflict (d1 from B to B2, d2 from B2 to B, same claim P, incompatible headers). Zero opaque hypotheses; the full pathology theorem `header_stripping_produces_pathology` holds under the mild structural premise `has_cross_field_alternatives d` (Standard and ErrorModel are not singletons relative to d's header) — a type-universe nontriviality condition, not an architectural assumption. |
| C1 | Bundled as CommitmentsCtx field |

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
| `Bank.lean` | Bank substrate (concrete operators + opaque behavioral predicates) |
| `Commitments.lean` | Structural commitments (proved + CommitmentsCtx bundle) |
| `Invariants.lean` | Grounded operational invariants |
| `StepSemantics.lean` | Concrete step semantics |
| `Theorems.lean` | Derived theorems |
| `ConcreteLedgerModel.lean` | Constructive concrete model |
| All others | Theorem-bearing or definitional surfaces only |
