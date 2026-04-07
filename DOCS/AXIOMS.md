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

### CommitmentsCtx — Structural Commitments as a Hypothesis Bundle

**File:** `EpArch/Commitments.lean`

The four structural commitments that define the conforming-architecture class
are bundled as fields of `CommitmentsCtx` (modelled on `WorldCtx`). They are
not `axiom` declarations; they are hypotheses that appear explicitly in theorem
signatures:

    theorem T (C : CommitmentsCtx PropLike Standard ErrorModel Provenance) ...

| Field | Commitment | Plain reading |
|-------|------------|---------------|
| `traction_auth_split` | C1: certainty_L ⊥ knowledge_B (neither implies the other) | An agent can be certain of P without any bank deposit for P, and a bank deposit can exist without the agent being certain. Feeling sure and being authorized are different kinds of things. |
| `no_global_ledger` | C2: no ledger simultaneously supports innovation and coordination | A single shared ledger cannot simultaneously allow heterodox claims (innovation) and enforce shared acceptance standards (coordination). Scoped validation domains (bubbles) are forced by this tradeoff. |
| `consensus_not_sufficient` | C4b: consensus does not imply redeemability | A deposit that everyone agrees on in a bubble can still fail against the external constraint surface. Group agreement does not discharge the evidence requirement. |
| `header_asymmetry` | C7b: stripped disputes produce sticky ∧ proxy_battles | Removing the S/E/V metadata from a deposit before it reaches a dispute makes the dispute harder to resolve and harder to diagnose. The asymmetry is directional: stripping is not a neutral operation. |

Forward theorems (`certainty_insufficient_for_authorization`, `no_universal_ledger`,
`redeemability_requires_more_than_consensus`, `header_stripping_produces_pathology`,
and their contradiction companions) are conditioned on `(C : CommitmentsCtx ...)`.

### Opaque Domain Primitives

Opaque constants (`opaque foo : T`) are uninterpreted domain predicates.
They are not `axiom` declarations but are underspecified by design —
their intended interpretation is given in comments, not derived.

Key opaque primitives:

| Primitive | File | Role |
|-----------|------|------|
| `certainty_L` | Basic.lean | Agent-side certainty (Ladder top) |
| `hasDeposit` / `deposited` | Bank.lean | Deposit membership predicates |
| `reliance_level` | Bank.lean | Quantitative reliance |
| `blast_radius` | Bank.lean | Impact spread of deposit failure |
| `success_driven_bypass` | Bank.lean | Behavioral claim over opaque reliance predicate |
| `blast_radius_scales_with_reliance` | Bank.lean | Quantitative claim over opaque blast predicate |
| `GlobalLedger` | Commitments.lean | Abstract ledger type |
| `supports_innovation` / `supports_coordination` | Commitments.lean | Ledger capability predicates |
| `dispute` / `sticky` / `proxy_battles` | Commitments.lean | Header-stripping consequence predicates |
| `acl_permits` | Invariants.lean | Access-control permission predicate |

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
proved as a theorem by `Iff.rfl`. Two behavioral claims remain as
opaque-predicate theorems (`success_driven_bypass`, `blast_radius_scales_with_reliance`).

### Structural Commitments (formerly up to 12 axioms → 0)

Four commitments are now fields of `CommitmentsCtx`. The others were discharged as theorems:

| Commitment | Resolution |
|------------|------------|
| C3 (`SEVFactorization`) | Proved by rfl |
| C5 (`ExportGating`) | Proved from LTS export constructors |
| C6b (`NoSelfCorrectionWithoutRevision`) | Proved from StepSemantics |
| C8 (`TemporalValidity`) | Proved from header τ definition |
| C1, C2, C4b, C7b | Bundled as CommitmentsCtx fields |

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
