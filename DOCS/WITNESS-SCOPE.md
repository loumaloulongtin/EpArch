# Witness Scope Matrix

This document specifies **exactly** which axioms/properties are witnessed by `ConcreteLedgerModel.lean` and which are **not**.

---

## What "Witnessed" Means

A property is **witnessed** if `ConcreteLedgerModel.lean` contains a proof that a concrete instantiation satisfies it. This demonstrates:

1. **Satisfiability** — The property is not vacuously true or contradictory
2. **Realizability** — At least one concrete system can satisfy it
3. **Non-triviality** — The axiom set doesn't collapse

**Witnessing does NOT prove:**
- Uniqueness (other models may exist)
- Necessity (other designs may work)
- Empirical truth (this is a formal model)

---

## Witness Matrix

### ✅ Witnessed Properties (proved in ConcreteLedgerModel.lean)

| Property | Theorem | Location |
|----------|---------|----------|
| Bubbles exist | `concrete_has_bubbles` | Line ~841 |
| Trust bridges exist | `concrete_has_trust_bridges` | Line ~846 |
| Headers exist (SEV structure) | `concrete_has_headers` | Line ~851 |
| Revocation mechanism exists | `concrete_has_revocation` | Line ~856 |
| Bank primitive exists | `concrete_has_bank` | Line ~861 |
| Redeemability exists | `concrete_has_redeemability` | Line ~866 |
| **All properties satisfied** | `concrete_satisfies_all_properties` | Line ~891 |
| Well-formedness | `concrete_wellformed` | Line ~908 |
| Revision traces exist | `concrete_revision_trace_exists'` | Line ~1154 |
| Self-correction supported | `concrete_model_supports_self_correction7` | Line ~1170 |
| SEV factorization | `concrete_has_factorization8` | Line ~1180 |
| Repair path exists | `concrete_has_repair_path8` | Line ~1187 |
| Withdrawal gates | `concrete_withdrawal_requires_gates` | Line ~737 |
| Export needs provenance | `concrete_export_needs_provenance` | Line ~695 |
| Headerless → undiagnosable | `concrete_headerless_undiagnosable` | Line ~779 |

### ⚠️ Not Witnessed (axioms, not instantiated)

| Property | Category | Notes |
|----------|----------|-------|
| World assumption bundles (`W_*`) | Tier B premises | These are *assumed*, not witnessed |
| Health necessity theorems | Tier A (proved) | Proved from definitions, not axioms |
| Invariants (C1-C8) | Tier C spec | Protocol requirements, not witnessed |
| LTS refinement properties | Tier A | Proved abstractly, not via concrete model |

### ❌ Explicitly Out of Scope

| Property | Reason |
|----------|--------|
| Cryptographic security | Not a crypto formalization |
| Implementation correctness | Spec ≠ implementation |
| Physical realizability | Formal model only |
| Empirical correspondence | Model ≠ world |

---

## Satisfiability Summary

The concrete model witnesses that the **core axiom set is satisfiable**:

```lean
∃ (W : WorkingSystem), 
  WellFormed W ∧ 
  SatisfiesAllProperties W ∧
  containsBankPrimitives W
```

This is packaged in `EpArch.Feasibility.existence_under_constraints`.

The architecture is **not vacuous** — there's at least one instantiation, AND
success forces Bank primitives (minimality).

---

## What This Does NOT Imply

| Non-implication | Why |
|-----------------|-----|
| "All axioms are witnessed" | Only structural axioms; W bundles are assumed |
| "The model is complete" | Other models may exist with different properties |
| "The model is optimal" | No optimality claim |
| "The model is unique" | Explicitly not claimed |

---

## Audit Command

```bash
# Count witness theorems
Select-String -Path "EpArch/ConcreteLedgerModel.lean" -Pattern "theorem concrete_"
```
