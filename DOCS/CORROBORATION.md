# Multi-Agent Corroboration Module

**File:** `EpArch/Agent/Corroboration.lean`

## Overview

This module provides formal machinery for reasoning about when multi-agent
corroboration is required (conditional minimality) and when it fails
(common-mode/correlated compromise).

The key insight: corroboration is not "magic." Its value depends entirely on
whether attestation sources satisfy an explicit **independence/diversity interface**.
When sources share failure modes (common-mode), corroboration can fail
spectacularly—this is the formal version of "bubble infection."

## Three Structural Conditions

### 1. Goal Condition: No Single Point of Failure

The `NoSinglePointFailure` goal makes corroboration mandatory:
- If your system goal includes resilience to single-source compromise
- AND single-source attacks are possible
- THEN single-attestation acceptance is forbidden

This is **conditional minimality**: corroboration is forced by the goal, not assumed universally.

### 2. Independence Condition (Explicit, Not Baked In)

Independence is a parameter `Independent : Source → Source → Prop`, NOT a baked-in assumption.
This design choice is critical:

- **Theorems are conditional:** "k-of-n works IF independence holds"
- **No hidden realism:** We don't claim sources ARE independent
- **The knob is explicit:** You can instantiate with your diversity assumptions or leave abstract

### 3. Common-Mode Condition (Bubble Infection)

`CommonModeAttack` models correlated compromise:
- Multiple sources share an upstream/bubble/channel
- Adversary can compromise them jointly
- Naive k-of-n corroboration fails

This is the formal version of:
> "An adversary can infect a whole bubble; corroboration inside that bubble is not safety."

## Theorems

The four theorems form a natural arc: corroboration is required (T1), works under independence (T2), fails under common-mode (T3), and diversity is the reason it fails (T4).

### T1: Necessity
**`single_source_can_accept_false`**
- If single-source attacks are possible, single-source acceptance can accept false statements
- Direct counterexample proof using attack scenario

**`no_spof_requires_multi_source`**
- If NoSPoF goal AND single-source attacks possible → contradiction from single-source acceptance
- Conditional minimality: corroboration is forced by the goal, not assumed universally

### T2: Sufficiency Under Independence
**`k_of_n_suffices_under_independence`**
- If at most t independent sources are compromised, k > t independent attestations → resilience
- Formal reason why 2–3 independent attestations beats one
- Fully proved via pigeonhole helper lemmas (see Technical Notes)

### T3: Common-Mode Failure
**`common_mode_breaks_naive_corroboration`**
- If common-mode compromise is possible, k-of-n (for any k up to the compromised set size) can accept false
- The formal version of "bubble infection"

**`two_of_two_fails_under_common_mode`**
- Even 2-of-2 corroboration fails under common-mode (minimal interesting case)

### T4: Diversity Requirement
**`common_mode_requires_diversity`**
- Universal quantification over k: naive k-of-n fails when k ≤ compromised set size
- Corroboration needs diversity, not just multiplicity

## Claim Budget

### What This Buys (Strong, Paper-Usable)

- ✅ Formal reason "why 2-3 independent attestations beats one" under explicit independence interface
- ✅ Formal reason "why corroboration can fail spectacularly" when independence violated
- ✅ Conditional minimality: if NoSPoF goal, corroboration is FORCED
- ✅ No sociology: everything about admissible models and explicit constraints

### What This Does NOT Buy

- ❌ "Humans do this in practice" / "reasonable people will..."
- ❌ "The real world satisfies the independence interface"
- ❌ "Corroboration guarantees truth" (only reduces risk under explicit constraints)
- ❌ Claims about specific social institutions or practices

## Integration

- **Imports:** Only `EpArch.Basic`
- **Re-exported via:** `EpArch/Agent.lean`
## Technical Notes

### Proof Status
All theorems are fully proved with **zero sorry statements**:
- T1 (`single_source_can_accept_false`, `no_spof_requires_multi_source`) — fully proved
- T2 (`k_of_n_suffices_under_independence`) — fully proved via pigeonhole helper
- T3 (`common_mode_breaks_naive_corroboration`) — fully proved
- T4 (`common_mode_requires_diversity`) — fully proved

Helper lemmas proved from scratch:
- `mem_of_mem_take` — element of `List.take k L` is in `L` (induction proof)
- `length_take_ge` — `|List.take k L| ≥ k` when `k ≤ |L|`
- `filter_length_le` — `|List.filter p L| ≤ |L|`
- `exists_not_of_length_gt_filter` — pigeonhole for filter
- `pigeonhole_filter` — main pigeonhole lemma for T2

### Type Signatures

```lean
structure SingleSourceAttack (Source Statement : Type) where
  Attests : Source → Statement → Prop
  TrueStmt : Statement → Prop
  compromisable_source : Source
  false_stmt : Statement
  stmt_is_false : ¬ (TrueStmt false_stmt)
  can_be_made_to_attest : Attests compromisable_source false_stmt

structure CommonModeAttack (Source Statement : Type) where
  Attests : Source → Statement → Prop
  TrueStmt : Statement → Prop
  compromised_sources : List Source
  at_least_two : compromised_sources.length ≥ 2
  false_stmt : Statement
  stmt_is_false : ¬ (TrueStmt false_stmt)
  all_attest : ∀ s, s ∈ compromised_sources → Attests s false_stmt
```
