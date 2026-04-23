# Multi-Agent Corroboration

Corroboration is conditional, not magic. Its formal value depends entirely on
whether attestation sources satisfy an explicit independence interface; when
they share failure modes, naive k-of-n acceptance fails. This module
(`EpArch/Agent/Corroboration.lean`) makes both sides of that conditional
machine-checked.

---

## The goal toggle: no single point of failure

The resilience goal is encoded as the hypothesis
`h_goal : ∀ s phi, SingleSourceAcceptance ... → TrueStmt phi`
in `no_spof_requires_multi_source`. There is no separate named structure or
type for this goal — the hypothesis itself is the toggle.

- if single-source attacks are possible (`SingleSourceAttack`), and
- the acceptance policy is required to admit only true statements
  (`h_goal`),
- then single-attestation acceptance leads to a contradiction.

This is conditional minimality: corroboration is not assumed universally —
it is forced by an explicit hypothesis.

---

## The independence interface

Independence is a parameter `Independent : Source → Source → Prop`, not a
baked-in assumption. The design choice is load-bearing:

- theorems are stated as "k-of-n suffices *if* independence holds";
- the framework does not claim that real-world sources are independent;
- the assumption is an explicit hypothesis the caller must supply or
  refuse.

`k_of_n_suffices_under_independence` is the positive form: given
`HonestImpliesTrue` (honest sources tell the truth) and `IndependenceBounded`
(at most `t` independent sources compromised), requiring `k > t` independent
attestations yields `TrueStmt phi`. The proof uses pigeonhole over the
filtered attestation list to extract one honest witness, then applies
`HonestImpliesTrue`.

---

## Common-mode failure

`CommonModeAttack` models the negative case: multiple sources share an
upstream channel, bubble, or substrate, and an adversary compromises them
jointly. The architecture exposes this as a structure with a
`compromised_sources : List Source` field and an `at_least_two` witness.

Two theorems close the failure side:

- `common_mode_breaks_naive_corroboration`: under common-mode, k-of-n (for
  any `k` up to the compromised set size) can accept a false statement.
- `two_of_two_fails_under_common_mode`: even the minimal interesting case
  (2-of-2) is insufficient.

`common_mode_requires_diversity` quantifies over `k ≤ compromised_sources.length`:
for any threshold up to the pool size, naive k-of-n fails. The unbounded
form — where no threshold is safe regardless of pool size — is
`common_mode_fails_regardless_of_k` (over `UnboundedCommonModeAttack`). Both
conclude: corroboration needs *diversity*, not just multiplicity.

---

## Relation to PRP and agent constraints

`Corroboration.lean` imports only `EpArch.Basic`. It has no formal connection
to `Agent/Constraints.lean`, `Agent/Resilience.lean`, or the bank deposit
lifecycle. PRP (Permanent Redeemability Pressure) is defined separately in
`Agent/Constraints.lean`; the architectural motivation for multi-source
attestation comes from that framing, but no theorem in `Corroboration.lean`
has a proof dependency on it.

---

## What this module does not claim

This file is about *the formal arc of corroboration under explicit
independence and common-mode interfaces*. It does not claim that human
institutions practice corroboration well, that real-world sources satisfy
the independence interface, that corroboration guarantees truth (it
reduces risk under explicit conditions), or anything about specific social
systems. The broader scope-defense for the witness family is centralized in
[reference/WITNESS-SCOPE.md](../reference/WITNESS-SCOPE.md).

---

## Go next

- [MODULARITY.md](MODULARITY.md) — how config-facing theorem clusters are exposed
  through the certified-projection surface.
- [../START-HERE.md](../START-HERE.md) — terminology and reading routes.
