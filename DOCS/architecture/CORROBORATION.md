# Multi-Agent Corroboration

Corroboration is conditional, not magic. Its formal value depends entirely on
whether attestation sources satisfy an explicit independence interface; when
they share failure modes, naive k-of-n acceptance fails. This module
(`EpArch/Agent/Corroboration.lean`) makes both sides of that conditional
machine-checked.

---

## The goal toggle: no single point of failure

`NoSinglePointFailure` is a *goal* the system can adopt. Adopting it forces
corroboration:

- if the goal includes resilience to single-source compromise, and
- single-source attacks are possible (`SingleSourceAttack`),
- then single-attestation acceptance is forbidden.

This is conditional minimality: corroboration is not assumed universally —
it is forced by an explicit goal predicate.

---

## The independence interface

Independence is a parameter `Independent : Source → Source → Prop`, not a
baked-in assumption. The design choice is load-bearing:

- theorems are stated as "k-of-n suffices *if* independence holds";
- the framework does not claim that real-world sources are independent;
- the assumption is an explicit hypothesis the caller must supply or
  refuse.

`k_of_n_suffices_under_independence` is the positive form: with at most `t`
compromised independent sources, any `k > t` independent attestations
guarantee at least one honest attestation. The proof uses pigeonhole over
the filtered attestation list.

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

`common_mode_requires_diversity` quantifies over all `k`: corroboration
needs *diversity*, not just multiplicity.

---

## Relation to PRP and agent constraints

The independence interface is the formal locus where the agent-side
constraints (`Agent/Constraints.lean`) and the resilience layer
(`Agent/Resilience.lean`) connect to the bank's deposit lifecycle. The bank
records what is presented; the agent decides what to present and through
which sources. PRP (Public Receivability Pressure) is the upstream
framing: the corroboration theorems are what the formalization actually
delivers when PRP is operationalized as multi-source attestation.

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

- [MODULARITY.md](MODULARITY.md) — how the corroboration cluster is exposed
  through the certified-projection surface.
- [../START-HERE.md](../START-HERE.md) — terminology and reading routes.
