# People Disagree → Separate Spaces

## Cluster

- [What the Architecture Was Forced Into](../forcing.md) — the eight pressures and the schema that turns them into structure
- **People Disagree → Separate Spaces** — distributed agents force scope separation *(you are here)*
- [Checking Takes Work → Trust Bridges](checking-takes-work.md) — bounded verification forces trust-based import
- [Things Travel → Metadata Travels With Them](things-travel.md) — cross-boundary export forces headers
- [Accepted Things Can Turn Out Bad → Revocation](accepted-can-turn-bad.md) — adversarial pressure forces a way out of *accepted*
- [People Need to Coordinate → Shared Storage](people-need-to-coordinate.md) — coordination need forces a bank
- [Reality Pushes Back → Redeemability](reality-pushes-back.md) — truth pressure forces external constraint-surface contact
- [Not Everyone Can Do Everything → Granular ACL](not-everyone-can-do-everything.md) — staged access forces tier separation
- [Storage Runs Out → Storage Management](storage-runs-out.md) — bounded capacity forces eviction, archival, or pruning
- [What Goes Wrong When You Drop a Piece](../pathologies.md) — the crosswalk made vivid

---

## Two reviewers, one paper

A journal sends the same paper to two reviewers.

The first reviewer is from the field the paper builds on. She knows the standards. She reads the abstract, looks at the methods section, sees the right citations, finds the proofs intelligible, and recommends acceptance.

The second reviewer is from a neighbouring field that uses some of the same words to mean different things. He reads the abstract, finds the methods unfamiliar, sees citations he does not recognise, finds the proofs hard to follow, and recommends rejection.

The paper is one paper. The two reviewers are competent, careful, and acting in good faith. They disagree about whether to accept it.

Now imagine the journal trying to use a single yes-or-no rule for all incoming papers. Some rule, evaluated once per paper, that produces *accept* or *reject*. Whatever rule the journal picks, one of the two reviewers is going to be told their judgment was wrong about this paper. Either the rule accepts and the second reviewer's *no* is overridden, or the rule rejects and the first reviewer's *yes* is overridden. There is no rule that lands on both reviewers' answers at once, because their answers contradict on this paper.

The journal's actual practice — multiple reviewers, separate scores, an editorial decision that reads them in context — is not a workaround. It is the only thing that can fit. The reason it is the only thing that can fit is the load-bearing claim of this corner.

---

## What the kernel proves

The kernel calls a situation like this an `AgentDisagreement`. It has four pieces:

- a type of things that can be claimed (papers, in the scene),
- two acceptance criteria (the first reviewer's, the second reviewer's),
- a *witness* — one specific claim on which the two criteria disagree (this paper),
- and the proof that they actually do disagree on it (one accepts, the other rejects).

The simplest-than-bubbles design is *one shared acceptance function* — a single rule that both reviewers are supposed to be honestly represented by. The kernel proves this is impossible. The proof is short:

> Suppose such a function `f` exists. Faithfulness to the first reviewer means `f` accepts the paper. Faithfulness to the second reviewer means `f` rejects it. The same function cannot return both answers on the same input. The supposition contradicts itself.

The piece that gets forced in is the obvious one once it is named: each acceptance criterion gets its own *space* — its own scope — where it gets to be the rule. The journal does not collapse the two reviewers into one verdict; it carries both verdicts forward, each in its own scope, and lets the editor work over the pair. EpArch calls those scopes *bubbles*. The bubble is the kernel's name for *the place where one acceptance criterion is the rule*.

---

## Why dressing it up doesn't help

The contradiction is sharp enough that it is tempting to look for a clever way around it. The kernel checks three of the obvious dodges and shows each of them collapses back into the same impossibility.

**Capability tokens.** "Make acceptance depend on which token the reviewer holds." If the two reviewers genuinely disagree on a paper, then for the witness paper the relevant token discipline separates them: one reviewer satisfies the token requirement and the other does not. That split ownership is exactly the disagreement the kernel was talking about. The kernel proves this directly: a capability system with split token ownership is just an `AgentDisagreement` in heavier clothing, and the same impossibility fires.

**Federated namespaces.** "Tag every claim with the scope it lives in, then evaluate per-scope." This is not a dodge so much as the same answer arrived at earlier and under a different name. Federated namespaces predate EpArch by decades; *per-scope evaluation* is exactly what the corner forces. EpArch calls the construct a *bubble* rather than a *namespace*, *tenant*, *partition*, or *realm* on purpose — each of those names already carries a particular instantiation with it (DNS-style hierarchy, multi-tenant isolation, sharded storage, security domains), and the corner does not endorse any one of them. The bubble is the neutral name for *the place where one acceptance criterion is the rule*; federated namespaces are one valid way to instantiate it.

**Dynamically parameterized gates.** "Make the acceptance function take a parameter — different parameters for different reviewers — so it is technically one function." If the two parameter bundles disagree on the witness, the curried-on-parameters functions are exactly two acceptance criteria, and the original impossibility fires on the curried form. If the parameters can be tuned so the function agrees with both reviewers on every claim — then the reviewers do not actually disagree, and the pressure was never present to begin with.

The pattern across all three is the same: any architecture that *looks* like a single shared rule but actually fits both reviewers is doing per-criterion evaluation under the hood. Calling it something other than a bubble does not change what it is.

---

## What this corner does not claim

It does not claim the journal needs *exactly* the design EpArch ships. The kernel proves that *some* per-criterion partitioning is required. What that partitioning looks like in any particular system — how many scopes, how they are named, how a piece of work moves between them, who arbitrates when scopes conflict — is design space the corner does not constrain. A journal with two reviewers, a journal with five, a journal with field-specific track editors, and a journal with a rotating panel are all valid implementations as far as this corner is concerned. What none of them can be is *one rule, evaluated once, faithful to all reviewers*.

It also does not claim that disagreement between people is the only source of the bubble pressure. *Distributed agents* in the kernel covers anything that exhibits the structural shape of two-or-more acceptance criteria disagreeing on a witness — different teams, different time periods of the same team, different versions of a policy, different jurisdictions. The reviewers are a vivid case. The pressure is broader.

And it does not claim that the witness paper *should* be accepted or *should* be rejected. The kernel says nothing about which reviewer is right. It says only that *no single rule can be faithful to both at once*, and that any architecture that pretends otherwise is silently overriding one of them.

---

## Takeaway

When two acceptance criteria genuinely disagree on a single claim, no shared rule can land on both their answers. The contradiction is structural: the same function cannot return *yes* and *no* on the same input.

The minimal piece that closes the gap is to give each criterion its own scope and stop trying to collapse them. EpArch calls that scope a *bubble* — a deliberately neutral name, picked so the corner does not silently endorse any one of the older instantiations (federated namespaces, tenants, partitions, realms) that already implement it. Two of the three plausible dodges (capability tokens, parameterized gates) collapse back into the same impossibility; the third (federated namespaces) is not a dodge at all but an existing implementation of what the corner forces.

The architecture's job is not to decide which reviewer is right. It is to refuse to silently overwrite one of them with the other.

---

*← [Forcing](../forcing.md)  ·  Next: [Checking Takes Work → Trust Bridges](checking-takes-work.md) →*
