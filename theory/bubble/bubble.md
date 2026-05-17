# Bubbles

*[The Bank →](bank/bank.md)*

---

## Cluster

- [Bubbles](bubble.md) — policy index, scope, peer composition *(you are here)*
- [The Bank](bank/bank.md) — substrate, lifecycle, governance
  - [The Deposit](bank/deposits/deposit.md) — the unit: P + header
    - [The Claim](bank/deposits/claim.md) — P: what the deposit is *of*
    - [Header Fields](bank/deposits/headers/headers.md) — why deposits need structure
      - [Standard](bank/deposits/headers/standard.md) — V and S: the cook story
      - [Error Model](bank/deposits/headers/error-model.md) — E: the throw story
      - [Provenance](bank/deposits/headers/provenance.md) — V deep dive: the gift box story
      - [Access Control](bank/deposits/headers/access-control.md) — ACL: the salary spreadsheet story
      - [Redeemability](bank/deposits/headers/redeemability.md) — redeemability: the bushes story
      - [Temporal Validity](bank/deposits/headers/temporal-validity.md) — τ: the milk and Rolex stories

---

## What a bubble is

A bubble is a policy index.

That is the whole architectural commitment. A bubble does not act. It does not believe. It does not enforce. It is the parameter that selects *which acceptance policy is in force here*, *which ledger an agent is reading from*, and *which bridges to other bubbles are open*. Everything in the architecture that looks like it happens "in a bubble" is parameterized *by* the bubble. The bubble itself is just the index that makes the parameterization meaningful.

In the Lean this shows up as the bluntest possible definition: `Bubble` is a minimal Nat-indexed inductive — `inductive Bubble | mk : Nat → Bubble` — with no governance fields, no methods, no operations defined on it. The `Bank.Accept` predicate that decides whether a candidate deposit gets promoted is *indexed by* `Bubble`. A deposit carries a `bubble` field that says which bubble it lives in. `knowledge_B` is bubble-indexed. `TrustBridge`, `Export`, and `Import` take bubbles as arguments. The bubble is everywhere as a *parameter* and nowhere as an *actor*.

A working one-line definition:

> **A bubble is the scope under which an `Accept` policy applies, a ledger view exists, and bridges to other bubbles are addressable. It is a passive index, not an active institution.**

The bank file (next door) covered the substrate. This file covers the scope under which the substrate is parameterized.

---

## Why scopes are needed at all

The architecture could in principle have committed to a single global ledger. One bank. One `Accept`. One `knowledge` predicate. The financial-bank metaphor would even support that reading — the world has banks, but mathematically you could imagine merging them.

It does not work, and the architecture is explicit about why. **Same claim, different status, different scope** is a fact about how knowledge institutions actually behave. A claim that is `Deposited` in a research community can be `Revoked` in a regulatory body. A claim that is `Quarantined` in one jurisdiction can be `Deposited` in another. A single global ledger collapses these into a contradiction. The architecture refuses the collapse by making *scope* a first-class architectural object.

That object is the bubble. Once `knowledge_B` is bubble-indexed, "P is known in B" and "P is not known in B′" are not in tension — they are two true statements about two different ledgers, and the bubble parameter makes the difference visible to every theorem that touches it.

---

## Bubbles can be anything that has its own `Accept`

Because the bubble has no internal structure, the architecture commits to nothing about what the bubble *is* in any particular application. The same primitive supports:

* **A single agent's private bubble.** One person's own scope for what they have authorized themselves to rely on. The "memory bank" of a single mind, in epistemic terms.
* **A small group bubble.** A research collaboration, a partnership, a household. Multiple agents sharing one `Accept`.
* **An institutional bubble.** A laboratory, a newsroom, a journal, a court. Many agents under a shared and explicit acceptance protocol.
* **A corporate bubble.** A firm with internal compliance, audit, and authorization rules — its own institutional `Accept`.
* **A jurisdictional bubble.** A regulatory body, a national licensing scheme, a treaty zone. Acceptance scoped by legal authority.
* **A field bubble.** A scientific discipline's consensus body. Reviewers, editors, replication norms. Acceptance by professional governance.

The architecture treats all of these as the same kind of object. What distinguishes them is *which `Accept` they carry and which bridges they have to other bubbles*, not their size, their formality, or the number of agents inside them. The personal bubble and the multinational corporation are the same architectural primitive instantiated at different scales.

---

## The single-agent personal bubble — degenerate but on-spec

The smallest interesting case is the bubble with one agent in it. A reader who has internalized the bank-as-substrate framing might worry that this is degenerate to the point of pointlessness — what is an institutional ledger doing if the institution is one person?

Two answers.

First, the bubble is not doing anything *extra* in the single-agent case. It is doing the same thing it does at every scale: providing a scope under which `Accept` applies and a ledger view exists. With one agent the scope is small and the ledger is private, but the architecture does not pay any structural cost for the smallness. There is no "is this bubble big enough to count?" predicate. The same theorems apply.

Second, having the bubble structure available even in the degenerate case is exactly what makes the architecture compose. If a single-agent bubble *did not* exist as a first-class object, then every multi-agent construction would need a special case for "what was this agent doing before they joined the institution?" or "what does this agent fall back to if they leave?" By keeping the bubble primitive uniform — applicable to one agent or many — the architecture lets a personal bubble bridge to a corporate bubble, share information across the bridge, and let the agent participate in both without any special-case machinery. The personal bubble is the unit case that makes composition work.

The slogan: **the personal bubble is not useful in itself, but it is structurally on-spec, and that is what lets larger instantiations stay on-spec too.**

---

## Bubbles do not need to be nested — peer composition is enough

The architecture deliberately does not formalize nesting. There is no `parent : Bubble → Option Bubble` field, no containment relation, no "this bubble is inside that one" predicate. Bubbles are flat opaque indices.

This is not an oversight. It is a positive design choice that needs naming, because the application-domain intuition — "the marketing department sits inside the corporation, which sits inside the regulatory environment" — naturally reaches for a containment hierarchy.

What the architecture commits to instead is **peer bubbles with explicit bridges**. The marketing department is one bubble. The corporation is another bubble. The regulator is a third. Each has its own `Accept`. Information that needs to move between them moves via `TrustBridge` (cross without re-verification, when the bubbles have an established trust relationship) or via `Revalidate` (the receiving bubble runs its own `Accept` on the incoming deposit). The relations between bubbles are *named*, *directional*, and *explicit* — not implicit consequences of a containment hierarchy.

Why peer-with-bridges instead of nesting:

* **Real institutions don't have uniform inheritance.** A corporation does not automatically inherit its regulator's `Accept`, and a department does not automatically inherit its corporation's. Inheritance is *negotiated*, often explicitly contradicted (a department's compliance rules can be stricter than the corporation's; a corporation can hold itself to standards beyond what its regulator requires). A built-in nesting operator would impose the inheritance pattern automatically and force every application to either accept the imposition or work around it.
* **Bridges are bidirectional and selective.** A `TrustBridge B B′` does not imply a `TrustBridge B′ B`. A department might trust the corporation's authorizations without the corporation automatically trusting the department's. Containment gives this for free in the wrong way; explicit bridges give it for free in the right way.
* **Cross-cutting relationships exist.** An agent participates in their personal bubble *and* their employer's bubble *and* their professional society's bubble *and* their citizenship bubble. None of these contains the others. Peer-with-bridges handles this natively. A nesting model would have to invent multiple-inheritance machinery to cover it.

Architecturally: **anything a nesting model would have given you, the peer-with-bridges model gives you by composition.** A reader who wants nested institutional structures gets them by stacking bubbles and wiring bridges, not by invoking a built-in nesting operator. This is the same architectural posture as "the bank does not gate action" or "no scarce reserve" — the kernel deliberately stays minimal and lets richer patterns be constructed on top.

---

## An agent in many bubbles

This is the case the personal-bubble plus institutional-bubble combination was designed for.

A research scientist has their own personal bubble — what they have authorized themselves to rely on, including hunches not yet shared, working drafts, private notes. They are also a member of a laboratory bubble — the lab's shared body of internally certified results. They publish into a field bubble — a discipline's consensus body. They consult on policy in a regulatory bubble — a state body with its own acceptance rules.

The same scientist participates in all four bubbles. Architecturally, the scientist's *agent identity* is a single object that operates against multiple bubble parameters. The scientist's hunch lives in their personal bubble (`Deposited` there). When it survives lab review, a corresponding deposit appears in the lab bubble (`Deposited` there too — possibly as a bridged deposit, possibly as a freshly accepted deposit under the lab's `Accept`, depending on the bridge structure). When it survives peer review, a deposit appears in the field bubble. The regulator may never see it. None of this requires the personal bubble to be "inside" the lab bubble or the lab bubble to be "inside" the field. They are peer scopes, related by bridges that the scientist's actions exercise.

The thing this framing buys: **the scientist does not lose their personal bubble when they join the lab.** The personal scope persists. The lab scope is added. Information flow between the two is governed by bridges, not by containment. If the scientist later leaves the lab, the personal bubble is still there, with its own ledger and its own history.

---

## Information sharing across bubbles is exactly what bridges are for

The natural follow-up question: how does a deposit in one bubble become available in another?

Two paths, governed by two concrete operators in the architecture.

**Status-preserving transfer (`Export_B_C`)**: the deposit's `bubble` field is rebadged to the receiving bubble while its status is left unchanged. A deposit that was `Deposited` in B arrives in B′ still carrying `Deposited`. The precondition for taking this path is `TrustBridge B B′` — a relation the architecture treats as established between the two bubbles. `TrustBridge` is the institutional commitment that makes the receiving bubble willing to carry the sending bubble's status forward; the transfer itself is an agent-level action in the operational semantics, not something the bank initiates. Examples in the application domain: a court recognizing a sister court's judgment under full faith and credit, a credentialing body honoring a medical license under a reciprocity treaty, a parent company carrying forward a subsidiary's internal certifications.

**Revalidating transfer (`Import_C`)**: the deposit's `bubble` field is rebadged to the receiving bubble and its status is reset to `Candidate`. Whatever authorization it held in B, it does not carry that authorization into B′. The receiving bubble's `Accept` must promote it before it counts as `Deposited` there. The sending bubble's authorization is input to the receiving bubble's lifecycle, not a conclusion that the receiving bubble inherits. Examples: a journal evaluating a preprint as a new submission, a regulator reviewing a corporation's internal safety analysis from scratch, a court treating a foreign judgment as evidence rather than a binding ruling.

These two paths cover the load-bearing distinction: *does the receiving bubble re-run its `Accept` or not?* Everything else — federations, recognition networks, witness relationships — is built by composition from these primitives. The actual workflow (which agent decides to transfer, which path they take, how the step sequences) lives in `StepSemantics` as an agent-level action, not as a bank lifecycle primitive.

---

## Bubbles are not echo chambers

A reader from a media-criticism background will have an immediate concern. The word "bubble" has a colloquial sense that means "self-reinforcing isolated belief community immune to outside correction." Is that what this is?

No. The architectural bubble is not an echo chamber, for three structural reasons:

1. **Bubbles have explicit bridges.** Echo chambers are defined by their *lack* of cross-validation pathways. EpArch bubbles are equipped with `TrustBridge` and `Revalidate` precisely so that cross-bubble information flow has structure. A bubble with no bridges to anywhere else is a pathological case the architecture allows but does not endorse.
2. **Acceptance is governance, not insulation.** A bubble's `Accept` is a policy about what gets authorized inside it. It does not block external challenges. A deposit can be challenged inside its own bubble, by a member of the bubble, against the bubble's own standards. The bubble's authorization is *defeasible* under its own lifecycle; it is not a sealed ratification.
3. **The architecture supports `Quarantined` and `Revoked`.** Bubbles whose deposits cannot be quarantined or revoked when challenged are not on-spec — the lifecycle gates are part of what makes a bubble a bubble. An institutional structure that calls itself a bubble while refusing the lifecycle gates has stepped outside the architecture, not made better use of it.

The colloquial echo-chamber sense and the architectural bubble sense are unrelated. The architectural bubble is a scope; the echo chamber is a *failure mode* of a scope that has decoupled itself from its bridges and lifecycle. The architecture names the structure that an echo chamber abandons.

---

## Bubbles are not agents

The other structural confusion to close off. A bubble has an `Accept` policy, a ledger view, and bridges to other bubbles. None of those make it an agent.

* A bubble does not consult itself. *Agents* operating within the bubble consult the bubble's ledger.
* A bubble does not decide. *The agents who instantiate the bubble's `Accept` policy* — bank tellers, peer reviewers, judges, the agent themselves in the personal-bubble case — make the decisions.
* A bubble does not have stakes. The agents who participate in the bubble have stakes; the bubble itself is the scope under which their authorizations are recorded.
* A bubble does not act in the world. Agents act; deposits in the bubble's ledger inform their action.

The bubble is *what gets indexed*, not *who indexes*. Conflating the two is the same kind of mistake as treating the bank as believing things, and the file is built to close it off in the same way.

---

## `knowledge_B` and the bubble parameter

The architectural payoff of bubble-indexing is in the definition of `knowledge_B`.

`knowledge_B B P` says: *there exists an active authorized deposit for P in bubble B*. Every claim about institutional knowledge in the architecture carries the bubble parameter, and the parameter is what keeps the claims honest. "P is known" is not a fact the architecture supports. "P is known in B" is. The drop from one to the other is what bubble-indexing buys.

This means every theorem, every gate, every lifecycle move is implicitly relativized to a scope. There are no scope-free epistemic claims in the architecture, and that is by design. The architecture refuses the possibility of a global epistemic state because the application domain — real knowledge institutions interacting with each other — refuses it too.

---

## Takeaway

A bubble is a passive policy index. It does not act, decide, believe, or enforce. It is the parameter under which `Accept` applies, a ledger view exists, and bridges to other bubbles are addressable.

The architecture commits to nothing about what bubbles *are* in any particular application — they can be a single agent's private memory, a research lab, a corporation, a regulator, a discipline, a jurisdiction. They scale from the degenerate one-agent case to multinational institutions using the same primitive, and they compose into hierarchies, federations, and overlapping relationships using `TrustBridge` and `Revalidate` rather than a built-in nesting operator.

The personal bubble — useless on its own, structurally on-spec — is what lets the same architecture cater to a single agent's reasoning and to a continent-spanning regulatory regime without changing primitives. Larger institutional structures are not architecturally different from personal ones; they are the same primitive instantiated at scale and bridged to peers. That is what makes the architecture *for any kind of agent*, not for a particular institutional silhouette.

---

*[The Bank →](bank/bank.md)*

---

*Proof-side companion: [../../DOCS/architecture/SEMANTICS.md](../../DOCS/architecture/SEMANTICS.md).*
