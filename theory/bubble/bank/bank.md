# The Bank

*[← Bubbles](../bubble.md) · [The Deposit →](deposits/deposit.md)*

---

## In this section

- [The Deposit](deposits/deposit.md) — the unit the bank holds
  - [The Claim](deposits/claim.md) — P and the truth/status orthogonality
  - [Header Fields](deposits/headers/headers.md) — why deposits need structure beyond P

---

## What the bank is

The bank is the substrate that holds authorized deposits.

It is not an agent. It does not believe anything. It does not remember anything in the agent-psychological sense. It has no preferences. It does not want outcomes. It is a shared institutional layer that multiple agents read from and write to, and its entire job is to keep a structured ledger of what has been authorized, label each entry with where it stands in the lifecycle, and stand behind those labels until something changes them.

When this file says *the bank knows P*, it does not mean the bank is having a thought about P. It means the bank holds an active authorized deposit for P in some bubble. That is a fact about the institutional record, not a fact about a mind. The architecture is careful about this distinction because the bank and the agents that consult it are different layers and the moves they make are different moves.

The deposit file (next door) covered the unit. This file covers the institution that holds the units.

---

## The two-step that everyone gets wrong the first time

There is one architectural distinction that has to be installed before anything else in this file makes sense. It comes straight out of the Lean and it is load-bearing for the rest of the architecture:

> **The agent decides whether to consult the bank. The bank decides whether to accept the deposit.**

These are two different decisions made by two different parties.

A customer walks into a branch holding a check. The customer chose to walk in — that was an *agent-side* decision about whether to consult the institution at all. The teller looks at the check and decides whether to accept it for deposit — that is an *institution-side* decision about whether the artifact in front of it meets the bank's standards. The customer cannot make the bank accept a check it would otherwise reject; the bank cannot make the customer come in.

The architecture insists on this split because the most common confusion is to collapse it. Once collapsed, every interesting question becomes muddled: who decides what counts as authorized? who decides what counts as worth consulting? where does institutional authority end and agent autonomy begin? Keep them separate and the rest of the file falls into place.

---

# Scenario: a customer and a check

A customer walks into a branch with a paycheck. We will follow that paycheck through the bank's lifecycle, viewed from the institution's side of the counter.

This is the same lifecycle the deposit file walked through, but the camera is now on the bank rather than on the deposit. What we are watching is what the *institution* does at each step: promote, freeze, re-promote, mark, purge.

---

## Candidate — the check is on the ledger but the funds are on hold

The teller takes the check, scans it, and creates an entry. The deposit exists on the ledger but the funds are on hold pending clearance.

This is **Candidate**. The bank has the entry. The bank has not yet authorized withdrawal against it. A downstream agent — the customer trying to spend the money, another teller asked about the balance — would see the entry and would also see that it is not yet drawable.

The lifecycle gap between *submitted* and *authorized* is exactly this state. The bank has accepted the artifact for processing; the bank has not yet promoted it to something a downstream agent may rely on.

---

## Deposited — the check clears

The clearance process completes. The check is good. The institution promotes the entry from `Candidate` to `Deposited`.

This is the only status that licenses withdrawal in the institutional sense — the only status at which the bank says *we stand behind this*. The customer can now draw against the funds. Other tellers asked about the account will see a balance that includes the new deposit. The bank is now publicly committed to the deposit's authorization, scoped to its own bubble.

---

## Quarantined — the issuing bank flags it

A few days later, the issuing bank flags the check. There is a question about whether the account it was drawn on actually had funds, or whether the routing number on the slip was forged.

The receiving bank does not yet know the check is bad. But it can no longer confidently stand behind it. The deposit moves to **Quarantined**: still on the ledger, no longer drawable, pending resolution.

This is the institution doing what only an institution with a structured lifecycle can do. It is not retracting (which would assert the deposit was wrong). It is not standing pat (which would assert it is still authorized). It is *holding*, visibly, while the question of which field broke gets investigated.

---

## Revoked — the check is bad

The investigation completes and the news is bad. The check was fraudulent; there were never funds behind it. The deposit is **Revoked**.

`Revoked` is not the same as "removed from the ledger." It is a permanent epistemic boundary: this path was tested, it was found closed, the bank now signals that it has been closed. A downstream agent who later searches for the deposit will find the revocation and know that the institution made a judgment about it.

Two further moves out of `Quarantined` and one further fate of any deposit are deliberately not walked here. A deposit that turns out to be repairable rather than fraudulent goes back through the lifecycle by a path that the financial metaphor cannot model. A deposit that is eventually `Forgotten` does not become a different kind of deposit; it ceases to be one. Both are taken up in the section below on what the EpArch bank does that a real bank does not, where the metaphor is finally set aside.

---

# Where the analogy stops and the EpArch bank begins

Up to here the financial-bank metaphor has been doing real work. Customer, teller, check, branch, ledger, clearance, hold, freeze, retraction, archival purge — each maps cleanly onto something architectural. If a reader has followed the scenario above, they are oriented.

The metaphor now stops being a help and starts being a hazard. The EpArch bank is more *minimal* than a commercial bank in several specific ways, and a reader who carries the financial intuitions any further will silently import constraints that the architecture does not have. This section names the disanalogies so they cannot ambush downstream sections.

---

## The bank does not gate action

A real bank gates withdrawal. If the check has not cleared, the teller will not hand over the cash. The bank stands between the customer and the action; that is what the bank's authority *is*.

The EpArch bank does not do this. It exposes every deposit with its current status — `Candidate`, `Deposited`, `Quarantined`, `Revoked`, `Forgotten` — and that is the entire scope of what the bank says about any of them. An agent that wants to act on a `Candidate` deposit can do so. An agent that wants to act on a `Revoked` deposit can do so. The bank will not stop them. The status is information, not a gate.

This is deliberate. The architecture separates two questions the financial metaphor collapses:

* **What has the institution authorized?** The bank's job. Answered by the deposit's status.
* **What should the agent rely on?** The agent's job. Answered by the agent's own credit-management policy, defined relative to its own situation, its own stakes, its own fallbacks.

A cautious agent treats `Deposited` as the floor and rejects anything below it. An exploratory agent might choose to act on a high-confidence `Candidate` while the desk is still finishing review. An agent under time pressure might act on a `Quarantined` claim because the cost of waiting exceeds the cost of being wrong. An agent investigating a closed case might go back to a `Revoked` deposit deliberately, knowing exactly what the revocation means and acting on the underlying claim anyway. None of these are violations of the bank's authority, because the bank does not have that kind of authority. The bank labels; the agent decides.

The load-bearing consequence: **credit management is an agent-side concern, not a bank-side concern.** A deposit's status is evidence about how much the institution stands behind the claim. Turning that evidence into a decision to act is everything the agent does that the bank does not. The architecture refuses to do this conversion on the agent's behalf, because there is no situation-independent right answer to it. Two agents reading the same `Quarantined` deposit can correctly arrive at opposite decisions because they have different stakes, different fallbacks, different windows.

---

## Withdrawal is non-consuming

A financial withdrawal removes value from the ledger. The next withdrawal sees a smaller balance. Money is a resource that gets spent down by use.

EpArch withdrawal is not consumption. A `Deposited` claim withdrawn by ten different agents on ten different occasions remains exactly the same `Deposited` claim. The ledger does not decrement. A claim that is currently authorized is currently authorized for everyone, repeatedly, until something in the lifecycle moves it to a different status.

The right financial analogy is not a checking account. It is something more like a recorded title — a deed, a court judgment, a registered patent — which can be presented, relied on, and pointed to indefinitely without diminishing the institutional record. Deposits are not a resource that gets spent down by use.

---

## There is no scarce reserve

A real bank holds reserves. Promotion of a check to drawable funds is constrained by whether the bank has the money to back it; runs are possible because the backing is finite.

The EpArch bank has no scarce backing pool. Promotion to `Deposited` is constrained by the bank's acceptance criteria, not by a resource budget. There is no run on an EpArch bank. There is no scenario in which the bank "does not have enough P" to honor an authorization request. The institution either accepts the deposit under its standards or it does not, and the answer does not depend on how many other deposits have already been authorized.

---

## There is no debt and no negative balance

A real bank can be owed money. It issues credit. It carries liabilities. Its ledger can run negative for a particular account, and that negative state has its own institutional meaning (overdraft, default, collection).

The EpArch bank holds deposits in five named statuses and that is the entire universe of states. There is no analog of a loan, no credit line, no overdraft. A claim is either authorized or it is not; the ledger does not extend itself to support claims it has not certified.

---

## Repair has no financial counterpart

A real bank does not "repair" a check. It bounces it or it accepts it. There is no third option in which a bad check becomes a good check through targeted institutional intervention.

The EpArch bank's `Quarantined → Repair → Candidate` loop is a first-class lifecycle path that the financial metaphor cannot model at all. This is one of the most important features of the architecture, and it is one the metaphor *actively obscures*. The moment the lifecycle reaches `Quarantined`, the financial reader's intuition stops helping and starts misleading: a real bank has no notion of repairing the entry to a state where re-promotion is possible. The EpArch bank does, and the field-localized diagnosis that drives that repair is exactly what the architecture exists to support.

Two things about that loop are worth pulling out, because they do not have financial counterparts to lean on. First, repair is targeted: it acts on the deposit's structure — a header field, a redeemability path, a provenance link — rather than on the underlying claim's truth. The bank does not decide that P became true; it decides that the structural defect that drove the deposit into `Quarantined` has been addressed and the deposit is once again a coherent object the lifecycle can act on. Second, repair returns the deposit to `Candidate`, not to `Deposited`. Re-authorization is a separate gate that the repaired deposit has to clear on its own merits. The repair removes the obstruction; the promotion still has to happen. Both points are visible in the kernel, and neither is something the financial scenario could have illustrated honestly.

---

## Deposits are structured, not fungible

A dollar is a dollar. Two deposits of the same amount are interchangeable.

EpArch deposits are addressable individual records with their own headers. Two deposits with the same P are not interchangeable: their V, S, E, τ, ACL, and redeemability fields can differ, and downstream operations (challenge, repair, export) act on individual deposit objects, not on aggregates. There is no "balance of P." There is *this deposit* of P, *that deposit* of P, possibly with conflicting headers, all visible on the ledger at the same time. The institution does not fold them together.

---

## Forgotten is the absence of a deposit, not a kind of deposit

A real bank does not have a "forgotten" state. Closed accounts are closed; archived records are archived; what is gone is gone, and that is the end of the institutional story.

The EpArch bank treats *capacity deletion* and *epistemic closure* as different operations, and the lifecycle marks them with different statuses. `Revoked` is epistemic closure: the bank tested the deposit, found the path closed, and stands behind that judgment. The record persists; an agent that looks the deposit up reads its content and sees the revocation. `Forgotten` is capacity deletion: the deposit is no longer there. There is no content to read, no judgment to consult, nothing for an agent to reason about. A forgotten deposit is not a deposit the bank holds in a special status; it is the absence of a deposit the bank used to hold.

The distinction matters because the two operations encode different bank-side acts and license different downstream moves. An agent searching for what the institution has said about P will find a `Revoked` deposit and learn that the institution closed the path; the same agent will not find a `Forgotten` deposit at all, because there is nothing to find. The financial metaphor collapses these into "closed" because real banks do not need to say anything else about what is gone. The EpArch bank does, because the constraint that capacity is finite is real and the architecture is honest about which deletions were made for capacity reasons and which were made because the bank reached an epistemic judgment. The two are distinguishable from outside; only one of them has content; neither of them is a state in which an agent does ongoing work.

---

## Putting it together

The pattern across all seven disanalogies is the same. The EpArch bank is more *minimal* than a financial bank, not more elaborate. It does less. It does not consume on use, does not hold reserves, does not extend credit, does not enforce authorization, does not adjudicate truth. What it *does* — keep a structured ledger with a five-state lifecycle and a first-class repair path — is exactly what is needed for downstream agents to do field-localized diagnosis and targeted repair, and nothing more.

A working one-sentence definition that does not depend on the financial metaphor at all:

> **An EpArch bank is a non-consuming, non-scarce, non-enforcing ledger that records authorized deposits in a five-state lifecycle and exposes them to agents who manage their own credit.**

The rest of the file talks about that object.

---

## Acceptance is governance, not truth

The bank's authority is `Accept`. `Accept` is the predicate that decides whether a candidate deposit gets promoted to `Deposited` within this bubble.

`Accept` is *governance*, not *adjudication*. The bank is not certifying that the underlying claim is true about the world. It is certifying that, by the bank's own standards, this deposit currently meets the bar for authorization. Different banks have different bars. A claim that clears at Bank A might not clear at Bank B. A deposit that is authorized in one bubble might not be authorized in another.

The constraint surface — the world, the records, the redeemability path — is what eventually rules on truth. The bank is the institution that records what has currently been certified pending such a ruling. Acceptance is upstream of agent action and downstream of the constraint surface, and treating it as either of those endpoints is a category error.

This is the second of the two misreadings the file is built to close off. The first was *the bank is the agent's beliefs*; this one is *the bank decides what is true*. Neither is what the bank is for.

---

## Bubbles and inter-bank transfer

Each bubble is its own bank. Same depositor, same underlying claim, different bank — different ledger, different acceptance criteria, different `Accept` predicate, different lifecycle history.

When a deposit moves between bubbles, one of two things has to happen. Either the receiving bubble has an established trust relationship with the sending bubble — a `TrustBridge` in the architecture, a correspondent-banking arrangement in the metaphor — and the deposit crosses without re-verification. Or the receiving bubble runs its own acceptance protocol on the incoming deposit, **revalidating** it under its own standard before promoting it. The wire that clears under a syndication agreement is doing the first. The international transfer that has to satisfy KYC at the receiving bank is doing the second.

The bubble dimension is what makes the architecture's claim about same-claim-different-status coherent. A claim can be `Deposited` in B and `Revoked` in B′, and there is no contradiction, because each bank's ledger is its own ledger. The deposit is the unit; the bubble is the scope; an authorization in B is not automatically an authorization in B′. Every theorem about `knowledge_B` is bubble-indexed for exactly this reason.

---

## `knowledge_B` is what the bank stands behind, not what anyone believes

The architectural payoff sits in the definition of `knowledge_B`.

`knowledge_B B P` is defined as: *there exists an active authorized deposit for P in B*. That is a fact about the institutional ledger. It is not a fact about any agent's psychology. It is not a feeling. It is not a belief. It is what the institution is currently committed to having certified, scoped to a specific bubble.

An agent that consults the bank receives access to this signal. The agent's *own* belief about P is a separate layer that the agent forms on the basis of consultation, weighed against its own stakes, fallbacks, and credit policy. The architecture is careful to keep these layers apart. The financial-bank metaphor makes the separation feel obvious — my belief that I have money in the bank is one thing, the bank's ledger entry is another, the actual reserves are a third — and the architecture is named for the middle one.

Three layers, three different objects, three different kinds of evidence. The bank is the middle layer. It is the layer that is *shared*. It is the layer that exposes structure to inspection. It is the layer that supports field-localized diagnosis and targeted repair. The other two layers — agent psychology above it, constraint surface below it — exist, are real, and are out of scope for what the bank itself does.

---

# Takeaway

The bank is the substrate that holds authorized deposits, runs the lifecycle, and certifies authorization within its scope.

It is not an agent. It does not believe. It does not adjudicate truth. It does not gate action. It does not consume deposits on use, hold reserves, extend credit, or distinguish closed from forgotten by accident. It does what an institution does and only that: keeps a ledger, applies its acceptance criteria, runs the lifecycle gates, distinguishes the five named statuses, exposes everything it knows to whoever consults it, and stands behind what it has certified — within its bubble, until challenged, repaired, revoked, or forgotten.

The financial-bank metaphor is the on-ramp. The minimal-ledger definition above is the architectural object. Once a reader has both, the rest of the architecture — challenges, repair pipelines, export, multi-bubble theorems — has somewhere to land.

---

*[← Bubbles](../bubble.md) · [The Deposit →](deposits/deposit.md)*
