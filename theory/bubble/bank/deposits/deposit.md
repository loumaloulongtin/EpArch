# The Deposit

*[← The Bank](../bank.md) · [The Claim →](claim.md)*

---

## In this section

- [The Claim](claim.md) — P: what the deposit is *of*
- [Header Fields](headers/headers.md) — why deposits need structure beyond P
- [Standard](headers/standard.md) · [Error Model](headers/error-model.md) · [Provenance](headers/provenance.md) · [Access Control](headers/access-control.md) · [Redeemability](headers/redeemability.md) · [Temporal Validity](headers/temporal-validity.md)

---

## Why P alone isn't enough

The simplest mistake is to think an epistemic system stores bare propositions.

A bare proposition is atomic. It can be kept or discarded. Nothing else. If it turns out to be wrong, the only available move is to throw it out and find another one.

The unit EpArch actually stores is a **deposit**: a proposition **P** packaged with the metadata an agent needs to decide whether to act on it, push back on it, repair it, pass it on, or close it out. The metadata is the validation header — the six fields covered individually in 01–06: standard (S), error model (E), provenance (V), temporal validity (τ), access control (ACL), redeemability.

A bare answer is *actionable*. A deposit is *repairable*.

That word — repairable — is the one that earns the headers. Without them, every failure is total: a wrong claim has to be replaced wholesale. With them, a failure can be localized to a particular field, the rest of the deposit can be preserved, and a targeted fix becomes possible. "The source was wrong" is a different problem from "the standard was too lax," and the system needs to be able to tell them apart in order to do anything other than throw the whole thing out.

The headers are not decoration. They are what makes the difference between a system that can only forget its mistakes and a system that can correct them.

---

## Why a deposit is not a memory

There is also a mistake in the other direction.

If the deposit feels like the natural unit for "everything I know about X," it has been inflated past its actual size. A deposit is *less* than a memory or an experience; it is the atom underneath one.

A memory is a *cluster* of deposits.

Walk into a kitchen you have never been in. In the first second your eyes hand you a stack of separate items: there is a kettle on the counter, the floor is tiled, the window faces a yard, someone has left a mug by the sink. Each of those is its own deposit. Each has its own P. Each has its own error model — the kettle might be a stage prop, the mug might be unwashed, the tile might be slippery underfoot. Each has its own redeemability path: pick the kettle up, step on the tile, look closer at what is in the mug.

What makes them feel like a single "memory of walking into the kitchen" is not that they are one deposit. It is that they share a **V**. Same observer, same instant, same room, same lighting. Provenance is the thread that ties the cluster together.

This matters because the headers are *per-deposit*, not per-cluster. When one item in the cluster fails — you look again and realize the kettle is actually a coffee maker — only that one deposit needs to be quarantined and repaired. The rest of the room stays standing. The tile is still tile. The mug is still by the sink. The window still faces the yard. The "memory of walking into the kitchen" survives an error inside it, because the error is localized to a single deposit and the cluster has structure beyond a single P.

A naive view says *the memory was wrong*. The deposit-level view says *one deposit in the cluster failed; the rest are intact, and the failed one can be repaired without taking down the others*.

That is the granularity the architecture is committed to. It is finer than people usually expect, and the room example is the cleanest way to feel why the finer granularity is worth having.

---

## The headers, briefly

The six fields, in the order they receive their own files:

| Field | Function | File |
|---|---|---|
| **P** | The claim. | (covered everywhere) |
| **S** | The standard the claim has to meet. | 01 |
| **E** | The error model — what could be wrong. | 02 |
| **V** | Provenance — where it came from. | 03 |
| **ACL** | Who is authorized to receive or rely on it. | 04 |
| **Redeemability** | How the claim can be tested against a constraint surface. | 05 |
| **τ** | Currentness — how stale the deposit has become. | 06 |

Each gets its own intuition pump in its own file. This file is about the deposit *as a whole* — the unit those fields hang off of, and the lifecycle the unit moves through.

---

# Scenario: a story going to press

A reporter has been working on a story. By the time it goes to press it has moved through a recognizable series of states, and the names the architecture uses for those states match the names a newsroom would use.

This scenario is the anchor for everything below. We will follow one claim from the moment the reporter files it through publication, pushback, correction, and — in one of the branches — retraction.

The claim:

> A named city official approved a contract to a firm owned by a relative.

Call this the **P** of the deposit. The story around it carries the rest of the header — sourcing standards (S), known failure modes the desk worried about (E), provenance (V: the documents and named sources behind it), the audience the piece is going out to (ACL: subscribers, syndicates, the public web), the path on which the claim could be tested (redeemability: FOIA records, court filings, on-the-record statements), and how recently the underlying records were checked (τ).

---

## Candidate — the story is filed but not yet published

The reporter sends the draft to the editor. At this point the deposit exists but is not yet authorized: the bank has the entry, but not as a withdrawable claim.

In the architecture this state is **Candidate**. The deposit is on the ledger; it is visible to the editorial process; but no agent is yet allowed to *rely* on it. The editor reads the draft, sends back questions about sourcing, asks the reporter to confirm a date with a second source, and pushes the V field a little further before the desk will sign off.

This is the role of the Candidate state. It is the gap between *submitted* and *authorized*. A claim that is on the ledger but still in Candidate has been written down but has not been promoted to something a downstream agent may withdraw and act on.

---

## Deposited — the story runs

The desk is satisfied. The piece runs in the morning edition. The deposit's status moves from `Candidate` to `Deposited`.

This is the only status that licenses withdrawal. A claim in `Deposited` is one that another agent — a reader, a wire service, another reporter writing a follow-up — is allowed to rely on as something the bank stands behind. The headers are the bank's record of *why* it stands behind this claim: the standard the desk applied, the error modes they considered, the provenance they checked.

The story is now public. P is being acted on by readers.

---

## Quarantined — pushback arrives

By mid-morning, two things have happened.

A second reporter at a different outlet has written that the relative in question divested from the firm two years ago. And a lawyer for the official has sent the paper a letter pointing to a corrected disclosure form.

The desk does not yet know whether the story is wrong. But it can no longer be confidently relied on. The deposit moves to **Quarantined**: still on the ledger, no longer withdrawable, pending resolution.

This is the architectural value of having an intermediate state. The claim is not retracted (that would assert it was wrong). It is not still live (that would assert it is still trustworthy). It is held — visible, suspended, under review — and the question of *which field broke* is now the point of the investigation.

This is where field-localization earns its keep. The same surface event ("the story is in trouble") decomposes into six different possible underlying failures, and the repair path is different for each:

- **V** — the documents the reporter relied on were superseded by a later filing the desk did not see. Provenance failure.
- **S** — the desk's standard for "approved a contract" was looser than it should have been; the official signed a procedural memo, not the contract itself. Standard failure.
- **E** — the desk did not consider that a relative might have divested between the contract date and publication. Missing failure mode.
- **τ** — the records the reporter pulled were current as of last quarter but not as of yesterday. Temporal validity failure.
- **ACL** — the wire pickup pushed the story to outlets the desk had not actually cleared it for. Access-control failure.
- **Redeemability** — the underlying records turn out to be sealed; there is no path on which the claim can actually be tested by anyone. Redeemability failure.

Each of these is a different problem, and each has a different fix. A claim in `Quarantined` does not get treated as one undifferentiated "wrong." The desk's job — and, in the architecture, the agent's job — is to identify which field is the locus of the failure and act accordingly. The header files take up each field in turn and show what its failure mode looks like in operation; the lifecycle file picks up what the institution does once that diagnosis has landed.

---

## Repaired → Candidate — the correction

Suppose the failure localizes to V. The desk pulls the more recent disclosure, confirms that the relative did divest two years ago, and reissues the story with a correction note: *An earlier version of this piece reported that the contract was awarded to a firm owned by a relative; the relative had divested before the contract was signed.*

The architectural shape of this is:

> Repair the V-field. Re-enter as `Candidate`, not as `Deposited`.

This is load-bearing. A repaired deposit does not simply get reinstated. It re-enters the lifecycle at `Candidate` — meaning the desk has to *re-promote* it before any other agent may rely on the corrected version. The repair itself is not the authorization. The re-promotion is.

This is what makes the system *repairable* rather than *replaceable*. The claim was not thrown out and replaced by a new one with a different identity. The same deposit was repaired at the field that broke, sent back through the validation gate, and re-authorized. The history is preserved: there is a record that this deposit was once `Deposited`, then `Quarantined`, then repaired, then re-promoted. A reader who pulls the article in six months can see both the corrected text and the correction note that explains what changed.

---

## Revoked — the alternative branch

Suppose instead that the failure is at S. The desk concludes that what the official signed was a procedural memo, not an approval of a contract; the entire frame of the story is wrong. There is nothing to repair — the claim itself was the wrong thing to claim.

The deposit is **Revoked**.

`Revoked` is not the same state as "removed from the website." It is a permanent epistemic boundary: this path was tested, it was found closed, and the bank now signals that it has been closed. The story comes down with a retraction note. Subsequent searches turn up the retraction. Any wire outlets that picked it up are notified.

The distinction between `Quarantined` and `Revoked` matters because they say different things to downstream agents. `Quarantined` says *we are still working this out*. `Revoked` says *we worked it out and the answer was no*. Both are pieces of information; they are not the same piece.

---

## Forgotten — the deposit that is no longer there

There is one more state, and it is the one most likely to be misread.

Suppose, years later, the paper is migrating to a new content management system and old retracted articles are being purged from the archive for storage reasons. The deposit becomes **Forgotten**.

`Forgotten` is not a stronger version of `Revoked`. It is categorically different.

`Revoked` is an *epistemic* state. The record persists. The retraction note is on file. An agent that pulls the article in the future can read both the content and the marker showing it was retracted. The bank made a judgment and the judgment is still readable.

`Forgotten` is an *operational* state. The deposit is gone. An agent looking for it finds nothing — not a deposit in a different status, not a marker, nothing. `Forgotten` is not a state an agent reasons about the contents of, because there are no contents to reason about.

The separation from `Revoked` exists so that an agent cannot mistake capacity deletion for epistemic closure. `Revoked` is the bank having made a judgment; `Forgotten` is the bank having freed capacity. Two different acts, and the architecture names them differently so a reader of the ledger can tell which happened.

---

## Bubbles and export — the deposit is scoped

There is one more piece of the deposit's structure worth surfacing at this level: a deposit is not global. It lives in a **bubble**.

A bubble is the scope in which a deposit was authorized. The newsroom is one bubble. A wire service that picks the story up is another. A foreign-language outlet that translates and republishes it is a third. Same P, three deposits, three bubbles.

When a deposit moves between bubbles, one of two things has to happen. Either the receiving bubble has an established trust relationship with the sending bubble — a `TrustBridge` in the architecture, a syndication agreement in the newsroom — and the claim crosses without revalidation. Or the receiving bubble runs its own acceptance protocol on the incoming deposit, **revalidating** it under its own standard. The wire service that picks up the story under a syndication deal is doing the first; the foreign outlet that re-reports it with its own desk is doing the second.

This is not a footnote. It is the reason "the same claim" can be live in one bubble and revoked in another without contradiction. The deposit is the unit; the bubble is the scope; an authorization in B is not automatically an authorization in B′.

The headers and the lifecycle covered above are the shape of the deposit *inside one bubble*. The export story is what happens when it crosses.

---

# Takeaway

The deposit is the unit of an epistemic system that wants to be *repairable* rather than only *replaceable*.

It is more than a bare proposition: the headers are what make field-localized diagnosis and targeted repair possible at all. Without S, E, V, τ, ACL, and redeemability, every failure is total, every fix is replacement, and every claim's history is lost the moment it is corrected.

It is also less than a memory: a memory is a cluster of deposits tied together by shared V. Looking around a new room produces a stack of separate atomic deposits, not one big undifferentiated remembrance, and the cluster's resilience to a single error inside it is exactly the payoff of working at deposit granularity instead of memory granularity.

The lifecycle — `Candidate → Deposited → Quarantined → (Repaired → Candidate) / Revoked / Forgotten` — gives those deposits names for the states they actually move through. Each transition has a meaning, and the meanings are not interchangeable: `Quarantined` is not `Revoked`, `Revoked` is not `Forgotten`, and a repaired deposit re-enters as `Candidate` rather than being silently reinstated. The architecture refuses to collapse these distinctions, and the refusal is what gives the system enough structure to talk about correction at all.

Bubbles scope the whole thing: a deposit is authorized somewhere, and crossing into a new somewhere requires either a trust bridge or revalidation under the new bubble's standard.

The remaining files in this series open each header field individually — what S is and how it is set, what E is and how it grows, what V looks like as a chain, what ACL governs and what it doesn't, what redeemability requires of a path, and what τ does that no other field can. This file is the frame those fields hang on. The next files are the fields themselves.

---

*[← The Bank](../bank.md) · [The Claim →](claim.md)*
