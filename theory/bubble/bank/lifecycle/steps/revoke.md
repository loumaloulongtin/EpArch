# The Failure-Bin Story

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [← Register](register.md) · [← Withdraw](withdraw.md) · [← Challenge](challenge.md) · [← Tick](tick.md) · [← Repair](repair.md) · [Promote →](promote.md)*

---

## In this series

- [The Cooling Rack Story](submit.md) — `Submit`, the standard entry path
- [The Central Kitchen Delivery Story](register.md) — `Register`, the vouched-for entry path
- [The Front Counter Story](withdraw.md) — `Withdraw`, the recorded reliance event
- [The Returned Loaf Story](challenge.md) — `Challenge`, the recorded act of pulling a live entry out of circulation
- [The Wall Clock Story](tick.md) — `Tick`, the only event that moves the bank's clock
- [The Hold-Tray Story](repair.md) — `Repair`, the recorded return of a quarantined deposit to the candidate queue
- [The Failure-Bin Story](revoke.md) — `Revoke`, the recorded closure of a quarantined deposit *(you are here)*
- *(more step files follow: promote, forget, update)*

---

## Late morning, after the call to the supplier

The hold tray still has half of S-04-26 in it. The other half went back to the cooling rack after the central-kitchen call. But the manager has talked it over with the head baker, looked at the remaining loaves, and — given the pattern of the complaints, and the smell of one of the cross-sections — made a call: *these don't go back out, they go to the failure bin*. The remaining loaves go into the bin in the back, the day-book entry is updated — *S-04-26 (remaining), revoked after manager's review of cross-section, complaint slip and call notes attached* — and the bin is what it is. Anyone walking past can see what was in there and read the slip. The loaves are not coming back to the front shelf. The record of *we judged this batch bad and pulled it out for these reasons* is filed and visible.

The bakery does not erase the entry. It does not pretend the loaves never existed. It records, plainly and durably, that *we had this batch, we judged it bad, here is the slip and here is the call notes, the loaves are in the bin*. Three months later, if a regulator or a curious customer or the head baker's apprentice asks *what happened with S-04-26*, the day-book and the bin between them tell the whole story.

That is what `Revoke` does to a deposit. The bank takes the slot from `Quarantined` to `Revoked` and leaves the deposit's content readable. The status flag has changed; the headers and the proposition and the provenance and the standard and the temporal window are all where they were. An agent looking up the slot finds a deposit that the bank has marked as closed-as-failure, with the full record of what it had said still on the page. *Revoke* is the bank's commitment that this slot is not coming back to circulation through the normal lifecycle, and that the institutional judgment about the slot is itself a thing on the trace.

---

## What the move actually does

In the kernel, `Step.revoke` carries an agent `a`, a bubble `B`, a slot index `d_idx`, and a single bank-side hypothesis: `h_quarantined : isQuarantined s d_idx`. The successor state is `{ s with ledger := updateDepositStatus s.ledger d_idx .Revoked }` — the ledger is the same except the deposit at that slot now reads `Revoked`. The deposit's content is not modified by the kernel-level step. Other deposits' statuses are untouched. The clock does not move. The bubbles field does not change. The agents' ladder map is the same.

The constructor's own comment is brief and exact: *deposit removed from circulation. Authorization is an agent-level concern external to the bank's LTS*. The kernel does not adjudicate whether the revocation is justified — the surrounding workflow does that, possibly drawing on the same complaint slip the original `Challenge` filed, possibly on subsequent investigation, possibly on policy. What the kernel commits to is the structural fact that *this agent, in this bubble, recorded the revocation of this slot*, and that the deposit's content is still readable for whoever needs to read it later.

---

## Why quarantined

The reason `isQuarantined` is the precondition is the same shape as the rest of the lifecycle's preconditions. *Revoke* is the recorded closure of something that has already been pulled from circulation. A `Deposited` deposit has not been pulled; the architecture insists on the intermediate step — first `Challenge` to `Quarantined`, then `Revoke` from there — because the slip that landed the deposit in quarantine and the judgment that closes it out are two different recorded events, and the trace should carry both. A `Candidate` deposit has not entered circulation; closing-out a never-circulated deposit is not a coherent revocation event (capacity-side deletion lives in `Forget`). A `Revoked` or `Forgotten` deposit is past the point.

`Revoke` is reserved for the recordable transition `Quarantined → Revoked`, because that is the transition the bakery has to write down: *the loaves we pulled to the hold tray are now in the failure bin, here is what we judged and why*.

---

## Revoked vs Forgotten

`Revoke` and `Forget` are the two ways a deposit leaves circulation, and they are categorically different. The parent file makes this contrast in passing; it is worth being explicit about it here because it is the architectural payload of `Revoke`.

`Revoke` keeps the content. The headers stay readable, the proposition stays readable, the provenance stays readable, and the recorded sequence of events around the slot is on the trace. The challenge slip is paired with the slot through the trace: the `Challenge` action carried the structured challenge object when the slot was moved to `Quarantined`. The `Revoked` deposit itself preserves the deposit content and status; the grounds for the challenge and revocation are recovered from the recorded events around that slot. *Revoked* is the bank's commitment that *we judged this deposit and closed it out as a failure*, and that the judgment itself is part of the bank's epistemic record. A regulator asking *what got revoked, when, and on what grounds* is asking a question the trace and the ledger together can answer in full.

`Forget` voids the content. The slot stops being an operational deposit; what remains is the `.Forgotten` tombstone whose role is index stability. *Forgotten* is the bank's commitment that this slot has been deleted from operational memory. A regulator asking *what was at slot 47 before the forget* is asking a question the bank no longer carries the answer to; the slip that may have been filed alongside it is no longer paired with a content-carrying deposit.

The two are not interchangeable. A bakery that puts every bad batch straight into the dumpster outside, with no record of *we judged this batch bad and binned it*, is a different kind of institution than one that keeps a failure bin with the slip attached. The bank takes the second posture as its default for adjudicated failure: the institutional judgment is part of what the bank has the right to be asked about.

---

## What `Revoke` does not do

`Revoke` does not modify the deposit's content. The headers, the proposition, the provenance, the standard, the error model, the temporal window — all stay as they were when the deposit was challenged. If the deployment's revocation workflow involves rewriting what the deposit *says* (a substituted source, a corrected wording, a revised standard), that rewrite is the heavier `Update` path with its `isRevision = true` cost; `Revoke` is the cleaner path that preserves the content.

`Revoke` also does not, by itself, prevent agents from reading the deposit. The status flag says *closed as failure*, but the content is still on the page. What changes is whether agents *should rely* on it: a downstream reliance policy, on top of `Step.withdraw`, is what filters revoked deposits out of the live-entry pool. The kernel-level `Step.withdraw` requires `Deposited`, not `Revoked`, so the kernel itself blocks reliance through the structural precondition. The deposit's *readability* is not the same as its *availability for reliance*; revocation closes the latter while preserving the former.

`Revoke` does not move the deposit out of the ledger. The slot stays at the same index. Other deposits' indices are unchanged. A deployment that wants to void the slot from operational memory — not merely close it out as a failed deposit — invokes `Forget` later as a separate move. `Revoke` blocks structured reliance by leaving the slot non-Deposited; `Forget` deletes the operational content and leaves only the tombstone.

---

## How the trace reads later

A trace reader scans for `Action.Revoke _ _ _` entries to find recorded closures. The action label names the revoking agent, the bubble, and the slot. The kernel guarantees, by the `Step.revoke` constructor precondition, that the slot was in `Quarantined` status when the transition fired. How it became `Quarantined` is a separate trace question. In the ordinary structured lifecycle, that will be a prior `Challenge`; but the trace may also begin with the slot already quarantined, or a heavier `Update` path may have installed that status. The reader can read off whatever pull-and-close arc the trace carries: what the kernel certifies is that the slot was quarantined at the moment of revocation.

The deposit's content remains accessible at the slot — anyone with a reason to ask *what was the deposit at slot 17, and what is its current status* gets back the same content they would have got at any earlier point, with the status now reading `Revoked`. The bank's commitment to keep the institutional judgment readable is not a side comment; it is what the lifecycle actually does.

---

## Takeaway

`Revoke` is the recordable closure of a quarantined deposit. The bank-side precondition is the single fact that the deposit is in `Quarantined` status; the successor state takes that one slot to `Revoked`; the deposit's content is preserved so the institutional judgment and the original deposit are both on the record. `Revoke` is not deletion — that is `Forget`'s job — and `Revoke` is not content rewrite, which lives in the heavier `Update` path.

The two-move shape *Challenge → Revoke* is the architecture's pull-and-close path, and it leaves the trace and the ledger both readable as the institutional record of the closure. The next file in the series is `Promote`, the move that takes a candidate deposit across the boundary into circulation in the first place.

---

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [← Register](register.md) · [← Withdraw](withdraw.md) · [← Challenge](challenge.md) · [← Tick](tick.md) · [← Repair](repair.md) · [Promote →](promote.md)*
