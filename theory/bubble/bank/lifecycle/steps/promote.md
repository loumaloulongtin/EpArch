# The Front-Shelf Boundary Story

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [← Register](register.md) · [← Withdraw](withdraw.md) · [← Challenge](challenge.md) · [← Tick](tick.md) · [← Repair](repair.md) · [← Revoke](revoke.md) · [Forget →](forget.md)*

---

## In this series

- [The Cooling Rack Story](submit.md) — `Submit`, the standard entry path
- [The Central Kitchen Delivery Story](register.md) — `Register`, the vouched-for entry path
- [The Front Counter Story](withdraw.md) — `Withdraw`, the recorded reliance event
- [The Returned Loaf Story](challenge.md) — `Challenge`, the recorded act of pulling a live entry out of circulation
- [The Wall Clock Story](tick.md) — `Tick`, the only event that moves the bank's clock
- [The Hold-Tray Story](repair.md) — `Repair`, the recorded return of a quarantined deposit to the candidate queue
- [The Failure-Bin Story](revoke.md) — `Revoke`, the recorded closure of a quarantined deposit
- [The Front-Shelf Boundary Story](promote.md) — `Promote`, the recorded crossing of the candidate-to-live boundary *(you are here)*
- *(more step files follow: forget, update)*

---

## The moment the loaf goes out

The sourdough has been on the cooling rack since 5:12. The head baker has tapped the bottom of two loaves to listen for the right hollow, weighed one, looked at the crumb on a sliced corner. The labels are on, the headers check out, the morning's QC sheet has been initialled. At 5:58, two minutes before the doors open, the head baker walks the trays from the cooling rack to the front shelf. The day-book gets an entry: *5:58, S-04-26 to front shelf, headers and QC verified*. Until that moment, no customer could buy from S-04-26 — the loaves were behind the counter, in the back room, in the queue. After that moment, S-04-26 is part of what the bakery is selling. A customer pointing at the basket at 6:01 is pointing at something the bakery has *committed to* as on-the-shelf.

The committing is the move. Not the baking; not the labelling; not the QC; not the carrying of the trays. Those happen around it and prepare for it, but the committing is the day-book entry that says *as of now, this batch is what we're selling*. Before the entry, the trays are in the back room as a matter of fact; whether they go to the front shelf is still an open question the head baker is settling. After the entry, the trays are on the front shelf as a matter of *bank-recorded commitment*, and the rest of the day's selling is built on that commitment.

That is what `Promote` does to a deposit. The bank takes the slot from `Candidate` to `Deposited`. The deposit becomes a live entry, available for reliance. The kernel's commitment is the boundary crossing — the structural fact that *this slot, which was previously a candidate, has now been crossed over into the live pool*. Whatever multi-stage validation the deployment ran in the surrounding workflow to decide the candidate was ready does not appear on the trace as a sequence of events; what appears is the single boundary crossing, recorded with the agent and bubble that crossed it.

---

## What the move actually does

In the kernel, `Step.promote` carries an agent `a`, a bubble `B`, a slot index `d_idx`, and a single bank-side hypothesis: `h_candidate : isCandidate s d_idx`. The successor state is `{ s with ledger := updateDepositStatus s.ledger d_idx .Deposited }` — the ledger is the same except the deposit at that slot now reads `Deposited`. The deposit's content is not modified by the kernel-level step. Other deposits' statuses are untouched. The clock does not move. The bubbles field does not change. The agents' ladder map is the same.

The constructor's own comment is explicit: *implementations may use multi-stage internal validation pipelines between Candidate and Deposited; this step records the minimal architectural boundary at which a deposit becomes live — not the validation mechanism that preceded it*. The architecture is deliberately quiet about *how* a candidate gets cleared. A deployment may run a heavy validation stack — checks against external sources, peer review, automated test suites, a human committee — or a light one, or none at all beyond the agent's say-so. None of that appears in the kernel's commitment. What appears is the line the deposit crossed.

This is the same shape as the `Submit` / `Register` distinction: `Register` is the path that vouches a deposit straight into `Deposited` without going through the candidate queue, and `Promote` is the path that takes a candidate across into `Deposited` after whatever queue-side validation the deployment chose to run. The two paths land at the same status, by different boundary crossings, and the trace records which path was taken because the entry actions (`Submit` followed by `Promote`, versus `Register`) are distinguishable.

---

## Why candidate

The reason `isCandidate` is the precondition is the same shape as the rest of the lifecycle's preconditions. *Promote* is the recorded crossing of the candidate-to-live boundary. A `Deposited` deposit is already across — a second `Promote` against it would not be a coherent recorded event. A `Quarantined` deposit must come back through `Repair` before it can be re-promoted (this is the forced revalidation path the `Repair` file describes); the architecture refuses to let a quarantined deposit jump straight back to live. A `Revoked` deposit is closed for the structured promote/repair path, and a `Forgotten` deposit is operationally void. If a deployment wants to replace a non-Forgotten closed slot anyway, that is the heavier `Update` path, not `Promote`.

`Promote` is reserved for the recordable transition `Candidate → Deposited`, because that is the boundary the bakery has to write down: *what was a queue item is now what we are selling*.

---

## What `Promote` does and does not adjudicate

`Promote` is the architecture's commitment that a deposit is now live. It is *not* the architecture's commitment that the deposit's content is true, or that the standard is appropriate, or that the provenance is reliable, or that any external verification has been done. The kernel records the boundary crossing; the deployment's surrounding validation workflow is what makes the boundary crossing a reasoned act. A deployment that runs a thorough validation pipeline before `Promote` and a deployment that fires `Promote` on every candidate immediately are deploying the same kernel; the kernel's guarantee about a `Deposited` deposit is just *some agent in some bubble crossed it across the boundary*, and reliance policy on top of `Step.withdraw` is what decides what to make of that guarantee.

This is the architecture's deliberate refusal to bake validation into the kernel. Different deployments need different validation; some need none, some need heavy, and the lifecycle does not pretend to know which. What the lifecycle commits to is the trace shape: *the candidate stage exists, it can be longer or shorter, and the boundary crossing into live is recorded as its own event with its own attribution*.

`Promote` does not modify the deposit's content. The headers and the proposition the deposit went into the candidate queue with are the same headers and proposition it leaves with. If the deployment's validation discovered something the deposit needed to *say differently*, that change is the heavier `Update` path; `Promote` is the cleaner path that crosses the boundary without rewriting what the deposit says.

`Promote` does not interact with quarantine or revocation. Once a candidate is promoted, the only way back is through `Challenge` (which requires `Deposited` and lands in `Quarantined`). The `Repair` file's note that there is no architectural shortcut from `Quarantined` to `Deposited` is the same shape from the other side: the only architectural path *into* `Deposited` from a non-candidate state is `Register` (vouched entry) or `Update` (revision-mode overwrite); from `Candidate` the path is `Promote`.

---

## How the trace reads later

A trace reader scans for `Action.Promote _ _ _` entries to find recorded boundary crossings. The action label names the promoting agent, the bubble, and the slot. The kernel guarantees, by the `Step.promote` constructor precondition, that the slot was in `Candidate` status when the transition fired.

How the slot became `Candidate` is a separate trace question. It may have entered as Candidate through `Submit`; it may have returned to Candidate through `Repair`; it may have been installed as Candidate through `Update`; or it may already have been Candidate in the trace's initial state. `Promote` does not identify that history by itself. It records only the boundary crossing from Candidate to Deposited at this point in the trace.

If a deposit becomes `Deposited` during a trace from a state where that claim was not already deposited, the kernel-level entry paths are `Register`, `Promote`, or `Update` with a `Deposited` target status. A trace may also begin with deposits already in `Deposited` status, in which case the entry event lies outside the observed trace. Which path was taken is a question the trace answers; the kernel makes the three actions distinguishable.

---

## Takeaway

`Promote` is the recordable crossing of the candidate-to-live boundary. The bank-side precondition is the single fact that the deposit is in `Candidate` status; the successor state takes that one slot to `Deposited`; the deposit's content is unchanged; the validation work that justified the crossing lives in the surrounding workflow, not in the kernel.

The architecture's commitment is structural: *being live is the result of a recorded boundary crossing by an attributed agent in an attributed bubble*, and the kernel guarantees no more and no less. Combined with `Submit` on one side and `Challenge` / `Repair` / `Revoke` on the other, `Promote` completes the central spine of the lifecycle: deposits enter, get cleared into circulation, may be pulled out and re-cleared or closed out. The next file in the series is `Forget`, the capacity-management move that voids a slot from the bank's operational memory and leaves only the tombstone the ledger needs for index stability.

---

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [← Register](register.md) · [← Withdraw](withdraw.md) · [← Challenge](challenge.md) · [← Tick](tick.md) · [← Repair](repair.md) · [← Revoke](revoke.md) · [Forget →](forget.md)*
