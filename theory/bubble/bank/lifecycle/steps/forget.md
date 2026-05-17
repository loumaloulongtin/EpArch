# The Dumpster Story

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [← Register](register.md) · [← Withdraw](withdraw.md) · [← Challenge](challenge.md) · [← Tick](tick.md) · [← Repair](repair.md) · [← Revoke](revoke.md) · [← Promote](promote.md) · [Update →](update.md)*

---

## In this series

- [The Cooling Rack Story](submit.md) — `Submit`, the standard entry path
- [The Central Kitchen Delivery Story](register.md) — `Register`, the vouched-for entry path
- [The Front Counter Story](withdraw.md) — `Withdraw`, the recorded reliance event
- [The Returned Loaf Story](challenge.md) — `Challenge`, the recorded act of pulling a live entry out of circulation
- [The Wall Clock Story](tick.md) — `Tick`, the only event that moves the bank's clock
- [The Hold-Tray Story](repair.md) — `Repair`, the recorded return of a quarantined deposit to the candidate queue
- [The Failure-Bin Story](revoke.md) — `Revoke`, the recorded closure of a quarantined deposit
- [The Front-Shelf Boundary Story](promote.md) — `Promote`, the recorded crossing of the candidate-to-live boundary
- [The Dumpster Story](forget.md) — `Forget`, the agent-invoked deletion of a slot from operational memory *(you are here)*
- *(more step files follow: update)*

---

## End of day, or whenever the slot is no longer worth carrying

Closing time. The day-book has rows from a quiet Tuesday three weeks ago — loaves from a small batch nobody is buying from any more, the row has just been sitting there, taking up a line in the spreadsheet. The manager points at the row, asks the staff to deal with it. Whatever physical loaf might have remained in the back goes into the dumpster outside. As far as the bakery is concerned, that loaf no longer exists. The row's number stays on the spreadsheet only because the spreadsheet is a list and renumbering everything below would break every reference to every other entry — but operationally, the row is gone.

That is what `Forget` does to a deposit. The bank's commitment is that this slot is no longer carrying anything the bank should be reasoning with: no agent should rely on it, no future move can reason with it, and it cannot be forgotten again. The slot's index is preserved for the sake of the indices around it, but the deposit at the slot is, for the bank's purposes, gone.

---

## What the move actually does

In the kernel, `Step.forget` carries an agent `a`, a bubble `B`, a slot index `d_idx`, the existing deposit `d_old`, a hypothesis `h_exists` that `s.ledger.get? d_idx = some d_old`, and a hypothesis `h_not_forgotten` that `d_old.status ≠ .Forgotten`. The successor state takes the slot to `.Forgotten`. Other deposits' statuses are untouched. The clock does not move. The bubbles field does not change. The agents' ladder map is the same. (The reason the slot is marked `.Forgotten` rather than physically removed from the ledger is a representation choice — the ledger is implemented as an indexed list and other slots' indices have to remain stable. The architectural intent is straightforward: the slot is gone.)

The two preconditions read together as: *a deposit currently exists at this slot, and it is not already forgotten*. The first is what makes the action coherent at all — there has to be something at the slot for the forget to be a forget of *something*. The second is what makes `Forget` irreversible: a slot that has already been forgotten cannot be forgotten again, because there is no operational deposit there to void.

Every other status is forgettable. A `Candidate` deposit can be forgotten — the agent decided not to carry the candidate any further, and clears the slot. A `Deposited` deposit can be forgotten — the agent decides the live entry is no longer worth carrying as a reliance target (the fact may still be true; the agent simply chooses not to carry it). A `Quarantined` deposit can be forgotten — pulled from circulation and then deleted from operational memory without going through the structured `Revoke` path. A `Revoked` deposit can be forgotten — the institutional judgment was filed at the time of revocation; the slot's continued operational existence is no longer needed.

---

## Forget vs. Revoke

The parent file's `Forget` / `Revoke` contrast comes through here in operational form. `Revoke` is the bank's way of saying *we judged this deposit bad and we are keeping the record readable so the judgment stays on file*; the deposit's content survives the move. `Forget` is the bank's way of saying *this deposit is gone from our operational memory*; the content does not survive the move. They are categorically different commitments, used for categorically different reasons.

A deployment that wants both — the institutional judgment on file *and* the operational content eventually voided — uses them in sequence: `Challenge → Revoke → Forget`. The revoke files the judgment on the trace; the later forget voids the content. A forget without a prior revoke leaves no surviving content-readable record of what was at the slot; what remains is whatever the trace records of moves that touched it.

---

## What `Forget` does not do

`Forget` does not propagate. A forget at one slot does not touch any other slot; a forget in one bubble does not touch the same content in another bubble; the agents' ladder positions are untouched.

`Forget` does not fire on an already-forgotten slot. The `h_not_forgotten` precondition is what makes this true. There is nothing operational to forget a second time.

---

## How the trace reads later

A trace reader scans for `Action.Forget _ _ _` entries to find recorded deletions. The action label names the forgetting agent, the bubble, and the slot. The kernel guarantees, by the `Step.forget` constructor preconditions, that some non-Forgotten deposit existed at the slot at the moment of the forget. *What* that deposit was is recoverable from the trace history or from the trace's initial state, depending on where the observed trace begins. Earlier moves at that slot may record what entered, what status changes happened, and what slip, if any, was filed at challenge time. After the forget, the slot's state-time content is the tombstone; what the slot had been is read from the prior record, not from the post-forget ledger entry.

A reader who wants to know whether a slot's institutional judgment was filed before its operational void looks for an `Action.Revoke` ahead of the `Action.Forget` at the same slot. The presence or absence of that prior revoke is what distinguishes *forgotten after a recorded judgment* from *forgotten before any judgment was recorded*. The trace carries the distinction; the post-forget ledger does not.

---

## Takeaway

`Forget` is the recordable agent-invoked deletion of a slot from the bank's operational memory. The bank-side preconditions are that a deposit currently exists at the slot and is not already forgotten; the successor state takes that one slot to `.Forgotten`. The architecture's commitment is that the slot is gone — no agent should rely on it, no future move can reason with it, and it cannot be forgotten again.

The next file in the series is `Update`, the heavier wholesale-overwrite move that replaces a slot's deposit in entirety and pays the revision-trace cost.

---

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [← Register](register.md) · [← Withdraw](withdraw.md) · [← Challenge](challenge.md) · [← Tick](tick.md) · [← Repair](repair.md) · [← Revoke](revoke.md) · [← Promote](promote.md) · [Update →](update.md)*
