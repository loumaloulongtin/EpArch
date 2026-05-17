# The Hold-Tray Story

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [← Register](register.md) · [← Withdraw](withdraw.md) · [← Challenge](challenge.md) · [← Tick](tick.md) · [Revoke →](revoke.md)*

---

## In this series

- [The Cooling Rack Story](submit.md) — `Submit`, the standard entry path
- [The Central Kitchen Delivery Story](register.md) — `Register`, the vouched-for entry path
- [The Front Counter Story](withdraw.md) — `Withdraw`, the recorded reliance event
- [The Returned Loaf Story](challenge.md) — `Challenge`, the recorded act of pulling a live entry out of circulation
- [The Wall Clock Story](tick.md) — `Tick`, the only event that moves the bank's clock
- [The Hold-Tray Story](repair.md) — `Repair`, the recorded return of a quarantined deposit to the candidate queue *(you are here)*
- *(more step files follow: revoke, promote, forget, update)*

---

## Mid-morning, after the complaint

The hold tray has the remaining loaves of S-04-26 in it. The complaint slip is paper-clipped to the day-book entry. The manager rings the central kitchen, asks about the morning's flour delivery; the kitchen confirms there was a brief pH issue with the starter that they have since corrected, and that the test loaves they baked since came out fine. The manager goes to the hold tray, picks up the loaves, and walks them back to the *cooling rack* — not the front shelf. They are not going straight back into circulation. They are going back into the queue where the cooling-rack-and-front-check sequence happens, with a note: *S-04-26, repaired after starter-pH note from central, re-check before promotion*.

The bakery does not, at this moment, decide the loaves are good. It decides they are *eligible to be checked again*. The actual go/no-go on whether they go to the front shelf is the same go/no-go any candidate gets — the morning's promotion check, run again, with the hold-tray history attached. If the re-check clears, the loaves get promoted to the front shelf as they would have on any other day. If the re-check does not clear, the loaves go a different route — back into the hold tray, into the failure bin, whatever the bakery's procedure says next.

That is what `Repair` does to a deposit. The bank takes the slot from `Quarantined` back to `Candidate`, attributes the move to a repairing agent and bubble, and records the field that the repair targets. The bank does not *fix* the deposit; it does not adjudicate whether the repair is sufficient. It records the structural fact that a repair was attempted and returns the deposit to the queue where re-promotion can be considered.

---

## What the move actually does

In the kernel, `Step.repair` carries an agent `a`, a bubble `B`, a slot index `d_idx`, a field `f`, and a single bank-side hypothesis: `h_quarantined : isQuarantined s d_idx`. The successor state is `{ s with ledger := updateDepositStatus s.ledger d_idx .Candidate }` — the ledger is the same except the deposit at that slot now reads `Candidate`. The deposit's content is not modified by the kernel-level step. Other deposits' statuses are untouched. The clock does not move. The bubbles field does not change. The agents' ladder map is the same.

The `f : Field` argument is what the action label carries about *what* the repair was directed at — which header field, which content piece, which aspect of the deposit the repairing agent claims to have addressed. The kernel does not interpret `f`. It records that the repair was directed at this field; the deployment's surrounding workflow is what knows what that field means and whether the repair plausibly addressed it.

The constructor's own comment is explicit: *the bank does not evaluate or fix the deposit content; it records that a repair action was taken and sets the slot back to Candidate, requiring the deposit to pass through revalidation (re-promotion) before it can be relied upon again*. The architecture does not let a quarantined deposit re-enter circulation by being repaired; it lets it re-enter the *queue* where re-circulation is decided. That is the whole point.

---

## Why quarantined

The reason `isQuarantined` is the precondition is the same shape as every other lifecycle precondition: the recorded event is *return-to-queue of something that was pulled from circulation*. A `Candidate` is already in the queue; *repairing* a candidate would not be a coherent recorded event because there is nothing to return it to that it is not already in. A `Deposited` deposit has not been pulled; *repairing* it would skip the quarantine step that the architecture takes seriously enough to make a precondition. A `Forgotten` deposit is operationally void. A `Revoked` deposit is closed as an epistemic failure and cannot use the structured `Repair` path; if a deployment wants to replace that slot anyway, it must use the heavier `Update` maintenance path and pay the revision-trace cost.

`Repair` is reserved for the recordable transition `Quarantined → Candidate`, because that is the transition the bakery has to write down: *a thing that was in the hold tray is back in the cooling-rack queue, and here is the field the repair was directed at*.

---

## The forced revalidation

The architectural weight of `Repair` is in where it puts the deposit. Sending it back to `Candidate` rather than directly to `Deposited` is not a procedural inconvenience; it is the architecture refusing to let the bank treat *quarantined-then-repaired* as equivalent to *was always live*. A repaired deposit must pass through `Promote` — with whatever validation the surrounding workflow has wired into the gap between `Candidate` and `Deposited` — before any agent can withdraw against it again. The bakery does not put the loaves straight back on the front shelf because the front-shelf check is the bakery's *commitment* about what is on the shelf, and it has to commit again from scratch after a complaint, not from where it was before.

This is why the parent file singles out `Repair` and `Promote` as the second half of the quarantine-and-recovery story. `Challenge` opens the question; the deposit lands in `Quarantined`; either `Repair` then `Promote` returns it to circulation through the queue, or `Revoke` closes it out. There is no architectural shortcut from `Quarantined` directly back to `Deposited`. The architecture takes seriously that a deposit that was once pulled is, until it has been re-cleared, not the same kind of thing as a deposit that was never pulled.

---

## What `Repair` does not do

`Repair` does not modify the deposit's content. The headers, the proposition, the provenance, the standard, the error model, the temporal window — none of these are rewritten by the kernel-level step. If the deployment's repair workflow involves changing what the deposit *says* (replacing the substrate of the claim, correcting a misattributed source, installing a tighter standard), that change is recorded by the lifecycle's *other* mechanism for content overwrite — `Update`, which carries `isRevision = true` and opts the trace out of revision-free guarantees. `Repair` is the cleaner path: the deposit's content stays as it was, and the architecture commits only that *some repair action was taken, directed at this field*, before sending the slot back to the queue.

`Repair` also does not adjudicate whether the repair was good. It does not decide whether `Promote` will fire next, or when, or with what surrounding validation. It does not prevent the candidate from being inspected, objected to, revised in the surrounding workflow, or refused promotion. The kernel's commitment is narrow: a quarantined slot is now a candidate slot, and the agent and field of the repair are on the trace.

---

## How the trace reads later

A trace reader scans for `Action.Repair _ _ _ _` entries to find recorded repairs. The action label names the repairing agent, the bubble, the slot, and the field. The kernel guarantees, by the `Step.repair` constructor precondition, that the slot was in `Quarantined` status when the transition fired. After `Repair`, the slot is `Candidate`. From there, the kernel-level lifecycle does not allow another `Challenge` immediately, because `Challenge` requires `Deposited` status. The candidate may later be `Promote`d back to `Deposited`, `Forget`ten for capacity/deletion, or left in the candidate queue while the surrounding validation workflow continues. If it is promoted and then contested again, a new `Challenge` can fire later from `Deposited`. The trace reader can read the full history of pull, repair, and re-clearance off the action sequence at the slot.

The kernel does not check that the repair's `f` actually corresponds to whatever was wrong about the deposit at the moment of the challenge. The slip filed at challenge time and the field named at repair time are two pieces of evidence on the trace; whether they cohere is a deployment-level interpretation, the same way the slip's grounds are a deployment-level interpretation. The kernel ships the structural record and lets the surrounding workflow do the meaning-making.

---

## Takeaway

`Repair` is the recordable return of a quarantined deposit to the candidate queue. The bank-side precondition is the single fact that the deposit is in `Quarantined` status; the successor state takes that one slot to `Candidate`; the field the repair targeted is on the action label. The deposit's content is not modified, and the deposit cannot become live again without passing through `Promote`.

The architecture's commitment is structural: the path back into circulation runs through revalidation, not around it. The next file in the series is `Revoke`, the other half of the quarantine outcome — the move that closes a quarantined deposit out of circulation and keeps the institutional judgment on the trace.

---

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [← Register](register.md) · [← Withdraw](withdraw.md) · [← Challenge](challenge.md) · [← Tick](tick.md) · [Revoke →](revoke.md)*
