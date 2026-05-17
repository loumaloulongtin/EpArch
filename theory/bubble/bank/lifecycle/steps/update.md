# The Substitute-Loaf Story

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [← Register](register.md) · [← Withdraw](withdraw.md) · [← Challenge](challenge.md) · [← Tick](tick.md) · [← Repair](repair.md) · [← Revoke](revoke.md) · [← Promote](promote.md) · [← Forget](forget.md) · [Safety →](../safety.md)*

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
- [The Dumpster Story](forget.md) — `Forget`, the agent-invoked deletion of a slot from operational memory
- [The Substitute-Loaf Story](update.md) — `Update`, the agent-invoked wholesale overwrite of a slot's deposit *(you are here)*

---

## The substitute that came in mid-morning

Mid-morning. The labels on the front shelf say *sourdough, batch S-04-26, baked 05:12*. But one of the trays — the one in the corner — is not actually S-04-26. The head baker, in a small rush after the morning's complaint, accepted a substitute tray from the central kitchen to cover the gap S-04-26 left when half of it went to the hold tray. The substitute is a different bake, with a different batch number, a different time of bake, and a different provenance. The label on the front-shelf tray is wrong. The day-book row for that slot says S-04-26, and it should say something else entirely.

The bakery does not pretend nothing happened. It does not just edit the row's batch field as though the original entry had said the new thing all along. It records, plainly, that *the row at this slot has been overwritten*: *11:17, slot 12 substituted from central kitchen tray K-04-26-a, replaces previous S-04-26 entry, manager's call*. The row's content, after the overwrite, says what the substitute tray actually is. The day-book carries the overwrite as a separate event, and any reader looking at the row later sees both the new content and the trace of the overwrite-event that put it there.

That is what `Update` does to a deposit. The bank installs a new deposit `d_new` at the slot, in entirety: new headers, new proposition, new provenance, new standard, new error model, new temporal window, *new status*. The action is on the trace as an `Action.Update` event with the new deposit attached. The institutional commitment is heavy: the bank no longer claims that what is at the slot is what was originally submitted; the bank claims that what is at the slot is what was *put there by this overwrite event*, with full attribution to the agent and bubble that did the overwriting.

---

## What the move actually does

In the kernel, `Step.update` carries an agent `a`, a bubble `B`, a slot index `d_idx`, the new deposit `d_new`, the existing deposit `d_old`, a hypothesis `h_exists` that `s.ledger.get? d_idx = some d_old`, and a hypothesis `h_not_forgotten` that `d_old.status ≠ .Forgotten`. The successor state is `{ s with ledger := modifyAt s.ledger d_idx (fun _ => d_new) }` — the deposit at that slot is replaced wholesale by `d_new`. Other deposits are untouched. The clock does not move. The bubbles field does not change. The agents' ladder map is the same.

`Update` is the only lifecycle move that uses `modifyAt` to install a fresh deposit rather than `updateDepositStatus` to flip a status flag. Every other slot-editing lifecycle move preserves the deposit record and changes only its status. `Update` is different: it replaces the deposit record itself. *Anything* in `d_new` may differ from `d_old`. The new status field may be `Candidate`, `Deposited`, `Quarantined`, `Revoked`, or even `Forgotten`. The new headers may have a different temporal window, a different ACL, a different provenance. The new proposition may be a different proposition. The slot's *identity* is the index; what occupies the index, after `Update`, is whatever the agent supplied.

The two preconditions are minimal. There has to be a deposit at the slot — you cannot update a slot that was never written to. The existing deposit cannot be the `.Forgotten` tombstone — once a slot has been forgotten, it is gone from operational memory and cannot be revived by overwriting the tombstone. Every other status is updatable: `Candidate`, `Deposited`, `Quarantined`, `Revoked` deposits can all be replaced. The constructor's own comment is explicit: *all other status semantics are the agent's responsibility*. The kernel does the slot-existence and tombstone-boundary checks and stops there.

---

## Update is a revision action

The cost the architecture extracts for the wholesale-overwrite power is on the trace. `Update` carries `Action.isRevision = true`. So do `Challenge` and `Revoke`. A trace that contains any of these is a *revision trace*, and the lifecycle's safety guarantees come in two layers: ones that hold over any trace, and ones that hold only over *revision-free* traces. Using `Update` opts the trace out of the second layer. The structured `Challenge → Repair → Promote` route also costs the second layer, because `Challenge` is itself a revision action.

What the architecture preserves is the visibility of the cost. A deployment cannot quietly use `Update` and keep the strong guarantees. The trace records every `Update` as such, the `isRevision` predicate is checkable, and any theorem that quantifies over revision-free traces has the right to refuse to apply to a trace that contains an `Update`. The safety file develops what those two layers of guarantee actually are; for the present file, the relevant fact is that `Update` is one of the moves that lands a trace in the revision class.

The structured route — `Challenge`, then `Repair` if recoverable or `Revoke` if not, then `Promote` for return to circulation — is also a revision route, but it is a *transparent* revision route: every status change is recorded as its own event with its own attribution, and the trace reader can walk the slot's history move by move. `Update` is the *opaque* revision route: the slot's previous content is replaced in one stroke, and what survives on the trace is the `Action.Update` event with `d_new` and the agent's attribution. A reader who wants to know what was at the slot before the update has to walk back through the trace to find earlier moves at the same slot; the post-update ledger does not carry the previous content.

---

## What `Update` does and does not adjudicate

The kernel does not validate the new deposit. It does not check that the new headers are well-formed, that the new proposition is consistent with anything else in the ledger, that the new status is *appropriate* (a deployment may use `Update` to install a `.Deposited` deposit without going through `Promote`; the kernel allows it), or that the agent had any business overwriting the slot at all. The constructor's comment frames it directly: *all other status semantics are the agent's responsibility*. The kernel enforces only the slot-existence and tombstone-boundary preconditions; the rest is the deployment's problem, and the trace's `isRevision = true` flag is the architecture's compensation for the kernel's narrow check.

The constructor's comment also distinguishes `Update` from `Repair` directly. `Repair` is reactive: it requires `isQuarantined` and only changes status, leaving content unchanged. `Update` is proactive and wholesale: it requires only slot existence and tombstone-boundary, and it replaces the entire deposit. A deployment that wants the structured, transparent path uses `Repair`; a deployment that needs the wholesale-overwrite power, and is willing to pay the revision-trace cost, uses `Update`. The architecture's intent is that the structured path is the default and `Update` is the escape hatch.

`Update` does not propagate to other slots, other bubbles, or the ladder map. A wholesale overwrite at slot 47 does not touch slot 48; an update in one bubble does not touch the same content in another bubble; the agents' ladder positions are untouched. The architecture's general invariants on what a step preserves apply to `Update` as they apply to every other step.

---

## How the trace reads later

A trace reader scans for `Action.Update _ _ _ _` entries to find recorded wholesale overwrites. The action label names the updating agent, the bubble, the slot, and the new deposit `d_new` itself — the new deposit is part of the action label, not just part of the post-state. The kernel guarantees, by the `Step.update` constructor preconditions, that some non-Forgotten deposit existed at the slot at the moment of the update. The action label carries `d_new`, not `d_old`. A reader who wants to know what was overwritten must look at the pre-state or the `Step.update` constructor evidence directly, or reconstruct the slot's prior content from earlier trace events or the trace's initial state. The post-update ledger carries only `d_new`.

A reader using `Action.isRevision` can mark every `Update`-bearing trace as a revision trace, alongside any trace that contains a `Challenge` or `Revoke`. Revision-free guarantees do not apply to such traces by hypothesis; the reader gets the broader trace-class guarantees and pays the architectural visibility cost the `Update` event itself carries.

A reader who wants to walk the full content history of a slot reads off the trace: the `Submit` or `Register` (or earlier `Update`) that installed an entry; whatever status-flipping moves followed; any `Update` events that wholesale-overwrote the slot, with each overwrite's `d_new` available on the action label; and any final `Forget` that voided the slot. The lifecycle is built to keep that walk possible, even when the moves involve heavy overwriting.

---

## Takeaway

`Update` is the recordable agent-invoked wholesale overwrite of a slot's deposit. The bank-side preconditions are that a deposit currently exists at the slot and is not already forgotten; the successor state replaces the slot's deposit in entirety with `d_new`; the new deposit may differ from the old in any field, including status. `Update` is the only lifecycle move that installs a fresh deposit rather than flipping a status flag, and it pays for that power by carrying `Action.isRevision = true`, which opts its trace out of revision-free guarantees.

`Update` and `Forget` together complete the lifecycle's escape-hatch and end-of-life mechanics: `Update` wholesale-overwrites, `Forget` operationally voids. The structured central spine — `Submit` / `Register` for entry, `Promote` for crossing to live, `Challenge` / `Repair` / `Revoke` for the pull-and-resolve cycle, `Withdraw` for reliance, `Tick` for time — provides the transparent lifecycle path; the safety layer then separates guarantees that hold for all traces from those that require revision-free traces. `Update` and `Forget` handle the cases the structured spine is not built to cover.

The next layer in the cluster is *safety*: what the lifecycle is provably unable to do by accident, with both flavours of guarantee — the ones that hold over any trace and the ones that hold only over revision-free traces — laid out together.

---

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [← Register](register.md) · [← Withdraw](withdraw.md) · [← Challenge](challenge.md) · [← Tick](tick.md) · [← Repair](repair.md) · [← Revoke](revoke.md) · [← Promote](promote.md) · [← Forget](forget.md) · [Safety →](../safety.md)*
