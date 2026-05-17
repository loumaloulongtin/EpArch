# The Bakery Story

*[← Temporal Validity](../deposits/headers/temporal-validity.md) · [Submit →](steps/submit.md)*

---

## In this series

- [The Bakery Story](lifecycle.md) — what the bank actually *does*; the LTS as the operational engine *(you are here)*
- *steps/* — one file per major step (deposit, challenge, quarantine, repair, revoke, forget) walked through one developing case
- *safety.md* — what the lifecycle is provably unable to do by accident
- *under-attack.md* — the engine under coordinated pressure

---

## The morning rush

A bakery opens at six. Bread comes out of the oven, gets a label that says what it is and when it was baked, and goes onto the front shelves. By eight there is a queue. By nine someone returns a loaf saying it tasted off; the manager pulls every loaf from the same batch off the shelf and into the back. Two of them get re-baked into croutons after the supplier confirms the flour was fine; the rest go into the failure bin with the incident record kept on file. By closing time, an entry on the spreadsheet for a loaf from a quiet Tuesday three weeks ago gets its content wiped and the loaf, if any of it physically remained, goes into the dumpster outside. As far as the bakery is concerned, that loaf no longer exists.

That is one bakery's day, and beat for beat it is the bank's:

- Bread coming out of the oven onto the shelf — *submit* then *promote*.
- Pre-cleared bread arriving from the central kitchen and going straight on the shelves — *register*.
- The label on the loaf — the deposit's headers.
- A sale at the counter — *withdraw*.
- A complaint — *challenge*.
- Pulling the batch — *quarantine*.
- Re-baking the salvageable loaves — *repair*.
- Binning the bad ones with the incident on file — *revoke*.
- Wiping the old spreadsheet row and dumpstering whatever remained — *forget*.
- The wall clock being read and the new time written down — *tick*.
- Wholesale rewriting a slot — *that loaf was actually a substitute from elsewhere* — *update*.

Those ten are the constructors of `Action`, and they are *all* the recordable events the bank has. The state between events is small: the ledger of deposits with their current statuses, the collection of bubbles, the clock. Nothing else.

The constructor list is what the bank commits to *writing onto the trace* — not a list of what agents are permitted to do. The spreadsheet is visible: anyone can read a label, talk about a candidate, decide they don't like a batch and tell the manager not to promote it. None of those activities change the spreadsheet, so none of them appear as constructors. There is no `Inspect`, no `Review`, no `RaiseConcernAboutCandidate`. They happen in the surrounding workflow, in full view of the same ledger, without the bank needing to commit anything.

---

## Why each event has a precondition

The bakery cannot bin a loaf it never pulled, cannot repair a loaf it already binned, cannot record the sale of bread that is not on the shelf. The order is not arbitrary: each event's *meaning* depends on the state it presupposes. *Binning* is a thing that happens to a loaf that has been pulled; the same word applied to a front-shelf loaf would not be the same event.

The kernel ships the lifecycle the same way: each constructor's precondition is part of the relation, not advice attached to it. Try to record a withdrawal against a deposit that is not in `Deposited` status and the relation simply does not connect to a successor state. Try to record a repair against something that was never quarantined and the same. This is what makes the lifecycle an *engine* rather than a list of names: a graph of states with arrows that refuse to fire from the wrong starting state. When the bank does the morning's work, it is walking around inside that graph.

The two-step from the bank file lives here. Agent decision and bank decision are different decisions; the bank's decision is the precondition check on whether the requested event is a coherent edit. The customer chooses to bring the bread back; the manager checks whether the loaf is in a state where pulling it is a coherent recorded event, and records the pull only if it is. The lifecycle's arrows are where the bank's half of the two-step actually lives.

---

## What withdrawal looks like as a worked move

Pick one of the ten and follow it through. *Withdrawal* is a good one to walk because it is the move every other piece of the architecture is shaped around: agents rely on the bank by withdrawing.

A customer comes to the counter and points at a loaf. *That one.* The staff member glances at the shelf to confirm: the loaf is actually on the front shelf right now — it has not been pulled, not been binned, not been sitting in the back. That single check is what the bank is in charge of. The loaf may have a *reserved-for* tag on it, naming who is allowed to walk out with it; it may have a best-before stamp that has expired. Both of those are properties of the loaf itself, sitting right there on the shelf as labels. But whether *this* customer is on the reservation, and whether *today* is past the best-before — those are reads the counter policy performs against the labels. The shelf glance does not perform them.

The kernel's `Step.withdraw` rule is deliberately thin in the same way. The only bank-side precondition is `isDeposited s d_idx` — the deposit at that slot must currently be in `Deposited` status. The rule's comment says it explicitly: *authorization is an agent-level concern external to the bank's LTS*. A successful withdrawal records that the agent relied on a live bank entry and leaves the system state unchanged.

The ACL and temporal-validity headers really are on the deposit — the *reserved-for* tag and the *best-before* stamp on the loaf. A deployment that wants those gates enforced wraps `Step.withdraw` with a policy that reads the headers and refuses the withdrawal when the requesting agent is not on the ACL or the validity window has passed. That wrapping is where the bakery's *we don't sell that loaf to that customer today* lives. It is not a precondition of the kernel-level step, and the withdrawal-gate theorem the kernel ships extracts only what `Step.withdraw` actually requires from the constructor that fired — deposited status, nothing more.

That is still the pattern of how the lifecycle gives the architecture its leverage. The moves are concrete transitions; anything a downstream theorem wants to say about *what must have been true for this to happen* it can say by reading the preconditions of whichever move actually fired. With withdrawal, what gets read back is a single fact: the deposit was live. Stronger gates — ACL admission, temporal validity — are stronger reliance policies a deployment may layer on top by reading the headers the deposit already carries; at the kernel level the bank's job at withdrawal is to confirm the loaf is on the shelf.

---

## When the move changes what is recorded

Some of the moves change the status of an existing deposit. Some add a new deposit. One of them — `Update` — wholesale overwrites a slot's contents.

The first kind is the bulk of the lifecycle. Promote moves a deposit from `Candidate` to `Deposited`; quarantine moves it from `Deposited` to `Quarantined`; revoke moves whatever-it-was to `Revoked` and keeps the content readable so the institutional judgment stays on file. This is the bakery moving a loaf from the shelf to the back to the failure bin, with the loaf's slot in the spreadsheet keeping the same number throughout and the record of *what we judged and why* still readable.

Forget is in this same family on the surface — the slot's number stays put — and categorically different underneath. Architecturally, `Forget` is permanent deletion: the bank has no further operational use for the deposit's content, no agent should rely on it, no future move can update through it, and the deposit cannot be forgotten again. The reason the slot's record is not physically removed from the Lean ledger is that the ledger is implemented as an ordered list and other references must not shift; what gets installed at the slot is a `.Forgotten` tombstone whose role is index stability, not survival of the deposit. An agent looking up that slot does not find an operational deposit-with-Forgotten-status to reason with; they find the marker the architecture leaves behind to say *the content here has been voided*. The loaf has been put in the dumpster outside; nothing operational of it remains in the bakery. Revoked means the bank judged the deposit bad and kept the record readable as an epistemic closure; Forgotten means the bank deleted it from operational memory and left a tombstone only because the ledger would break without one.

The second kind — submit and register — adds new deposits. A new entry comes onto the ledger. The new entry has its own slot number. Subsequent moves can act on it.

The third kind, `Update`, is special and the kernel singles it out. It wholesale overwrites a slot's contents — *that loaf I labelled as our sourdough, actually it's a substitute from the central kitchen, here is what it really is*. The kernel marks `Update` as a *revision* (the action carries `isRevision = true`) rather than as an addition or a status change. The reason this matters is that the lifecycle's safety guarantees come in two flavours: ones that hold over any trace, and ones that hold only over *revision-free* traces. Using `Update` opts the trace out of the second flavour. The bank still allows the move, but it costs you the stronger guarantees, and the architecture insists on naming this so a deployment cannot quietly use `Update` and keep the strong guarantees too. The next file in the cluster, *safety*, is about what those two flavours of guarantee are.

---

## What does not change

Each step is a small, local edit; what it does *not* touch is as architecturally important as what it does. Across every one of the ten moves, three things in the system are required to stay where they are:

- **The ladder map.** Who is at what stage on which claim. Untouched by any bank step.
- **Other deposits' statuses.** A move on slot 7 does not change the status of the deposit at slot 8.
- **The clock.** Advances only on `Tick`. No other move moves it.

The ladder map is the bank/ladder independence the agent cluster covered, made operational here: every step in the kernel carries with it a proof, `step_preserves_ladder_map`, that the ladder map after the step equals the ladder map before. The agent cluster argued the architectural reason; the lifecycle is where the architecture *enforces* it.

The other-deposits invariant sounds obvious until you ask what would happen without it. Without it, a quarantine in one bubble could ripple to every bubble that imports the deposit; a revoke could leak across scope. With it, every move stays inside its scope and the bubbles stay separate even when they share material. This is *scope irrelevance* in its operational form, and the safety file develops it.

The clock invariant sounds trivial too, but it means the bank can never make time go faster or slower by what it does to deposits, and a temporal-validity check at one moment refers to the same moment that any other temporal-validity check at the same step would have referred to.

These *invariants the steps preserve* are what the architecture has the right to call provable safety. A deployment that lifts the lifecycle and changes any of them — say, a deployment where promote also bumps the clock — has built a different thing, and the kernel's safety theorems do not transfer to it. The lifecycle is *the* engine the safety theorems are theorems about.

---

## Takeaway

The lifecycle is what the bank records: ten named moves over a small state — ledger, bubbles, clock, ladder map — with preconditions baked into the relation. Theorems like the withdrawal-gate result do their work by reading those preconditions back out: *if* the move fired, *then* its precondition held. The leverage is structural.

What the lifecycle preserves across every move — the ladder map, scope locality, the clock advancing only on `Tick` — is the *safety* file. What goes wrong under coordinated pressure is *under-attack*. The *steps* cluster walks each of the ten moves through one developing case, so the engine can be felt one move at a time.

---

*[← Temporal Validity](../deposits/headers/temporal-validity.md) · [Submit →](steps/submit.md)*
