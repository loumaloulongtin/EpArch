# The Returned Loaf Story

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [← Register](register.md) · [← Withdraw](withdraw.md) · [Tick →](tick.md)*

---

## In this series

- [The Cooling Rack Story](submit.md) — `Submit`, the standard entry path
- [The Central Kitchen Delivery Story](register.md) — `Register`, the vouched-for entry path
- [The Front Counter Story](withdraw.md) — `Withdraw`, the recorded reliance event
- [The Returned Loaf Story](challenge.md) — `Challenge`, the recorded act of pulling a live entry out of circulation *(you are here)*
- *(more step files follow: quarantine, repair, revoke, promote, forget, update)*

---

## Quarter past nine

A customer comes back into the shop with a paper bag. The loaf inside is half-eaten and the customer is unhappy: *this tasted off, sour in a wrong way, my partner felt sick, here's the receipt, it was from this morning*. The staff member reads the receipt, identifies the batch — *sourdough, S-04-26* — and walks to the front shelf. She pulls every remaining loaf from S-04-26 off the shelf and into a tray marked *hold — do not sell*. The day-book gets a new entry: *9:14, complaint raised against S-04-26 by counter customer, batch pulled to hold pending review, complaint slip filed*.

The complaint slip is not just the word *bad*. It carries the customer's account, the receipt, the staff member's note about which loaves were on the shelf when the complaint came in, and the time. The slip is filed, paper-clipped to the day-book entry. Whatever happens next — the batch goes back into circulation after a check, or it goes to the failure bin with the slip still attached — the slip is the structured record of *why we pulled this batch*.

That is what `Challenge` does to a deposit. The bank takes the slot from `Deposited` to `Quarantined`, attributes the move to the challenging agent and bubble, and records a structured challenge object alongside it. The challenge object is the slip. The status change is the move from front shelf to hold tray. The architecture commits, in the same step, both to *what changed in the ledger* and to *what reasons were filed at the moment of the change*.

---

## What the move actually does

In the kernel, `Step.challenge` carries an agent `a`, a bubble `B`, a structured challenge object `c : EpArch.Challenge PropLike Reason Evidence`, a slot index `d_idx`, and a single bank-side hypothesis: `h_deposited : isDeposited s d_idx`. The successor state is `{ s with ledger := updateDepositStatus s.ledger d_idx .Quarantined }` — the same ledger except the deposit at that slot now reads `Quarantined`. Other deposits keep their status. Bubbles do not change. The clock does not move. The agents' ladder map is untouched. What moves is the one slot, and what is committed to the trace is the `Action.Challenge a B c` entry that accompanies the move.

The challenge object `c` is structured: it carries reasons and evidence in fields the deployment is free to populate. The kernel does not verify those fields. It does not adjudicate whether the reasons are good reasons or whether the evidence justifies the move. It records that the agent filed *this* slip at *this* slot at *this* moment, and it makes the status change at the same step so the slip and the status change are paired in the trace forever.

---

## Why deposited

The reason `isDeposited` is the precondition is the same shape as the withdrawal one. *Challenge* is the recorded act of pulling a live entry out of circulation. A `Candidate` is not in circulation — there is nothing to pull from a shelf the deposit is not yet on. A `Quarantined` deposit is already pulled; pulling it again would be a category error rather than a refused permission. A `Revoked` or `Forgotten` deposit is gone. *Pulling a live entry out of circulation* is defined to be a thing that happens against a deposit currently in `Deposited`, and the precondition is what makes the recorded event coherent.

This is also why pre-promotion disagreement is not `Challenge`. A staff member who looks at a candidate loaf on the cooling rack and says *that one's underbaked, don't promote it* is doing real work, and the bakery has procedures for it — refusing the promotion, sending the loaf back to be re-baked, discarding it before it ever reaches the front shelf. None of those are *pulling a live entry off the front shelf*, because the loaf was never on the front shelf. Disagreement at the candidate stage happens in the surrounding validation workflow and resolves through whether `Promote` ever fires, not through `Challenge`. `Challenge` is reserved for the recordable transition `Deposited → Quarantined`, because that is the transition the bakery has to write down: *a thing that was in circulation is no longer in circulation, and here is the slip*.

---

## What `Challenge` does not decide

Quarantine is not the end of the loaf's story; it is the move that opens the question. The same constructor does not decide whether the batch comes back to the shelf or goes to the failure bin. Those are subsequent recordable events: `Repair` is the move from `Quarantined` back to `Candidate` for re-check, and `Revoke` is the move from `Quarantined` to `Revoked` with the institutional judgment kept on file. The challenge fires; the deposit lands in quarantine; what happens to it from there is another step in the lifecycle, with its own precondition and its own commitment.

The kernel also does not, at this step, verify the structured challenge object's grounds. The slip is filed; whether the reasons inside the slip are sufficient is a deployment-level interpretation, possibly drawing on bank-side data, possibly on agent-side reasoning, often on both. What the kernel guarantees is that the slip and the status change are paired in the trace, so any later adjudication has the *whole* recorded event — agent, bubble, slip, slot, status change — to work from.

The kernel also does not check that the challenge object's `P` matches the deposit's `P` at the challenged slot. In a well-run deployment, the validation or logging layer should ensure that correspondence. At the kernel level, the guarantee is narrower: a structured challenge object was recorded with a challenge transition, and the selected slot was live when it was moved to `Quarantined`.

---

## How the trace reads later

Suppose someone asks, two weeks on: *what got pulled, when, by whom, on what grounds*. A trace reader scans for `Action.Challenge _ _ _` entries to find recorded challenge events. The action label names the challenging agent, the bubble, and the structured challenge object. The slot index belongs to the corresponding `Step.challenge` transition evidence — or, in an implementation log, to the recorded state transition / state diff. The action label alone does not carry `d_idx`. The kernel guarantees, by the `Step.challenge` constructor precondition, that the selected slot was in `Deposited` status when the transition fired, so each recorded challenge corresponds to a live entry that was pulled out of circulation at that moment. The slip and the pull are inseparable in the trace.

What happened *after* the quarantine — repair back to candidate, revoke to the failure bin, the deposit sitting in quarantine until the day rolls over — is read off the subsequent events in the trace, each one with its own precondition that the kernel will read back the same way.

---

## Takeaway

`Challenge` is the recordable act of pulling a live entry out of circulation. The bank-side precondition is the single fact that the deposit is in `Deposited` status; the successor state takes that one slot to `Quarantined`; the structured challenge object is filed in the same step, paired forever in the trace with the status change it accompanies. The kernel does not adjudicate the challenge's grounds and does not decide what happens next.

What happens next — quarantine sitting open, repair back into the candidate queue, revoke to the failure bin — is the next group of moves in the lifecycle, and the next files in the series.

---

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [← Register](register.md) · [← Withdraw](withdraw.md) · [Tick →](tick.md)*
