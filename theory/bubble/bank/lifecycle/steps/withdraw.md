# The Front Counter Story

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [← Register](register.md) · [Challenge →](challenge.md)*

---

## In this series

- [The Cooling Rack Story](submit.md) — `Submit`, the standard entry path: a deposit enters the system as a `Candidate`
- [The Central Kitchen Delivery Story](register.md) — `Register`, the vouched-for entry path: a deposit enters straight as `Deposited`
- [The Front Counter Story](withdraw.md) — `Withdraw`, the recorded reliance event: an agent leans on a live entry *(you are here)*
- *(more step files follow: challenge, quarantine, repair, revoke, promote, forget, update)*

---

## The morning rush

Quarter past seven. The first wave of customers is in. A regular comes to the counter, points at the basket on the front shelf, and says *one of those, please*. The staff member glances at the basket — it is on the front shelf, not in the back, not in the failure bin, not crossed off the morning's list — and hands one over. The customer pays at the till, walks out with the loaf, and the day-book at the counter gets a tick: *7:14, sourdough sold, batch S-04-26*. That tick is what the bakery cares about, later, when someone asks *did anyone actually buy from this batch this morning*. The tick says yes, and names the batch, and names the moment.

The glance the staff member made was small. It was *is the loaf on the front shelf right now*. It was not *is the customer entitled to be in the shop*; the door, the till, the customer-side policy handle that. It was not *is the loaf still within its best-before*; the labels carry the times and the customer-facing display rules pull anything past its time off the shelf before it gets to this point. The glance was the one thing the bakery, as a recording institution, has to commit to: the loaf was on the shelf when the reliance happened.

That is what `Withdraw` does to a deposit. The bank records the event *agent `a`, in bubble `B`, relied on the deposit at slot `d_idx`*. The bank-side check is the glance: the deposit at that slot is currently in `Deposited` status — it is on the front shelf, not pulled, not binned, not voided. Beyond that, the kernel records the reliance and leaves the system state exactly where it was.

---

## What the move actually does

In the kernel, `Step.withdraw` carries an agent `a`, a bubble `B`, a slot index `d_idx`, and a single bank-side hypothesis: `h_deposited : isDeposited s d_idx`. The successor state is `s` itself — the same state the move started in. No status changes. No new deposit. The clock does not move. The bubbles field does not change. The ledger is the same ledger. What changes is what the trace says happened: the trace now contains an `Action.Withdraw a B d_idx` entry at this point, and downstream theorems about reliance can read that entry back.

The constructor's own comment says it explicitly — *authorization is an agent-level concern external to the bank's LTS*. ACL admission, temporal validity, agent eligibility, bubble-membership policy: these are real architectural questions the deposit's headers and a deployment's surrounding policy are equipped to answer. They are not preconditions of the kernel-level step. The kernel's job at withdrawal is to glance at the shelf and confirm the loaf is on it, and to commit the reliance to the trace if it is.

This is what the withdrawal-gate theorem in the kernel reads back. *If* `Step.withdraw` fired against `s` at slot `d_idx`, *then* `isDeposited s d_idx` held. There is one fact to extract, because the constructor demands one fact. A deployment that wants to enforce more — *and the headers were temporally valid at* `s.clock`, *and the agent was on the deposit's ACL* — layers that policy on top, around the kernel, in the workflow that decides whether to invoke `Step.withdraw` in the first place. The kernel does not pretend to have done that work.

---

## Why deposited

The reason `isDeposited` is the precondition, and not something weaker, is the same reason the bakery's till tick refers to *a loaf on the front shelf*. The recorded event is *reliance on a live entry*. A `Candidate` is not yet a live entry — the bank has not committed to it as something to lean on. A `Quarantined` deposit has been pulled from circulation; the bakery is no longer letting customers buy from it. A `Revoked` deposit is the bank's standing record that *we judged this bad and closed the matter* — readable for downstream reasoning, but not a thing in circulation. A `Forgotten` deposit is gone from operational memory entirely; the slot carries a tombstone for index stability and nothing more. None of those are loaves a customer can buy from the front shelf, so none of them are slots a withdrawal can coherently be recorded against. *Withdrawal as a recorded reliance event* is defined to be the bank's commitment that, at this moment, this slot was a thing in circulation, and an agent leant on it. The precondition is what makes that commitment coherent.

The parent file makes the larger point: the LTS is the catalogue of events the bank commits to writing onto the trace, not the menu of activities the world is permitted to do. Reading the headers, glancing at a candidate, weighing in on whether a candidate should be promoted, asking the manager about a batch — none of those are recorded events; the bank's ledger does not change when they happen. *Withdrawal is the recording channel for reliance.* It is not the access channel and it is not the consultation channel. There is no kernel constructor for *agent looked at a deposit*; the bank does not need one, because looking does not change what the bank has committed to.

---

## How the trace reads later

Suppose, three weeks later, someone asks: *did any agent actually rely on the deposit at slot 17 between Tuesday and Thursday*. The answer is read off the trace: scan the relevant portion of the trace for an entry of the form `Action.Withdraw _ _ 17`. If one exists, the kernel guarantees — by the withdrawal-gate theorem — that at the state the constructor fired, slot 17 was in `Deposited` status. The trace is a record of *what was leant on, by whom, in which bubble, against a live entry*, and the kernel ships the receipt that the live-entry condition held at the moment of the recorded reliance.

Stronger questions — *was the deposit's temporal validity intact at* `s.clock`, *was the agent on the ACL* — are answered by reading the deposit's headers and the deployment's surrounding policy alongside the trace. Those answers are available; they just are not what the kernel-level step's hypothesis demands. The kernel keeps its own promise small and exact: *Deposited at the moment of recording*. The deployment's reliance policy keeps its own promises stacked on top.

---

## Takeaway

`Withdraw` is the recordable reliance event. The bank-side precondition is the single fact that the deposit at the slot is in `Deposited` status — the loaf is on the front shelf at the moment of the glance. The successor state is unchanged; the event exists because the trace includes the `Action.Withdraw a B d_idx` label, attributed to an agent and a bubble, against a slot the kernel can later guarantee was live.

The next file in the series is the other half of the live-entry story: what happens when a customer brings a loaf back, and a live entry has to be pulled out of circulation. That is `Challenge`.

---

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [← Register](register.md) · [Challenge →](challenge.md)*
