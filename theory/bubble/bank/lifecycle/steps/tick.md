# The Wall Clock Story

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [← Register](register.md) · [← Withdraw](withdraw.md) · [← Challenge](challenge.md) · [Repair →](repair.md)*

---

## In this series

- [The Cooling Rack Story](submit.md) — `Submit`, the standard entry path
- [The Central Kitchen Delivery Story](register.md) — `Register`, the vouched-for entry path
- [The Front Counter Story](withdraw.md) — `Withdraw`, the recorded reliance event
- [The Returned Loaf Story](challenge.md) — `Challenge`, the recorded act of pulling a live entry out of circulation
- [The Wall Clock Story](tick.md) — `Tick`, the only event that moves the bank's clock *(you are here)*
- *(more step files follow: repair, quarantine-handling, revoke, promote, forget, update)*

---

## Half past nine

The bakery has a wall clock above the counter. Until someone walks over and confirms a new time onto the day-book — *9:30, second tray of croissants out, sourdough still selling, batch S-04-26 in the hold tray* — the day-book's *current time* line says whatever it last said. The loaves do not change as the wall clock ticks; the croissants do not appear; the hold tray does not empty itself. Time, *as the bakery records it*, is a thing the bakery commits to writing down at intervals of its own choosing.

When the staff member writes the new time, two things are true. The new time cannot be earlier than the last one written — *9:30, then 9:15* would be a clerical error, not a time correction. And nothing else changes in the day-book at the same moment. The shelves are what they were a heartbeat ago; the hold tray is what it was; the failure bin is what it was. Only the *current time* line moves.

That is what `Tick` does. `Tick` is the only event that can change the bank's clock, and when it changes state, the clock is the only field it changes. `Withdraw` also leaves the state unchanged, but it does not move the clock.

---

## What the move actually does

In the kernel, `Step.tick` carries a target time `t'` and a single hypothesis: `h_mono : s.clock ≤ t'`. The successor state is `{ s with clock := t' }` — the same state with the clock field set to `t'`. The ledger is the same ledger. The bubbles field is the same. The agents' ladder map is the same. Every deposit's status is what it was. The only field that changes is `clock`.

The hypothesis is the only thing the kernel insists on: the new clock value must not be less than the current one. Time, in the bank's record, is monotone. The kernel does not say *how much* time advances — `t'` may be `s.clock + 1` or it may be hours later — only that the new value is not earlier than the old. A deployment may impose stronger discipline (regular ticks, a maximum stride, alignment to a real-time source) in the surrounding workflow; the kernel guarantees only the monotonicity.

The action label is the bare `Action.Tick`. There is no agent, no bubble, no slot index. `Tick` is not attributable to any one agent's decision because, as the bank records it, the passing of time is not anyone's individual move. It is the bakery walking over to the wall clock and writing the new time onto the day-book.

---

## Why monotonicity, and only monotonicity

The reason the kernel-level constraint is monotonicity rather than uniform stride or real-time alignment is the same reason the bakery's day-book does not insist that every entry be exactly fifteen minutes apart. *What the day-book commits to* is a record of times that go forward, not a record of times that are evenly spaced. Even spacing is a deployment-level discipline; if a deployment wants its trace to look like a heartbeat, it can; the kernel does not need to be the thing enforcing that.

What monotonicity buys is the stable time axis that temporal-validity policies can reason over. If a deployment interprets `τ` as an expiry-style window, then the fact that the bank clock never rewinds supports the expected asymmetry: expired deposits do not become current again merely because the bank moved time backward. The kernel itself proves the clock discipline; the deployment's validity predicate supplies the exact expiry rule.

It also means that any safety theorem that quantifies over time is quantifying over a clock that goes one way. There is no construction in which the bank silently undoes a temporal-validity expiry by walking the clock back. The only event that can move the clock is `Tick`, and `Tick` cannot move it backwards.

---

## What `Tick` does not do

`Tick` does not look at the ledger. It does not check whether any deposit's temporal-validity window has just closed; it does not flip any status; it does not generate a quarantine or a revoke for a newly-stale deposit. In the bakery, the wall-clock writer does not also walk the front shelf pulling expired loaves; that is the staff member with the front-counter job, doing it as a separate move (a `Challenge`, in the bank's case). The bank treats time as a fact about *when* things happened, not as a force that itself causes things to happen.

`Tick` also does not change which bubbles exist, which agents are at which ladder stage, or which deposits are in which status. It is the move with the smallest possible effect: one field of the system state changes; everything else is identical. Of the ten constructors, `Tick` is the cleanest case of *the move that records exactly one thing and nothing else*.

---

## How the trace reads later

A trace reader looking for the bank's view of *when* things happened scans for `Action.Tick` entries between other actions. The state immediately before each `Tick` carries the old `s.clock`; the state immediately after carries the new one. The kernel guarantees, by the `Step.tick` constructor precondition, that the new clock is not less than the old. A reader who wants to know what `s.clock` was at the moment some other recorded event fired walks back to the most recent `Tick` (or to the trace's initial state) and reads off the clock the bank was committed to at that point.

This is the channel through which every other temporal claim in the architecture is grounded. *The deposit was within its temporal window at the moment of withdrawal* is checked against the `s.clock` at that withdrawal step, which is the `s.clock` set by whatever `Tick` last fired. *No `Tick` fired between this challenge and that revoke* says, equivalently, *the bank's recorded time did not advance between those two events*. The clock is the bank's stamp on the rest of the trace.

---

## Takeaway

`Tick` is the only event that moves the clock and the only event that does *only* that. The kernel's bank-side discipline is monotonicity: the new clock cannot be earlier than the old. There is no agent, no bubble, no slot. The action label is just `Action.Tick`, and the successor state differs from the predecessor in exactly one field.

This is what gives every later temporal claim something to be grounded against. The next file in the series is `Repair`, the move that returns a quarantined deposit to the candidate queue for re-validation.

---

*[← The Bakery](../lifecycle.md) · [← Submit](submit.md) · [← Register](register.md) · [← Withdraw](withdraw.md) · [← Challenge](challenge.md) · [Repair →](repair.md)*
