# Accepted Things Can Turn Out Bad → Revocation

## Cluster

- [What the Architecture Was Forced Into](../forcing.md) — the eight pressures and the schema that turns them into structure
- [People Disagree → Separate Spaces](people-disagree.md) — distributed agents force scope separation
- [Checking Takes Work → Trust Bridges](checking-takes-work.md) — bounded verification forces trust-based import
- [Things Travel → Metadata Travels With Them](things-travel.md) — cross-boundary export forces headers
- **Accepted Things Can Turn Out Bad → Revocation** — adversarial pressure forces a way out of *accepted* *(you are here)*
- [People Need to Coordinate → Shared Storage](people-need-to-coordinate.md) — coordination need forces a bank
- [Reality Pushes Back → Redeemability](reality-pushes-back.md) — truth pressure forces external constraint-surface contact
- [Not Everyone Can Do Everything → Granular ACL](not-everyone-can-do-everything.md) — staged access forces tier separation
- [Storage Runs Out → Storage Management](storage-runs-out.md) — bounded capacity forces eviction, archival, or pruning
- [What Goes Wrong When You Drop a Piece](../pathologies.md) — the crosswalk made vivid

---

## A driver's licence that cannot be cancelled

A licensing authority issues driving licences. The process is careful: a written test, a road test, an eyesight check, a background check on prior driving offences, a photo. When all of that passes, the licence is *accepted* — printed, mailed, and entered into the central register as a valid permission to drive.

Now imagine an authority where the register has exactly one transition out of *accepted*: there isn't one. Once a licence is in the register, it stays there forever. There is no field for *revoked*, no field for *expired*, no field for *suspended pending review*. The lifecycle of a licence is enter-as-accepted, then absorb every subsequent event — every drink-driving conviction, every fatal collision, every medical episode, every fraudulent-application discovery — into the same accepted state, because there is nowhere else for the licence to go.

A driver who never offends is fine. A driver whose application turns out to have been fraudulent is also still licensed: the register cannot say otherwise. A driver who develops a condition that makes them dangerous behind the wheel is still licensed. A driver convicted of vehicular manslaughter is still licensed. The register's structure makes this true regardless of any official's wish to act on it. The most the authority can do is *announce* that a licence is no longer valid; the register itself will keep saying it is.

The actual practice — a *revoked* state, a *suspended* state, fields for adjudicated facts that move the licence out of *accepted* — is not bureaucratic theatre. It is the only thing that fits, and the reason it is the only thing that fits is the load-bearing claim of this corner.

---

## What the kernel proves

The kernel calls a lifecycle of this shape a `MonotonicLifecycle`. It has three substantive ingredients, plus a fact about how they fit together:

- a type of states the deposit can be in (licence-register entries, in the scene),
- an *accepted* state that the deposit reaches when the receiving scope says yes,
- a *step* function that takes one state to the next under whatever events the system handles,
- and the *absorbing* fact: stepping from *accepted* returns *accepted*.

The simplest-than-revocation design is exactly this: an accepted state with no exit. The kernel proves that under such a lifecycle, no number of subsequent steps moves a deposit out of *accepted*. The proof is short:

> Take a deposit in the accepted state. After zero steps it is still in the accepted state. After one step it is `step accepted`, which by the absorbing fact is *accepted*. By induction, after any number of steps it is still *accepted*. The supposition that some number of steps escapes is false.

The piece that gets forced in is the obvious one once it is named: the lifecycle must include at least one transition that takes a deposit *out* of the accepted state. EpArch calls such a transition *revocation*. The kernel exhibits three structural variants — *quarantine*, *hold*, *rollback* — under the same forcing argument. Everyday vocabulary attaches further names to the same shape (*suspension*, *recall*, *cancellation*); these are not kernel terms, but they describe transitions of the same structural kind. The revocation is the kernel's name for *some way for an accepted thing to stop being accepted*.

---

## Why dressing it up doesn't help

The shortfall is sharp enough that it is tempting to look for an arrangement that handles bad-after-acceptance without admitting that the lifecycle has an exit from *accepted*. The kernel checks three of the obvious dodges and shows each of them either *is* a revocation in disguise — in which case the absorbing condition is violated and we have admitted the exit — or fails to remove the bad deposit at all.

**Quarantine.** "Don't revoke; just move it to a *quarantined* state pending further investigation." The kernel models this as `QuarantineLifecycle` — an accepted state, a quarantine state distinct from accepted, and a step that takes accepted to quarantine. It proves directly that `step accepted ≠ accepted`. That is, by hypothesis, exactly the negation of the absorbing condition. Quarantine *is* an exit from accepted; calling it quarantine instead of revocation does not change the structural fact. (If, alternatively, quarantine is unreachable from accepted — if the system has a quarantine state but no transition into it from accepted — then the lifecycle is back to monotonic on accepted and the bad deposit stays accepted forever. We have a label that the system never applies.)

**Hold or shadow state.** "Don't revoke; just put a *hold* on the licence — flag it as under review without removing it." The kernel models this as `HoldLifecycle`: accepted, held, distinct, with `step accepted = held`. The same argument fires: `step accepted ≠ accepted`, the absorbing condition is violated, the hold *is* an exit from accepted. The cosmetic difference between *quarantine* and *hold* — one names a place, the other names a status — does not change the structural shape of the transition.

**Rollback to a prior state.** "Don't add a new state; just roll the licence back to *applied-but-not-yet-decided* and run the decision again." The kernel models this as `RollbackLifecycle`: accepted, prior, distinct, with `step accepted = prior`. The same argument fires once more: the rollback transition violates the absorbing condition. Rollback is exit-from-accepted under a different name, this time the name of the destination state.

The pattern across all three is the same: any architecture that handles bad-after-acceptance is admitting that the lifecycle has a transition out of accepted. What that transition is called in the kernel — *revocation*, *quarantine*, *hold*, *rollback* — or in everyday vocabulary — *suspension*, *recall*, *cancellation* — and what state the deposit lands in are design choices. The transition itself is forced.

---

## What this corner does not claim

It does not claim revocation must be undoable, automatic, or fast. The kernel proves only that *some* exit from accepted exists. Whether revocations can be reversed, whether they require human adjudication or fire on automated triggers, how long a deposit can sit in *suspended* before being either restored or fully revoked — all of that is design space the corner does not constrain. A licensing authority that revokes only after a hearing, an authority that auto-revokes on a positive fraud match, and an authority that suspends provisionally and decides later are all valid implementations as far as this corner is concerned. What none of them can be is *an authority whose register has no transition out of accepted at all*.

It does not claim revocation can detect every bad deposit. The corner says only that the lifecycle must have *somewhere to put* a deposit that has been determined to be bad. *How* badness gets detected — by adversarial deposits being challenged, by external evidence arriving, by drift over time — is the work of other parts of the architecture. Revocation is the destination, not the detector. (The detection question is taken up in the *Reality pushes back* corner; the challenge mechanics are part of the bubble lifecycle.)

And it does not claim revocation removes the historical fact that the deposit was once accepted. The kernel says nothing here about whether the system retains audit history, whether downstream systems that consumed the deposit while it was accepted are notified, or whether the revocation is forward-only. Those are jobs for the *Things travel* corner (revocation propagation across exports) and the lifecycle module on under-attack behaviour. The revocation being forced and the revocation being broadcast cleanly are separate questions.

---

## Takeaway

When acceptance can later be defeated — when a deposit that passed gates can later turn out to be wrong, defective, fraudulent, stale, or otherwise no longer acceptable — no lifecycle whose accepted state is absorbing can cope. The shortfall is structural: by induction on steps, no number of subsequent events moves the deposit out of accepted; the bad deposit is permanently licensed.

The minimal piece that closes the gap is at least one transition out of *accepted*. EpArch calls the forced shape *revocation*: some transition out of accepted. The kernel also shows that *quarantine*, *hold*, and *rollback* variants have the same structural shape for this argument: each violates accepted-as-absorbing by providing an exit from accepted. Three plausible dodges (quarantine state, hold state, rollback to prior) are each proved to be an exit from accepted under another name; none of them escapes the forcing.

The architecture's job is not to prejudge what counts as grounds for revocation. It is to refuse to silently lock the lifecycle into *once accepted, always accepted*.

---

*← [Forcing](../forcing.md)  ·  ← Previous: [Things Travel](things-travel.md)  ·  Next: [People Need to Coordinate → Shared Storage](people-need-to-coordinate.md) →*
