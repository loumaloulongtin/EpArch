# Storage Runs Out → Storage Management

## Cluster

- [What the Architecture Was Forced Into](../forcing.md) — the eight pressures and the schema that turns them into structure
- [People Disagree → Separate Spaces](people-disagree.md) — distributed agents force scope separation
- [Checking Takes Work → Trust Bridges](checking-takes-work.md) — bounded verification forces trust-based import
- [Things Travel → Metadata Travels With Them](things-travel.md) — cross-boundary export forces headers
- [Accepted Things Can Turn Out Bad → Revocation](accepted-can-turn-bad.md) — adversarial pressure forces a way out of *accepted*
- [People Need to Coordinate → Shared Storage](people-need-to-coordinate.md) — coordination need forces a bank
- [Reality Pushes Back → Redeemability](reality-pushes-back.md) — truth pressure forces external constraint-surface contact
- [Not Everyone Can Do Everything → Granular ACL](not-everyone-can-do-everything.md) — staged access forces tier separation
- **Storage Runs Out → Storage Management** — bounded capacity forces eviction, archival, or pruning *(you are here)*
- [What Goes Wrong When You Drop a Piece](../pathologies.md) — the crosswalk made vivid

---

## A kitchen drawer that nobody empties

A household has a kitchen drawer for paper — receipts, takeaway menus, school notices, warranty cards, the odd birthday card. Every time something paper-shaped comes in, it goes in the drawer. Every time someone needs an old receipt, they fish through the drawer until they find it. Nothing ever leaves. This works fine for a few weeks. After six months the drawer is full. After a year the drawer will not close, and the family has started a second drawer. After three years, half the kitchen is drawers.

The household never set out to fill the kitchen with paper. They set out to keep things in case they were needed. Each individual decision — *put the receipt in the drawer, just in case* — was reasonable; the cumulative effect was not. At some point, somebody has to decide that the warranty card for the kettle they replaced two years ago can go, and put it in the recycling. Without that step, the drawer system is not a storage system; it is a slow-motion overflow.

The same shape shows up wherever a system records things and never removes them. A logging service that retains every line forever; a database that creates a new row for every state change and never compacts; a multi-tenant hosting platform where each tenant can use unbounded space; a backup system that keeps every snapshot. Each of these works on day one. None of them works on day ten thousand. The architecture's job, on day ten thousand, is to have already decided what gets removed and when — not because storage is morally suspect, but because the alternative is that the system tries to accept something it has no room for, and breaks.

---

## What the kernel proves

The kernel calls a setup of this shape `BoundedStorage`. It has four substantive ingredients, plus the overflow witness:

- a type of states (the global ledger state, in the kernel's framing),
- a *budget* — the fixed capacity, as a natural number,
- a *count* function — how many active deposits a given state holds,
- a *deep_state* — a concrete state whose count is larger than the budget,
- and the *exceeds_budget* condition: the deep state's count is strictly greater than the budget.

The simpler-than-storage-management design is exactly this: there is a fixed budget, and the system claims it can stay inside it forever. The kernel proves that under such an arrangement, no fixed budget covers all states. The proof is one inequality:

> Suppose every state's count is at most the budget. Apply this to the deep state. Its count is at most the budget. But the deep state's count strictly exceeds the budget. The two cannot both hold.

The piece that gets forced in is what the contradiction ruled out: there must exist some mechanism that prevents the system from sitting in the deep state forever. EpArch calls that mechanism *storage management*. Storage management is the kernel's name for any structural means of moving the count back down — eviction, archival, expiry, pruning, compaction — so that the system does not require the budget to cover states it could otherwise reach by accumulation.

---

## Why dressing it up doesn't help

The shortfall is sharp enough that it is tempting to look for a storage architecture that *seems* not to need management — a design that hides the unboundedness behind a more elaborate structure. The kernel checks three of the obvious candidates and shows that each of them, when actually deployed without a management mechanism, *is* a `BoundedStorage` overflow scenario underneath.

**Append-only logs.** "We just keep adding entries; we never delete." The kernel models this as `AppendOnlyLog`: a state type, an entry count, an *append* operation, and the structural condition that *append_grows* — appending always increments the count by exactly one. Combined with a *full_state* whose count already exceeds the budget, this is a direct `BoundedStorage` instance. `append_only_to_bounded` exhibits the embedding, and `append_only_log_overflows` fires the impossibility through it. The append-only log did not avoid the overflow; it gave the overflow a particular accumulation pattern.

**Versioned entry stores.** "Each update creates a new version; we keep all versions for audit and rollback." The kernel models this as `VersionedStore`: a state type, a version count, an *update* operation, and *update_grows* — update always increments by exactly one. A concrete *overflow_state* with count above the budget is the witness. `versioned_to_bounded` exhibits the embedding into `BoundedStorage`, and `versioned_store_overflows` fires through it. Versioning did not eliminate the overflow; it encoded the overflow as version history.

**Per-partition quotas.** "We don't have one big store; we have per-tenant or per-shard partitions, each with its own count, so global capacity isn't the right question." The kernel models this as `PartitionedStore`: a partition type, a per-partition count, a global budget, and a witness *overflow_partition* whose count in some *overflow_state* exceeds the global budget. `partitioned_to_bounded` exhibits the embedding by fixing the overflow partition; `partitioned_store_overflows` fires the impossibility. The partitions did not eliminate the overflow; they relocated it from the global store to a single misbehaving partition.

The pattern across the three is the same: any storage architecture that grows monotonically without a removal mechanism eventually exhibits a state whose count exceeds the budget, and that state is exactly the witness `BoundedStorage` requires. The kernel exhibits the embedding in each case. Storage management, in the kernel's sense, is not a particular implementation strategy (compaction, garbage collection, retention policies, archival to cold storage); it is whatever structure plays the role of *moving the count back down* so that the system is not condemned to its own deep state.

---

## What this corner does not claim

It does not claim every system has finite capacity. The corner fires only when there is a real budget — a finite number that a real implementation cannot exceed without failing. A purely abstract specification with infinite memory does not instantiate `BoundedStorage`; the budget is hypothetical and there is no overflow witness. The corner is about systems that have to live on actual hardware (or any other resource with a hard ceiling), and it forces management *given* that the ceiling is real.

It does not claim what the management policy must be. Eviction by age, eviction by least-recent-use, archival to cold storage, expiry by retention rule, compaction of redundant versions, garbage collection of unreachable entries, hard quotas with backpressure, soft quotas with notification — all of these are valid implementations of storage management as far as this corner is concerned. The corner says only that *some* mechanism that brings the count back down must exist; choosing which mechanism, when it fires, and what it removes is a design decision the corner does not make. The kernel formalises the need for such a mechanism, not the policy that chooses what to remove.

It does not claim management is loss-free. Eviction, archival, and pruning all involve trade-offs: a record that gets evicted is no longer available for the access patterns that wanted it; a version that gets compacted away can no longer be rolled back to; a partition's quota can refuse a legitimate write. The kernel says nothing here about which records are safe to remove, how to ensure that audit obligations survive eviction, or how to recover when management fires inappropriately. Those are jobs for the lifecycle module on under-attack behaviour and for the application-level retention policy. The corner forces the *existence* of removal capacity; what is safe to remove is a different question.

And it does not claim management can be deferred until overflow happens. The kernel proves that overflow is reachable, not that overflow is acceptable when reached. A system that runs without management until the disk fills up and then crashes has technically satisfied *count exceeds budget* — but the architecture forces management as a structural feature precisely so that the deep state is not reached in deployment. The kernel exhibits the deep state as a witness against the *no-management* design; it does not licence that state as a normal operating point.

---

## Takeaway

When a system has a finite capacity budget and a count that grows by accumulation, no claim that the system stays within budget forever can hold. The shortfall is structural: the model contains a concrete overflow state whose count exceeds the budget by construction, so the claim that all states stay within budget cannot hold.

The minimal piece that closes the gap is the existence of *some* mechanism that can move the count back down. EpArch calls that mechanism *storage management*. Three plausible architectural designs (append-only logs, versioned stores, per-partition quotas) do not escape the corner: each one supplies a direct embedding into `BoundedStorage` when run without a removal mechanism. The kernel exhibits the embedding in each case.

The architecture's job is not to specify which records get removed, when, or how. It is to refuse to silently pretend that a finite-capacity system can keep everything forever — and to make the existence of removal capacity a structural feature, not a runtime afterthought.

---

*← [Forcing](../forcing.md)  ·  ← Previous: [Not Everyone Can Do Everything](not-everyone-can-do-everything.md)  ·  Next: [What Goes Wrong When You Drop a Piece](../pathologies.md) →*
