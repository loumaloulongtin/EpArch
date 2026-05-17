# Things Travel → Metadata Travels With Them

## Cluster

- [What the Architecture Was Forced Into](../forcing.md) — the eight pressures and the schema that turns them into structure
- [People Disagree → Separate Spaces](people-disagree.md) — distributed agents force scope separation
- [Checking Takes Work → Trust Bridges](checking-takes-work.md) — bounded verification forces trust-based import
- **Things Travel → Metadata Travels With Them** — cross-boundary export forces headers *(you are here)*
- [Accepted Things Can Turn Out Bad → Revocation](accepted-can-turn-bad.md) — adversarial pressure forces a way out of *accepted*
- [People Need to Coordinate → Shared Storage](people-need-to-coordinate.md) — coordination need forces a bank
- [Reality Pushes Back → Redeemability](reality-pushes-back.md) — truth pressure forces external constraint-surface contact
- [Not Everyone Can Do Everything → Granular ACL](not-everyone-can-do-everything.md) — staged access forces tier separation
- [Storage Runs Out → Storage Management](storage-runs-out.md) — bounded capacity forces eviction, archival, or pruning
- [What Goes Wrong When You Drop a Piece](../pathologies.md) — the crosswalk made vivid

---

## Two crates on the same loading dock

A receiving warehouse has a loading dock. Crates arrive on the dock from various senders. The warehouse manager has a simple job: route each crate either to *bonded storage* (accept, file, mark for downstream use) or to *return-to-sender* (reject, do not put into circulation).

Two crates arrive on the same morning. They are the same size and the same shape. They have the same brown cardboard exterior and the same packing tape. From across the dock they are visually identical.

One contains a properly manufactured shipment of vaccine vials, ordered by the warehouse, paid for in advance, and within shelf life. The other contains expired stock that was supposed to be destroyed by the sender, mistakenly loaded onto the wrong truck. The warehouse should accept the first and return the second.

Now imagine the manager trying to make the routing call without looking at *anything attached to the crates* — no shipping label, no manifest, no purchase-order reference, no consignor identifier, no temperature-log printout, no destruction-certificate paperwork, nothing. The manager can see the crates, but the crates carry no information about themselves beyond their physical presence on the dock.

Whatever rule the manager applies, it is a rule that takes a crate and returns *accept* or *reject*. From the manager's vantage point the two crates look the same. Any rule will return the same answer on both. Either they both get accepted — and the expired stock enters circulation — or they both get rejected — and the warehouse fails to receive its own paid-for order. There is no rule that lands on different answers for two crates that present identically.

The actual practice — shipping labels, manifests, consignor identifiers, batch numbers, temperature logs, destruction certificates — is not warehouse bureaucracy that could be trimmed away by a sufficiently clever manager. It is the only thing that fits, and the reason it is the only thing that fits is the load-bearing claim of this corner.

---

## What the kernel proves

The kernel calls the situation a `DiscriminatingImport`. It has three substantive ingredients, plus a proof that the two witness claims are distinct:

- a type of things that can be claimed (crates, in the scene),
- a *good* claim — one specific thing the receiver should accept (the paid-for vaccine order),
- a *bad* claim — one specific thing the receiver should reject (the expired stock),
- and the proof that they are not the same thing.

The simplest-than-headers design is *uniform import* — a routing function that treats every claim the same regardless of any per-claim information, because there is no per-claim information to look at. The kernel proves this is incompatible with sound-and-complete routing. The proof is short:

> A uniform function returns the same value on the good claim and the bad claim, by definition of uniformity. A sound-and-complete policy returns *false* on the bad claim and *true* on the good claim. The same function cannot return both *false* and *true* on its outputs at once. The supposition contradicts itself.

The piece that gets forced in is the obvious one once it is named: each claim travels with structured per-claim information sufficient to distinguish it from claims it should be routed differently from. The kernel calls a function over claims that successfully distinguishes good from bad an `IsHeader`. EpArch calls the per-claim information itself a *header*. The header is the kernel's name for *whatever travels with the claim that lets the receiver tell it apart from claims that should be routed differently*.

---

## Why dressing it up doesn't help

The shortfall is sharp enough that it is tempting to look for a way to import claims without admitting that per-claim metadata is doing the routing. The kernel checks two of the obvious dodges and shows each of them collapses back into the same impossibility or quietly implements a header.

**Route by content hash.** "Don't attach metadata; just hash the claim itself and route based on the hash." If the hash function actually distinguishes the good claim from the bad claim — if it is collision-resistant on those two — then `import_by_hash ∘ hash` is a function that returns different values on good and bad. The kernel proves this *is* a header, by literally calling the composite function as a witness for `IsHeader`. The hash machinery did not avoid metadata; it manufactured metadata on the fly from the claim's contents and routed by it. There is also a more informal observation worth noting alongside the kernel claim: a hash is one-way, so the hash on its own tells the receiver nothing about what the claim *is* — to act on it, the receiver has to maintain a side table mapping known-good hashes to routing decisions, and that side table is itself per-claim metadata stored at the receiving end of the wire. The kernel does not formalise this point, but it is consistent with what the kernel does prove: the metadata cannot be eliminated, only relocated. If, alternatively, the hash function fails to distinguish the two — collision on the witnesses — then the routing is uniform on the embedded `DiscriminatingImport` and the original impossibility fires. Either way: the routing either *uses* a discriminating function over claims, which is a header, or it cannot route correctly.

**Route by global state.** "Maintain a single shared routing rule on the receiver side — *accept everything today, reject everything tomorrow* — applied uniformly to whatever arrives." The kernel models this as `GlobalRoutingState`: a single `global_policy : Bool` applied to every claim. It proves directly that the policy returns the same value on the good claim and the bad claim — by the trivial computation `(fun _ => global_policy) good = (fun _ => global_policy) bad`. The routing cannot tell good from bad at all. Per-claim state would be a header by another name; global state cannot discriminate.

The pattern across both is the same: any architecture that *looks* like it has eliminated per-claim metadata but still routes correctly is either deriving the metadata from the claim (in which case it is a header) or routing on something else that varies across claims (also a header, just stored separately). The minimum discriminating structure the receiver needs is header-like: some per-claim basis on which good and bad can be routed differently, whether it is carried on the payload, derived from it, or stored in a side table keyed by it.

---

## What this corner does not claim

It does not claim headers must take any particular form. The kernel proves that *some* discriminating per-claim function is required. Whether that information rides on a shipping label, a printed manifest, a digital signature attached to the payload, a database lookup keyed by the claim, a content-derived hash, or a manifest distributed out-of-band is design space the corner does not constrain. A warehouse with paper labels, a warehouse with QR codes, and a warehouse with cryptographic envelopes are all valid implementations as far as this corner is concerned. What none of them can be is *a warehouse that distinguishes good and bad shipments without using any per-claim information at all*.

It does not claim headers are honest. The kernel proves the receiver needs *enough information to route correctly when the headers are accurate*. What happens when a header is forged, stale, or maliciously crafted — when the destruction-certificate paperwork accompanies the expired stock that was supposed to be destroyed — is a question for *Adversarial pressure → revocation* and the access-control corner. The header being forced is not the same as the header being trusted; the second question is answered elsewhere in the architecture.

And it does not claim the receiver must read every header field. The corner says only that *some* function over the headers must discriminate good from bad; many header fields will be inert for a given routing decision. The minimum is *enough to discriminate*, not *everything that could conceivably be attached*.

---

## Takeaway

When two distinct claims must be routed differently, no rule that ignores per-claim information can land on different answers for them. The shortfall is structural: the same uniform function cannot return different values on different inputs that it cannot tell apart.

The minimal piece that closes the gap is to attach to each claim some structured information that lets a routing function tell it apart from claims that should be routed differently. EpArch calls that information a *header*. Two plausible dodges (content-hash routing, global routing state) either reduce to a header by another name or fail to discriminate at all.

The architecture's job is not to specify what headers look like. It is to refuse to silently pretend the routing is happening on nothing.

---

*← [Forcing](../forcing.md)  ·  ← Previous: [Checking Takes Work](checking-takes-work.md)  ·  Next: [Accepted Things Can Turn Out Bad → Revocation](accepted-can-turn-bad.md) →*
