# Checking Takes Work → Trust Bridges

## Cluster

- [What the Architecture Was Forced Into](../forcing.md) — the eight pressures and the schema that turns them into structure
- [People Disagree → Separate Spaces](people-disagree.md) — distributed agents force scope separation
- **Checking Takes Work → Trust Bridges** — bounded verification forces trust-based import *(you are here)*
- [Things Travel → Metadata Travels With Them](things-travel.md) — cross-boundary export forces headers
- [Accepted Things Can Turn Out Bad → Revocation](accepted-can-turn-bad.md) — adversarial pressure forces a way out of *accepted*
- [People Need to Coordinate → Shared Storage](people-need-to-coordinate.md) — coordination need forces a bank
- [Reality Pushes Back → Redeemability](reality-pushes-back.md) — truth pressure forces external constraint-surface contact
- [Not Everyone Can Do Everything → Granular ACL](not-everyone-can-do-everything.md) — staged access forces tier separation
- [Storage Runs Out → Storage Management](storage-runs-out.md) — bounded capacity forces eviction, archival, or pruning
- [What Goes Wrong When You Drop a Piece](../pathologies.md) — the crosswalk made vivid

---

## A package at the customs desk

A truck pulls up to a national customs checkpoint with a shipping container full of medical devices. The customs officer has a budget — a finite amount of time, a finite team, finite test equipment — to clear the container before the next truck arrives.

For a small box of stationery the budget covers full inspection: open the box, count the items, compare against the manifest, done. For a single artisan crate the budget covers it too. For *this* container — three thousand sealed sterile units, each accompanied by manufacturing batch records, software-validation reports, and a chain of subcontractor certificates — the budget does not cover full inspection. Full inspection of one unit means tearing down sterile packaging, running calibration tests, and reading the validation evidence end to end. The container holds three thousand. The officer's shift is eight hours.

The officer has two options. She can refuse the container — in which case nothing imported is ever a complex medical device, because no shift covers a complex medical device end to end. Or she can accept the container on the strength of *somebody else's* checking: the manufacturer's quality system, the exporting country's regulator, the notified-body certification on file. She is not re-doing the work. She is accepting an endorsement from a scope whose work she trusts.

The second option is what real customs systems generally have to do in complex supply chains. The scene is not relying on a survey of customs law; it is using customs as a familiar case of the bounded-verification shape. The reason that shape forces the second option, and not just makes it convenient, is the load-bearing claim of this corner.

---

## What the kernel proves

The kernel calls the situation a `BoundedVerification`. It has four pieces:

- a type of things that can be claimed (containers, in the scene),
- a *cost* function — how much work it takes to fully verify each claim,
- a *budget* — the most work the receiving scope is willing or able to do per import,
- and a *hard claim* — at least one specific thing whose cost exceeds the budget.

The simplest-than-trust-bridges design is *verify everything from scratch*: a policy that says no claim is accepted unless the receiving scope re-does the full verification work itself. The kernel proves this is incomplete. The proof is short:

> Suppose the policy covers every claim — every claim's cost is within budget. The hard claim's cost exceeds the budget by hypothesis. The same number cannot be both within and over the budget. The supposition contradicts itself.

The piece that gets forced in is the obvious one once it is named: the receiving scope accepts the hard claim on the basis of an *endorsement* from a scope whose verification work it relies on, rather than re-doing that work locally. EpArch calls those acceptances *trust bridges*. The trust bridge is the kernel's name for *accepting a claim because some other scope's verification stands behind it, not because this scope re-did the verification*.

---

## Why dressing it up doesn't help

The shortfall is sharp enough that it is tempting to look for a clever way around it without admitting that some scope's endorsement is being trusted. The kernel checks two of the obvious dodges and shows each of them collapses back into the same incompleteness or quietly implements a trust bridge.

**Stage the verification.** "Don't try to do the whole inspection in one shift. Spread the work across multiple rounds — partial check at the port, partial check at the warehouse, partial check at the hospital — and the cumulative budget will be enough." The kernel models this as `StagedVerification`: a per-round cost function and a total budget summed across all rounds. If the *cumulative* cost on the hard claim still exceeds the *cumulative* budget, the same impossibility fires on the staged form. Spreading the work over more rounds does not create new budget; it only re-bookkeeps the existing budget. Either the rounds together cover the hard claim — in which case the original "single budget" was just under-scoped and we never had a hard claim to begin with — or they do not, and we are back where we started.

**Delegate to a verification market.** "The customs office cannot do it; pay a third-party inspection firm to do it on the customs office's behalf." This is closer to honesty about what is happening, but it is not an escape. The kernel models this as `DelegatedVerification`: an importer with a budget shortfall plus a delegate whose acceptance the importer relies on for claims over budget. The structure embeds directly into `BoundedVerification` (`delegated_to_bounded`), and the same incompleteness theorem fires on the embedded form. Delegation is not local verification becoming cheap. It is local verification being replaced by reliance on another scope's verification. That second scope's endorsement *is* the trust bridge. The kernel makes this exact equivalence explicit: a claim requires trust bridging if and only if it is not locally verifiable (`trust_required_iff_not_locally_verifiable`), and a system needs delegation if and only if it has at least one locally inadequate claim (`delegation_necessary_iff_locally_inadequate`).

The pattern across both is the same: any architecture that *looks* like it has eliminated trust by working harder is either still constrained by the same budget or has imported a second scope's work and called it something else.

---

## Why this isn't an empirical assumption

A reviewer might push: "Maybe verification is cheap in your domain. Maybe everything fits in budget. Then your forcing argument never fires."

The kernel meets this push directly. It constructs `depth_bounded_verification` — a family of `BoundedVerification` instances built from `Nat` itself, where the hard claim is a depth-`d+1` claim and the budget is `d`. The cost is structural: verifying a depth-`n` claim requires the kernel to traverse `n` constructors, and no smaller number of constructor steps will type-check. The hard-claim hypothesis (`exceeds_budget`) is `Nat.lt_succ_self d` — a one-line lemma about the successor function on natural numbers. The instance is non-vacuous *by construction*, not because the kernel makes a domain claim about real-world verification cost.

So the corner does not depend on empirical claims about how much work verification takes in practice. It depends on the existence of *any* claim family with irreducible cost, and the kernel exhibits one out of arithmetic. Once at least one such family exists, the trust bridge is forced for it. Empirical questions about which real-world claim families look like this can be argued separately; the architectural conclusion does not wait on that argument.

---

## What this corner does not claim

It does not claim the receiving scope must trust *any particular* endorser. The kernel proves that *some* trust relationship is forced for hard claims. Which scope to trust, what evidence the endorsement must carry, how endorsements are checked for authenticity, what happens when a trusted endorser turns out to have been wrong — all of that is design space the corner does not constrain. A customs office that trusts the manufacturer, a customs office that trusts the exporting government, and a customs office that trusts an independent notified body are all valid implementations as far as this corner is concerned. What none of them can be is *a customs office that re-verifies every complex container from scratch within its own budget*.

It does not claim trust bridges are always safe. The kernel says the bridge is *forced*; it says nothing here about how a bad endorsement can be detected, revoked, or compensated. Those are jobs for the *Accepted things can turn out bad* and *People disagree* corners. The bridge being forced and the bridge being safe are separate questions; the second one is answered elsewhere in the architecture.

And it does not claim there is a unique cost model. `verify_cost` in the kernel is whatever the modelling scope chooses to count — wall-clock time, money, attention, computational steps, energy. The corner fires under any cost model in which at least one claim costs more than the budget. The ledger of what counts as "work" is a modelling choice; the impossibility holds regardless.

---

## Takeaway

When at least one claim costs more to verify than the receiving scope's budget allows, no policy of *re-verify everything from scratch* can cover that claim. The shortfall is structural: the same number cannot be both within and over the budget.

The minimal piece that closes the gap is to accept the hard claim on the strength of some other scope's verification work — a *trust bridge*, in EpArch's vocabulary. Two plausible dodges (stage the work across rounds, delegate to a third-party market) either reproduce the same shortfall on the staged form or quietly implement a trust bridge under a different name. The kernel exhibits a non-vacuous instance out of arithmetic, so the forcing does not depend on empirical claims about real-world verification cost.

The architecture's job is not to decide who deserves to be trusted. It is to refuse to silently pretend nothing is being trusted.

---

*← [Forcing](../forcing.md)  ·  ← Previous: [People Disagree](people-disagree.md)  ·  Next: [Things Travel → Metadata Travels With Them](things-travel.md) →*
