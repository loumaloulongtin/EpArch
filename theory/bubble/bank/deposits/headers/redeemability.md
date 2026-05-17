# The Bushes Story

*[← Access Control](access-control.md) · [Temporal Validity →](temporal-validity.md)*

---

## When the path to redemption is too expensive to walk

A forager is moving through the brush. He stops.

The bushes ahead of him just moved. He heard a low sound he cannot place. Something is in there.

His working deposit:

* **P**: There is a tiger in those bushes.
* **S**: A pattern of rustling and a low sound consistent with a large animal.
* **E**: Could be a tiger. Could be a boar. Could be wind. Could be another forager.
* **V**: His own ears and eyes, just now.
* **Redeemability**: Walk into the bushes and look.

The redeemability path exists. It is cheap to describe. It would settle the question definitively. One verdict, no ambiguity.

He does not take it.

He backs away and goes around.

Not because the deposit is unreliable. Not because S is too weak or V is too thin. The deposit could in principle be redeemed, and the redemption would be conclusive.

He does not redeem because *the cost of walking the path, conditional on P being true, is his life*.

Redeemability is graded by cost, not just by whether a path exists. A path that exists but cannot be afforded is not, for practical purposes, a redemption path. The agent has to act on the unredeemed deposit.

So he treats the deposit as if it were true. He does not need to *know* there is a tiger. He needs to *act* as though there is.

---

## Same field, different cost, different decision

Move the same proposition to a different setting.

A wildlife biologist on a tracking team hears the same rustle in the same bushes. The deposit looks identical:

* **P**: There is a tiger in those bushes.
* **S**: Pattern of rustling, low sound consistent with a large animal.
* **E**: Could be a tiger. Could be a boar. Could be wind.
* **V**: Their own ears and eyes, just now.
* **Redeemability**: Send the drone up. Check the camera traps. Look at the GPS collar feed for collared individuals in the area. If still uncertain, approach with the team and the rifle.

Same P. Same S. Same E. Same V.

The redemption is not free here either, but it is affordable. There are intermediate paths — proxies — that contact the constraint surface without putting a body in the bushes. The drone gives a verdict that discriminates a tiger from a boar from wind. The collar feed gives a verdict that discriminates a known individual from anything else.

The biologist takes the path. The forager does not.

The field doing the work in both cases is redeemability. What differs is what it costs to walk it and what proxies are available along the way.

---

## What the bushes show

Redeemability is not a binary "checkable / not checkable." It is a path with a cost and a set of available proxies. A deposit is redeemable to the extent that the agent can afford to walk a path whose verdict discriminates the truth of P.

Two situations come up constantly:

* **The cheap path exists.** Walk it. The deposit either holds or fails, and the agent updates accordingly.
* **The cheap path does not exist.** Either there is no path at all, or the only path is too expensive to take. The agent must act on the unredeemed deposit, and the size of E does most of the work that redemption would normally do.

Most real reasoning lives between these two. Proxies — partial, indirect, weaker contacts — are how redeemability works in practice. The drone is a proxy. The camera trap is a proxy. The neighbor saying "I just saw it walk that way" is a proxy. Each proxy is its own miniature deposit, with its own provenance and its own verdict, and stacking them is how an agent earns confidence when the direct path is closed.

---

# The Rubber-Stamp Audit Story

## When the path is walked but the verdict does not discriminate

A vendor is selling a system. They claim it is secure.

The buyer asks for a redemption: how do they know?

The vendor produces a security audit report. There is a logo at the top. There is a signature at the bottom. There is a checklist in the middle. Every box is checked.

The deposit looks redeemed:

* **P**: This system is secure.
* **S**: The system passes a security audit by an external auditor.
* **E**: A determined attacker may still find a vulnerability.
* **V**: The audit firm.
* **Redeemability**: The audit was performed and the report is available.

A path exists. Contact was made. There is a document.

But here is the structure of that audit: the vendor filled in the checklist themselves. The auditor's role was to receive the completed checklist and stamp it. No test was run. No code was read. Every system that asks for the stamp gets the stamp.

A vulnerable system passes this audit. A secure system passes this audit. The verdict the audit produces is the same in both worlds.

The redemption looked complete. The path was there. The contact happened. But the verdict does not discriminate the truth of P from the falsity of P. The audit cannot fail.

That is the failure. Not the absence of a path. Not the failure to walk it. The path is walked, the report exists, and *no possible outcome of the test would have indicated trouble*.

---

## What this shows

The bushes story showed that redeemability has a cost that can dominate the decision. The audit story shows that redeemability has internal structure: a path, a contact, and a verdict. Any of the three can fail independently.

* **Path**: there is some way the deposit could, in principle, contact a constraint surface.
* **Contact**: the deposit *did* contact it, directly or through proxies.
* **Verdict**: the contact would have produced a different result if P were false.

The forager has the path; he refuses contact because cost is prohibitive. The biologist has the path, takes contact through proxies, gets a discriminating verdict. The vendor has a path; contact happens; the verdict is rigged. The first two are real choices the agent gets to make about cost. The third is a deposit that *looks redeemed and is not*.

This is the structural difference between a bubble that grades its own homework and a bubble that exposes its claims to something it does not author. A self-stamped audit, an unfalsifiable theory, a survey whose questions all lead to the same answer — all path-and-contact present, verdict absent. The architecture has been defeated at the only subpart that does the work.

The repair path is the same shape every time: introduce a verdict that *could* come out the other way. An independent auditor whose report can say "fail." A test the theory could lose. A control group. A second source the first does not control. The point is not the audit; the point is whether a counterfactual P-is-false world produces a different reading.

---

# Takeaway

Redeemability is the field that names how a deposit can be brought into contact with something the bubble does not author, and what it costs to do so. It has three subparts — path, contact, verdict — and any of the three can be the locus of failure.

Redeemability failures cluster around a small number of patterns:

* **No path.** The claim cannot, in principle, contact anything outside the bubble. Pure consensus presented as truth.
* **Path closed off.** A path exists but is forbidden, gagged, or deferred. NDAs, classified results, "you'll see when it's too late."
* **Path too expensive.** The path exists and is open, but walking it costs more than acting on the unredeemed deposit. The forager and the bushes. The agent acts on E instead.
* **Contact never made.** The path is open and affordable; nobody walked it. "We didn't get around to testing it."
* **Non-discriminating verdict.** Contact happened; the test passes regardless of truth. The rubber-stamp audit. Unfalsifiable theory. Self-graded homework.
* **Wrong constraint surface.** A real test was run, but on the wrong domain. A lab result mapped to a clinical question without justification.

The first three are path failures. The fourth is a contact failure. The last two are verdict failures.

The bushes story is mostly about the third — the agent has the path and refuses it on cost grounds, then acts on E. The audit story is mostly about the fifth — the path looks taken and the verdict is rigged. Both shapes show up in everything from foraging to engineering, and the difference between an honest deposit and a sealed one usually comes down to which of the three subparts the agent is willing to actually inspect.

---

*[← Access Control](access-control.md) · [Temporal Validity →](temporal-validity.md)*
