# The Claim

*[← The Deposit](deposit.md) · [Header Fields →](headers/headers.md)*

---

## Why the most fundamental field is the easiest to misread

Every deposit is a deposit *of* something. That something is **P** — the claim, the proposition, the content of what is being said. P is the thing the lifecycle moves around. It is what `Accept` accepts, what `Challenge_B` challenges, what `Revoke_B` revokes, what `knowledge_B B P` records as known in bubble B. Without P, none of the other fields have anything to attach to.

P is also the field that almost every reader silently misreads on first contact. The misreading is small and consequential, and the entire architecture is built so that catching it early matters: a `Deposited` deposit for P does **not** mean P is true. A `Revoked` deposit for P does **not** mean P is false. The deposit's status records *what the institution has authorized*, not *whether the world agrees*. P's truth-value and the deposit's lifecycle status are two different axes, and the architecture refuses to collapse them.

This file is about that gap. What P is, what it isn't, what makes the gap survivable, and what the rest of the headers are doing to manage it.

---

## The two axes

There are two questions you can ask about a claim:

1. **What does the institution say about P?** Answered by the deposit's status. `Candidate`, `Deposited`, `Quarantined`, `Revoked`, `Forgotten`. This is the bank's job.
2. **Is P actually true?** Answered by the world. Not by the bank. The bank does not have access to this answer and does not pretend to.

The two questions are independent. All four combinations of (status, truth) are coherent and all four happen:

|                       | **P is true**                                                                                  | **P is false**                                                                                |
|-----------------------|-------------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------------|
| **`Deposited` in B**  | The aligned case. The institution has authorized something the world also bears out.            | The institution has authorized something the world does not bear out. Survivable; correctable. |
| **`Revoked` in B**    | The institution has rejected something the world bears out. Survivable; restorable.             | The aligned case on the other side. The institution has rejected what the world rejects too.   |

The aligned cases are the goal. The misaligned cases are facts about how knowledge institutions actually operate, and the architecture is built to *survive* them, *diagnose* them, and *correct* them — not to pretend they cannot happen.

The headers are the survival kit. V tells you who said it. E tells you what failure modes it is exposed to. Redeemability tells you what path leads back to the world. τ tells you whether the path is still walkable. ACL tells you who is allowed to ask. None of these fields make P true. All of them help an agent figure out, when the misalignment shows, *which field broke* and *what to repair*.

---

## Scenario 1: ulcers — false-but-`Deposited` for forty years

Through most of the twentieth century, the medical bubble carried a deposit:

> P: most peptic ulcers are primarily stress/acid disorders rather than bacterial infection.

The deposit was `Deposited`. Patients were treated for stress and acid. Pharmacology was built around it. Textbooks reproduced it. V was deep — the chain reached back through decades of clinical observation, peer-reviewed studies, professional consensus. E carried the usual medical caveats but no entry for "this might not be the cause at all." Redeemability looked perfectly fine: the path-route-exists for testing the hypothesis, and verdicts came back, and the verdicts agreed.

P was false.

The architecture did not break during the forty years it held a false claim as `Deposited`. The bank does not have a "wait, but is this actually true?" predicate to consult. It applied its `Accept` standard, the deposit met the standard, the deposit got promoted, and the deposit stayed promoted because no challenge moved it out. The institution behaved exactly as the architecture says an institution behaves: it stood behind what it had certified.

What eventually broke the misalignment was not the bank noticing. It was an agent walking a redeemability path that the bubble's existing tests had not walked: Barry Marshall ingested *Helicobacter pylori* himself in 1984, developed gastritis, and treated it with antibiotics. That was a fresh contact-with-constraint-surface — a path-route the existing acceptance protocol had implicitly assumed was unnecessary. The verdict discriminated. The deposit moved through `Quarantined`, the new evidence was repaired into the deposit's E and V, and over the following decade the deposit was `Revoked` and a new deposit entered the lifecycle and was `Deposited` in its place:

> P′: many peptic ulcers are driven by *Helicobacter pylori* infection and can be treated by eradicating the bacterium.

What this story shows about P:

* The institution can hold a false P as `Deposited` indefinitely without violating any architectural rule. The architecture does not promise truth-tracking; it promises *standards-tracking*, and standards can be wrong.
* The redeemability field is what gives the architecture its eventual self-correction. As long as *some* path to the constraint surface remains walkable, a sufficiently motivated agent can walk it and force a revalidation. The architecture does not guarantee anyone will walk the path. It guarantees that the deposit can record whether such a path exists, whether it was walked, and where the path failed if it did.
* The other headers are what make the correction *targeted* once it begins. When Marshall's evidence arrived, the deposit did not have to be discarded as a black box. The bubble could ask: which V step is suspect? Which E term needs to be added? Was the original redeemability path actually walked, or was it skipped on cost grounds? The diagnosis was field-localized because the deposit was structured.

The architecture's promise is not "the bank tracks truth." It is "when the bank diverges from truth, the divergence is *diagnosable* and *repairable* through the same lifecycle that produced it."

---

## Scenario 2: continental drift — true-but-`Revoked` for fifty years

In 1912, Alfred Wegener proposed:

> P: the continents have moved across the surface of the Earth over geological time.

Within the geology bubble of the 1920s, P was deposited, challenged, and `Revoked`. The challenge was reasonable on the bubble's standards: Wegener could not specify a mechanism by which continents could plough through oceanic crust, and the available evidence (matching coastlines, distributed fossils, glacial striations) was open to alternative explanations the bubble already accepted. Under the bubble's `Accept`, P did not clear.

P was true.

The truth-value of P did not change in 1925 when the deposit was revoked. It did not change in 1935 when the geology bubble continued to teach against it. Continental drift was happening the entire time, regardless of what the institutional ledger said about it. The world is not waiting on the bank.

What changed was the bubble. In the 1950s and 1960s, paleomagnetic surveys and seafloor spreading data accumulated a contact-with-constraint-surface that the original revocation could not survive. The deposit was `Restored`, re-entered as `Candidate` (the lifecycle, not the original revocation, dictated this), revalidated under the bubble's now-updated `Accept`, and `Deposited`. Plate tectonics was institutionally authorized by the late 1960s. P had been true the whole time.

What this story shows about P:

* `Revoked` is an institutional verdict, not a metaphysical one. A bubble can revoke a true claim because its evidentiary standards at the time, applied honestly, did not warrant authorization. The architecture allows this; it does not pretend the bubble's standards are infallible.
* The V chain that was built up around the revoked deposit was not erased. When restoration came, the bubble had a record of what had been said, by whom, and why it had been rejected. The diagnostic surface for *why the revocation happened* remained intact, which is what made the eventual restoration honest rather than embarrassed retraction.
* `Restore_B` exists in the lifecycle precisely so that this case has a clean path. The architecture takes seriously that revocations can be wrong, and provides the same kind of structured correction for revocations as for promotions.

The architecture's posture toward truth, again: it does not adjudicate. It records. It exposes the record to challenge. It supports the lifecycle moves that let a misaligned record correct itself when evidence arrives.

---

## Why the bank's silence on truth is a feature

A reader who has internalized the orthogonality might still feel something is missing. *Shouldn't an epistemic architecture care about truth?*

It does. It cares about it the way an honest institution cares about it: by *not pretending to certify it*.

Truth is the constraint surface. It is what the world enforces, regardless of whether anyone has noticed. The architecture's claim is that an institution's job is not to *be* the constraint surface — that is a job no institution can actually do — but to maintain a structured ledger of *what has been authorized*, expose that ledger to *challenges* against the constraint surface, and run a *lifecycle* that lets misalignments enter `Quarantined`, get repaired, and either re-promote or revoke. The architecture's contribution is the lifecycle and the headers, not a truth predicate.

The misreadings the bank file warned against were *the bank is the agent's beliefs* and *the bank decides what is true*. P is the field where the second misreading is most tempting, because P looks like the place where truth would live if it lived anywhere. It does not live there. P is the *content* of what is being said. Whether the saying is correct is between the agent, the redeemability path, and the world — and the architecture is built so that the conversation between those three has somewhere structured to land.

Two consequences worth pulling out:

* **The institution does not lie when it stands behind a false `Deposited`.** It is reporting what its standards have authorized. The standards may be miscalibrated, or the evidence may have been incomplete, or the redeemability path may not have been walked. None of these turn the deposit into a lie; they turn it into a target for diagnosis. The lie would be the bank claiming the deposit was true. The architecture forbids the bank from claiming that.
* **The agent does not get to skip work.** The agent cannot read `Deposited` and conclude *true*. The agent is the one with stakes in the world, and the agent is the one who must walk the redeemability path when the stakes warrant it. The bank tells the agent what the institution has authorized; what to do about it is the agent's call.

---

## How the rest of the headers serve P

The other six header fields exist because P, on its own, is not enough to either *test* the institution's claim against the world or *diagnose* a misalignment when one shows up. Each field provides one part of the diagnostic surface:

* **S** — the standard under which P was assessed. If P turns out to be misaligned, the standard is one of the places the bubble can ask whether it was set right.
* **E** — the failure modes the deposit's holders know to watch for. The ulcers case is, in retrospect, partly a story about an E that did not include "the cause is something we have not considered." E expansion is one of the main mechanisms by which a bubble notices that the deposit it has been holding may be wrong.
* **V** — who said it, what they were drawing on, who they got it from. When a misalignment surfaces, V is the chain you walk back along to find the step that should be re-examined.
* **ACL** — who is allowed to read, challenge, or import the deposit. ACL does not affect P's truth, but it affects who is in a position to test P against the world.
* **Redeemability** — the path back to the constraint surface. This is the field that makes alignment-correction possible. A deposit with no walkable redeemability path is one whose misalignments cannot be caught from inside the architecture; one with a costly path is one where misalignments will only be caught when the cost becomes worth paying. The ulcers story turns on someone deciding the cost was worth paying.
* **τ** — whether the deposit has aged out of the window in which redemption is possible. A path-walkable-in-principle that no longer fits inside τ is the same as no path at all for the current decision.

P is the *what*. The headers are the *what-can-be-done-about-it-when-it-turns-out-to-be-wrong*. The architecture's commitment is not that P will always be right, but that when it is wrong, the diagnostic surface required to find out and to fix it is built into the deposit itself.

---

## Takeaway

P is the proposition being authorized. It is not what the institution certifies as true; it is what the institution certifies as *having met its acceptance standards*. The truth-value of P is a fact about the world, decided on the world's terms, and the architecture is careful never to claim otherwise.

`Deposited` does not entail true. `Revoked` does not entail false. The lifecycle moves through institutional verdicts; the truth-value sits underneath, unaffected by the verdicts and only visible when an agent takes the redeemability path and brings back evidence.

This is the architecture's most fundamental claim and its most easily misread one. The other headers exist so that when the misalignment between status and truth surfaces — and it will, in any institution that operates long enough — the gap is *diagnosable* and *repairable* through the same structured lifecycle that produced it. Ulcers and continental drift are the same story told from opposite sides of the truth axis: the institution got it wrong; the architecture survived; the headers gave the agents the structure they needed to eventually set it right.

---

*[← The Deposit](deposit.md) · [Header Fields →](headers/headers.md)*
