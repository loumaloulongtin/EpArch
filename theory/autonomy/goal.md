# The Autonomy Goal — Obligation by Obligation

## Cluster

- *[Autonomy](autonomy.md) — what a system does next when the menu runs out*
- **The Autonomy Goal — `AutonomyUnderPRPGoal` as the obligation-by-obligation answer** *(you are here)*
- *[Corners](corners.md) — when one branch is unavailable, the others stop being optional*
- *[Risk](risk.md) — classifying actual bridge use, and what the risk layer does and does not promise*

---

## "We have procedures"

A safety review board asks the operator of a complex system — an autonomous vehicle programme, a clinical-decision-support deployment, an algorithmic-trading desk, an LLM agent platform — what the system does when it encounters an obligation it cannot handle by its standard verification process. The operator answers, in good faith: *we have procedures*. There is a written escalation policy, an exception-handling document, a runbook for unusual cases. The reviewer reads the documents and confirms they exist and are coherent. The operator and the reviewer go home thinking the question is answered.

It is not. *We have procedures* and *for every obligation that arrives, the system can point to which sound branch handles this particular obligation* are completely different claims. The first is a claim about the document set. The second is a claim about every individual case the system actually faces. A document set that says *if X arises, escalate; if Y arises, bridge from a similar case; if Z arises, verify in scratch* is consistent with a deployment where many of the actual obligations that arrive are none of X, Y, or Z, and the *we have procedures* answer is silent about what the system does in those cases. The runbook covers what was anticipated; the goal under discussion in this file covers what is *actually faced*.

The recurring confusion the autonomy goal disarms is exactly this slip from *the document set is coherent* to *every obligation has a sound response*. Coherent procedures with full-coverage obligations is what the goal demands. Coherent procedures with the obligations the system actually receives drifting outside what they cover is what the goal refuses to certify. The previous file argued that the architecture's offer for the obligation room is the three branches. This file is about the goal that says *and the offer must apply to every obligation the system accepts as one it must handle, not just the obligations the runbook anticipated*.

---

## The shape of the commitment

The goal is universally quantified over obligations the system has *flagged as ones it must handle* and existentially quantified over which of the three branches discharges each one. The two quantifier choices are doing distinct work and a deployment can fail the goal at either one.

The universal side is what makes the *we have procedures* answer insufficient. The goal does not ask whether *some* obligation has a sound response; it asks whether *every* obligation flagged as must-handle does. A deployment whose escalation runbook handles three quarters of the cases that arrive and silently coerces the remaining quarter into the closest in-budget verification it can fake has not satisfied the goal — the quarter where neither the in-budget branch, the bridge branch, nor the escalation branch *actually* applies are the cases the goal makes visible. The runbook may be coherent on its own terms; the goal exposes what the runbook did not contemplate.

The existential side is what makes the goal a *goal* and not a procedure. The architecture does not insist that any particular branch handle any particular obligation. It does not say bridges should be preferred to escalation, or scratch verification to bridges, or escalation to either. It says: produce *some* branch, and produce it in the architecture's vocabulary, for every obligation. Different obligations may take different branches; the same obligation may take different branches in different bubbles; the same obligation in the same bubble may have multiple branches available and the deployment may pick. The goal is about the *non-emptiness* of the set of branches, not the choice within it.

The combination — universal over flagged obligations, existential over branches — is the shape that turns the three-branch vocabulary from *autonomy.md* into a goal a deployment can publish on its profile. Formally, the branch choice is represented as a disjunction: scratch verification, or an existential bridge witness, or escalation. *AutonomyUnderPRPGoal: yes* says: for every obligation we flag as must-handle, we can point to which of the three branches discharges it, and we have done so. *AutonomyUnderPRPGoal: no* says: there exists at least one obligation we flag as must-handle for which we cannot. *AutonomyUnderPRPGoal: vacuous* says: we never flag any obligation as must-handle, so the universal claim is trivial.

---

## Which obligations even count

The goal is scoped by `mustHandle`, not by the universe of all deposits the system is operationally aware of. This is load-bearing and is the second confusion-disarming move the goal makes.

A deployment is constantly faced with claims, requests, inputs, presentations, queries that pass through it. It is not the case — and cannot be the case — that every such claim is one the deployment is *obligated to give a sound response to within its bubble*. Many are routed elsewhere before reaching the deployment's verification surface; many are filtered out as out-of-scope; many are marked as requests the deployment is allowed to refuse. The system's *obligation surface* is strictly smaller than its *exposure surface*, and it is on the obligation surface that the autonomy goal lives.

The clinical-decision-support deployment is exposed to every chart it sees but is obligated only on charts whose presentation falls within its certified scope. The autonomous-vehicle deployment is exposed to every road condition it perceives but is obligated to handle only the ones that fall within its operational design domain. The LLM agent is exposed to every prompt that arrives but is obligated only on prompts whose intent and content match its declared task. *Where the obligation surface ends* is itself a deployment-design choice, and the goal does not police that choice; it polices what happens *inside* the surface the deployment has drawn.

This is why a deployment that publishes *AutonomyUnderPRPGoal: yes* with a small obligation surface is not cheating. A surgical-pathology deployment that flags only six classes of biopsy as in-scope and has the three-branch coverage on each of those six classes has honestly satisfied the goal — for those six classes. A reader who wants to know what the deployment will do on a seventh class is reading the wrong row of the profile; that is not a question the autonomy goal is shaped to answer. The honest answer there is *out of scope*, and the deployment is obligated to expose its scope clearly enough that the question can be asked. Drawing the obligation surface narrowly is honest; drawing it widely and then satisfying the goal is more impressive; drawing it widely and *failing* the goal is what the goal makes visible.

A deployment cannot wriggle out of the goal by drawing the obligation surface to include only the cases it can already discharge — it can, but doing so is not a defect the goal alone catches. The goal says *for the obligations you have flagged, you have an answer*. It does not say *you have flagged the right obligations*. That second question is downstream of regulatory regime, contractual scope, audience expectation, and the deployment's own honest declaration; it lives in the meta cluster's compliance-API material and the world cluster's bridge predicates, not here.

---

## The bridge branch, read carefully

Of the three branches the goal accepts, the bridge branch is the one most often misread. The reading the goal *does not* support is: *we discharged the obligation by analogy because no analogous case exists in the world that would have made another branch necessary*. This is a metaphysical claim — about what does or does not exist outside the system — and the goal is not in the metaphysics business.

The reading the goal *does* support is operational on three points at once. First, the bridge candidate is *banked* — the system actually has it, in some prior bubble, with whatever architectural standing prior banked material has. Second, the candidate is *similar enough to the obligation in the architecture's similarity vocabulary* — the architecture's similarity relation, whatever its specific content for this deployment, does in fact relate the candidate to the obligation. Third, *verification-via-the-bridge fits the bubble's effective-time budget* — having the bridge does not mean the bridge gets used for free; the verify-via step still has to be in-budget for it to count.

All three conjuncts are conditions the deployment can in principle exhibit and a reviewer can in principle inspect. None of them require a claim about what is or is not the case outside the system. A deployment that says *we used the bridge branch on this obligation* is publishing a checkable, three-part architectural fact, not a metaphysical hope. The goal is honest precisely because it commits the deployment to making *that* fact, and not the metaphysical hope, the basis of the bridge response.

The other two branches are simpler in this respect. The in-budget branch reuses the bank-profile layer's verification/budget machinery — `verifyWithin B d (effectiveTime B)` — but it is not the same predicate as `SoundDepositsGoal`. `SoundDepositsGoal` says true claims are verifiable within budget; the autonomy branch says this must-handle obligation itself can be verified within budget. The escalation branch is a deployment-architectural fact about whether the bubble has an escalation path the architecture treats as a sound terminus for this obligation. Neither is metaphysically loaded. The bridge branch needs the careful reading because the word *bridge* will, on its own, drag the reading toward the metaphysical version, and the goal is built specifically to refuse that drag.

---

## What this goal is not claiming

The goal is bookkeeping about the model. It is not bookkeeping about the world. *AutonomyUnderPRPGoal: yes* says that for every must-handle obligation, the deployment can exhibit a branch in the architecture's vocabulary. It does not say the patient will be treated soundly, the turn will complete safely, the contract opinion will hold up in court, or the agent's output will be correct. The world-side question is in the world cluster's bridge predicates and is governed by them, not by this goal. A deployment that satisfies the goal and then suffers a bad outcome in the world has not falsified the goal; it has exhibited a case where the architecture's bookkeeping is in order and the world did not cooperate. That is the situation the world cluster's scope guards exist to keep separate.

The goal is not a recommendation about which branch a deployment should prefer. It is symmetric across the three branches in the sense that any of them satisfies the obligation in the goal's eyes; the goal's content is *some branch*, not *the right branch*. A surgical deployment that bridges aggressively when escalation would have been safer has not failed the goal; it has made a deployment-design choice the goal is not in a position to evaluate. A real-time control deployment that escalates when bridges were available has likewise made a choice. The goal's silence on which branch is preferable is not a gap to be filled in by the goal; it is the goal's correctly recognising that the question lives elsewhere.

The goal does not promise that a deployment satisfying it will satisfy the goal in the future. A deployment whose obligation surface widens because the world supplies it with cases it had not anticipated may discover, on a Tuesday, that it has an obligation flagged as must-handle that none of the three branches can in fact discharge. That discovery does not retroactively falsify the deployment's previous *yes* — at the time, the goal held — and it does not necessarily mean the deployment is compromised; it means the deployment has work to do. The goal is a statement about the model at the time of evaluation; it is not a future-proofing promise. A deployment that wants the *yes* to keep holding has to keep checking it, and the kernel cannot do that check on the deployment's behalf.

---

## Takeaway

`AutonomyUnderPRPGoal` is the goal that closes the gap between *we have procedures* and *every obligation we have flagged as one we must handle has a sound response in the architecture's vocabulary*. It is universally quantified over the obligation surface (`mustHandle`) the deployment has drawn for itself, and existentially quantified over which of the three branches — in-budget verification, an available-witness analogical bridge, principled escalation — discharges each obligation. A deployment claiming the goal commits to producing one of those branches for every obligation on its surface; it does not commit to any particular branch and does not commit to the obligation surface being the right one.

The bridge branch is the one to read carefully. It is the operational fact that a candidate is banked, similar enough in the architecture's relation, and verification-via-it fits the budget — not a metaphysical claim that no analogous case exists outside the system. The goal works because it refuses the metaphysical reading and commits the deployment to the three-conjunct operational one.

The next file in the cluster does the structural work behind why the three branches are not a menu the deployment can pick from at will: when one branch is structurally unavailable, the architecture forces the others not to be optional. That is what the corner theorems for autonomy say, and it is what makes the three-branch vocabulary load-bearing rather than decorative.

---

← [Autonomy](autonomy.md) · ↑ [Goals](../goals/goals.md) · Next: [Corners](corners.md) →
