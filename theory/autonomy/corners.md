# Corners — When One Branch Is Unavailable, the Others Stop Being Optional

## Cluster

- *[Autonomy](autonomy.md) — what a system does next when the menu runs out*
- *[The Autonomy Goal](goal.md) — `AutonomyUnderPRPGoal` as the obligation-by-obligation answer*
- **Corners — when one branch is unavailable, the others stop being optional** *(you are here)*
- *[Risk](risk.md) — classifying actual bridge use, and what the risk layer does and does not promise*

---

## The Sunday-night corner

It is Sunday at 11pm in a regional hospital and the only neurologist on the on-call rota for three counties has been in surgery for the last four hours. A scan comes in for a patient who cannot wait until morning. The clinic's standing answer to a case like this has, for years, been the same: when the in-house team cannot read it inside the time the patient has, page the on-call neurologist. Tonight, that page will not be answered. The case is still in front of someone. Something will happen next.

The picture this case unsettles is the comfortable one in which a system facing hard cases has *several* honest things it can do — read the case itself, lean on a closely similar prior case, escalate to a human authority — and gets to pick whichever feels right. That picture is fine when all three are open. The Sunday-night corner is what happens when one of them closes, and the question becomes whether the system was relying on having choices, or relying on having *an* answer.

What the corners in this file say is that the second posture is the one the autonomy goal commits a system to. When a branch closes for a particular case, the system's commitment does not close with it — it presses harder on the branches that remain. There is no fourth thing the architecture quietly accepts in the corner; whatever the system does next, if it is not one of the remaining branches in the form the goal recognises, it is not a discharge of the goal.

---

## Two corners, walked

The cluster's two corner theorems are two snapshots of the same mechanism, taken under different operational conditions.

### First corner: when in-budget verification fails

The deployment has flagged the obligation as must-handle. In-budget verification is unavailable for this obligation: within the bubble's effective-time budget, the obligation cannot be verified. Maybe a procedure was attempted and ran out of time; maybe the deployment can already show no such procedure fits. Either way, the scratch branch is closed. The corner says: under the live commitment to *AutonomyUnderPRPGoal*, exactly two branches remain in play, and one of them must apply to this obligation. Either there is a banked candidate similar enough that verifying-via the candidate fits the budget (the bridge branch as the goal file reads it — banked, similar, budget-fitting, all three), or there is an escalation path the deployment treats as a sound terminus for this obligation.

What is *not* offered by the corner: the architecture does not pick between the two. A surgical pathology deployment may have rich banked material and cheap bridges and almost never escalate; an emergency-medicine deployment may have sparse priors and weight escalation heavily. Both can satisfy the corner because both can produce, on each must-handle obligation that exceeds in-budget verification, *one* of the two branches. The corner is the disjunction; it is silent on the choice within it.

What is *also* not offered: the corner does not say that the bridge-or-escalation pair is *easy* to satisfy, or that real deployments typically do. It says that the alternative to satisfying it is having mis-stated the goal claim. The corner converts an ambient *we have procedures* posture, on the obligation where in-budget verification has failed, into the sharper question *which of these two branches do you have for this obligation*.

### Second corner: when escalation is also closed

Now compose the Sunday-night case. The obligation is must-handle, scratch verification will not cover it, and escalation — the runbook's usual fallback — is for this obligation, in this bubble, at this moment, not available. The deployment is not in a position to claim *we'll escalate*; the path it would have taken is shut. Two of the three branches the goal accepts are now structurally unavailable for this case.

The corner says: under the live commitment to *AutonomyUnderPRPGoal*, the bridge branch is no longer one option among several. It is the only branch whose availability is consistent with the goal still holding for this obligation. The deployment must be able to produce the three-conjunct bridge witness — banked candidate, similarity in the architecture's relation, verify-via that fits the budget — or the *yes* on its profile is, for at least this obligation in this bubble, false. The two corners taken together are the architectural statement that the three-branch vocabulary is not a menu of conveniences. The branches are the deployment's *only* honest places to land, and which of them is forced is a function of which others have closed.

The bridge-as-fallback role this corner highlights is exactly why the goal file insisted on the three-conjunct operational reading of the bridge branch and refused the metaphysical reading. A bridge branch that meant *no comparable case exists in the world* would be a hope the deployment cannot inspect, much less produce on demand on a Sunday night. A bridge branch that means *we have this prior, the architecture's similarity relation in fact relates it to the obligation, and verifying-via-it fits the budget* is something the deployment can either exhibit at the moment the corner forces it or admit it cannot. The corner only does its work because the bridge is operational.

---

## What the corners do not say

The corners do not promise that the bridge or escalation path will exist in the world. They are conditional: *if* the deployment claims *AutonomyUnderPRPGoal* and *if* the obligation is on the must-handle surface and *if* the foreclosed branches are foreclosed, *then* the remaining branch is forced. A deployment that finds itself in the second corner and cannot produce a bridge witness has not falsified the corner; it has discovered that its earlier *yes* was, for at least this obligation in this bubble, overstated. The corner is a statement about what the goal claim *means*; whether any given deployment in any given moment satisfies the meaning is a separate empirical question about the deployment.

The corners do not recommend that deployments engineer themselves to keep one branch closed so the others get exercised. The forcing is descriptive of the goal's structural commitment, not prescriptive of operational policy. A deployment that arranges its bubbles so that escalation is reliably available *and* in-budget verification is generously sized *and* a rich bank of priors is maintained is not somehow under-using the corners — it is satisfying the goal across the whole obligation surface with margin, which is exactly what the goal is set up to allow.

The corners do not extend to the broader question of whether the deployment has drawn its must-handle surface honestly. That question lives one cluster outward, in the meta-cluster's compliance-API material and in the world cluster's bridge predicates. The corners take the obligation surface as given; what they police is what happens *inside* it when branches close. A deployment that quietly trims its must-handle surface every Sunday night to exclude the obligations whose branches it cannot produce is not caught by the corners — it is caught further out. The corners are tight on what they cover and silent past it; that silence is the layer above's job, not theirs.

---

## Takeaway

The two corner theorems — `autonomy_forces_bridge_or_escalation` and `no_escalation_forces_bridge` — turn the three-branch vocabulary from an architectural option-set into a structural commitment. When in-budget verification fails for a must-handle obligation, the goal forces the deployment onto the bridge-or-escalation pair. When escalation is also closed, the goal forces the bridge alone, in its three-conjunct operational reading. Neither corner picks a branch the deployment ought to prefer, and neither converts the goal into a guarantee about the world. Both convert the goal into something that cannot be satisfied by simply having a runbook: the deployment's commitment redistributes onto whatever branches remain, and refuses to disappear when the convenient ones do.

The next file in the cluster looks at what happens when the bridge branch is the one being used — how that use is *classified* by the operational risk layer, and the careful distinction between that classification and the residual-risk story the meta cluster's compliance API tells.

---

← [The Autonomy Goal](goal.md) · ↑ [Goals](../goals/goals.md) · Next: [Risk](risk.md) →
