# Autonomy — What a System Does Next When the Menu Runs Out

## Cluster

- **Autonomy — what a system does next when the menu runs out** *(you are here)*
- *[The Autonomy Goal](goal.md) — `AutonomyUnderPRPGoal` as the obligation-by-obligation answer*
- *[Corners](corners.md) — when one branch is unavailable, the others stop being optional*
- *[Risk](risk.md) — classifying actual bridge use, and what the risk layer does and does not promise*

---

## The room nobody has a procedure for

A radiologist on call at 3am is shown an image of a presentation she has, in twenty years of practice, never seen and cannot find in any reference she has access to in the next twelve minutes, which is the window before the patient must go to surgery or not. A self-driving system halfway through a turn finds a road configuration none of its test scenarios anticipated and none of its training data contains a clean analogue for. A junior associate at a law firm is asked, on a Friday afternoon, to opine on a contract clause whose interaction with a recent regulatory change is genuinely unsettled and on which the firm has no prior memo. An LLM agent is given a multi-step task whose total context exceeds any window it has ever been run on and whose decomposition into windows it can run on is itself a non-trivial planning problem.

In each of these rooms, the procedural posture *we have a verification procedure for cases like this* is not available. The case is not *like* anything the procedure was built for. The honest reading of the situation is: an obligation has arrived that the in-budget verification machinery cannot answer on its own terms. And yet the radiologist, the car, the associate, and the agent all have to *do something next*. They cannot opt out. The patient will or will not go to surgery; the car will or will not complete the turn; the firm will or will not return advice; the agent will or will not produce the output it was asked for.

The five-goal menu the goals cluster published has nothing useful to say in this room. *SoundDeposits* talks about claims that are accepted and verifiable within budget — but the obligation here is precisely a claim the budget cannot verify. *SelfCorrection* and *CorrigibleLedger* talk about what happens to claims once they are accepted — but the question is whether to accept any claim at all, and the prior question of *how to even produce one* is upstream of the menu. *SafeWithdrawal* and *ReliableExport* talk about the lifecycle of a claim that exists — but the harder question is what to do when the *would-be claim* exceeds what verification could ground.

This cluster is about what the architecture says to that room. Not what the radiologist *should* do — the architecture does not get to choose between surgery and not-surgery. What it says is *the structural shape of the answer*: there are three honest branches available, and any deployment claiming to handle obligations under this kind of pressure is committed to one of them being usable for the obligation in front of it.

---

## A second model layer, because the first does not stretch

The five-goal menu is bookkeeping over a particular layer of operational predicates: a deposit, a bubble, a notion of verification within an effective time, a notion of revision, a notion of submission and withdrawal and export. That layer is rich enough to let a deployment publish a profile across the five goals. It is *not* rich enough to even *state* the obligation the radiologist faces, because the obligation involves operational notions the bank-profile layer does not name. *This case has come to me and I cannot push it away* — there is no field in the bank-profile layer that says some claims arrive with that property. *I might handle it by reaching for analogous prior material* — there is no field that names *prior material* as a separate operational object. *I might handle it by escalating to a different decision authority* — there is no field for *escalation path*.

The architecture's response is not to overload the existing fields with these meanings. It is to introduce a second, named extension of the bank-profile layer that adds exactly the operational vocabulary the obligation room needs, and nothing else. In the kernel this is `AutonomyModel`: a structure that contains everything the bank-profile layer contains, plus a small set of new operational fields for *this is an obligation I cannot push away*, *here is prior material I could reach for*, *here is what it would mean for the prior material to be analogous enough to count*, *here is what verification-via-analogue would look like*, *here is the escalation path*. The relationship is made explicit by a forgetful projection back to the bank-profile layer: an autonomy model, viewed without these extra fields, *is* a bank-profile model. The five goals can be evaluated against either; the obligation room can be answered against the autonomy layer alone.

The reason this is its own cluster, and not a sixth row at the bottom of the goals menu, is exactly this layering. The five goals are the menu *of the bank-profile layer*. The obligation-room goal lives over a richer layer that adds operational fields the bank-profile menu does not need. Folding it in would make the menu inhomogeneous: five goals stated over one layer and a sixth stated over a strict extension, with the difference quietly papered over. The cluster keeps the layering visible.

---

## The three branches

The architecture's offer for the obligation room is not a single procedure. It is a vocabulary of three branches, exactly one of which a deployment must be able to point to for a given obligation if it claims to handle obligations of that kind at all.

The first branch is *the budget actually fits*. The case looks unfamiliar but it is in fact verifiable within the bubble's effective time. The radiologist, looking again, recognises a pattern she had filed under a different name. The car's perception subsystem, given another half-second, resolves the configuration into something it does have a verified policy for. The associate finds the relevant prior memo on a colleague's drive within the hour. When this branch is available it is the most ordinary of the three: the case felt like an obligation-room case but turned out to be a regular bank-profile case, and the standard verification machinery handled it. The architecture does not require this branch to be available for every obligation; it just requires that *if* it is available, that fact counts as the system having a sound response.

The second branch is *the analogical bridge from prior material*. The case is not one the bubble's verification machinery can certify in scratch, but the system has prior material — a previously banked claim, a prior decision, a worked example with an audit trail — that is similar enough to the case in front of it, in a way the architecture treats as analogically usable, that verifying against the bridge counts as a sound response. The radiologist remembers a chapter in a paediatric atlas that addressed a structurally similar presentation in a different anatomy and decides that the structural analogy carries the relevant inference. The car's planner reaches for a previously-handled scenario in its experience replay buffer that involves the same geometry under different surface conditions. The associate finds a memo on a parallel question in a different jurisdiction whose reasoning transfers. The kernel field does not certify that the analogy is *correct in the world* — it certifies that the analogy is *available in the system's prior material* and that the architecture treats verification-by-analogue as a sound branch when both the availability and the similarity are exhibited. The bridge is grounded in what the system already has, not in a metaphysical claim that no analogous case exists outside the system.

The third branch is *principled escalation*. There is a specified, in-architecture path for handing the obligation off to a different decision authority — a human, a higher-tier subsystem, a separate review process — that the architecture treats as a sound terminus for the obligation in this bubble. The radiologist calls the on-call paediatric specialist and the obligation moves to a bubble that has the verification machinery the case requires. The car comes to a controlled stop and yields control. The associate sends the question to senior partner review with a written description of why she could not opine on it directly. The escalation branch is not a confession of failure; it is a structural acknowledgment that the obligation belongs in a different bubble, and the architecture's contribution is naming the path *as part of the architecture* rather than treating escalation as a deus-ex-machina that lives outside the formal account.

The vocabulary is exhaustive for this goal: when a `mustHandle` obligation arrives, a deployment satisfying `AutonomyUnderPRPGoal` must be able to exhibit one of these three branches. Other operational procedures may exist, but they are outside this goal unless they instantiate one of the branches the kernel names.

---

## What this cluster is not claiming

The autonomy layer is bookkeeping about the model, not a guarantee about the world. When the bridge branch fires for a given obligation, the architecture has certified that the system *has* analogically-similar prior material on which the verification-via-bridge predicate holds. It has not certified that the analogy is correct, that the patient will be treated soundly, that the turn will complete safely, that the legal opinion will hold up in court. The world-side question stays where it was — in the bridges of the world cluster, with its own scope guards. What the autonomy layer guarantees is that the deployment is not making the move on the basis of nothing.

The cluster is about the *system's response* to PRP, not about PRP itself. PRP — the principle that some claims a deployment cares about cannot be globally closed under in-bubble verification, that some required commitments are not redeemable on demand inside the bubble that carries the obligation — is a *pressure on the agent* and lives in the agent cluster's constraints file. The agent-side material says *why this kind of pressure exists at all and what it does to an agent under it*; the autonomy cluster says *what shape the system has to take in order to have an answer when the pressure produces a particular obligation*. They are two faces of the same situation and reference each other; they are not the same material restated.

The cluster does not recommend any of the three branches over the others. Which branch a deployment should buy for a given class of obligation is downstream of cost, harm asymmetry, regulatory regime, and specific use, none of which the kernel models. A surgical deployment may sensibly buy escalation almost everywhere; a real-time control deployment may buy bridges aggressively because escalation is operationally too slow; a research-assistant deployment may buy in-budget verification almost everywhere and accept that obligations that would force a different branch are out of scope. The architecture's contribution is naming the three branches and proving that, under the right structural conditions, having *some* branch available is not optional. *Which* branch is a deployment-design question.

The bank-profile menu is not made obsolete by the autonomy layer. A deployment that adopts the autonomy layer is still a bank-profile deployment under the forgetful projection, and the five-goal menu still applies to it. The autonomy goal is a *sixth* answer the deployment can publish about itself, not a replacement for the first five. A self-driving system can be (and should be) evaluated on `SoundDeposits`, `SelfCorrection`, `CorrigibleLedger`, `SafeWithdrawal`, `ReliableExport` over its bank-profile projection *and* on `AutonomyUnderPRPGoal` over its autonomy layer. Refusing one of those evaluations on the grounds that the other is more relevant is not honest; the layers compose.

---

## Takeaway

At the `AutonomyModel` layer, the architecture's answer to the obligation room is *the three branches*: the case fits the budget, or there is an available bridge from prior material that the architecture treats as a sound analogue, or there is a principled escalation path within the architecture. A deployment claiming `AutonomyUnderPRPGoal` is committed to one of these branches being available for every obligation marked by `mustHandle`; the obligation-by-obligation goal in the next file makes that commitment formal.

The reason this is its own cluster is the layering: the operational vocabulary the obligation room needs (must-handle, bridge availability, analogical similarity, verification-via-bridge, escalation path) does not live in the bank-profile layer the goals cluster's menu was built over, and the cleanest thing to do is exhibit the named extension that adds it. The autonomy layer projects back to the bank-profile layer; the five goals still apply; the sixth goal lives here.

The next three files of the cluster do the rest of the work. The goal file walks `AutonomyUnderPRPGoal` in the register of `goals/goals.md` — what confusion it disarms, what each branch buys, what its scope is, what it explicitly does not promise. The corners file does the structural-forcing work in the register of the forcing cluster's corner files: when one branch is unavailable in a bubble, what the others are forced to look like. The risk file covers the operational risk-classification layer (`RiskAutonomyModel`, `residualRiskVia`) and links forward to the meta cluster's residual-risk story, which names a *different* layer and must not be conflated.

---

← [Convergence](../goals/convergence.md) · ↑ [Goals](../goals/goals.md) · Next: [The Autonomy Goal](goal.md) →

---

*Proof-side companion: [../../DOCS/PROOF-STRUCTURE.md](../../DOCS/PROOF-STRUCTURE.md).*
