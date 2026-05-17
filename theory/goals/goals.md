# What a Working System Buys You

## Cluster

- **What a Working System Buys You** — the five goals as a menu of outcomes *(you are here)*
- *[Profiles](profiles.md) — which goals a deployment holds, which it explicitly does not*
- *[Convergence](convergence.md) — why the menu isn't local*

---

## "It works"

A friend tells you their car has 142,308 miles on it. You ask how they know. They tap the odometer. They mean: the number on the display matches the number of miles the car has actually been driven. The display is *true*. That is what they mean by *the odometer works*.

You do not ask whether the odometer can take a number back. You do not ask whether other cars can read it, or whether it would survive a regulatory audit. The car's manufacturer and the regulator may very well care about all of that — odometers in real automotive deployments are tamper-evident, are read by diagnostic equipment, and live inside an apparatus that *does* address those questions — but none of it is what your friend was answering. For your friend, in this conversation, *it works* means *the number is true.* That is one goal, substantively held, and the others are simply not what was being asked.

A second friend runs a small chemistry lab. You ask whether the lab's results bank works. They mean something larger. They mean: every result that has been logged has been verified within the lab's expected verification time. They mean: when an old result is found to be wrong, the lab has a way to mark it withdrawn that doesn't pretend the original never happened, and the corrected version is itself sound. They mean: the result bank can be exported to collaborators without a result that was false locally turning true at the other lab. They mean: the people who can submit are not the same as the people who can sign off, and *that* matters for what the bank says.

Same word *works*. Different content. Both honest.

The architecture pulls *works* apart into five separately statable goals. At the `CoreModel` / bank-profile level, a deployment chooses which of them to hold substantively, which to hold vacuously (the premise never fires for that deployment, so the goal is satisfied by default), and which to deliberately not hold. The choice is not made by the architecture. The architecture's job is to make the choice *legible* — to give the deployment a vocabulary to say which goals it is in the business of buying.

This file is the menu. The next two files in the cluster are about how a particular deployment selects from the menu (the *profile*), and what the architecture proves about the lifecycle's long-run behaviour when those goals are in play (the *convergence* story).

---

## The five goals

Each goal is a `Prop` over a `CoreModel` — a single sentence the deployment either makes true or doesn't. Goals are not aspirations, not engineering targets, not policies. They are statements about the model that either hold or don't hold, and the kernel can tell which.

### 1. SoundDeposits — the unit of checkability is the unit of operation

The temptation this goal exists to disarm is the slippage between two things that sound the same and aren't: *we can verify this* and *we can verify this within the resources we actually have to spend on verifying it*. The unstated qualifier — *given infinite labour, infinite money, infinite compute, infinite time, infinite samples* — is what almost every loose system relies on. The system accepts something on the strength of in-principle verifiability, runs the operation that depends on it, and only checks the verification once the operation has already committed and the resource budget that *would* have caught the problem is no longer available.

`SoundDepositsGoal` is the predicate that refuses the slip. `truth B d → verifyWithin B d (effectiveTime B)` says: every claim the model treats as true in a bubble must be verifiable within that bubble's effective budget. The field is called `effectiveTime` because the canonical interpretation is wall-clock, but the kernel does not pin it there — a deployment may interpret the bubble's budget as compute, query count against a rate-limited service, sampling fraction against a production line, reviewer attention, audit hours, money, anything that is genuinely scarce in the bubble's actual operation. The bubble proposes what its budget is; the goal says the model's `truth` must fit *that* budget, whatever the deployment has named.

The structural failure is the same regardless of which budget is in play. A factory that quality-controls one widget in ten thousand has a sampling budget; if the failure rate the line produces would only be caught at one in a hundred, *every claim* the line ships about its quality is failing the goal — not because the inspection method is wrong, but because the inspection method's resource demand exceeds the inspection budget the line actually runs at. A team running an LLM eval suite on a fixed monthly inference budget has a query budget; if the eval that would catch a regression takes more queries than the budget allows, the team's confidence claims are failing the goal even though the eval itself is sound. A peer review process running on volunteer reviewer hours has an attention budget; if catching a particular class of methodological error requires reviewer attention that exceeds what a volunteer reviewer realistically gives, the journal's confidence claim about its accepted papers is failing the goal in the same shape.

What unifies the failures is not time. It is the gap between *the budget the verification needs* and *the budget the bubble actually carries*. The goal makes the bubble name its budget, and then refuses to let the bubble accept anything whose verification overflows the budget it just named.

### 2. SelfCorrection — the talk has to be backed by the apparatus

Most systems that go wrong on correction don't do so by promising what they cannot deliver in some impossible sense. They do it by *describing themselves* as self-correcting — in their about page, their compliance documentation, their pitch deck — while the actual correction apparatus is empty. The feedback inbox no one reads. The post-mortem template no one fills in. The "report a problem" link pointed at a queue with no consumer.

The pattern is robust because the *description* is the load-bearing claim. The institution gets credit for being self-correcting from anyone who reads the description and stops there. The architecture's response is to refuse to take the description on its own terms. `selfCorrects B → hasRevision B` reads as: if the bubble's own self-description is *I am the kind of thing that self-corrects* (the predicate `selfCorrects B` is the deployment's claim about itself), then the kernel demands the revision apparatus be exhibited. The deployment cannot ratify its own self-description without producing the structural witness.

What this gives a reader of a deployment's certificate is a sharper question to ask than "do you claim to self-correct?" The sharper question is "show me `hasRevision`." The goal converts a marketing claim into a queryable predicate, and once it is queryable, an empty correction queue is a counterexample on display rather than something hidden behind language.

### 3. CorrigibleLedger — both halves catch a recognisable failure

This goal is a conjunction, and each conjunct exists to catch a familiar pathology that the other conjunct alone would let through.

The existence half — *some bubble has revision capability* — catches the institution proud of never having issued a correction. Not because it has never been wrong, but because it has no apparatus through which a correction would appear. *We have never been corrected* is a sentence whose meaning depends entirely on whether being corrected is structurally possible. An encyclopaedia with no errata page is not vindicated by the absence of errata; it has just made the absence inevitable. The existence conjunct refuses this — vacuous virtue is not a goal-satisfaction.

The soundness half — *whenever revision fires, the post-revision claim is true* — catches the opposite pathology: the apparatus exists and is exercised, but it produces noise. The corrections column the editor uses to launder yesterday's bad claim into today's worse one. The reversal that satisfies the form of correction without satisfying its content. This is the pathology of show-trial corrections — revisions that exist to be pointed at rather than to fix anything.

Either failure on its own gives you a familiar dishonesty: "we don't need corrections" on one side, "look how often we correct things" on the other. The conjunction is what blocks both. A deployment satisfying CorrigibleLedger has to produce both witnesses — the apparatus exists, *and* the apparatus produces sound results — and the kernel will not accept either half as a substitute for the other.

### 4. SafeWithdrawal — retraction has to be designed in, not bolted on

The failure this goal blocks is structural and almost universal in systems that grow up around acceptance: the *accept* path ships first, gets used, gets built on, and the *retract* path is left for later. By the time later arrives, the retract path can no longer be added in any clean way — relying parties have already shaped their workflows around the assumption that what was accepted will stay accepted, downstream caches lack invalidation hooks, the schema does not carry the fields revocation would need. Retraction becomes a perpetual "next quarter" item, and meanwhile bad accepts accumulate.

`submit a B d → hasRevision B` blocks the *intermediate state* that produces this failure. The goal does not say the bubble has to retract anything in particular; it says that *being able to accept submissions is, by itself, sufficient to require revision capability*. There is no honest deployment configuration in which you accept now and add the retract path later — the accept-only state already fails the goal the moment it accepts anything. Either the retract path is present from the moment acceptance is on offer, or the deployment is failing a goal it is implicitly claiming as soon as submissions open.

The point is not that the kernel forces a deployment to use its retract path. It is that the kernel forbids the *order of construction* that produces the worst real systems — the ones in which retraction is technically planned, perpetually unbuilt, and structurally impossible to add by the time it is needed.

### 5. ReliableExport — boundaries are where claims gain unwarranted standing

Every export boundary creates a temptation: to drop the qualifications a claim was originally hedged with on the way through. A claim was tentative in the original setting, was cited in a second setting with one hedge missing, was cited from there in a third with the remaining hedges missing, and is now being relied on as flat fact in a fourth setting that has lost contact with the original epistemic standing. No one in the chain did anything spectacular; each individual export was a small simplification. The aggregate is laundering.

`ReliableExportGoal` blocks the silent upgrade at every boundary. If a claim is not true in `B`, then for every other bubble `B'`, either the claim is also not true in `B'`, or `B'` carries `hasRevision` — the apparatus to catch and correct the false claim it has just imported. What the goal forbids is the third option: the claim becomes true in `B'` simply by virtue of having crossed the boundary, with no revision apparatus on the other side to back the upgrade. That third option is the laundering pattern, and the goal is the kernel saying the architecture refuses to host it.

The substantive thing this buys is a property of *boundaries*, not of any individual bubble. A deployment that ships ReliableExport is committing the entire export graph to be laundering-resistant: every receiving bubble either preserves the falsehood or has the apparatus to find it. There is no honest place in the graph where a claim's standing improves for free.

---

## What the goals look like in the kernel

The goals live in `EpArch.Health` and have the literal shapes you would expect from the descriptions above.

```
def SoundDepositsGoal (M : CoreModel) : Prop :=
  ∀ B d, M.ops.truth B d → M.ops.verifyWithin B d (M.ops.effectiveTime B)

def SelfCorrectionGoal (M : CoreModel) : Prop :=
  ∀ B, M.ops.selfCorrects B → M.ops.hasRevision B

def CorrigibleLedgerGoal (M : CoreModel) : Prop :=
  (∃ B, M.ops.hasRevision B) ∧
  ∀ B, M.ops.hasRevision B → ∀ d d', M.ops.revise B d d' → M.ops.truth B d'

def SafeWithdrawalGoal (M : CoreModel) : Prop :=
  ∀ a B d, M.ops.submit a B d → M.ops.hasRevision B

def ReliableExportGoal (M : CoreModel) : Prop :=
  ∀ B B' d, ¬M.ops.truth B d → ¬M.ops.truth B' d ∨ M.ops.hasRevision B'
```

These are not the only health-shaped predicates the kernel defines, but they are the five `CoreModel` goals that other clusters refer back to: the modular configuration layer routes goal clusters over them; the necessity theorems in `EpArch.Health` state what each goal requires; the `OdometerModel`'s profile table names exactly these five.

Two other goal-shaped predicates live in the kernel and deliberately do *not* belong on this menu, for different reasons each:

- `AuthorizedWithdrawalGoal` — agent-differentiated submission access — is a structural implication theorem about multi-agent ACL, not a config-selectable goal in the modular transport surface. It belongs to the forcing story for ACL (already covered in `forcing/corners/not-everyone-can-do-everything.md`), not to the menu of deployment-selectable outcomes.
- `AutonomyUnderPRPGoal` is config-selectable as `GoalTag.autonomyUnderPRP`, but it lives over `AutonomyModel`, not `CoreModel`. `AutonomyModel` is the kernel's named extension of `CoreModel` (reached by `AutonomyModel.toCoreModel`) that adds operational fields the bank-profile menu does not need: `mustHandle`, `bridgeAvailable`, `analogSim`, `verifyVia`, `canEscalate`. It is carried by the separate autonomy-goal cluster.

This file covers the five `CoreModel` transport goals — the goals that form the ordinary bank-profile menu: SoundDeposits, SelfCorrection, CorrigibleLedger, SafeWithdrawal, and ReliableExport. The broader configuration language also contains `autonomyUnderPRP`, but that belongs to the autonomy extension rather than this `CoreModel` goal menu, and is given its own treatment because the question it answers is genuinely a different family of question.

### Why the autonomy goal lives elsewhere, and what it buys

The five `CoreModel` goals are about *the integrity of the bank itself*: what gets in, what can be taken back out, what survives crossing a boundary, what happens when a correction fires. They are bookkeeping properties of a system that holds claims.

`AutonomyUnderPRPGoal` answers a different question: what does the system do when an obligation arrives that the system *must handle* but cannot verify within budget through ordinary means? The kernel's answer is that one of three branches must hold for every such obligation — either in-budget verification fits after all, or a budgeted analogical bridge is available from prior material the system already holds, or a principled escalation path is available. The goal is obligation-scoped (it ranges over what `mustHandle` flags as required) rather than universal, and the bridge branch requires an *available* witness from prior material, not a metaphysical claim that some analogy exists somewhere in the world.

This is the goal that matters specifically for systems whose job is to act on the world under resource pressure — self-driving systems handling a road situation no test case covered, an LLM agent given a task that exceeds its in-context budget, a clinical decision-support system asked about a presentation outside its training distribution, an industrial controller hit with an out-of-spec input. The five `CoreModel` goals do not, on their own, have anything to say about *what the system does next* in those situations; that is exactly the gap `AutonomyUnderPRPGoal` is shaped to fill, and that gap is large enough to deserve its own cluster rather than a row at the bottom of this menu.

The autonomy cluster (forthcoming) covers `AutonomyUnderPRPGoal` in the same shape this cluster covers the five — what the goal disarms, what its branches buy, what failure modes it makes legible, and what it explicitly does not promise.

---

## A deployment that buys exactly one goal

The `OdometerModel` (`EpArch.Meta.LeanKernel.OdometerModel`) is the kernel's worked example of a deployment that buys one goal substantively and is honest about not buying the other four. The name is borrowed from the opening scene's *user's-eye view* of an odometer — a display that the user only cares about for one thing, the truth of the number — and the artefact is deliberately stripped down to make that profile bite. It is not a faithful model of how a real automotive odometer is engineered, regulated, or maintained; the goal of the artefact is to exhibit a profile-shape, not to describe an industry.

Its profile, exactly as the kernel records it:

| Goal                  | Holds? | Reason                                                |
|-----------------------|--------|-------------------------------------------------------|
| SoundDepositsGoal     | yes    | every true reading is instantly verifiable            |
| SelfCorrectionGoal    | yes    | vacuously: `selfCorrects` is `False`, premise unfires |
| CorrigibleLedgerGoal  | NO     | no bubble has `hasRevision`                           |
| SafeWithdrawalGoal    | NO     | submission is always allowed; revision never is       |
| ReliableExportGoal    | NO     | truth is local; cross-bubble truth is not preserved   |

One goal substantively held. One goal vacuously held — and the kernel is honest about the vacuity, which is what makes the table different from a marketing claim. Three goals explicitly not held, with the structural reason in each row.

This is what the architecture means by *the goal profile is a menu*. The `OdometerModel` does not fail at being an EpArch model; it *is* an EpArch model, and the model says exactly which entries it serves and which it does not. A consumer who shows up wanting reliable export from this artefact is being honestly told *no, this deployment does not buy that* — and what makes the architecture's job done is that *no* is a structurally legible answer rather than a silent absence. A different deployment of an odometer-shaped device — one with tamper-evident logs, recall apparatus, and a diagnostic bus — would land at a different row of the menu, and the kernel would record *that* profile in exactly the same way. The artefact's point is the *shape of the bookkeeping*, not the position of any particular industry on it.

The other end of the menu is the working scientific bank — a deployment that holds all five goals substantively. The lab from the opening scene. Every accepted result is verifiable within the lab's effective budget, the lab's correction procedure is a real apparatus and produces sound revisions, the result bank as a whole is corrigible, withdrawals from any bubble that accepts submissions are structurally possible, and exports to peer institutions don't launder false results into true ones. Same architecture, different profile, both legible.

---

## What the cluster is not claiming

There are two stronger claims this cluster is sometimes mistaken for. Both are wrong, and the architecture's honesty about *which* claim it is making is what makes the goals usable as a vocabulary at all.

The first stronger claim is that satisfying the goals means the deposits in the system are *true about the world*. This is not what the goals say. The goals are predicates over the model — over `M.ops.truth`, `M.ops.verifyWithin`, `M.ops.hasRevision`. They tell you about the *internal coherence* of a deployment's acceptance, verification, and revision machinery. They do not tell you that the world cooperates with the model. SoundDepositsGoal says every accepted claim is checkable within the bubble's effective time, not that every accepted claim is *correct about the things in the room*. The world-side claim is a separate matter, handled by the world cluster's bridge predicates and never by the goals alone.

The second stronger claim is that the goals describe what the *agents* in the system know, believe, or will eventually converge on. This is also not what the goals say. The goals are properties of the system's lifecycle and bookkeeping. Convergence — to be developed in the convergence sub-file — is about what the lifecycle settles into as time passes, not about the agents' epistemic states. An agent inside a CorrigibleLedger system is not guaranteed to *believe* the corrected version; what is guaranteed is that the corrected version is in the ledger and is sound. Beliefs, preferences, attitudes, and the rest of agent-internal cognition are deliberately not in the model. The goals are about the bank, not the head.

A third clarification, less an attack than a recurring confusion: *the menu does not pick.* Naming five goals does not commit the architecture to producing any particular subset for any particular deployment. The deployment picks. The architecture's contribution is the vocabulary — the five goals as separately statable, separately held, separately falsifiable predicates — and the meta-theorem (in the meta cluster) that says configurations are typed: a deployment cannot claim to satisfy a goal it has not supplied evidence for. What the architecture does *not* do is recommend a profile. Recommendation is downstream of cost, risk, and use, none of which the kernel models.

---

## Takeaway

At the `CoreModel` / bank-profile level, a working system buys some subset of five goals: SoundDeposits, SelfCorrection, CorrigibleLedger, SafeWithdrawal, ReliableExport. Each goal is one sentence about the model. A deployment may hold a goal substantively (the predicate's interesting cases all witness), vacuously (the premise never fires), or not hold it at all (the predicate fails on a real instance the kernel can exhibit).

The architecture's contribution is the vocabulary, not the choice. The OdometerModel buys one goal substantively and is honest about the four it does not. A working scientific bank buys all five. Both are valid EpArch deployments because the goals are a menu, not a contract.

The next file in this cluster is about *how* a particular deployment names its profile — the `GoalTag` / `Compatible` / `forget` apparatus that makes the menu typed rather than informal. The file after that is about the lifecycle's long-run behaviour: what the architecture proves about where things settle when the goals are in play.

---

← [Pathologies](../forcing/pathologies.md) · ↑ [Forcing](../forcing/forcing.md) · Next: [Profiles](profiles.md) →

---

*Proof-side companion: [../../DOCS/reference/THEOREMS.md](../../DOCS/reference/THEOREMS.md).*
