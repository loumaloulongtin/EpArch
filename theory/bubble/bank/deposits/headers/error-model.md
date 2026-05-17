# The Throw Story

*[← Standard](standard.md) · [Provenance →](provenance.md)*

---

## Why the error model is the hardest field to maintain — and the most teachable

Of the fields that make up a working deposit, the error model (E) is the most difficult to keep accurate and the most expensive to expand.

S is a gate: the claim is accepted under these standards or it is not.  
V is a chain: the provenance is grounded or it is not.  

E is a *model* — a list of plausible ways the claim could fail, weighted by likelihood and consequence. It scales with the stakes, shifts as the world pushes back, and is rebuilt when the context changes.

The right error model for one agent and one task can look comically thin compared with the error model another agent needs for what looks like the same task.

E is also where the agent's history shows up most directly. It is the field that grows through direct teaching, trial-and-error, and **pattern matching** as the agent's personal ledger of past deposits accumulates.

---

## Same proposition, wildly different error models

Someone picks up a ball (or a rocket). They want to send it to a precise target.

The working deposit is:

* **P**: I can launch this object and get it to land wherever I want.  
* **S**: A successful launch under controlled conditions counts as evidence I can do it again.  
* **E**: (this is where the models diverge)  
* **V**: I am the one launching it, using my own hands or my own equipment.

The proposition stays identical. A reader might object that "throwing a ball" and "docking a supply ship" are obviously different claims — but formally both are *I can send this object to a target*. Holding P fixed is the point: it isolates what E must do at different levels of consequence and competence. What changes is how rich and cautious the error model must be before the deposit can clear the standard and move the ladder.

---

## Case 1 — The kid learning to throw

A child is in the backyard with a tennis ball. The target is a patch of grass twenty feet away.

The child’s error model at the start is simple and lightweight:

* **E**:  
  * I might throw too hard or not hard enough.  
  * I seem to pull a little to the left every time.  
  * My arm might get tired after a few throws.  
  * The ball might hit a tree branch or a gust of wind might push it.

This E is updated after every single throw. The kid throws, watches where the ball lands, feels the feedback in the arm, and immediately revises the model. The redeemability path is cheap and fast: launch → observe landing → update E.

The deposit is good enough for the stakes. The child keeps throwing, refining the model in real time.

Now the dad raises a challenge. He does not say the proposition is false. He does not attack S or V. He says:

> “Bend your knees a little!”

That challenge is pure E-refinement. It adds a new term to the child’s error model: “My stance might be too stiff, costing me power and accuracy.” The child tries it, sees the improvement, and the deposit gets stronger. Over weeks and months the error model stops being a list of guesses and becomes a growing, pattern-matched library of failure modes the child can anticipate before the ball even leaves the hand.

---

## Case 2 — The space agency launching a supply ship

Now change only the stakes.

The same proposition — “I can launch this object and get it to land wherever I want” — is now being made by a space agency sending a cargo vessel to dock with the International Space Station.

The error model here is orders of magnitude richer and must be built *before* any launch:

* **E** (vastly expanded):  
  * Atmospheric turbulence, wind shear, and jet-stream effects during ascent.  
  * Thermal expansion and contraction of fuel lines and structural components.  
  * Guidance-system sensor drift, software timing bugs, or bit-flip radiation errors.  
  * Orbital mechanics perturbations from solar pressure, lunar gravity, or space debris.  
  * Failure cascades: a single valve stuck open could drain propellant and make docking impossible.  
  * Human factors: a technician miswiring a connector during final assembly.  
  * Unknown-unknowns that only exhaustive simulation and redundancy can bound.

Trial-and-error is not an option. “Launch it and see where it lands” would be catastrophic. The redeemability path is deliberately closed during the critical phase. Instead, the agency spends years building simulators, running Monte-Carlo analyses, adding triple-redundant systems, and stress-testing every component so the error model can predict failure modes with extreme confidence *before* the button is pressed.

The deposit still has the same P. But the E field is now so thick and so conservative that only a tiny handful of organizations on Earth can even write it down, let alone maintain it.

---

## What this shows

Same proposition, same physical act, unrecognizably different error models — both fitted to their context. In the backyard, a lightweight E updated after every throw. At the launch pad, an exhaustive predictive E built before the button is pressed.

The kid and the space agency are not using different architectures. They are at different points on the E-maturity curve: a thin, rapidly updating ledger versus a thick, heavily pattern-matched one. The architecture is the same; the ledger depth is not.

E is also where targeted criticism lands. A challenge of the form

> Your E here is too thin for these stakes. You haven't modeled cross-contamination / sensor drift / wet-grass effects.

does not attack the proposition. It points at the field that needs more weight.

---

## Takeaway

A thin E is not automatically a weak E. An agent with a deep ledger who says "my E here is deliberately lightweight — the feedback loop is fast and the stakes are low" carries a different deposit than an agent making the same written claim with no track record. A receiving agent can weight E-challenges against the sender's demonstrated history, not only against the E on the page. (The Bank itself only reads what is in the headers; cross-agent reputation lives at the receiver, not in the substrate.)

# The Throw Story — Part 3

## A third source of E-growth

Parts 1 and 2 showed two ways an error model expands.

The kid expands E through **feedback**: throw, observe, update. Each cycle adds a term grounded in something that just happened.

The space agency expands E through **preemptive modeling**: simulate, stress-test, derive failure modes from physics and history before any launch.

These are both the agent's own work. The agent owns the additions. The agent can audit them.

There is a third way E expands: **another agent inserts a term from outside.**

Sometimes this is benign. A senior engineer says "watch out for thermal expansion in that joint" and a new term enters E that the junior engineer would not have generated alone. The challenge in Part 1 — "Bend your knees" — was exactly this. Externally injected E-terms are how teaching works.

But the channel that lets a teacher expand E is the same channel an adversary can use. The architecture does not know whether the inserted term is true or motivated. It only knows the term is now in E and has to be weighed.

A **threat** is the adversarial use of that channel.

---

## Same P, same S, same V, same own-E — only the injected term changes

A junior employee is asked by a coworker to sign off on a minor expense report that looks a little sloppy.

The employee's working deposit, sitting on their own desk:

* **P**: This report is accurate enough to approve.
* **S**: For a small internal expense, a quick glance and a signature are enough.
* **E** (the employee's own): There might be a small error, but nothing serious.
* **V**: The coworker who prepared it.

The employee is leaning toward signing. Acting on the deposit is cheap; the worst case from a flawed expense report is small.

Hold the entire deposit fixed.

Now run two scenarios that differ only in what the coworker says next.

**Scenario A — Honest pushback.**
The coworker says: "Actually, double-check the dates against the trip itinerary. I think I might have copied the wrong column." A new term enters E: *"I may have mis-keyed dates."* The employee checks, finds the error, and the deposit is repaired before signing. E grew. The growth was useful. This is the same shape as the dad's "bend your knees" — externally inserted, evaluable, productive.

**Scenario B — Threat.**
The coworker says: "If you don't just sign it and move on, I'll tell the whole team you were the one who messed up last quarter's numbers." A new term enters E: *"refusing to sign produces social punishment unrelated to whether the report is accurate."* P has not been challenged. S has not been challenged. V has not been challenged. The employee's own E has not been challenged. Only the externally injected term differs.

The injected term in B is doing exactly what the injected term in A did — it expanded the error model. What is different is the term's *content*: in A it concerns whether P is true, in B it concerns whether *acting on the deposit* triggers an unrelated harm.

The architecture treats both the same way. E is a model; new terms get weighed. That is precisely what makes the attack work. Many agents will sign the report in scenario B not because the report became more accurate but because the dominant term in E is now the social punishment, not the small probability of an expense error.

---

## Why the attack uses E and not S, V, or P

P, S, and V are claims the architecture can dispute on their merits. *"This report is accurate"* can be argued. *"For a small internal expense a glance is enough"* can be argued. *"The coworker prepared it"* can be argued.

E cannot be argued the same way, because E is a *list of failure modes the agent should consider*. A new candidate term cannot be dismissed for being uncomfortable; the discipline of E is exactly that uncomfortable terms must be admitted if they are real. The attacker exploits this discipline. They submit a term — *"refusing produces social punishment"* — that is, in fact, true. The harm really would happen. The error model has no principled way to refuse it.

The threat does not corrupt E. It uses E correctly. That is what makes it surgical: the same architectural property that lets the kid get better at throwing and the space agency avoid disasters is the property the threat rides on.

---

## Part 3 takeaway

E grows from three sources: the agent's own feedback, the agent's own preemptive modeling, and externally injected terms from other agents. The first two are auditable by the agent. The third is not, in the same way — the agent can only ask whether the inserted term *would* be true, not whether the inserter is acting in good faith.

A threat is the adversarial form of external E-injection. Its signature is the one shown above: P, S, V, and the agent's own E remain untouched, and only the injected term changes between the honest-teaching scenario and the coercive scenario. The mechanism is "if you act on this deposit, an unrelated harm will follow," and the term is added to E correctly — that is the point.

The same channel that lets teachers expand learners' error models lets adversaries hijack them. The architecture does not seal the channel. It cannot, without also sealing teaching. What it can do is make the *source* of each E-term part of the term itself, so the agent at least sees that this particular failure mode entered through coercion rather than evidence.

---

*[← Standard](standard.md) · [Provenance →](provenance.md)*