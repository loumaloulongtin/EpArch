# When the Engine Comes Under Coordinated Pressure

*[← The Bakery](lifecycle.md) · [← What the Lifecycle Cannot Do by Accident](safety.md)*

---

## In this series

- [The Bakery Story](lifecycle.md) — the lifecycle as the operational engine
- *steps/* — one file per recordable event, walked through one developing case
- [What the Lifecycle Cannot Do by Accident](safety.md) — the safety guarantees the engine ships
- [When the Engine Comes Under Coordinated Pressure](under-attack.md) — the engine under coordinated pressure *(you are here)*

---

## A different scene

This file leaves the bakery. The bakery has been good to us — small enough that every loaf is visible, slow enough that every challenge can be walked through. But the bakery cannot stage what this file needs to stage. Some failure modes only appear when the engine is being pushed, deliberately, on every channel at once.

So a different scene. A regional approach-control sector, the airspace where en-route traffic is handed off to terminal control. Ten or fifteen aircraft within a few minutes' flying time of one another. Separation minimums measured in seconds and nautical miles. Every aircraft on the controller's scope is, in the lifecycle's terms, a deposit: it carries a claim (this is United 412, at this altitude, on this heading), provenance (where the claim came from — primary radar return, secondary radar interrogation, transponder, ADS-B), a temporal validity window (a track update is good for a small number of seconds before it must be refreshed), and an error model (radar uncertainty, transponder lag, known equipment quirks). The controller's job is to decide, every few seconds, whether to authorize a maneuver against this scope. The lifecycle's per-step gates are doing real work: a withdrawal — a clearance issued — has its preconditions; a challenge — a TCAS resolution advisory, a primary/secondary mismatch — has its preconditions; a repair — the controller asks the pilot to re-squawk and gets a clean response — has its preconditions.

On a normal day this works. Single-move-at-a-time attacks are exactly what the per-step gates are good at. A spoofed transponder identity in isolation produces a primary/secondary mismatch — a challenge fires, the track is quarantined, the controller asks for a re-squawk, repair fires or revoke fires. The lifecycle responds with a sequence of attributable events, each with a precondition the kernel proves the constructor enforces.

Today is not a normal day. Today the sector is under coordinated electronic-warfare pressure. The scene is not offered as a claim about any particular real incident; it is a vehicle for the kernel's adversarial vocabulary. The attack does not pick one of the controller's verification channels and break it. It pushes against all of them at once.

---

## What "all at once" looks like

The first symptom is volume. The radar correlator begins receiving more candidate tracks than it can resolve within a single sweep. Some are real aircraft, some are injected phantoms with plausible kinematics, some are amplified noise. The controller's scope, which would normally show twelve aircraft, is trying to show forty. This is the kernel's `attack_volume > channel_capacity` made vivid: the audit channel — in this scene the radar correlator and the controller's attention together — has finite capacity, and that capacity has been exceeded.

The second symptom is time pressure. Aircraft do not stop flying while the scope catches up. Decisions that the controller would have taken with thirty seconds of buffer must now be taken with five. The kernel calls this `τ_compress`: the deposit's verification window collapses to a fraction of what its TTL would normally allow. The structural cost is that the per-step verification gates the lifecycle ships still hold — they are still preconditions on every constructor — but the controller no longer has the *time* to evaluate the evidence each gate would otherwise consume.

The third symptom is spoofed provenance. Several of the phantom tracks carry valid-looking ADS-B identities — flight numbers, altitudes, headings consistent with published flight plans. To a single-channel check (does the ADS-B claim parse? is its callsign in the published schedule?) they pass. The kernel calls this `V_spoof`: the deposit's V field carries fabricated provenance that survives the cheap surface check.

The fourth symptom is consultation suppression. The controller would normally cross-reference uncertain tracks against the secondary radar feed from the next sector, against the air-defense liaison, against the airline's flight-following desk. Today every one of those channels is also under load — the next sector is seeing the same flood, the liaison's frequency has more traffic than it can route, the airline's desk is fielding identical queries from three other sectors. The kernel calls this `consultation_suppressed`: the validators that would normally be reachable are unreachable not because they have been disabled, but because they have been saturated.

The fifth symptom is the cheap-cue substitution that follows. With deep checks unaffordable and consultation unreachable, the controller is forced to triage on signals that fit in the time budget: callsign plausibility, vector consistency over the last two sweeps, gut feel about what kind of aircraft the radar return looks like. The kernel calls this `amplify_cues`: the proxy signals that would normally be supporting evidence become the *only* evidence, because the expensive evidence cannot be reached.

The sixth symptom is the expertise gap exploited. A junior controller, working a sector they would normally be backed up on, cannot reliably distinguish a cleverly-constructed phantom from a real aircraft. The senior watch supervisor can — but the supervisor is one person and the sector now has dozens of pseudo-decisions per minute waiting on judgment.

These six symptoms together are what the kernel names `FullStackAttack`. The kernel's `attack_succeeds` predicate gives the structural condition: the attack succeeds when `τ_compressed` holds *and* the V-side failure clause fires — represented by the disjunction `V_spoofed ∨ consultation_blocked` — *and* `cues_amplified` holds *and* `expertise_exploited` holds. Each of those is a real, distinct mechanism. The architecture's claim is that they compose: the attack does not need any single one to be devastating, it needs all of them to fire at once, and the controller — like the kernel — has no per-step gate that defeats the conjunction by itself.

---

## Why the per-step gates do not catch this

This is the architectural payoff of having walked the per-step gates first. Each constructor's preconditions handle the single-move-at-a-time attack on its own channel. `Submit` can always record a candidate entry. `Promote` only requires that the slot is currently `Candidate`. Any substantive standards check that makes promotion responsible is deployment-side validation around the kernel step, not a kernel precondition. At the lifecycle level, `Withdraw` only records reliance against a slot that is currently `Deposited`. Stronger reliance gates — ACL admission, temporal validity, consultation, cross-checking — belong to the surrounding policy an implementation may wrap around `Step.withdraw`. The per-step gate theorems say exactly that the kernel will not let a constructor fire without its preconditions being satisfied.

What the per-step gates do not protect is the *capacity to verify* the preconditions. At the lifecycle level `Withdraw` records that the slot was live; stronger deployment-side checks may require consultation, ACL admission, or temporal validity. Under coordinated pressure, those surrounding checks are where capacity collapse bites. The kernel-level step can still say exactly what it says: if withdrawal fires, the slot was live. It does not prove that every richer deployment-side check was reachable or completed. Operationally the controller is left with an incoming track they can neither approve nor reject in the time they have.

This is a structural fact about the architecture: the per-step gates are preconditions on individual constructors, and the safety theorems are properties of trace shapes. Neither vocabulary, on its own, can describe what happens when verification *capacity* is exhausted. The vocabulary that does is the one this file works in — the kernel's adversarial layer.

---

## The kernel's vocabulary for capacity exhaustion

The adversarial layer carries the predicates this scene needs. `AuditChannel` is the abstract resource through which verification is performed; `channel_capacity` and `attack_volume` are its two relevant numbers; `channel_overwhelmed c` is `attack_volume c > channel_capacity c`. Lifted to the agent level, `verification_collapsed a channels` says the agent has at least one audit channel and *every* channel they have is overwhelmed. The structural definition is exactly what it needs to be: the agent has not lost a channel they never had (an agent with no channels was never verifying); the agent has lost the use of every channel they did have.

Once `verification_collapsed` holds for an agent, and once a deposit's τ has been driven to zero by the collapse, the architecture proves a structural consequence: there is no `PathExists` witness for that deposit. The theorem `collapsed_to_path_failure` is purely structural — no world assumption is consumed — and it shows that under verification collapse plus τ = 0 at a deposit, no `PathExists` can be exhibited. Formally, the contradiction is carried by τ-zero: `PathExists` requires `d.h.τ > 0`. The collapse hypothesis explains where the τ exhaustion came from; the τ-zero equality is the immediate blocker. The verification path, in the kernel's sense, has been destroyed.

The link between channel saturation and τ-exhaustion at a particular deposit is the one piece the kernel keeps as a separate hypothesis rather than baking into a single bundle. The reason is honest: that link is the arithmetic bridge between population-scale capacity exhaustion and per-deposit window collapse, and that arithmetic depends on richer agent structure than the bare adversarial layer carries. The kernel exposes it as `h_exhausts_tau` — "if verification has collapsed, then this deposit's τ window is zero" — and uses it explicitly in the chain theorems. The architectural meaning is that the chain from DDoS to path failure is not a single inevitability; it is two structural facts joined by a hypothesis the deployment must be willing to assert.

The kernel's adversarial-obligations layer then ties two structurally distinct attack chains together. The Rolex chain — single-deposit τ compression — produces τ = 0 directly. The DDoS chain — population-scale capacity exhaustion plus the τ-exhaustion bridge — produces τ = 0 indirectly via verification collapse. The theorem `rolex_ddos_share_path_failure_structure` proves that both chains end at the same architectural place: no `PathExists` for the affected deposits. Two different attacks, the same structural failure. The architecture treats them as the same kind of failure not because it cannot tell them apart — the trace evidence is different, the W-bundles are different, the chains in the proof tree are different — but because the *consequence* the deployment cares about is the same.

---

## The chain to centralization

What does the controller do when verification has collapsed? The kernel proves the next move is structural too. The world-bundle `W_collapse_centralization` carries the conditional claim that exhausted agents seek delegation: when verification fails, the behavioral path of least resistance is to defer to a single trusted authority. The full obligation theorem `ddos_to_centralization_of_W` chains any of the four DDoS vectors all the way to `trust_centralized a`.

In the scene, this is the supervisor taking the boards. The controller has stopped trying to verify individual tracks and is now executing whatever clearances the supervisor approves. The system has a single bottleneck where it used to have a layered verification stack. The architectural concern is not that delegation is wrong — sometimes delegation is the correct emergency response — but that the move *from layered verification to centralized authority* is what the attacker was trying to produce. The attacker did not need to corrupt the controller. They needed to make verification expensive enough that the controller would stop attempting it, and the kernel proves that this is what coordinated capacity attacks do by construction, *given* the world-bundle assumption that exhaustion produces delegation.

The architectural reading of the centralization chain is that it makes the attacker's *goal* a structural prediction, not an empirical accident. The DDoS chain is not a story about how attacks happen to succeed sometimes; it is a theorem that says, given `W_ddos_full` and its assumption that exhaustion produces delegation, every DDoS vector ends at a centralized-trust state. The conditional shape of the theorem is load-bearing here: a deployment that disputes the W-assumption — that argues *its* agents do not delegate under exhaustion — has to discharge the bundle differently, and the architecture exposes exactly which assertion is in dispute.

---

## What the architecture promises and what it does not

The architecture's promise here is narrow and worth stating exactly. It promises that the failure modes coordinated pressure produces are *named*: `verification_collapsed`, `attack_succeeds` for FullStackAttack, `trust_centralized` as the consequence of collapse, `PathExists` as the structural witness whose absence the path-failure theorems prove. It promises that the chains between these are theorems, not narratives — the deployment cannot be surprised by a DDoS-to-centralization outcome and call it an unforeseeable accident, because the kernel has already proved that the chain is structural and named the assumptions on which it depends.

It does not promise that the attacks can be prevented. The W-assumption bundles are explicit: each obligation theorem is conditional on a world-bundle that names exactly the assumption being made about the world (provenance can be spoofed, channels can be overwhelmed, exhausted agents do delegate). A world that satisfies these bundles is a world in which the attacks are possible. The architecture's contribution is not to legislate the world out of these conditions; it is to make sure that, *when* the world satisfies them, the architecture's predictions follow as theorems and not as guesses.

This is what the residual-risk layer is for. EpArch's `ResidualRiskMitigation` taxonomy names structural failure modes that remain architecturally visible even after the ordinary mechanisms are present — among them `staleness`, `provenanceGap`, `adversarialImport`, `unrevokedDefect`, `overbudgetReliance`. Each is named because the operating regime forces it: bounded verification plus PRP plus novel inputs cannot, by construction, eliminate them. The layer is a coverage and diagnosis tool, not an elimination theorem. The architecture's mechanisms *cover* each mode in the sense that each mode has a designated mitigation; a deployment that has assembled every mechanism will still see the modes appear under coordinated pressure, because the modes are properties of the regime, not gaps in the implementation.

The under-attack reading of residual risk is that coordinated pressure is what makes these modes operationally visible. On a normal day a deployment can run with the residual-risk modes *covered* in the architectural sense and never see them; under coordinated pressure the modes become the dominant failure surface. The architecture's contribution is to have *named the modes ahead of time*, so that when they appear, the deployment knows what it is looking at and which of its mechanisms is the designated mitigator. The mode does not become a surprise. The chain from coordinated attack to verification collapse to centralization to the specific residual-risk surface is, for the deployment that has done its homework, the predicted shape of bad days — not a mystery to be diagnosed afterward.

---

## What the architecture does not buy here

A few clarifications, because the under-attack vocabulary is rich enough to be misread in either direction.

It does not buy that DDoS implies centralization unconditionally. The chain `ddos_to_centralization_of_W` is conditional on `W_ddos_full`, and that bundle carries the explicit assertion that exhausted agents delegate. A deployment whose agents respond to exhaustion differently — by halting, say, instead of delegating — does not satisfy the bundle, and the chain's conclusion is not entailed for that deployment. The chain is a theorem about a world-shape, not a theorem about the world.

It does not buy that the controller is at fault for the centralization. The architectural reading is the opposite: the centralization is what the attacker was trying to produce, and the controller's behavior under exhaustion is the path of least structural resistance. Naming the chain as a theorem is exactly what shifts the analysis from *the controller failed* to *the attack succeeded along its predicted route*.

It does not buy that the per-step gates were the wrong defense. The per-step gates do exactly what they claim to do — they catch single-move-at-a-time attacks, and they continue to do so under coordinated pressure for the moves that still complete. What they do not do is provide capacity. The under-attack layer is what carries the capacity vocabulary; the per-step layer is what carries the move-shape vocabulary. They are complementary, not in competition, and the architecture would be incomplete without either.

It does not, finally, buy any specific real-world claim about ATC, electronic warfare, or any other domain the scene draws on. The scene is a vehicle for the kernel objects; whether any particular sector is currently under attack, and what the attacker's capabilities actually are, is the deployment's empirical problem. The architecture's contribution is the vocabulary, the chains, and the explicit world-assumptions on which the chains depend.

---

## Takeaway

The lifecycle's per-step gates handle state-shape incoherence: a withdrawal cannot be recorded against a non-Deposited slot, a challenge cannot be recorded against a non-live slot, a repair cannot be recorded against a non-Quarantined slot, and so on. They do not, by themselves, catch every spoof, forgery, or out-of-policy act. Those richer checks belong to the surrounding validation and reliance policies. Coordinated pressure attacks that surrounding capacity: it exhausts the ability to evaluate the richer checks in the time available. The per-step gates do not, on their own, model or absorb coordinated capacity pressure. Coordinated pressure does not violate any per-step gate; it exhausts the capacity to evaluate the gates in the time available. The kernel's adversarial layer carries the vocabulary for that regime — `AuditChannel`, `channel_overwhelmed`, `verification_collapsed`, `attack_succeeds`, `trust_centralized` — and the obligation theorems prove that the chains between them are structural, not accidental, conditional on world-bundles the architecture exposes by name.

The architecture's promise under attack is not safety from attack. It is that the failure modes are *named*, the chains between them are *theorems*, the assumptions on which the chains depend are *explicit*, and the residual risks that remain even under full compliance are *predicted ahead of time*. A deployment that has internalized this layer is not a deployment that cannot be attacked. It is a deployment that, when attacked, is not surprised by which way the architecture says the attack will resolve.

The next cluster — *agent/* — turns the lens to private state. The shared-substrate story this cluster has just walked, including the engine that operates on it under coordinated pressure, is one half of what the architecture commits to; the other half is what an agent's relation to a claim looks like — the per-claim, per-agent stance vocabulary the architecture supplies once the substrate is in place. The forcing story for why both clusters have the shape they do is taken up after the agent cluster has put the second half on the table.

---

*[← The Bakery](lifecycle.md) · [← Safety](safety.md) · [The Night Nurse Story →](../../../agent/agent.md)*
