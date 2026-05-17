# Transport — What Survives a Configuration Change

## Cluster

- [Meta — the architecture as a configurable kernel](meta.md)
- [Configurations](configurations.md) — typed deployment surfaces
- **Transport — what survives a configuration change** *(you are here)*
- *[Grounded Evidence](grounded-evidence.md) — the user-facing compliance API and residual risk*
- *[Falsifiability](falsifiability.md) — claims you cannot make true by saying so*

---

## "What if I change something?"

configurations.md walked the surface as it stands at a single point: a deployment's declaration, a goal-stance profile, the proof-side subset that supplies evidence for the constraints in scope. It deliberately stopped short of the question a deployment will ask the moment it is in a position to ask anything: what happens to its certificates if it changes one of those things. Adds a constraint to the declaration. Removes a goal. Replaces its model with an extended one that adds operational fields. Switches from a CoreModel goal-profile witness to an ExtModel that projects down to it. Each of those is a movement on the configuration surface, and the architecture has a precise — and in places asymmetric — answer about what travels with the deployment and what does not.

The recurring confusion this file disarms is that movement on the surface is either free (every certificate survives every change) or destructive (every certificate is voided whenever anything is touched). Neither is what the architecture says. What the architecture says is that movement has a typed answer keyed to the *direction* of the movement and the *shape* of the claim being moved. The distinction between ∀-shaped and ∃-shaped claims, in particular, is load-bearing in a way that does not collapse under prose, and the architecture's transport theorems are where that distinction is settled.

---

## The two axes movement runs along

The first axis is the model axis. A deployment's model can be extended — a CoreModel can be embedded as the projection of an ExtModel that adds fields the core did not need to commit to. The architecture's machinery for relating the two is `Compatible`: a record of commuting laws stating that the operations the goal predicates depend on agree, on the projected side, with the operations on the core side. With `Compatible` in hand, the architecture's transport theorems lift the ∀-shaped CoreModel health-goal material: `SelfCorrectionGoal`, `SafeWithdrawalGoal`, `ReliableExportGoal`, `SoundDepositsGoal`, and the universal component of `CorrigibleLedgerGoal`. The full `CorrigibleLedgerGoal`, because it also contains an existential witness, does not transport on Compatible alone; it transports on `SurjectiveCompatible`, which adds the requirement that every core-side bubble and deposit has a preimage in the extension. The asymmetry is not a quirk of the formalism. It is the difference between universal claims, which can be transported along the commuting projection laws in `Compatible`, and existential claims, which require a preimage witness in the extension. `SurjectiveCompatible` supplies that preimage witness. Transport on the model axis is exactly as generous as the shape of the claim allows, and no more.

The second axis is the declaration axis. A deployment's declaration can shrink or grow: a constraint can be added to the in-scope list, a goal can be removed, a world bundle can be acknowledged or dropped. The architecture's transport story here is bookkeeping rather than mathematics — the kernel's underlying universal theorems do not change when a declaration changes; what changes is which of those theorems the deployment's certification routes to it. A declaration that grows enables further clusters and obligates the deployment to supply the witnesses those clusters need; a declaration that shrinks disables clusters and stops claiming the corresponding theorems on the deployment's behalf. Nothing the deployment was previously certified for becomes false; what changes is what the deployment is asking the architecture to certify on its behalf, and accordingly what the deployment may export to a downstream consumer. The architecture's universal claims — over all working systems, all compatible extensions, all world bundles — sit unchanged in the kernel; the declared projection is the deployment's window onto them, and movements on the declaration axis are movements of that window.

The two axes interact, but they do not collapse into each other. A deployment may extend its model without changing its declaration: the model-axis transport theorems then license the same goal cluster on the extension's projection that was licensed on the core. A deployment may change its declaration without changing its model: the declaration-axis projection then routes a different set of clusters to the same model. The architecture treats these as orthogonal movements with orthogonal transport answers; conflating them is one of the slips the cluster's separation between configurations.md and this file is built to prevent.

---

## What transport commits a deployment to and does not

What it commits a deployment to is keeping its claims aligned with its current movement. A deployment that has moved on the model axis to an extension cannot continue to claim the existential corrigible-ledger goal on the strength of a Compatible witness alone; either the witness is upgraded to SurjectiveCompatible, or the universal-corrigible part is the part that travels and the full goal is not claimed. A deployment that has moved on the declaration axis to a smaller declaration cannot continue to export certificates for clusters its current declaration no longer enables — the underlying kernel theorems are unchanged, but the projection that authorises the deployment's exports has narrowed, and the architecture's certification follows the projection, not the kernel. Honesty about which movement has happened is a typed property; the deployment cannot drift between regimes by overlooking which axis it moved along.

What it does not commit a deployment to is permanence of any particular declaration. The declaration is the deployment's signed posture at one point on the surface; movement is allowed, expected, and accommodated by the transport theorems. A deployment that started with a small declaration and has come to face a constraint it had previously opted out of can grow its declaration to take the new constraint in, supply the witness, and obtain the corresponding certificate. A deployment that has retired a use case can shrink its declaration and stop exporting the certificates that no longer apply. The architecture does not penalise either direction; the transport theorems make both coherent.

What it also does not commit a deployment to is automatic discharge of the new obligations a movement creates. Movement on the declaration axis creates obligations as well as availabilities — taking a constraint into scope means the deployment must supply, on the proof-side surface configurations.md described, the evidence that constraint's cluster requires. The architecture's certification will not produce a forcing certificate for a constraint just because the declaration has been amended; the witness has to show up as well. Transport, here, is a precise statement about what the architecture will recognise once the work is done, not a substitute for the work itself.

What it also does not commit a deployment to is retroactive repair of state the system has already accumulated. Movement on the configuration surface is forward-looking — it changes the typed claims the architecture is willing to make from this point on, given a witness that satisfies the new posture. It does not reach back into entries the system produced under the old posture and rewrite them to satisfy the new one. A deployment that takes the bank-header constraint into scope and supplies a header-respecting witness gets the corresponding forcing certificate going forward; the deposits made before the move do not retroactively grow headers because the certification has been amended. Whether the historical entries need to be re-issued, migrated, or grandfathered is a deployment-side question the architecture does not answer; the lifecycle the bank actually runs is what produces those entries, and changing the declaration does not change what the lifecycle has already done. Transport says what the architecture will certify about the deployment's posture from here; it does not run the lifecycle backwards.

---

## What this file is not

This file is not the meta-theorem. The modularity meta-theorem in meta.md is the device that licenses the projection at every point on the surface; this file reads what happens between points, not at any single one.

This file is not the configuration syntax. configurations.md walks the surface itself — the typed declaration, the proof-side subset, what filling either out looks like. This file presupposes both and asks what the architecture says about *changing* them.

This file is not the user-facing compliance API. What a deployment exports as evidence of its current posture is the grounded-evidence cluster's job; this file is about what the architecture's internal certification does as the deployment's posture moves, not about what the deployment hands a downstream consumer.

---

## Takeaway

Movement on the configuration surface — model-axis or declaration-axis — has a typed answer that is neither uniformly free nor uniformly destructive. The model-axis transport theorems lift the ∀-shaped health goals across compatible extensions, and lift the existential corrigible content only across surjective extensions; the asymmetry is the shape of the claim, not a limitation of the architecture. The declaration-axis projection re-routes which clusters reach the deployment as its declaration grows or shrinks, leaving the kernel's universal theorems untouched and the deployment's window onto them precise. Together, the two axes give the deployment a coherent answer to the question of what survives any movement it is contemplating; the next file picks up what the deployment hands a downstream consumer once a posture has settled.

---

↑ [Theory](../) · ← [Configurations](configurations.md) · Next: [Grounded Evidence](grounded-evidence.md) →
