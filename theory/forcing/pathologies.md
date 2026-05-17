# What Goes Wrong When You Drop a Piece

## Cluster

- [What the Architecture Was Forced Into](forcing.md) — the eight pressures and the schema that turns them into structure
- [People Disagree → Separate Spaces](corners/people-disagree.md) — distributed agents force scope separation
- [Checking Takes Work → Trust Bridges](corners/checking-takes-work.md) — bounded verification forces trust-based import
- [Things Travel → Metadata Travels With Them](corners/things-travel.md) — cross-boundary export forces headers
- [Accepted Things Can Turn Out Bad → Revocation](corners/accepted-can-turn-bad.md) — adversarial pressure forces a way out of *accepted*
- [People Need to Coordinate → Shared Storage](corners/people-need-to-coordinate.md) — coordination need forces a bank
- [Reality Pushes Back → Redeemability](corners/reality-pushes-back.md) — truth pressure forces external constraint-surface contact
- [Not Everyone Can Do Everything → Granular ACL](corners/not-everyone-can-do-everything.md) — staged access forces tier separation
- [Storage Runs Out → Storage Management](corners/storage-runs-out.md) — bounded capacity forces eviction, archival, or pruning
- **What Goes Wrong When You Drop a Piece** — the crosswalk made vivid *(you are here)*

---

## The negative twin

The corner files make the positive claim: each pressure, in its sharpest form, forces a specific minimal piece of structure. This file makes the negative claim, which is the same claim seen from the other side: a system that ships without the piece does not get to coast on its absence — there is a specific situation, exhibited by the kernel, in which the missing piece's absence becomes a contradiction.

What "specific situation" means here is precise. For each forced piece, the kernel constructs a small structural model — a few fields naming exactly the conditions under which the pressure is present in its sharpest form — and proves that any system claiming to satisfy that model without the piece runs into an impossibility. The proof is short in every case: a witness from the model is fed into the simpler-than-the-architecture system, and the answer is wrong.

This file walks the eight impossibilities one at a time. Each entry names a deployment that has tried to skip the piece, points to the structural model that the deployment has nonetheless instantiated, and shows what the contradiction looks like when it lands. The kernel does the proving; this file does the picturing.

---

## 1. Skip the bubbles → one shared list, two readers who do not agree

A small reading group keeps a shared list on the fridge: *books we recommend*. One member of the group is happy to recommend any book she has finished and enjoyed; another only recommends books he has finished, enjoyed, and re-read at least once. They have a single magnet-board. A new book goes up. Someone visiting the kitchen reads the list and asks, *do you recommend this one?* — and there is no honest answer the list can give on behalf of both members at once. Either the lenient member is misquoted (the book is on the list but the strict member would never have put it there) or the strict member is misquoted (the book is off the list but the lenient member loves it).

The same shape shows up wherever one acceptance flag is asked to speak for two acceptance criteria. A document review service that runs a single *approved* bit while two clients with different review standards both read from it. A package registry that marks every package *trusted* or *untrusted* while two consuming organisations have different ideas of what *trusted* means. A medical-records system with one *verified* flag for a patient note while a primary-care doctor and a specialist apply different verification thresholds.

The kernel's `AgentDisagreement` is exactly this picture in its smallest form: two acceptance functions and a witness claim where they disagree. `flat_scope_impossible` shows there is no single function that can be faithful to both — agreement with one on the witness forces agreement with the other on the witness, and the two cannot both hold. Whichever way the shared flag is set on the new book, somebody is being misrepresented. What the system must add is a way to ask *recommended by whom* — a separate scope per acceptance criterion, so the question always comes with an addressee. The kernel calls those scopes *bubbles*.

---

## 2. Skip the trust bridges → re-checking everything until you cannot finish

A jeweller has a strict rule: she does not sell anything she has not personally tested. Every gold ring gets weighed, every diamond gets inspected under her loupe, every watch movement gets opened and timed. The rule has served her well for thirty years. Then a colleague she has known and trusted for decades retires and offers her his entire stock — six hundred items, including pieces whose authentication takes a full afternoon each. She has two months before he closes his shop. The arithmetic is unkind: even working evenings, she cannot personally verify all six hundred pieces in time. She has two doors. Refuse the items she cannot get to (and lose pieces she actually wants). Or skip her own check on those items (and accept the stock on faith without admitting it). Both doors break the rule the policy was meant to deliver.

The same shape shows up wherever a verifier whose budget is real refuses to accept anything except by direct re-verification. A peer reviewer who insists on re-deriving every cited result before signing off. A package importer that re-runs the upstream test suite from scratch on every release. An auditor who treats *trust no upstream* as a strict policy rather than a calibration choice. Each of them works fine until the next claim arrives whose verification cost exceeds what they can spend; then they are choosing between dropping the claim and silently relaxing the policy.

The kernel's `BoundedVerification` is exactly this picture: a verification function with an explicit cost, a fixed budget, and a witness claim whose cost exceeds the budget. `verification_only_import_incomplete` is the arithmetic the jeweller ran. What she actually needs — and the kernel agrees — is a way to accept an expensive claim on grounds other than redoing the work: a clear attribution to her trusted colleague, recorded as the basis for accepting his pieces, with the work that licensed them living on his side of the handover. The kernel calls that attribution a *trust bridge*. The bridge is not a hole in the policy; it is the policy's honest accommodation of the fact that her budget is finite and his work is real.

---

## 3. Skip the headers → a parcel with no label

A receiving dock at the back of a warehouse takes in parcels all day. Two parcels arrive in the same brown box, the same shape, the same weight. One is the result of a clean order from a known supplier — exactly what the warehouse asked for, due today, under the supplier's standard terms. The other is a return from a customer who has wrapped the contents in an identical brown box without any paperwork — a return the warehouse did *not* ask for, a customer it has not heard from in months, under no agreed terms. The dock worker looks at both boxes. They are identical. The dock has no procedure that distinguishes them based on what is *inside* the wrapping, because the procedure works on what arrived, and what arrived is two indistinguishable boxes. He treats them the same: both go on the *received today* shelf and onward into inventory.

The same shape shows up wherever an importer accepts payloads with no metadata travelling alongside them. A logging endpoint that ingests JSON blobs as facts without origin or time. A federation service that accepts model outputs from any peer without source attribution. A messaging app that displays forwarded text without the chain of who forwarded what.

The kernel's `DiscriminatingImport` is exactly the receiving-dock picture: a good claim and a bad claim that the import function is supposed to treat differently. `uniform_import_nondiscriminating` is the formal version of *the dock has no discriminating input*: a uniform function returns the same verdict where the policy needs different verdicts. What the dock needs is a label on the box — origin, time, the standing terms it arrived under, the licensed use. The kernel calls those labels *headers*.

---

## 4. Skip revocation → a marriage register with no annulment column

Imagine a register of marriages that records who married whom and when, and only that. There is no column for divorce, no column for annulment, no procedure for a register entry to ever be marked otherwise-than-current. Once two people are entered, the register lists them as married forever, including in the obvious cases — they divorced; the marriage was annulled because one party was already married; one of them died. Officials downstream of the register — banks, insurers, courts, tax offices — read it and cannot tell that anything has changed.

The same shape shows up wherever a state is one-way. A reputation score that only goes up. A credentialing system that issues certificates and never revokes them, even after the credentialed party loses the qualifying competence. A vaccination database that records doses administered but cannot record a recall when the lot is later found defective. A *verified* badge that, once granted, has no procedure for being taken back. Each of these works while nothing goes wrong. The first time something does — a divorce, a competence loss, a recall, a verified-and-then-disgraced account — the register has no transition to fire. The wrong record sits there permanently, and every downstream reader treats it as still-good.

The kernel's `MonotonicLifecycle` is exactly the no-annulment register: a state space whose accepted state has no successor that is not also accepted. `monotonic_no_exit` shows the state is absorbing — there is no path out of *accepted* in this lifecycle, because the lifecycle relation forbids one. What the register must add is a column. The kernel does not insist what to call it (revoked, annulled, withdrawn, recalled) or how to fire it (challenge first, then quarantine, then revoke, in the kernel's lifecycle); it insists only that *accepted* must have a non-accepted successor reachable from it. Without one, accepting once is accepting forever — including when forever turns out to be the wrong answer.

---

## 5. Skip the bank → two cooks, two private recipe boxes

Two cooks work in the same restaurant, cooking the same menu, but each one keeps her own private recipe box on her own shelf. Neither has access to the other's box. They have started this way because privacy is convenient: each cook can adjust her own recipes without disturbing the other's, and there are no merge conflicts. For a while it works. Then the *coq au vin* needs to be the same on both stations because guests ordering it expect the same dish whichever cook plates it; then a reviewer asks for the recipe and there are two; then one cook is on holiday and the other has to cover her station and discovers that *cover the station* means *guess what is in her box from the dishes that came out last week*. They are technically a kitchen of two cooks. They are not a kitchen with a shared cookbook, and there is no structural way for them to be relying on the same recipe at the same time.

The same shape shows up wherever agents need to coordinate on a record but each one has only its own copy. A team that takes meeting minutes in private notebooks rather than a shared document. A multi-tenant system where every tenant has its own ledger and there is no cross-tenant store. A microservice architecture where each service maintains its own private state and *coordination* happens by gossip rather than by reference to a shared object.

The kernel's `PrivateOnlyStorage` is the two-recipe-boxes picture: a per-agent storage in which no deposit is accessible to two distinct agents at once. `private_storage_no_sharing` shows that under this constraint, no two distinct agents share access to any deposit — the *thing* both cooks are supposed to be relying on, the architecture cannot point to. What the kitchen needs is a binder on the counter that both cooks can open. Not necessarily one physical book — replicated cookbooks that synchronise, an attestation system where each entry is signed off by both, a wiki that resolves conflicts deterministically — but *something* with the structural role that two distinct cooks both have access to. The kernel calls that role the *bank*; the corner file ([People Need to Coordinate](corners/people-need-to-coordinate.md)) discusses why those alternatives all instantiate the role rather than escape it.

---

## 6. Skip redeemability → a panel that grades its own forecasts

A weather panel meets every Friday afternoon to issue forecasts for the coming week and, in the same meeting, to grade the previous week's forecasts. The grade is a vote: the panel decides whether each issued forecast was, on reflection, correct. There is no input from outside the room — no rain gauges consulted, no satellite imagery shown, no later observations entered into the procedure. The grade is whatever the panel says it is. By the end of the year, the panel's forecasts have a strikingly good track record. By construction, they could not have any other.

The same shape shows up wherever a claim's only correctness criterion is the endorsement procedure. A peer-review journal whose papers count as *correct* iff the editorial board says so, with no requirement that the experiments be reproducible. An expert system whose recommendations are *valid* iff the panel of experts who designed it ratifies them, with no procedure for an outcome in the world to count as a counterexample. A self-assessment regime in which the regulated party reports its own compliance and the regulator's check consists only of asking whether the report was issued.

The kernel's `ClosedEndorsement` is exactly the self-grading panel: an endorsement procedure together with a closure condition saying that endorsed claims are not externally falsifiable. `closed_system_unfalsifiable` is the formal version of *by construction, they could not have any other*: no fact outside the endorsement procedure can falsify an endorsed claim, because closure rules that out. What the panel must add is a path from outside the room to *not correct* — a constraint surface that can disagree. The kernel calls this *redeemability*: rain gauges, satellite imagery, later observations, external standards, all in structural positions where their disagreement with an endorsed forecast is *registered as* falsification rather than dismissed as out-of-process. Without that path, the panel is not making weather claims; it is making endorsement claims dressed up as weather claims.

---

## 7. Skip granular ACL → a single key that opens both the till and the safe

A small shop has one key. It opens the front door, the till, and the safe. The owner gave the same key to every member of staff because it was simpler than tracking who had access to what. The arrangement worked while staff turnover was low and the safe was rarely opened. Then the owner hires a new junior assistant, who needs to come in early to open the shop and to ring up sales — which means she needs the key. With the key, she also has unsupervised access to the safe. There is no way, with one key, to license the assistant's actual job (open up, run the till) without also licensing what was meant to be the manager's job (count the cash in the safe at end of day). The owner is now choosing between not hiring the assistant, refusing her the key, or accepting that *opening the till* and *opening the safe* are the same authorisation question, when they should not be.

The same shape shows up wherever two operational tiers have to be distinguished but the system offers a single boolean. A workflow that conflates *propose* and *approve*. An admin console with one *can manage* flag rather than separate *can read* and *can modify* permissions. A code-review system in which anyone who can submit a pull request can also merge it.

The kernel's `TwoTierAccess` is the till-and-safe key: two authorisation predicates `can_propose` and `can_commit`, plus a witness submitter who may do the first but not the second. `flat_authorization_impossible` shows there is no single boolean that can be faithful to both questions: agreement on the propose tier forces a verdict on the commit tier, and the witness submitter contradicts it. What the shop must add is a separate key for the safe — separate authorisation predicates per tier, so *may open the till* and *may open the safe* can disagree on the same person. The corner file ([Not Everyone Can Do Everything](corners/not-everyone-can-do-everything.md)) discusses how role-based, capability-token, and attribute-based designs all instantiate two-tier access rather than escape it.

---

## 8. Skip storage management → a phone that has never deleted a photo

Imagine a phone that has never deleted a photo. Not because the user has been disciplined about saving the keepers and removing the rest — because there is no procedure for removing them. Every photo taken since the phone was new is still on the device: thirty thousand photos, most of them duplicates, accidental shutter presses, screenshots of expired offers, blurred shots from the inside of a pocket. The phone is six years old. For the first three years it ran fine. Now it is full. The user wants to take a picture of her daughter's birthday cake. The phone returns *Storage full*. The reason the phone is full is not that the daughter took up too much space; it is that nothing was ever the candidate for going.

The same shape shows up wherever a system grows monotonically against a real budget. An append-only log on a finite disk. A version history that retains every revision forever. A multi-tenant store where every tenant can grow without bound and the global capacity is finite. Each of these works on the day it is provisioned. None of them works once enough activity has accumulated, because the budget was never going to be larger than activity could fill.

The kernel's `BoundedStorage` is the photo-roll picture: a budget, a count function, and a concrete state whose count exceeds the budget by construction. `monotone_active_accumulation_overflows` is the formal version of the overflow contradiction: a system cannot both claim all states stay within budget and contain such an overflow state. The phone's *defer the deletion question* posture turns out, structurally, to leave the system with no structural answer once accumulation reaches an overflow state: when the count climbs past the budget, the device is in exactly the state the kernel exhibits as the contradiction against any *we will stay within budget forever* claim. What the phone must add is a mechanism that brings the count back down — eviction, archival, expiry, pruning, compaction. The kernel does not insist which one; it insists that some such mechanism must exist, because the alternative is the *Storage full* the user is now staring at on the daughter's birthday.

---

## What the pathology crosswalk does and does not say

It does say that the eight forced pieces are not stylistic choices. For each one, dropping the piece is not the same shape of architectural decision as choosing a different colour scheme or a different storage backend; it is a commitment to fail in a structurally specific way the moment the corresponding pressure is present in its sharpest form. The kernel exhibits the failure as an impossibility theorem; the deployment exhibits it as a runtime symptom (wrong verdicts, dropped claims, absorbing accept states, divergent private stores, unfalsifiable consensus, collapsed authorization tiers, overflowing disks).

It does not say that every deployment that drops a piece is a broken deployment. A deployment that does not face the corresponding pressure in its sharpest form is not contradicted by the model. The kitchen thermometer drops headers, redeemability, and revocation; it is not broken because nobody is asking it to ingest claims from elsewhere, contest the temperature against an external standard, or revoke a reading that turned out to be wrong. The pathology fires when a deployment claims to handle the pressure *and* drops the piece. Both halves of the conjunction matter — the kernel is about what is structurally forced; the configurability cluster (downstream of forcing/) is about which pressures a given deployment is honestly claiming to face.

It does not say the kernel models the deployments themselves. The eight structural models are abstractions: they capture the worst-case shape of each pressure and prove an impossibility against the simpler-than-architecture system. Real deployments are messier — they may face one pressure intermittently, another in a softened form, a third only along certain interfaces. The kernel's claim is conditional: *if* the deployment has instantiated the structural model — and the alternative-architecture sections in each corner show that many ostensibly different designs do — *then* the impossibility lands. What the deployment does next (mitigate, accept the limitation, restructure) is not a kernel question.

---

## Takeaway

The forcing schema has a positive face and a negative face, and they say the same thing. The positive face is *the eight pressures force the eight pieces*. The negative face is *a system without one of the pieces hits the corresponding impossibility theorem the moment the pressure is present in its sharpest form*. The kernel exhibits both faces: each corner file walks the positive direction; this file walks the negative direction.

The eight failures are not abstract worries. They are the operational symptoms a deployment will exhibit if it ships without the corresponding forced piece while still claiming to handle the pressure: clients silently misrepresented, expensive claims dropped, bad payloads ingested as good, accepted-and-now-known-to-be-bad claims sitting in *accepted* forever, agents unable to coordinate on a shared record, consensus that the world cannot challenge, authorization that flattens proposers into committers, and disks that fill up and crash. The architecture is what survives the eight contradictions; the pathology crosswalk is what the contradictions look like when the architecture is missing.

---

*← [Forcing](forcing.md)  ·  ← Previous: [Storage Runs Out](corners/storage-runs-out.md)  ·  Next: [What a Working System Buys You →](../goals/goals.md)*
