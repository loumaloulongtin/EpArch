# Not Everyone Can Do Everything → Granular ACL

## Cluster

- [What the Architecture Was Forced Into](../forcing.md) — the eight pressures and the schema that turns them into structure
- [People Disagree → Separate Spaces](people-disagree.md) — distributed agents force scope separation
- [Checking Takes Work → Trust Bridges](checking-takes-work.md) — bounded verification forces trust-based import
- [Things Travel → Metadata Travels With Them](things-travel.md) — cross-boundary export forces headers
- [Accepted Things Can Turn Out Bad → Revocation](accepted-can-turn-bad.md) — adversarial pressure forces a way out of *accepted*
- [People Need to Coordinate → Shared Storage](people-need-to-coordinate.md) — coordination need forces a bank
- [Reality Pushes Back → Redeemability](reality-pushes-back.md) — truth pressure forces external constraint-surface contact
- **Not Everyone Can Do Everything → Granular ACL** — staged access forces tier separation *(you are here)*
- [Storage Runs Out → Storage Management](storage-runs-out.md) — bounded capacity forces eviction, archival, or pruning
- [What Goes Wrong When You Drop a Piece](../pathologies.md) — the crosswalk made vivid

---

## Anyone can ask for dinner; only one person cooks it

A family is making dinner. The father is at the stove. He asks the kids and his partner what they feel like eating tonight, listens to the answers — *pasta*, *something spicy*, *not chicken again* — weighs them against what is in the fridge, and starts cooking. Anyone in the family can put a request in. Only one person decides what actually goes in the pot, and only one person stirs it.

Now imagine the simpler arrangement. *We are all family; we all want to eat; let's drop the distinction. Whatever anyone in the house wants to add to dinner, they walk over and add it.* The toddler tips in a handful of breakfast cereal. The teenager pours in half a bottle of hot sauce. Someone's leftover yoghurt goes in because it was in the way. By the time everyone has had their turn there is something in the pot, and nobody wants to eat it. The original arrangement — anyone can request, one person commits — was not a power trip on the father's part. It was the only thing standing between *a meal* and *the contents of the pot*.

The same shape shows up wherever there is a regulated activity with an open intake. A bank: anyone can hand money over the counter to be deposited, only authorised account-holders can withdraw it. A doctor's surgery: anyone can walk in and describe their symptoms, only the doctor writes the prescription. A restaurant kitchen: any waiter can put an order through to the pass, only the chef plates the dish. In all of these the access surface is *staged*: an open request tier and a restricted commit tier. Collapsing the two breaks the system in one of two ways — either the intake closes (only doctors may describe symptoms; only account-holders may hand money over) or the commit opens (any visitor writes their own prescription; any customer reaches over the counter into the till). Neither is what the surgery, the bank, or the family kitchen actually is.

---

## What the kernel proves

The kernel calls a setup of this shape `TwoTierAccess`. It has six substantive ingredients, plus three witness conditions:

- a type of agents (contributors and maintainers, in the scene),
- a type of claims (pull requests, in the scene),
- a *can_propose* predicate — who may submit,
- a *can_commit* predicate — who may merge,
- a *submitter* — an agent who may submit but may not commit,
- a *committer* — an agent who may commit, establishing the commit tier is non-vacuous,
- a *tier_claim* — the claim on which the two tiers differ,
- and three witness conditions: the submitter *may_propose* the tier claim, the submitter *cannot_commit* it, and the committer *may_commit* it.

The simpler-than-granular-ACL design is a single authorisation predicate that decides who can do what to which claim. The kernel proves that no such single predicate can faithfully represent both tiers at once. The proof is two function applications:

> Suppose a flat `f` is faithful to both tiers. Submission is `can_propose`, so `f submitter tier_claim` follows from `may_propose`. Commit is `can_commit`, so the same `f submitter tier_claim` implies `can_commit submitter tier_claim`. That contradicts `cannot_commit`.

The piece that gets forced in is what the contradiction ruled out: the submission tier and the commit tier must be carried by separate predicates. EpArch calls that separation *granular ACL*. Granular ACL is the kernel's name for an access surface in which submission and commit (or, more generally, any two distinct tiers of a staged process) are governed by separate permissions, neither one collapsing into the other.

---

## Why dressing it up doesn't help

The shortfall is sharp enough that it is tempting to look for an authorisation mechanism that can sit on top of a single predicate and make the staging look like an artefact of how the predicate is computed rather than a structural fact. The kernel checks three of the obvious candidates and shows that each of them, when it actually delivers a working access regime, *is* `TwoTierAccess` underneath.

**Roles.** "We don't have two predicates; we have roles. *Maintainer* gets merge permission; *contributor* gets nothing extra. The authorisation function just looks up the agent's role." The kernel models this as `RBACAuthSurface`: agents have roles, roles have permissions, and authorisation is exactly *the agent's role has the permission*. Suppose at least one role has the merge permission and at least one role does not. The kernel constructs `rbac_to_grounded`, which turns the RBAC surface directly into a `TwoTierAccess` instance — the privileged role supplies the committer, the unprivileged role supplies the submitter, and `rbac_two_tier_impossible` fires via the bridge. The roles did not eliminate the two tiers; they sorted agents into them.

**Capability tokens.** "We don't have two predicates; we have tokens. An agent can merge a claim iff they hold a token that grants that claim. The authorisation function just checks token ownership." The kernel models this as `CapabilityTokenAuth` and constructs `capability_token_to_grounded` analogously: the agent who holds a granting token supplies the committer, the agent who holds none supplies the submitter, and `capability_token_two_tier_impossible` fires. Token ownership is a way of *recording* who falls into which tier, not a way of avoiding the tiers.

**Attribute-based access.** "We don't have two predicates; we have attributes. A claim demands certain attributes (e.g. *security clearance*, *signed CLA*, *employee status*); an agent is authorised iff they hold all demanded attributes." The kernel models this as `AttributeBasedAuth` and constructs `attribute_based_to_grounded`: the agent who has all required attributes is the committer, the agent who lacks at least one is the submitter, and `attribute_based_two_tier_impossible` fires. Attribute checking is policy expressed as a query over the agent's attribute set; the queries that produce different answers for different agents are exactly the ones that re-create the two tiers.

The pattern across the three is the same: any authorisation mechanism that actually distinguishes who-can-do-what is supplying the structural ingredients of `TwoTierAccess` — a permitted agent, a restricted agent, and a claim on which they differ. The kernel exhibits the bridge in each case, and the impossibility fires through it. Granular ACL, in the kernel's sense, is not a particular implementation strategy (roles, tokens, attributes); it is whatever structure plays the role of *keeping the submission and commit tiers separate so that neither one collapses into the other*.

---

## What this corner does not claim

It does not claim every system has two tiers. The corner fires only when a staged access surface is actually present — when there is genuinely an open submission tier and a restricted commit tier, with at least one agent in each. A fully closed system in which even submission requires clearance does not instantiate the `TwoTierAccess` witness: there is no submitter who may propose the tier claim but may not commit it, and the corner says nothing about such a system. The corner forces granular ACL *given* that the staging is real, not as a universal architectural mandate.

It does not claim only two tiers. The corner is stated for a two-tier surface because that is the minimal case where collapse becomes contradictory; the same argument iterates to any staged process with three, four, or more distinct permission tiers (submit, review, approve, deploy, audit). Each pair of tiers that have an agent who is in one but not the other supplies its own contradiction against any predicate that tries to collapse them. The kernel formalises the minimal case; the architectural reading covers the general one.

It does not specify the implementation mechanism. Roles, capability tokens, attributes, and any combination of them are valid implementations as far as this corner is concerned, and the kernel exhibits each one as a bridge into `TwoTierAccess` rather than an alternative to it. Choosing between role-based, capability-based, and attribute-based access is a design decision the corner does not make; the corner says only that *whichever mechanism is chosen must keep the tiers separable*. A flat predicate dressed up in any of those vocabularies still cannot represent both tiers at once.

It does not claim the access policy is correct. The kernel says nothing here about whether the right people are in the right tiers, whether the policy reflects organisational intent, or whether the privileged agents will use their privileges responsibly. Those are jobs for governance, audit, and the lifecycle module on under-attack behaviour. The corner forces the *structural separation* of the tiers; what fills each tier and how that filling is governed are different questions.

---

## Takeaway

When a system has a staged access surface — anyone can submit, only some can commit — no single authorisation predicate can faithfully represent both tiers at once. The shortfall is structural: the submitter who may propose but may not commit is a witness against any predicate that tries to identify the two.

The minimal piece that closes the gap is the existence of *separate* permission carriers for the submission and commit tiers. EpArch calls that separation *granular ACL*. Three plausible alternative authorisation mechanisms (role-based, capability-token, attribute-based) do not escape the corner: each one supplies a direct bridge into `TwoTierAccess` whenever its policy actually distinguishes any two agents on any claim. The kernel exhibits the bridge in each case.

The architecture's job is not to specify which mechanism implements the separation, or to dictate which agents belong to which tier. It is to refuse to silently collapse a staged access surface into a flat predicate that cannot represent it.

---

*← [Forcing](../forcing.md)  ·  ← Previous: [Reality Pushes Back](reality-pushes-back.md)  ·  Next: [Storage Runs Out → Storage Management](storage-runs-out.md) →*
