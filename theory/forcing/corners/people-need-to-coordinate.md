# People Need to Coordinate → Shared Storage

## Cluster

- [What the Architecture Was Forced Into](../forcing.md) — the eight pressures and the schema that turns them into structure
- [People Disagree → Separate Spaces](people-disagree.md) — distributed agents force scope separation
- [Checking Takes Work → Trust Bridges](checking-takes-work.md) — bounded verification forces trust-based import
- [Things Travel → Metadata Travels With Them](things-travel.md) — cross-boundary export forces headers
- [Accepted Things Can Turn Out Bad → Revocation](accepted-can-turn-bad.md) — adversarial pressure forces a way out of *accepted*
- **People Need to Coordinate → Shared Storage** — coordination need forces a bank *(you are here)*
- [Reality Pushes Back → Redeemability](reality-pushes-back.md) — truth pressure forces external constraint-surface contact
- [Not Everyone Can Do Everything → Granular ACL](not-everyone-can-do-everything.md) — staged access forces tier separation
- [Storage Runs Out → Storage Management](storage-runs-out.md) — bounded capacity forces eviction, archival, or pruning
- [What Goes Wrong When You Drop a Piece](../pathologies.md) — the crosswalk made vivid

---

## Two surgeons, one patient, two private notebooks

A patient is admitted to a hospital and seen, in succession, by two specialists. The first is a cardiologist; she examines the patient, takes a history, runs an ECG, and forms a working diagnosis. The second is an anaesthetist; he is going to operate the next morning, and he needs to know what the cardiologist found before he picks the anaesthetic.

Now imagine a hospital where each clinician keeps their notes in a strictly private notebook. The cardiologist's notebook is hers, locked in her desk drawer. The anaesthetist's notebook is his, locked in his desk drawer. Neither can read the other's notebook. There is no shared chart. There is no shared computer system. There is no message-passing intermediary. By construction of this scenario, anything the cardiologist writes is invisible to the anaesthetist, and vice versa.

The anaesthetist arrives at the operating room the next morning needing the cardiologist's findings. He cannot have them. The cardiologist could call him, leave a sticky note, walk into the operating room and tell him out loud — but each of those is a *shared channel*: a thing that exists outside both private notebooks and that both clinicians can reach. The hospital described, the one where storage is *strictly* private, has no such thing. The cardiologist's findings exist only inside her notebook; the anaesthetist's view of the patient exists only inside his.

The actual hospital — a shared chart, a shared electronic record, a shared whiteboard, even a shared phone line — is not bureaucratic centralisation that could be trimmed away by trusting clinicians to remember things. It is the only thing that fits, and the reason it is the only thing that fits is the load-bearing claim of this corner.

---

## What the kernel proves

The kernel calls a setup of this shape `PrivateOnlyStorage`. It has four substantive ingredients, plus an isolation condition:

- a type of agents (clinicians, in the scene),
- a type of deposits (clinical findings),
- an *access* relation — which agents can reach which deposits,
- two distinct agents *a₁* and *a₂* — the two clinicians who need to coordinate,
- and the *isolation* condition: any deposit accessible to *a₁* is *not* accessible to *a₂*.

The simplest-than-bank design is exactly this: each agent has their own store, and the stores do not overlap. The kernel proves that under such an arrangement, no deposit is simultaneously accessible to both agents. The proof is short:

> Suppose some deposit *d* is accessible to both. *a₁* has access to *d*, so by isolation *a₂* does not. The supposition that *a₂* also has access contradicts itself.

The piece that gets forced in is the obvious one once it is named: there must exist a deposit that both agents can reach — a place outside both private stores where coordination can land. EpArch calls that place a *bank* (or a *shared ledger*, or simply *the bank*). The bank is the kernel's name for the shared-ledger role: somewhere a deposit can sit such that more than one agent can reach it for coordination. Read versus write, who is allowed which, and how conflicts get resolved are governed by other corners and by the lifecycle module; the bank corner forces the existence of the shared-access object, not the access discipline on it.

---

## Why dressing it up doesn't help

The shortfall is sharp enough that it is tempting to look for an arrangement that lets agents coordinate without admitting that there is somewhere both of them can reach. The kernel checks three of the obvious dodges and shows that each of them, if it actually delivers coordination, *is* shared storage in disguise.

**Replicated logs.** "Each agent has their own log; we just synchronise them." The kernel models this as `ReplicatedLog`: an access relation, two distinct agents, and a *synchronisation* condition saying that any deposit accessible to *a₁* is also accessible to *a₂*. The kernel proves directly that synchronisation is shared access — `attestation_network_is_shared` and `replicated_log_is_shared` are one-line theorems showing that the synchronisation condition *is* the shared-access predicate. The replicated log did not eliminate shared storage; it spelled out shared storage as a per-agent replica plus a guarantee that the replicas agree. The bank is everywhere; it just isn't in any one place.

**Attestation networks.** "Each agent publishes signed attestations; the others read what they need." The kernel models this as `AttestationNetwork` and gives the same one-line theorem (`attestation_network_is_shared`): if *a₂* can read *a₁*'s published attestations, the isolation condition fails. Publishing-and-reading is shared access; calling the substrate an *attestation* rather than a *bank entry* does not change what is happening. The bank is the publication channel.

**CRDT-based shared state.** "Each agent has local state; the data structure is conflict-free, so the local states converge to the same value." The kernel models this as `CRDTStorage` with a *convergence* condition. Convergence directly states that any deposit accessible to one agent is also accessible to the other. Same one-line theorem, same conclusion: the isolation condition fails, the kernel-named bank is the converged state. The CRDT did not eliminate shared storage; it gave shared storage a particular consistency model and a particular implementation strategy.

The pattern across all three is the same: any architecture in which agents actually coordinate has *somewhere* a deposit can sit that both can reach. Calling that somewhere a *replica*, a *publication*, or a *converged value* renames it; it does not remove it. The bank, in the kernel's sense, is whatever object plays this role — wherever it physically lives, however it is replicated, whatever consistency model governs it.

---

## What this corner does not claim

It does not claim the bank must be physically central. The kernel proves that *some* shared-access object exists; it does not say the object lives on one machine, in one building, or under one administrator. A replicated database, a peer-to-peer network with eventual consistency, a federated set of mirrors, a single relational store, and a shared filesystem are all valid implementations as far as this corner is concerned. What none of them can be is *a system in which no two agents can ever reach the same deposit*.

It does not claim any particular consistency model. The corner says only that the access relation must overlap on at least one deposit when coordination is required. Whether the bank offers strong consistency, eventual consistency, causal consistency, or read-your-writes is a design choice the corner does not constrain. Whatever model is chosen, it is *a* consistency model on a shared object — and that shared object is the bank.

It does not claim every deposit must be in the bank. Many deposits remain private to one agent — drafts, working notes, internal scratch space. The corner fires only for deposits that two or more agents must coordinate on; for those, shared storage is forced. The architecture does not have to share everything to satisfy the corner; it has to share the right things, and *the right things* is whatever set has to be coordinated on.

And it does not claim the bank is safe from misuse. The kernel says nothing here about who is allowed to read or write, what happens when two agents try to write conflicting deposits, how access control governs the bank, or how to detect tampering. Those are jobs for the *Not everyone gets to do everything* corner (access control), the lifecycle module on under-attack behaviour (write conflicts and contestation), and the *Things travel* corner (the headers that ride on bank entries).

---

## Takeaway

When two agents must coordinate on the same deposit, no arrangement in which their stores never overlap can deliver coordination. The shortfall is structural: the isolation condition directly contradicts the existence of a deposit both agents can read.

The minimal piece that closes the gap is the existence of *some* deposit that both agents can reach. EpArch calls the structure that holds such deposits a *bank*. Three plausible dodges (replicated logs, attestation networks, CRDT-based shared state) each turn out to *be* shared storage on closer inspection — the kernel proves that their synchronisation, readability, and convergence conditions just spell out the shared-access predicate the corner forces.

The architecture's job is not to specify where the bank physically lives or how its replicas stay in sync. It is to refuse to silently pretend that coordination can happen in a system where agents have no shared reach.

---

*← [Forcing](../forcing.md)  ·  ← Previous: [Accepted Can Turn Bad](accepted-can-turn-bad.md)  ·  Next: [Reality Pushes Back → Redeemability](reality-pushes-back.md) →*
