/-
EpArch.Semantics.LinkingAxioms — (Retired)

This file previously contained export-gating operational grounding theorems
(`grounded_no_bridge_forces_revalidation`, `export_gating_forced`) for the
now-deleted `Action.Export` constructor.

Export is not a bank primitive. Inter-bubble transfer is an agent-level workflow:
the agent Withdraws from the source bubble, carries the deposit, then registers it
in the target bubble via `Step.register`. The bank records the event; it does
not verify the claimed source or maintain a trust-bridge registry. Trust relationships
are per-deposit (d.h.acl) and per-agent, not systemic bank-layer lists.

The export gating commitment (C5 in EpArch.Commitments) has been replaced by
`DirectRegisterEntersDeposited`: the direct-register path is the agent registration path.
-/

import EpArch.Semantics.StepSemantics

namespace EpArch.LinkingAxioms

end EpArch.LinkingAxioms
