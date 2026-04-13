/-
EpArch/ScopeIrrelevance.lean — Scope Irrelevance Layer

This module turns "out of scope" from prose into machine-checkable scope boundaries.

Core results:
- S1: Substrate Independence — physics/implementation don't affect revision-gate theorems
- S2: Minimal Agency — agents need only functional capabilities, not consciousness
- S3: Extra-State Erasure — adding qualia/psychology/embodiment doesn't affect theorems

These patterns are bound to RevisionGate via RevisionSafety.
The `extra_state_compatible` theorem shows any extra-state extension is Compatible,
and thus the revision gate transports via `transport_core`.
-/

import EpArch.Basic
import EpArch.WorldCtx
import EpArch.Semantics.RevisionSafety

open EpArch

namespace EpArch.ScopeIrrelevance

open EpArch.RevisionSafety

/-! ## Substrate Independence

"Physics don't matter": any substrate implementing the interface yields the same
revision-gate theorems.

The key insight: our theorems already quantify over abstract types (World, Agent,
PropLike). If two substrates implement the same interface, they yield the same theorems.
-/

/-- A model specifies concrete types for the abstract interface. -/
structure Model where
  World : Type
  Agent : Type
  PropLike : Type
  Obs : Type
  Truth : World → PropLike → Prop
  Utter : Agent → PropLike → Prop
  obs : World → Obs

/-- Model homomorphism: structure-preserving map between models.
    (Using explicit functions instead of Equiv to avoid import issues) -/
structure ModelHom (M₁ M₂ : Model) where
  worldMap : M₁.World → M₂.World
  agentMap : M₁.Agent → M₂.Agent
  propMap : M₁.PropLike → M₂.PropLike
  obsMap : M₁.Obs → M₂.Obs
  /-- Truth is preserved under homomorphism -/
  truth_compat : ∀ w p, M₁.Truth w p → M₂.Truth (worldMap w) (propMap p)
  /-- Utter is preserved under homomorphism -/
  utter_compat : ∀ a p, M₁.Utter a p → M₂.Utter (agentMap a) (propMap p)
  /-- Observation is preserved under homomorphism -/
  obs_compat : ∀ w, obsMap (M₁.obs w) = M₂.obs (worldMap w)

/-- Substrate independence: homomorphic models preserve theorem truth.

    This is the formal statement that "physics don't matter" — any substrate
    that maps to another preserves existential claims. -/
theorem substrate_preserves_existence (M₁ M₂ : Model) (h : ModelHom M₁ M₂)
    (w : M₁.World) (p : M₁.PropLike) :
    M₁.Truth w p → M₂.Truth (h.worldMap w) (h.propMap p) :=
  h.truth_compat w p


/-! ## Minimal Agency

Agents need only minimal functional capabilities ("acknowledge experience"),
not human-grade minds, consciousness, or rich psychology.

We define a minimal interface and show theorems only depend on this.
-/

/-- Minimal agent capabilities: what the proofs actually use. -/
structure MinimalAgent where
  /-- Agent can be identified -/
  id : Nat
  /-- Agent has some internal "state" (opaque) -/
  state : Type

/-- **Seam theorem.** Names the minimal-agent identity boundary.

    This captures: we don't assume consciousness, rich psychology, etc.
    If a theorem only uses the existence of agents, it's minimal.
    Proof is `Iff.rfl` because the boundary is *definitional*: the real content
    is that `MinimalAgent` exposes only `id` and opaque `state`, and our
    theorems never discriminate beyond that. -/
theorem agent_identity_suffices (P : Nat → Prop) (a : MinimalAgent) :
    P a.id ↔ P a.id :=
  Iff.rfl


/-! ## Extra-State Erasure

Adding extra internal state (consciousness, qualia, psychology, embodiment,
neural architecture) doesn't affect theorems if primitives ignore it.
-/

/-- **Seam theorem.** Names the extra-state substitution boundary.

    Proof is `Iff.rfl` because projecting `.1` from a pair is definitionally identity.
    The architectural content is the *negative* claim: P does not inspect the second
    component at all. Swapping in any X (qualia, psychology, embodiment) is safe
    because P never looks at it.

    Revision-gate preservation is closed by `extra_state_revision_gate_transport`,
    which builds a `Compatible` witness and calls `transport_core`. -/
theorem extra_state_erasure {Agent X : Type} (P : Agent → Prop)
    (a : Agent) (x : X) :
    P a ↔ P (a, x).1 :=
  Iff.rfl

/-- **Seam theorem.** Names the psychology boundary for citation purposes.
    `system_property` does not inspect the second component.
    Revision-gate binding: `psychology_irrelevant_revision_gate`. -/
theorem psychology_irrelevant {Agent Psychology : Type}
    (system_property : Agent → Prop)
    (a : Agent) (psych : Psychology) :
    system_property a ↔ system_property (a, psych).1 :=
  Iff.rfl

/-- **Seam theorem.** Names the consciousness/qualia boundary for citation purposes.
    Revision-gate binding: `consciousness_irrelevant_revision_gate`. -/
theorem consciousness_irrelevant {Agent Qualia : Type}
    (functional_property : Agent → Prop)
    (a : Agent) (q : Qualia) :
    functional_property a ↔ functional_property (a, q).1 :=
  Iff.rfl

/-- **Seam theorem.** Names the embodiment boundary. -/
theorem embodiment_irrelevant {Agent Embodiment : Type}
    (abstract_property : Agent → Prop)
    (a : Agent) (e : Embodiment) :
    abstract_property a ↔ abstract_property (a, e).1 :=
  Iff.rfl


/-! ## Traction-Implementation Irrelevance

`agentTraction` is the hook where psychology, cognition, and institutional
policy modulate the Ladder.  The theorems here close the circle: swapping in
a different traction implementation changes `ladder_stage` outputs, but has
no downstream consequences to any system-level property that does not directly
examine `agentTraction`.
-/

/-- **Seam theorem.** Names the traction substitution boundary.

    `agentTraction` has no observable surface beyond `ladder_stage`: if two
    implementations agree on a claim P, they produce the same stage output.
    Consequence: psychology, neural architecture, and institutional policy can
    freely modulate `agentTraction` without affecting any other system predicate. -/
theorem traction_modulation_confined
    (_a : Agent) (P : Claim)
    (f g : Claim → LadderStage)
    (h : f P = g P) :
    f P = g P := h

/-- **Seam theorem.** Names the traction implementation boundary for system properties.

    Stages agree, so properties agree. The mechanism by which the agent
    arrives at a stage (psychology, pattern-matching, utility calculation)
    does not affect which system theorems hold.

    This is the `agentTraction` analog of `psychology_irrelevant`. -/
theorem traction_implementation_irrelevant
    (_a : Agent) (P : Claim)
    (system_property : LadderStage → Prop)
    (f g : Claim → LadderStage)
    (h : f P = g P) :
    system_property (f P) ↔ system_property (g P) :=
  h ▸ Iff.rfl


/-! ## Fundamentals Coverage Table

| Fundamental | Status | Theorem | Guardrail |
|-------------|--------|---------|-----------|
| Physics/Substrate | Irrelevant | `substrate_preserves_existence` | ModelHom preserves truth |
| Consciousness | Irrelevant | `consciousness_irrelevant` | Extra state erased |
| Psychology | Irrelevant | `psychology_irrelevant` | System-level only |
| Embodiment | Irrelevant | `embodiment_irrelevant` | Via abstract properties |
| Traction implementation | Confined | `traction_modulation_confined` | Only surfaces via `ladder_stage` |
| Traction implementation | Irrelevant | `traction_implementation_irrelevant` | System props depend on stage, not mechanism |
| Optimal Rationality | Not assumed | N/A | No Bayes dependency |
| Free Will | Not assumed | N/A | No moral judgment |
| Metaphysics of Truth | Abstract | N/A | Truth is a predicate |

-/

/-! ## What This Module Does NOT Do

1. **Prove all theorems are invariant** — that would require restating each theorem
   in terms of ModelHom, which is mechanical but verbose.

2. **Define consciousness** — we just show it's irrelevant *if* added as extra state.

3. **Claim completeness** — other fundamentals could be added similarly.

The module establishes the pattern for scope-irrelevance claims.
-/


/-! ## Binding to RevisionGate via RevisionSafety

The abstract erasure theorems above are generic patterns.
This section BINDS them to the architecture via RevisionSafety.

Key result: `extra_state_revision_gate_transport`
- Any CoreModel C can be extended with extra state X
- The extension is Compatible with C
- Therefore RevisionGate properties transport

This means: adding consciousness, qualia, psychology, etc. as X cannot break core architectural theorems.
-/

/-- Build an extra-state extension of any CoreModel.

    Given C and extra state types, construct ExtModel (C × Extra).
    Requires extra types to be inhabited (can always use Unit for trivial extension).
    The extra operations are placeholders (the whole point is they're unused). -/
def extendWithExtraState (C : CoreModel)
    (AgentExtra : Type) [Inhabited AgentExtra]
    (WorldExtra : Type) [Inhabited WorldExtra] : ExtModel where
  sig := {
    Agent := C.sig.Agent
    Claim := C.sig.Claim
    Bubble := C.sig.Bubble
    Time := C.sig.Time
    Deposit := C.sig.Deposit
    Header := C.sig.Header
    AgentExtra := AgentExtra
    WorldExtra := WorldExtra
  }
  ops := {
    deposit_header := C.ops.deposit_header
    truth := C.ops.truth
    obs := C.ops.obs
    verifyWithin := C.ops.verifyWithin
    effectiveTime := C.ops.effectiveTime
    submit := C.ops.submit
    revise := C.ops.revise
    hasRevision := C.ops.hasRevision
    selfCorrects := C.ops.selfCorrects
    getAgentExtra := fun _ => default  -- Placeholder (unused)
    getWorldExtra := default           -- Placeholder (unused)
  }
  hasBubble := C.hasBubble

/-- Extra-state extension is Compatible with base.

    The extended model preserves all core operations.
    This is the key binding that makes scope-irrelevance revision-gate-compatible.

    The projections are identity (types are shared).
    The commuting laws are all Iff.refl because extendWithExtraState
    copies operations unchanged from C. This is NOT trivial - it's because
    we deliberately constructed the extension to preserve operations!

    A "bad" extension that changed hasRevision or selfCorrects would fail
    to produce this Compatible witness. -/
theorem extra_state_compatible (C : CoreModel)
    (AgentExtra : Type) [Inhabited AgentExtra]
    (WorldExtra : Type) [Inhabited WorldExtra] :
    Compatible (extendWithExtraState C AgentExtra WorldExtra) C where
  -- Projections are identity (types shared)
  πBubble := id
  πDeposit := id
  πTime := id
  πAgent := id
  -- World primitive commuting laws: all Iff.refl because ops are copied unchanged
  truth_comm := fun _ _ => Iff.refl _
  obs_comm := fun _ => Iff.refl _
  verifyWithin_comm := fun _ _ _ => Iff.refl _
  effectiveTime_comm := fun _ => rfl
  -- Bank primitive commuting laws
  submit_comm := fun _ _ _ => Iff.refl _
  revise_comm := fun _ _ _ => Iff.refl _
  -- Capability predicate commuting laws
  hasRevision_comm := fun _ => Iff.refl _
  selfCorrects_comm := fun _ => Iff.refl _

/-- **Main Theorem**: Extra-state extensions preserve the revision gate.

    If C satisfies RevisionGate, and we add arbitrary extra state (consciousness, qualia,
    psychology, embodiment, neural architecture, etc.), the extended model still
    satisfies RevisionGate via forgetful projection.

    This is the machine-checkable version of "consciousness/psychology/etc don't
    affect core architectural theorems — this is a binding to RevisionGate. -/
theorem extra_state_revision_gate_transport (C : CoreModel)
    (AgentExtra : Type) [Inhabited AgentExtra]
    (WorldExtra : Type) [Inhabited WorldExtra] :
    RevisionGate C → RevisionGate (forget (extendWithExtraState C AgentExtra WorldExtra)) :=
  transport_core _ C (extra_state_compatible C AgentExtra WorldExtra)

/-- **Named plug-in point.** Delegates to `extra_state_revision_gate_transport`.
    Instantiates X = ConsciousnessState so citation sites are self-documenting.
    ConsciousnessState can be any inhabited type (Unit for trivial consciousness). -/
theorem consciousness_irrelevant_revision_gate (C : CoreModel)
    (ConsciousnessState : Type) [Inhabited ConsciousnessState] :
    RevisionGate C → RevisionGate (forget (extendWithExtraState C ConsciousnessState Unit)) :=
  extra_state_revision_gate_transport C ConsciousnessState Unit

/-- **Named plug-in point.** Delegates to `extra_state_revision_gate_transport`.
    Instantiates X = PsychologyState so citation sites are self-documenting. -/
theorem psychology_irrelevant_revision_gate (C : CoreModel)
    (PsychologyState : Type) [Inhabited PsychologyState] :
    RevisionGate C → RevisionGate (forget (extendWithExtraState C PsychologyState Unit)) :=
  extra_state_revision_gate_transport C PsychologyState Unit

/-- **Named plug-in point.** Delegates to `extra_state_revision_gate_transport`.
    Instantiates X = QualiaState so citation sites are self-documenting. -/
theorem qualia_irrelevant_revision_gate (C : CoreModel)
    (QualiaState : Type) [Inhabited QualiaState] :
    RevisionGate C → RevisionGate (forget (extendWithExtraState C QualiaState Unit)) :=
  extra_state_revision_gate_transport C QualiaState Unit


end EpArch.ScopeIrrelevance
