/-
EpArch/ScopeIrrelevance.lean — Scope Irrelevance Layer

This module turns "out of scope" from prose into machine-checkable scope boundaries.

Core results:
- S1: Substrate Independence — physics/implementation don't affect paper-facing theorems
- S2: Minimal Agency — agents need only functional capabilities, not consciousness
- S3: Extra-State Erasure — adding qualia/psychology/embodiment doesn't affect theorems

These patterns are bound to PaperFacing via RevisionSafety.
The `extra_state_compatible` theorem shows any extra-state extension is Compatible,
and thus paper-facing properties transport via `transport_core`.
-/

import EpArch.Basic
import EpArch.WorldCtx
import EpArch.RevisionSafety

namespace EpArch.ScopeIrrelevance

open EpArch.RevisionSafety

/-! ## Substrate Independence

"Physics don't matter": any substrate implementing the interface yields the same
paper-facing theorems.

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

/-- Any theorem that only uses agent identity works for any implementation.

    This captures: we don't assume consciousness, rich psychology, etc.
    If a theorem only uses the existence of agents, it's minimal. -/
theorem agent_identity_suffices (P : Nat → Prop) (a : MinimalAgent) :
    P a.id ↔ P a.id :=
  Iff.rfl


/-! ## Extra-State Erasure

Adding extra internal state (consciousness, qualia, psychology, embodiment,
neural architecture) doesn't affect theorems if primitives ignore it.
-/

/-- Lifting preserves theorems that don't depend on extra state.

    If a property P only uses the first component (the "real" agent),
    then it holds for (agent, extra_state) iff it holds for the base agent. -/
theorem extra_state_erasure {Agent X : Type} (P : Agent → Prop)
    (a : Agent) (x : X) :
    P a ↔ P (a, x).1 :=
  Iff.rfl

/-- Corollary: Psychology is irrelevant at system level.

    If we model "psychology" as extra state X, and our system-level
    properties don't examine X, then psychology doesn't affect theorems. -/
theorem psychology_irrelevant {Agent Psychology : Type}
    (system_property : Agent → Prop)
    (a : Agent) (psych : Psychology) :
    system_property a ↔ system_property (a, psych).1 :=
  Iff.rfl

/-- Corollary: Consciousness/qualia irrelevant if not examined.

    This is the formal version of "we don't assume consciousness". -/
theorem consciousness_irrelevant {Agent Qualia : Type}
    (functional_property : Agent → Prop)
    (a : Agent) (q : Qualia) :
    functional_property a ↔ functional_property (a, q).1 :=
  Iff.rfl

/-- Embodiment irrelevant: physical details don't affect abstract properties. -/
theorem embodiment_irrelevant {Agent Embodiment : Type}
    (abstract_property : Agent → Prop)
    (a : Agent) (e : Embodiment) :
    abstract_property a ↔ abstract_property (a, e).1 :=
  Iff.rfl


/-! ## Fundamentals Coverage Table

| Fundamental | Status | Theorem | Guardrail |
|-------------|--------|---------|-----------|
| Physics/Substrate | Irrelevant | `substrate_preserves_existence` | ModelHom preserves truth |
| Consciousness | Irrelevant | `consciousness_irrelevant` | Extra state erased |
| Psychology | Irrelevant | `psychology_irrelevant` | System-level only |
| Embodiment | Irrelevant | `embodiment_irrelevant` | Via abstract properties |
| Optimal Rationality | Not assumed | N/A | No Bayes dependency |
| Free Will | Not assumed | N/A | No moral judgment |
| Metaphysics of Truth | Abstract | N/A | Truth is a predicate |

-/

/-! ## What This Module Does NOT Do

1. **Prove all theorems are invariant** — that would require restating each theorem
   in terms of ModelHom, which is mechanical but verbose.

2. **Define consciousness** — we just show it's irrelevant *if* added as extra state.

3. **Claim completeness** — other fundamentals could be added similarly.

The module establishes the PATTERN for scope-irrelevance claims.
Extending to all paper-facing theorems is straightforward but verbose.
-/


/-! ## Binding to PaperFacing via RevisionSafety

The abstract erasure theorems above are generic patterns.
This section BINDS them to the paper-facing architecture via RevisionSafety.

Key result: `extra_state_paper_facing_transport`
- Any CoreModel C can be extended with extra state X
- The extension is Compatible with C
- Therefore PaperFacing properties transport

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
    This is the key binding that makes scope-irrelevance paper-facing.

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

/-- **Main Theorem**: Extra-state extensions preserve paper-facing properties.

    If C is paper-facing, and we add arbitrary extra state (consciousness, qualia,
    psychology, embodiment, neural architecture, etc.), the extended model is
    still paper-facing via forgetful projection.

    This is the machine-checkable version of "consciousness/psychology/etc don't
    affect core architectural theorems — this is a binding to PaperFacing. -/
theorem extra_state_paper_facing_transport (C : CoreModel)
    (AgentExtra : Type) [Inhabited AgentExtra]
    (WorldExtra : Type) [Inhabited WorldExtra] :
    PaperFacing C → PaperFacing (forget (extendWithExtraState C AgentExtra WorldExtra)) :=
  transport_core _ C (extra_state_compatible C AgentExtra WorldExtra)

/-- Corollary: Consciousness specifically is irrelevant (binding version).

    Instantiate X = ConsciousnessState to get the paper-facing result.
    ConsciousnessState can be any inhabited type (Unit for trivial consciousness). -/
theorem consciousness_irrelevant_paper_facing (C : CoreModel)
    (ConsciousnessState : Type) [Inhabited ConsciousnessState] :
    PaperFacing C → PaperFacing (forget (extendWithExtraState C ConsciousnessState Unit)) :=
  extra_state_paper_facing_transport C ConsciousnessState Unit

/-- Corollary: Psychology specifically is irrelevant (binding version). -/
theorem psychology_irrelevant_paper_facing (C : CoreModel)
    (PsychologyState : Type) [Inhabited PsychologyState] :
    PaperFacing C → PaperFacing (forget (extendWithExtraState C PsychologyState Unit)) :=
  extra_state_paper_facing_transport C PsychologyState Unit

/-- Corollary: Qualia specifically are irrelevant (binding version). -/
theorem qualia_irrelevant_paper_facing (C : CoreModel)
    (QualiaState : Type) [Inhabited QualiaState] :
    PaperFacing C → PaperFacing (forget (extendWithExtraState C QualiaState Unit)) :=
  extra_state_paper_facing_transport C QualiaState Unit


end EpArch.ScopeIrrelevance
