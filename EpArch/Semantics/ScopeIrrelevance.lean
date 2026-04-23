/-
EpArch.Semantics.ScopeIrrelevance — Scope Irrelevance

Two transport results for extra-state invariance:

1. RevisionGate — `extra_state_revision_gate_transport`: extra-state extensions of a
   `CoreModel` preserve `RevisionGate` via a `Compatible` instance with identity
   projections and `transport_core`.

2. Convergence — `structurally_forced_phantom_extension`: `WorkingSystem` carries no
   `Agent` type parameter, so `StructurallyForced W` is independent of any agent-type
   annotation.  Phantom extensions are definitionally the identity.
-/

import EpArch.Basic
import EpArch.WorldCtx
import EpArch.Semantics.RevisionSafety
import EpArch.Convergence

open EpArch

namespace EpArch.ScopeIrrelevance

open EpArch.RevisionSafety


/-! ## RevisionGate Transport -/

/-- Extend `CoreModel C` with arbitrary `AgentExtra` and `WorldExtra` types, copying
    all core operations unchanged.  `getAgentExtra`/`getWorldExtra` are unused by
    `RevisionGate`. -/
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
    getAgentExtra := fun _ => default  -- unused by RevisionGate; any total value works
    getWorldExtra := default           -- unused by RevisionGate; any total value works
  }
  hasBubble := C.hasBubble

/-- `extendWithExtraState C` is `Compatible` with `C`: identity projections on all
    shared types; `Iff.refl` commuting laws because all ops are copied unchanged. -/
theorem extra_state_compatible (C : CoreModel)
    (AgentExtra : Type) [Inhabited AgentExtra]
    (WorldExtra : Type) [Inhabited WorldExtra] :
    Compatible (extendWithExtraState C AgentExtra WorldExtra) C where
  πBubble := id
  πDeposit := id
  πTime := id
  πAgent := id
  truth_comm := fun _ _ => Iff.refl _
  obs_comm := fun _ => Iff.refl _
  verifyWithin_comm := fun _ _ _ => Iff.refl _
  effectiveTime_comm := fun _ => rfl
  submit_comm := fun _ _ _ => Iff.refl _
  revise_comm := fun _ _ _ => Iff.refl _
  hasRevision_comm := fun _ => Iff.refl _
  selfCorrects_comm := fun _ => Iff.refl _

/-- `RevisionGate` transports across extra-state extension via `transport_core`. -/
theorem extra_state_revision_gate_transport (C : CoreModel)
    (AgentExtra : Type) [Inhabited AgentExtra]
    (WorldExtra : Type) [Inhabited WorldExtra] :
    RevisionGate C → RevisionGate (forget (extendWithExtraState C AgentExtra WorldExtra)) :=
  transport_core _ C (extra_state_compatible C AgentExtra WorldExtra)

/-- `RevisionGate` is invariant under consciousness-state extension. -/
theorem consciousness_irrelevant_revision_gate (C : CoreModel)
    (ConsciousnessState : Type) [Inhabited ConsciousnessState] :
    RevisionGate C → RevisionGate (forget (extendWithExtraState C ConsciousnessState Unit)) :=
  extra_state_revision_gate_transport C ConsciousnessState Unit

/-- `RevisionGate` is invariant under psychology-state extension. -/
theorem psychology_irrelevant_revision_gate (C : CoreModel)
    (PsychologyState : Type) [Inhabited PsychologyState] :
    RevisionGate C → RevisionGate (forget (extendWithExtraState C PsychologyState Unit)) :=
  extra_state_revision_gate_transport C PsychologyState Unit

/-- `RevisionGate` is invariant under qualia-state extension. -/
theorem qualia_irrelevant_revision_gate (C : CoreModel)
    (QualiaState : Type) [Inhabited QualiaState] :
    RevisionGate C → RevisionGate (forget (extendWithExtraState C QualiaState Unit)) :=
  extra_state_revision_gate_transport C QualiaState Unit


/-! ## Convergence Layer — Agent-Type Independence -/

/-- `WorkingSystem` carries no `Agent` type parameter: all fields are either `Bool` flags
    in `SystemSpec` or `Option GroundedXStrict` evidence records with locally-scoped
    types.  Annotating a `WorkingSystem` with a phantom agent type is the identity. -/
def phantomAgentExtension (_AgentType : Type) (W : WorkingSystem) : WorkingSystem := W

/-- `StructurallyForced W` is invariant under any phantom agent-type annotation.
    Because `WorkingSystem` has no `Agent` field, the extension is definitionally `id`. -/
theorem structurally_forced_phantom_extension
    (W : WorkingSystem) (AgentType : Type) :
    StructurallyForced (phantomAgentExtension AgentType W) ↔ StructurallyForced W :=
  Iff.rfl

/-- `StructurallyForced` is invariant under consciousness-state annotation. -/
theorem consciousness_invariant_under_forcing
    (W : WorkingSystem) (ConsciousnessState : Type) :
    StructurallyForced (phantomAgentExtension ConsciousnessState W) ↔ StructurallyForced W :=
  Iff.rfl

/-- `StructurallyForced` is invariant under psychology-state annotation. -/
theorem psychology_invariant_under_forcing
    (W : WorkingSystem) (PsychologyState : Type) :
    StructurallyForced (phantomAgentExtension PsychologyState W) ↔ StructurallyForced W :=
  Iff.rfl

/-- `StructurallyForced` is invariant under qualia-state annotation. -/
theorem qualia_invariant_under_forcing
    (W : WorkingSystem) (QualiaState : Type) :
    StructurallyForced (phantomAgentExtension QualiaState W) ↔ StructurallyForced W :=
  Iff.rfl


end EpArch.ScopeIrrelevance
