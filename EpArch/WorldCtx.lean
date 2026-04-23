/-
EpArch.WorldCtx — World Context (Parametric Semantic Signature)

This module defines WorldCtx: a parameterized semantic signature for world
layer theorems. Instead of concrete stubs (Truth := True), we use abstract
fields that can be instantiated differently for different purposes:
- WitnessCtx (in EpArch.WorldWitness): a concrete Bool-valued model proving
  that the assumption bundles are non-vacuous (satisfiable).
- Real domain models: domain-specific truth/verification semantics.

## Why Parametric?

Many EpArch claims are CONDITIONAL: "IF lies are possible AND
verification is bounded AND observation is partial, THEN mechanism M
follows." These conditions are formalized as W_* bundles (W_lies_possible,
W_bounded_verification, W_partial_observability, W_asymmetric_costs).

WorldCtx provides the parametric interface through which these world-level
assumptions enter the formalization. The obligation theorems in
AdversarialObligations take the form: W_* → mechanism claim.

By keeping WorldCtx abstract, we get two things:
1. Theorems that hold for ANY world satisfying the bundles (generality).
2. A clear separation between "what we assume about the world" and "what
   we prove about the architecture" (modularity).

## Design Philosophy

WorldCtx is NOT a world model — it's a signature/interface. Theorems stated
over (C : WorldCtx) hold for ANY instantiation satisfying the signature.
This makes assumptions explicit and avoids the "stubbed semantics" trap
where Truth := True makes everything vacuously satisfiable.

## Core Primitives

- World : Type — possible states of affairs
- Agent : Type — epistemic agents
- Claim : Type — propositions / things that can be true or false
- Obs : Type — observations (what's epistemically accessible)
- Truth : World → Claim → Prop — world-relative truth
- Utter : Agent → Claim → Prop — agent utterance (speech act)
- obs : World → Obs — observation function
- VerifyWithin : World → Claim → Nat → Prop — bounded verification
- effectiveTime : World → Nat — resource capacity at world

## Relationship to Other Files

- **EpArch.WorldWitness**: Concrete instantiation proving W_* bundles are
  satisfiable (non-vacuity).
- **EpArch.Adversarial.Obligations**: Obligation theorems conditioned on W_* bundles.
- **EpArch.Meta.FalsifiableNotAuthorizable**: Uses WorldCtx to prove the theory
  floor is falsifiable and not fully authorizable.
-/

import EpArch.Basic

namespace EpArch

universe u

/-! ## World Context Structure -/

/-- WorldCtx: semantic signature for world layer.

    This is the core interface that all world-parametric theorems
    are stated over. No concrete implementations here—just the shape. -/
structure WorldCtx where
  /-- Possible states of affairs -/
  World : Type u
  /-- Epistemic agents -/
  Agent : Type u
  /-- Propositions / claims -/
  Claim : Type u
  /-- Observations (epistemically accessible data) -/
  Obs : Type u

  /-- World-relative truth predicate -/
  Truth : World → Claim → Prop
  /-- Agent utterance (saying something, regardless of truth) -/
  Utter : Agent → Claim → Prop
  /-- Observation function: what's observable from a world -/
  obs : World → Obs
  /-- Bounded verification: can P be verified at w within t steps? -/
  VerifyWithin : World → Claim → Nat → Prop
  /-- Resource capacity at a world (for modeling constraints) -/
  effectiveTime : World → Nat

  /-- Witness that World is inhabited (for existential proofs) -/
  world_inhabited : Nonempty World
  /-- Witness that Agent is inhabited -/
  agent_inhabited : Nonempty Agent
  /-- Witness that Claim is inhabited -/
  claim_inhabited : Nonempty Claim


/-! ## Derived Concepts (Context-Parametric) -/

variable (C : WorldCtx)

/-- Lie: agent utters P, but P is false at w. -/
def WorldCtx.Lie (w : C.World) (a : C.Agent) (P : C.Claim) : Prop :=
  C.Utter a P ∧ ¬C.Truth w P

/-- Can_lie: agent can lie (exists a world and proposition where they do). -/
def WorldCtx.can_lie (a : C.Agent) : Prop :=
  ∃ w P, C.Lie w a P

/-- Partial observation equivalence: w0 and w1 look the same. -/
def WorldCtx.PartialObs (w0 w1 : C.World) : Prop :=
  C.obs w0 = C.obs w1

/-- P's truth is not determined by observations alone.
    There exist observationally equivalent worlds where P differs. -/
def WorldCtx.NotDeterminedByObs (P : C.Claim) : Prop :=
  ∃ w0 w1, C.PartialObs w0 w1 ∧ (C.Truth w0 P ↔ ¬C.Truth w1 P)

/-- P requires at least k steps to verify at w. -/
def WorldCtx.RequiresSteps (w : C.World) (P : C.Claim) (k : Nat) : Prop :=
  ∀ t, t < k → ¬C.VerifyWithin w P t


/-! ## World Assumption Bundles (Context-Parametric) -/

/-- Bundle for "lies are possible" assumption. -/
structure WorldCtx.W_lies_possible (C : WorldCtx) where
  /-- There exist false propositions -/
  some_false : ∃ w P, ¬C.Truth w P
  /-- Agents can utter any proposition -/
  unrestricted_utterance : ∀ a P, C.Utter a P

/-- Bundle for "verification is bounded" assumption. -/
structure WorldCtx.W_bounded_verification (C : WorldCtx) where
  /-- Some propositions require significant verification effort -/
  verification_has_cost : ∃ P k, k > 0 ∧ ∀ w, C.RequiresSteps w P k

/-- Bundle for "observations underdetermine truth" assumption. -/
structure WorldCtx.W_partial_observability (C : WorldCtx) where
  /-- Some truths are not determined by observations -/
  obs_underdetermines : ∃ P, C.NotDeterminedByObs P

/-- Bundle for "costs are asymmetric" assumption. -/
structure WorldCtx.W_asymmetric_costs (C : WorldCtx) where
  export_cost : Nat
  defense_cost : Nat
  asymmetry : export_cost < defense_cost

/-- Bundle for "multiple agents with heterogeneous epistemic access" assumption.

    Models the multi-agent collaboration case: distinct agents exist, lying
    pressure is real (false propositions exist), but not every agent has
    unrestricted access to every claim — secrets exist.

    This bundle is INCOMPATIBLE with W_lies_possible, which requires
    unrestricted utterance for all agents.  The incompatibility is the
    forcing argument: to maintain secrets under adversarial lying pressure,
    the authorization surface must be non-trivial (ACL cannot be open).

    Contrast with the single-agent case: one person managing their own bank
    under adversarial pressure from others does not need this bundle — they
    are the sole authority and open-mode ACL is correct for their bubble. -/
structure WorldCtx.W_multi_agent_heterogeneous (C : WorldCtx) where
  /-- At least two distinct agents exist -/
  distinct_agents : ∃ a₁ a₂ : C.Agent, a₁ ≠ a₂
  /-- False propositions exist (adversarial content pressure remains) -/
  some_false : ∃ w P, ¬C.Truth w P
  /-- Some agent cannot utter some claim — secrets / restricted access exists.
      This is the direct negation of W_lies_possible.unrestricted_utterance. -/
  secrets_exist : ∃ (a : C.Agent) (P : C.Claim), ¬C.Utter a P

/-- W_lies_possible and W_multi_agent_heterogeneous are mutually incompatible.

    W_lies_possible asserts unrestricted utterance for all agents.
    W_multi_agent_heterogeneous asserts some agent lacks utterance capability.
    They cannot both hold simultaneously.

    Forcing corollary (contrapositive): if secrets must be protected
    (W_multi_agent_heterogeneous holds), then the world cannot be fully
    adversarially open (W_lies_possible fails).  The authorization surface
    must be non-trivial to maintain the separation. -/
theorem WorldCtx.w_lies_multi_agent_incompatible (C : WorldCtx)
    (W_lies : C.W_lies_possible)
    (W_multi : C.W_multi_agent_heterogeneous) : False := by
  have ⟨a, P, h_no_utter⟩ := W_multi.secrets_exist
  exact h_no_utter (W_lies.unrestricted_utterance a P)


/-! ## Obligation Theorems (Context-Parametric)

These are the key theorems that convert mechanism claims into
conditional results over world assumptions.
-/

/-- Theorem: Lying is structurally possible under W_lies_possible. -/
theorem WorldCtx.lie_possible_of_W (C : WorldCtx) (W : C.W_lies_possible) :
    ∃ w a P, C.Lie w a P := by
  have ⟨w, P, h_false⟩ := W.some_false
  have ⟨a⟩ := C.agent_inhabited
  exact ⟨w, a, P, W.unrestricted_utterance a P, h_false⟩

/-- Theorem: Can_lie holds for all agents under W_lies_possible. -/
theorem WorldCtx.all_agents_can_lie_of_W (C : WorldCtx) (W : C.W_lies_possible)
    (a : C.Agent) : C.can_lie a := by
  have ⟨w, P, h_false⟩ := W.some_false
  exact ⟨w, P, W.unrestricted_utterance a P, h_false⟩

/-- Theorem: If all propositions are true in all worlds, no lie is constructible.

    The kernel discriminator is a no-op: every utterance is guaranteed true,
    so the accept/reject pass never rejects anything.  We would not need the
    kernel if this held — EpArch primitives exist precisely because it does not. -/
theorem WorldCtx.kernel_redundant_without_lies (C : WorldCtx)
    (h : ∀ w P, C.Truth w P) : ¬∃ w a P, C.Lie w a P :=
  fun ⟨w, _, P, _, h_false⟩ => h_false (h w P)

/-- Theorem: Bounded audit fails when time is insufficient. -/
theorem WorldCtx.bounded_audit_fails (C : WorldCtx) (w : C.World) (P : C.Claim)
    (k t : Nat) : C.RequiresSteps w P k → t < k → ¬C.VerifyWithin w P t := by
  intro h_requires h_lt
  exact h_requires t h_lt

/-- Theorem: Cost asymmetry follows from W_asymmetric_costs. -/
theorem WorldCtx.cost_asymmetry_of_W (C : WorldCtx) (W : C.W_asymmetric_costs) :
    W.export_cost < W.defense_cost :=
  W.asymmetry

/-- Theorem: Partial observability blocks omniscience.
    Under W_partial_observability, there exists a proposition that no agent
    can determine from observations alone — even with unlimited verification
    budget.  This is the epistemic-gap argument for why terminal closure is
    unreachable, distinct from the PRP cost-budget argument. -/
theorem WorldCtx.partial_obs_no_omniscience (C : WorldCtx) (W : C.W_partial_observability) :
    ∃ P, C.NotDeterminedByObs P :=
  W.obs_underdetermines


/-! ## Ledger Tradeoff: EpArch CAP Theorem (Commitment C2 Derived)

These definitions ground Commitment C2 ("no global ledger supports both innovation
and coordination") as a **proved theorem** rather than a hypothesis.  The key
insight is CAP-theoretic: under partial observability, no obs-based ledger can
simultaneously accept all locally-true claims (innovation / availability) and
reject all locally-false claims (coordination / consistency). -/

/-- An abstract ledger over a WorldCtx: maps each (world, claim) pair to a verdict. -/
def WorldCtx.Ledger (C : WorldCtx) : Type u := C.World → C.Claim → Prop

/-- Obs-based: observationally equivalent worlds receive the same verdict.
    This is the partition-tolerance leg of CAP: the ledger cannot distinguish
    worlds that look identical from the local observation channel. -/
def WorldCtx.obs_based (C : WorldCtx) (L : C.Ledger) : Prop :=
  ∀ (P : C.Claim) (w0 w1 : C.World), C.PartialObs w0 w1 → (L w0 P ↔ L w1 P)

/-- Supports innovation: accept every locally-true claim (availability leg).
    The ledger does not veto heterodox claims that are locally warranted. -/
def WorldCtx.supports_innovation (C : WorldCtx) (L : C.Ledger) : Prop :=
  ∀ (P : C.Claim) (w : C.World), C.Truth w P → L w P

/-- Supports coordination: only accept globally-true claims (consistency leg).
    The ledger enforces a shared acceptance standard across worlds. -/
def WorldCtx.supports_coordination (C : WorldCtx) (L : C.Ledger) : Prop :=
  ∀ (P : C.Claim) (w : C.World), L w P → C.Truth w P

/-- Latency partition bundle: communication latency exceeds the TTL window.
    When `latency > ttl_remaining`, any ledger deciding before expiry cannot
    have received information from a partitioned agent — motivating why
    ledgers in this regime are effectively obs-based. -/
structure WorldCtx.W_latency_partition (C : WorldCtx) where
  /-- Minimum propagation delay between partitioned agents (in steps) -/
  latency       : Nat
  /-- Steps remaining before the deposit expires (TTL window) -/
  ttl_remaining : Nat
  /-- The expiry deadline precedes the propagation delay: info cannot arrive in time -/
  partition_condition : latency > ttl_remaining

/-- **EpArch CAP Theorem** — Commitment C2 as a proved theorem.

    Under partial observability, no obs-based ledger can simultaneously support
    innovation (accept all locally-true claims) and coordination (reject all
    locally-false claims).

    Proof sketch: by `W_partial_observability`, pick P, w0, w1 with the same
    observable fingerprint but differing truth values.  If the ledger supports
    innovation it must accept P at whichever world has `Truth`.  Being obs-based,
    it gives the same verdict at the other world.  Coordination then forces `Truth`
    at that world too — contradicting the observation-differing hypothesis. -/
theorem WorldCtx.no_ledger_tradeoff (C : WorldCtx) (L : C.Ledger)
    (hObs : C.obs_based L) (W : C.W_partial_observability) :
    ¬(C.supports_innovation L ∧ C.supports_coordination L) := by
  intro ⟨hI, hC⟩
  -- Expose the ∀ forms so Lean sees them as functions without needing to unfold defs
  have hObs' : ∀ (P : C.Claim) (w0 w1 : C.World),
      C.PartialObs w0 w1 → (L w0 P ↔ L w1 P) := hObs
  have hI'   : ∀ (P : C.Claim) (w : C.World), C.Truth w P → L w P := hI
  have hC'   : ∀ (P : C.Claim) (w : C.World), L w P → C.Truth w P := hC
  have ⟨P, hND⟩ := W.obs_underdetermines
  have ⟨w0, w1, hPartial, hDiff⟩ := hND
  by_cases hT : C.Truth w0 P
  · -- Truth w0 P: innovation forces acceptance; obs-based propagates; coordination forces Truth w1.
    have hL0 : L w0 P       := hI' P w0 hT
    have hL1 : L w1 P       := (hObs' P w0 w1 hPartial).mp hL0
    exact hDiff.mp hT (hC' P w1 hL1)
  · -- ¬Truth w0 P: by hDiff.mpr contrapositive, Truth w1 P; symmetric.
    have hT1 : C.Truth w1 P :=
      Classical.byContradiction (fun hF1 => hT (hDiff.mpr hF1))
    have hL1 : L w1 P       := hI' P w1 hT1
    have hL0 : L w0 P       := (hObs' P w0 w1 hPartial).mpr hL1
    exact hT (hC' P w0 hL0)

/-- Corollary: in a latency-partitioned world, obs-based ledgers face the CAP tradeoff.
    `W_latency_partition` documents the physical mechanism (latency > TTL) explaining
    why any ledger deciding within the TTL window is effectively obs-based.
    Note: `hObs` remains an explicit assumption here; `W_latency_partition` is explanatory
    context motivating obs-basedness, not a proof of it.  For the architectural grounding
    that makes obs-basedness automatic, see `LocalLedger` below. -/
theorem WorldCtx.no_ledger_tradeoff_of_latency (C : WorldCtx) (L : C.Ledger)
    (W_po : C.W_partial_observability) (_ : C.W_latency_partition)
    (hObs : C.obs_based L) :
    ¬(C.supports_innovation L ∧ C.supports_coordination L) :=
  C.no_ledger_tradeoff L hObs W_po

/-- **Headline form** — no obs-based ledger simultaneously enables both goals.
    Existential-negation shape: it is impossible for any single obs-based ledger
    to satisfy both supports_innovation and supports_coordination.
    Reads as a direct global impossibility statement. -/
theorem WorldCtx.no_obs_based_universal_ledger (C : WorldCtx)
    (W : C.W_partial_observability) :
    ¬ ∃ L : C.Ledger,
      C.obs_based L ∧ C.supports_innovation L ∧ C.supports_coordination L := by
  intro ⟨L, hObs, hI, hC⟩
  exact C.no_ledger_tradeoff L hObs W ⟨hI, hC⟩

/-! ## Locally-Computed Ledgers: Architectural Grounding for obs_based

A locally-computed ledger is one whose verdict is determined solely by the
observation fingerprint `C.obs w`, not by the full world state `w`.  This is
the formal expression of the architectural constraint:

    the ledger lives inside the bubble and cannot see beyond the local
    observation boundary.

For such ledgers, `obs_based` is not an assumption — it is automatically
derived from the definition.  The dependency chain becomes:

    ledger locality (LocalLedger) → obs_based (automatic)
    + W_partial_observability → CAP tradeoff (no_ledger_tradeoff_local)

compared to the general theorem:

    hObs (assumed) + W_partial_observability → CAP tradeoff
-/

/-- A locally-computed ledger: verdict determined solely by the observable
    fingerprint `C.obs w`.  Formally a function `C.Obs → C.Claim → Prop`.
    This is the bubble-local decision procedure: it cannot read world state
    beyond what `C.obs` projects into the observation type. -/
def WorldCtx.LocalLedger (C : WorldCtx) : Type u := C.Obs → C.Claim → Prop

/-- Lift a LocalLedger to the full Ledger type by composing with `C.obs`. -/
def WorldCtx.localToLedger (C : WorldCtx) (f : C.LocalLedger) : C.Ledger :=
  fun w P => f (C.obs w) P

/-- Any locally-computed ledger is automatically obs-based.
    Proof: `PartialObs w0 w1 := C.obs w0 = C.obs w1`, so the verdict is identical
    by congruence — no external assumption about the ledger is needed. -/
theorem WorldCtx.localLedger_is_obs_based (C : WorldCtx) (f : C.LocalLedger) :
    C.obs_based (C.localToLedger f) :=
  fun P _ _ hPartial => Iff.of_eq (congrArg (f · P) hPartial)

/-- **CAP theorem for locally-computed ledgers** — `hObs` is not a free hypothesis.
    For any bubble-local ledger (one that reads only from `C.obs`), partial
    observability alone forces the innovation/coordination tradeoff.
    This is the clean architectural statement: locality + partial observability
    ⇒ no single ledger handles both goals. -/
theorem WorldCtx.no_ledger_tradeoff_local (C : WorldCtx) (f : C.LocalLedger)
    (W : C.W_partial_observability) :
    ¬(C.supports_innovation (C.localToLedger f) ∧
      C.supports_coordination (C.localToLedger f)) :=
  C.no_ledger_tradeoff (C.localToLedger f) (C.localLedger_is_obs_based f) W


/-! ## W4: WorldCtx Compatibility (Contract Mode)

This section defines compatibility for WorldCtx extensions, ensuring that
additions to a WorldCtx don't silently change the meaning of core primitives.
-/

/-- Extended WorldCtx: adds extra structure while preserving core. -/
structure ExtWorldCtx extends WorldCtx where
  /-- Extra world state -/
  WorldExtra : Type u
  /-- Extra agent state -/
  AgentExtra : Type u

/-- Compatibility witness for WorldCtx extensions.

    An extension E is compatible with a core C if:
    1. Core types can be projected from extended types
    2. Core operations commute with projection

    This ensures extensions can't silently change truth semantics. -/
structure WorldCtxCompatible (E : ExtWorldCtx) (C : WorldCtx) where
  /-- Projection on World -/
  πWorld : E.World → C.World
  /-- Projection on Agent -/
  πAgent : E.Agent → C.Agent
  /-- Projection on Claim -/
  πClaim : E.Claim → C.Claim
  /-- Projection on Obs -/
  πObs : E.Obs → C.Obs
  /-- Commuting law: Truth commutes with projection -/
  truth_comm : ∀ (w : E.World) (P : E.Claim),
    E.Truth w P ↔ C.Truth (πWorld w) (πClaim P)
  /-- Commuting law: Utter commutes with projection -/
  utter_comm : ∀ (a : E.Agent) (P : E.Claim),
    E.Utter a P ↔ C.Utter (πAgent a) (πClaim P)
  /-- Commuting law: obs commutes with projection -/
  obs_comm : ∀ (w : E.World),
    πObs (E.obs w) = C.obs (πWorld w)
  /-- Commuting law: VerifyWithin commutes with projection -/
  verify_comm : ∀ (w : E.World) (P : E.Claim) (t : Nat),
    E.VerifyWithin w P t ↔ C.VerifyWithin (πWorld w) (πClaim P) t
  /-- Commuting law: effectiveTime commutes with projection -/
  time_comm : ∀ (w : E.World),
    E.effectiveTime w = C.effectiveTime (πWorld w)

/-- Transport for W_lies_possible: compatible extensions preserve lies-possible.

    This transport requires an embedding witness showing the extension doesn't
    remove relevant worlds/claims from the domain. The embedding provides
    surjectivity-like properties needed to lift existential statements.

    See EpArch.Semantics.RevisionSafety for the full transport infrastructure. -/
structure WorldCtxEmbedding (E : ExtWorldCtx) (C : WorldCtx) (h : WorldCtxCompatible E C) where
  /-- Embed core world into extended world -/
  embedWorld : C.World → E.World
  /-- Embed core agent into extended agent -/
  embedAgent : C.Agent → E.Agent
  /-- Embed core claim into extended claim -/
  embedClaim : C.Claim → E.Claim
  /-- Embedding is section of projection (right inverse) -/
  world_section : ∀ w, h.πWorld (embedWorld w) = w
  agent_section : ∀ a, h.πAgent (embedAgent a) = a
  claim_section : ∀ P, h.πClaim (embedClaim P) = P

/-- Transport for W_lies_possible: compatible extensions with embeddings preserve lies-possible.

    **KEY THEOREM (Contract Mode)**: Uses embedding witness to lift existentials.

    The proof:
    1. C.W_lies_possible gives us w, P in C where ¬C.Truth w P
    2. Embed w, P into E using the embedding witness
    3. Use truth_comm to transfer: ¬E.Truth (embed w) (embed P)
    4. Use utter_comm similarly for unrestricted_utterance -/
theorem WorldCtx.transport_lies_possible (E : ExtWorldCtx) (C : WorldCtx)
    (h : WorldCtxCompatible E C) (emb : WorldCtxEmbedding E C h) :
    C.W_lies_possible → E.toWorldCtx.W_lies_possible := fun W_C =>
  -- Construct W_lies_possible for E.toWorldCtx
  { some_false :=
      let ⟨w, P, h_false⟩ := W_C.some_false
      ⟨emb.embedWorld w, emb.embedClaim P, fun h_true_E =>
        let h_true_C := (h.truth_comm (emb.embedWorld w) (emb.embedClaim P)).mp h_true_E
        h_false (emb.world_section w ▸ emb.claim_section P ▸ h_true_C)⟩
    unrestricted_utterance := fun a_E P_E =>
      (h.utter_comm a_E P_E).mpr (W_C.unrestricted_utterance _ _) }

/-- Transport for lie_possible_of_W: if C is lies-possible and E is compatible
    with embedding, then lies are possible in E.

    NOTE: This follows from transport_lies_possible + lie_possible_of_W. -/
theorem WorldCtx.transport_lie_possible (E : ExtWorldCtx) (C : WorldCtx)
    (h : WorldCtxCompatible E C) (emb : WorldCtxEmbedding E C h)
    (W : C.W_lies_possible) :
    ∃ w a P, E.Lie w a P := by
  have W_E := transport_lies_possible E C h emb W
  exact lie_possible_of_W E.toWorldCtx W_E


end EpArch
