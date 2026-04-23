/-
EpArch.Agent.Corroboration — Multi-Agent Corroboration and Common-Mode Compromise

This module provides formal machinery for reasoning about when multi-agent
corroboration is required (conditional minimality) and when it fails
(common-mode/correlated compromise).

## Key Claims (Conditional, Not Realist)

1. **Necessity (T1):** If the goal includes "no single point of failure" and
   single-source attacks are possible, then single-attestation acceptance is
   forbidden → corroboration is required.

2. **Common-Mode Failure (T3):** If common-mode compromise is possible, then
   k-of-n corroboration without independence guarantees is insufficient.

3. **Sufficiency Under Independence (T2):** If at most t independent sources
   can be compromised and k > t independent attestations are required, then
   acceptance is resilient to that attack class.

This does not guarantee that humans apply corroboration in practice (no sociology),
that the real world satisfies the independence interface (no realism), or that
corroboration guarantees truth — it only reduces risk under explicit constraints.

## Design Principles

- No sociology — everything about admissible models and explicit constraints
- No Obs surface changes — orthogonal to NotDeterminedByObs
- Independence is explicit and optional (parameter, not baked in)
- Necessity driven by goal toggle (NoSinglePointFailure)

-/

import EpArch.Basic

namespace EpArch.Agent.Corroboration

/-! ## 1. Threat Models (Explicit Toggles) -/

/-- Single-source attack possibility: there exists a source that can be compromised
    to attest to a false statement.

    This is the "weak adversary" model: can corrupt one source. -/
structure SingleSourceAttack (Source Statement : Type) where
  /-- Attestation predicate -/
  Attests : Source → Statement → Prop
  /-- Truth predicate -/
  TrueStmt : Statement → Prop
  /-- There exists a compromisable source -/
  compromisable_source : Source
  /-- There exists a false statement -/
  false_stmt : Statement
  /-- The statement is false -/
  stmt_is_false : ¬ (TrueStmt false_stmt)
  /-- Under attack, the source attests to the false statement -/
  can_be_made_to_attest : Attests compromisable_source false_stmt

/-- Common-mode attack possibility: multiple sources can be simultaneously compromised
    in a correlated way (e.g., same upstream, same bubble, same propaganda channel).

    This is the "strong adversary" model: can corrupt multiple sources at once
    if they share a common failure mode. -/
structure CommonModeAttack (Source Statement : Type) where
  /-- Attestation predicate -/
  Attests : Source → Statement → Prop
  /-- Truth predicate -/
  TrueStmt : Statement → Prop
  /-- The set of co-compromisable sources -/
  compromised_sources : List Source
  /-- At least two sources can be jointly compromised -/
  at_least_two : compromised_sources.length ≥ 2
  /-- The false statement they can all be made to attest to -/
  false_stmt : Statement
  /-- The statement is false -/
  stmt_is_false : ¬ (TrueStmt false_stmt)
  /-- All sources in the set can be made to attest -/
  all_attest : ∀ s, s ∈ compromised_sources → Attests s false_stmt


/-! ## 2. Acceptance Rules -/

/-- Single-source acceptance: accepting a statement based on one attestation. -/
def SingleSourceAcceptance {Source Statement : Type}
    (Attests : Source → Statement → Prop) (s : Source) (phi : Statement) : Prop :=
  Attests s phi

/-- Witnesses for k-of-n acceptance (propositional version without decidability). -/
def HasKWitnesses {Source Statement : Type}
    (Attests : Source → Statement → Prop)
    (k : Nat) (pool : List Source) (phi : Statement) : Prop :=
  ∃ witnesses : List Source,
    witnesses.length ≥ k ∧
    (∀ s, s ∈ witnesses → s ∈ pool) ∧
    (∀ s, s ∈ witnesses → Attests s phi)

/-- K-of-N acceptance with pairwise independence requirement.
    This is the "robust" version that actually provides guarantees. -/
def KOfNIndependentAcceptance {Source Statement : Type}
    (Attests : Source → Statement → Prop)
    (Independent : Source → Source → Prop)
    (k : Nat) (pool : List Source) (phi : Statement) : Prop :=
  ∃ witnesses : List Source,
    witnesses.length ≥ k ∧
    (∀ s, s ∈ witnesses → s ∈ pool) ∧
    (∀ s, s ∈ witnesses → Attests s phi) ∧
    (∀ s1 s2, s1 ∈ witnesses → s2 ∈ witnesses → s1 ≠ s2 → Independent s1 s2)


/-! ## 3. Theorem T1: Necessity (Goal => No Single-Source Acceptance) -/

/-- **Theorem T1 (Necessity):**
    If single-source attacks are possible, then single-source acceptance
    can lead to accepting false statements.

    **Role:** This is the "mandatory feature" theorem — corroboration is
    required (not optional) if you want resilience to single-source compromise.

    **Proof Pattern:** Direct counterexample using the attack scenario. -/
theorem single_source_can_accept_false {Source Statement : Type}
    (attack : SingleSourceAttack Source Statement) :
    -- Single-source acceptance can accept a false statement
    ∃ (s : Source) (phi : Statement),
      SingleSourceAcceptance attack.Attests s phi ∧ ¬ (attack.TrueStmt phi) :=
  ⟨attack.compromisable_source, attack.false_stmt, attack.can_be_made_to_attest, attack.stmt_is_false⟩

/-- **Corollary (No-SPoF Necessity):**
    To achieve "no single point of failure" resilience under single-source attack
    capability, single-source acceptance must be rejected as a policy.

    This is the conditional minimality result: corroboration is FORCED by the goal. -/
theorem no_spof_requires_multi_source {Source Statement : Type}
    (attack : SingleSourceAttack Source Statement)
    -- Goal: no false statement should be accepted
    (h_goal : ∀ s phi, SingleSourceAcceptance attack.Attests s phi →
                            attack.TrueStmt phi) :
    -- Then we have a contradiction (the attack scenario violates the goal)
    False :=
  let ⟨s, phi, h_accept, h_false⟩ := single_source_can_accept_false attack
  h_false (h_goal s phi h_accept)


/-! ## 4. Theorem T3: Common-Mode Breaks Naive Corroboration -/

/-- Helper: element of take is element of original list.
    Core list fact used in T3 proof. -/
theorem mem_of_mem_take {α : Type} {k : Nat} {L : List α} {x : α}
    (h : x ∈ L.take k) : x ∈ L := by
  -- Proof by induction on L, with cases on k
  induction L generalizing k with
  | nil =>
    -- L = [], so L.take k = [], and x ∈ [] is impossible
    cases k with
    | zero => cases h
    | succ _ => cases h
  | cons y ys ih =>
    -- L = y :: ys
    cases k with
    | zero =>
      -- take 0 (y::ys) = [], so h : x ∈ [] is impossible
      cases h
    | succ k' =>
      -- take (k'+1) (y::ys) = y :: take k' ys
      simp only [List.take] at h
      cases h with
      | head => exact List.Mem.head _
      | tail _ htail => exact List.Mem.tail _ (ih htail)

/-- Helper: length of take k L equals min k |L|.
    We need the weaker form: if k ≤ |L|, then |take k L| ≥ k. -/
theorem length_take_ge {α : Type} (k : Nat) (L : List α) (h : k ≤ L.length) :
    (L.take k).length ≥ k := by
  -- Proof by induction on L, with k tracked
  induction L generalizing k with
  | nil =>
    -- L = [], so L.length = 0, and k ≤ 0 implies k = 0
    cases k with
    | zero => exact Nat.le_refl 0
    | succ _ => exact absurd h (Nat.not_succ_le_zero _)
  | cons y ys ih =>
    -- L = y :: ys, so L.length = ys.length + 1
    cases k with
    | zero =>
      -- k = 0, take 0 L = [], |[]| ≥ 0
      exact Nat.zero_le _
    | succ k' =>
      -- k = k' + 1, take (k'+1) (y::ys) = y :: take k' ys
      simp only [List.take, List.length]
      -- Need: (take k' ys).length + 1 ≥ k' + 1
      -- i.e., (take k' ys).length ≥ k'
      -- We have: k' + 1 ≤ ys.length + 1, so k' ≤ ys.length
      simp only [List.length] at h
      have h' : k' ≤ ys.length := Nat.le_of_succ_le_succ h
      exact Nat.succ_le_succ (ih k' h')

/-- **Theorem T3 (Common-Mode Failure):**
    If common-mode compromise is possible, then k-of-n corroboration
    (without independence requirements) can accept false statements,
    for any k up to the size of the compromised set.

    **Role:** Explains "bubble infection" — why counting sources
    is not sufficient when sources share failure modes.

    **Proof Pattern:** Direct counterexample using the attack scenario.

    NOTE: The core claim is the theorem statement itself. The proof strategy
    is straightforward (use first k compromised sources as witnesses). -/
theorem common_mode_breaks_naive_corroboration {Source Statement : Type}
    (attack : CommonModeAttack Source Statement)
    -- Any k up to the number of compromised sources
    (k : Nat)
    (h_k_le : k ≤ attack.compromised_sources.length) :
    -- Naive k-of-n can accept a false statement (using compromised pool)
    HasKWitnesses attack.Attests k attack.compromised_sources attack.false_stmt ∧
    ¬ (attack.TrueStmt attack.false_stmt) := by
  constructor
  · -- Construct witnesses: use the first k compromised sources
    -- Strategy: take k witnesses from compromised_sources
    -- |take k L| ≥ k (since k ≤ |L|) by length_take_ge
    -- All in pool: take is subset of original (by mem_of_mem_take)
    -- All attest: by all_attest field of attack
    exact ⟨attack.compromised_sources.take k,
           length_take_ge k attack.compromised_sources h_k_le,
           fun s hs => mem_of_mem_take hs,
           fun s hs => attack.all_attest s (mem_of_mem_take hs)⟩
  · exact attack.stmt_is_false


/-- **Corollary:** Under common-mode attack, even 2-of-2 corroboration fails
    (minimal interesting case). -/
theorem two_of_two_fails_under_common_mode {Source Statement : Type}
    (attack : CommonModeAttack Source Statement) :
    HasKWitnesses attack.Attests 2 attack.compromised_sources attack.false_stmt ∧
    ¬ (attack.TrueStmt attack.false_stmt) :=
  common_mode_breaks_naive_corroboration attack 2 attack.at_least_two



/-! ## 5. Theorem T3b: Unbounded Common-Mode (Fails Regardless of k) -/

/-- Unbounded common-mode attack: for every threshold k the attacker can field
    k co-compromised sources attesting to the same false claim.

    Models a shared upstream (propaganda channel, shared bubble, common feed)
    that can corrupt arbitrarily many consumers. The bounded CommonModeAttack
    above only defeats k <= pool size; this structure captures the stronger claim
    that *no* threshold k is safe when the attacker's compromise power is
    unlimited. -/
structure UnboundedCommonModeAttack (Source Statement : Type) where
  Attests : Source -> Statement -> Prop
  TrueStmt : Statement -> Prop
  false_stmt : Statement
  stmt_is_false : Not (TrueStmt false_stmt)
  /-- For every k, field k co-compromised sources all attesting false_stmt. -/
  can_compromise_k : forall (k : Nat), Exists (fun pool : List Source =>
    And (k <= pool.length) (forall s, List.Mem s pool -> Attests s false_stmt))

/-- **Theorem T3b (Common-Mode Failure, Unbounded):**
    Under an unbounded common-mode attack, naive k-of-n corroboration
    fails for *every* k -- there is no safe threshold.

    The attacker fields k co-compromised sources matching whatever threshold
    the receiver sets. No amount of corroboration (without independence
    guarantees) provides safety against this adversary.

    Proof: for any k, obtain k co-compromised sources via can_compromise_k;
    they satisfy HasKWitnesses for the same k. -/
theorem common_mode_fails_regardless_of_k {Source Statement : Type}
    (attack : UnboundedCommonModeAttack Source Statement)
    (k : Nat) :
    Exists (fun pool : List Source =>
      And (HasKWitnesses attack.Attests k pool attack.false_stmt)
          (Not (attack.TrueStmt attack.false_stmt))) :=
  Exists.elim (attack.can_compromise_k k) (fun pool h =>
    Exists.intro pool (And.intro
      (Exists.intro pool (And.intro
        h.1
        (And.intro (fun _ hs => hs) (fun _ hs => h.2 _ hs))))
      attack.stmt_is_false))

/-! ## 5. Theorem T4: Diversity Requirement -/

/-- **Theorem T4 (Diversity Requirement):**
    If common-mode compromise is in the threat model, then for any k up to
    the common-mode size, naive k-of-n fails. Only independence-aware
    corroboration can provide guarantees.

    **Role:** Keeps prose honest — corroboration is not magic;
    its value depends on a diversity assumption. -/
theorem common_mode_requires_diversity {Source Statement : Type}
    (attack : CommonModeAttack Source Statement) :
    -- For any k <= compromised set size, naive k-of-n can accept false
    ∀ k, k ≤ attack.compromised_sources.length →
      HasKWitnesses attack.Attests k attack.compromised_sources attack.false_stmt ∧
      ¬ (attack.TrueStmt attack.false_stmt) :=
  fun k h_le => common_mode_breaks_naive_corroboration attack k h_le


/-! ## 6. Theorem T2: Sufficiency Under Independence Bound -/

/-- Helper: filter length is at most list length -/
theorem filter_length_le {α : Type} (p : α → Bool) (L : List α) :
    (L.filter p).length ≤ L.length := by
  induction L with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [List.filter]
    cases hp : p x with
    | false =>
      simp only [hp, List.length]
      exact Nat.le_succ_of_le ih
    | true =>
      simp only [hp, List.length]
      exact Nat.succ_le_succ ih

/-- Helper: if |L| > |filter p L|, there exists an element not satisfying p -/
theorem exists_not_of_length_gt_filter {α : Type} (p : α → Bool) (L : List α)
    (h : L.length > (L.filter p).length) :
    ∃ x, x ∈ L ∧ p x = false := by
  induction L with
  | nil =>
    -- L = [], |L| = 0, impossible since 0 > 0 is false
    simp only [List.length] at h
    exact absurd h (Nat.lt_irrefl 0)
  | cons y ys ih =>
    simp only [List.filter] at h
    cases hp : p y with
    | false =>
      -- y doesn't satisfy p, we found our witness
      exact ⟨y, List.Mem.head _, hp⟩
    | true =>
      -- y satisfies p, so filter keeps it
      simp only [hp, List.length] at h
      -- h : ys.length + 1 > (ys.filter p).length + 1
      -- so ys.length > (ys.filter p).length
      have h' : ys.length > (ys.filter p).length := Nat.lt_of_succ_lt_succ h
      let ⟨x, hx_mem, hx_p⟩ := ih h'
      exact ⟨x, List.Mem.tail _ hx_mem, hx_p⟩

/-- Helper: pigeonhole — if |L| ≥ k > t and |filter p L| ≤ t, exists element not satisfying p -/
theorem pigeonhole_filter {α : Type} (p : α → Bool) (L : List α) (k t : Nat)
    (h_len : L.length ≥ k) (h_k_gt_t : k > t) (h_filter : (L.filter p).length ≤ t) :
    ∃ x, x ∈ L ∧ p x = false := by
  -- We need |L| > |filter p L|
  -- We have |L| ≥ k > t ≥ |filter p L|
  have h1 : L.length > t := Nat.lt_of_lt_of_le h_k_gt_t h_len
  have h2 : L.length > (L.filter p).length := Nat.lt_of_le_of_lt h_filter h1
  exact exists_not_of_length_gt_filter p L h2

/-- Independence interface: a predicate that two sources don't share failure modes. -/
def IndependenceBounded {Source : Type}
    (Independent : Source → Source → Prop)
    (compromised : Source → Prop)
    [DecidablePred compromised]
    (t : Nat) : Prop :=
  -- At most t sources can be compromised among any pairwise-independent set
  ∀ sources : List Source,
    (∀ s1 s2, s1 ∈ sources → s2 ∈ sources → s1 ≠ s2 → Independent s1 s2) →
    (sources.filter (fun s => compromised s)).length ≤ t

/-- Honest attestation implies truth. -/
def HonestImpliesTrue {Source Statement : Type}
    (Attests : Source → Statement → Prop)
    (TrueStmt : Statement → Prop)
    (compromised : Source → Prop) : Prop :=
  ∀ s phi, Attests s phi → ¬ (compromised s) → TrueStmt phi

/-- **Theorem T2 (Sufficiency):**
    If independence is bounded (at most t compromised among independent sources),
    honest attestation implies truth, and we require k > t independent attestations,
    then accepted statements are true.

    **Role:** Formal reason "why 2-3 independent attestations beats one."
    The key is the independence interface — without it, the guarantee vanishes.

    **Proof:** Uses pigeonhole argument via `pigeonhole_filter` helper lemma.
    The key step: if |witnesses| ≥ k > t ≥ |filter compromised witnesses|,
    then ∃ honest (not compromised) witness that attests to phi. -/
theorem k_of_n_suffices_under_independence {Source Statement : Type}
    (Attests : Source → Statement → Prop)
    (TrueStmt : Statement → Prop)
    (Independent : Source → Source → Prop)
    (compromised : Source → Prop)
    [DecidablePred compromised]
    (t k : Nat)
    -- Honest sources tell the truth
    (h_honest : HonestImpliesTrue Attests TrueStmt compromised)
    -- At most t independent sources compromised
    (h_bound : IndependenceBounded Independent compromised t)
    -- Require k > t attestations
    (h_k_gt_t : k > t)
    -- K-of-N independent acceptance holds
    (pool : List Source)
    (phi : Statement)
    (h_accept : KOfNIndependentAcceptance Attests Independent k pool phi) :
    -- Then the statement is true
    TrueStmt phi := by
  -- Core argument: k witnesses, at most t compromised, k > t implies ∃ honest witness
  -- That honest witness attests to phi, so by h_honest, TrueStmt phi
  match h_accept with
  | ⟨witnesses, h_len, _, h_attest, h_indep⟩ =>
    -- By h_bound, at most t witnesses are compromised
    have h_compromised_bound := h_bound witnesses h_indep
    -- Use pigeonhole: |witnesses| ≥ k > t ≥ |filter compromised witnesses|
    -- So there exists an honest (not compromised) witness
    let ⟨honest_witness, h_mem, h_not_comp⟩ :=
      pigeonhole_filter (fun s => compromised s) witnesses k t h_len h_k_gt_t h_compromised_bound
    -- The honest witness attests to phi
    have h_attests := h_attest honest_witness h_mem
    -- By h_honest, since honest_witness is not compromised and attests to phi, TrueStmt phi
    have h_not_compromised : ¬ (compromised honest_witness) := by
      intro h_comp
      -- h_not_comp : (decide (compromised honest_witness)) = false
      -- h_comp : compromised honest_witness
      -- With DecidablePred, we can derive a contradiction
      -- The key insight: when compromised honest_witness is true,
      -- decide (compromised honest_witness) must be true
      -- But h_not_comp says it's false
      have h_eq_true : decide (compromised honest_witness) = true := decide_eq_true h_comp
      -- Now we have: true = false
      have h_contra : true = false := Eq.trans (Eq.symm h_eq_true) h_not_comp
      exact Bool.noConfusion h_contra
    exact h_honest honest_witness phi h_attests h_not_compromised


/-! ## 7. Headline Packaging -/

/-- **Corroboration Necessity Package:**
    Bundles the key results.

    1. Single-source acceptance is vulnerable (T1)
    2. Common-mode breaks naive corroboration (T3)
    3. Only independence-aware k-of-n provides guarantees (T2, implicit) -/
theorem corroboration_package {Source Statement : Type}
    (single_attack : SingleSourceAttack Source Statement)
    (common_attack : CommonModeAttack Source Statement) :
    -- T1: Single-source can accept false
    (∃ s phi, SingleSourceAcceptance single_attack.Attests s phi ∧
                   ¬ (single_attack.TrueStmt phi)) ∧
    -- T3: Common-mode breaks k-of-n for k <= compromised size
    (∀ k, k ≤ common_attack.compromised_sources.length →
      HasKWitnesses common_attack.Attests k common_attack.compromised_sources
                    common_attack.false_stmt ∧
      ¬ (common_attack.TrueStmt common_attack.false_stmt)) :=
  ⟨single_source_can_accept_false single_attack, common_mode_requires_diversity common_attack⟩

end EpArch.Agent.Corroboration
