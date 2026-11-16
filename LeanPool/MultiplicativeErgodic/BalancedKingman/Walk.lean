/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.BalancedKingman.Windows

/-!
# The greedy decomposition of `[0, n)`

The paper's `r_±`, `a_i`, `b_i`: from the current position jump to the start of the next window,
cross it, and repeat. `bWalk`, `aWalk` and `blockCount` are that walk.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter

open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
/-!
### The greedy decomposition of `[0, n)`

The paper's `r_±`, `a_i`, `b_i`: from the current position, jump to the start of the next
good window and then past its end. `bWalk` is strictly increasing, so it exhausts `ℕ` and the
block count `t_n = max {t : b_t ≤ n}` is well defined with `t_n → ∞`.
-/

/-- Start of the next good window, as an offset from `x`. -/
noncomputable def rMinus (σ : Ω → Ω) (Λm : Set Ω) (x : Ω) : ℕ := hitTime σ Λm x

/-- End of that window: the first time *strictly after* `rMinus` landing in `Λ₊`. -/
noncomputable def rPlus (σ : Ω → Ω) (Λm Λp : Set Ω) (x : Ω) : ℕ :=
  rMinus σ Λm x + 1 + hitTime σ Λp (σ^[rMinus σ Λm x + 1] x)

omit [MeasurableSpace Ω] in
theorem rMinus_lt_rPlus (σ : Ω → Ω) (Λm Λp : Set Ω) (x : Ω) :
    rMinus σ Λm x < rPlus σ Λm Λp x := by
  rw [rPlus]; omega

/-- The paper's greedy walk: `b 0 = 0`, and from `b i` jump past the next good window. -/
noncomputable def bWalk (σ : Ω → Ω) (Λm Λp : Set Ω) : ℕ → Ω → ℕ
  | 0, _ => 0
  | (i + 1), ω => bWalk σ Λm Λp i ω + rPlus σ Λm Λp (σ^[bWalk σ Λm Λp i ω] ω)

/-- The matching window starts. -/
noncomputable def aWalk (σ : Ω → Ω) (Λm Λp : Set Ω) (i : ℕ) (ω : Ω) : ℕ :=
  bWalk σ Λm Λp i ω + rMinus σ Λm (σ^[bWalk σ Λm Λp i ω] ω)

omit [MeasurableSpace Ω] in
theorem bWalk_lt_succ (σ : Ω → Ω) (Λm Λp : Set Ω) (i : ℕ) (ω : Ω) :
    bWalk σ Λm Λp i ω < bWalk σ Λm Λp (i + 1) ω := by
  have := rMinus_lt_rPlus σ Λm Λp (σ^[bWalk σ Λm Λp i ω] ω)
  rw [bWalk]; omega

omit [MeasurableSpace Ω] in
theorem bWalk_le_aWalk (σ : Ω → Ω) (Λm Λp : Set Ω) (i : ℕ) (ω : Ω) :
    bWalk σ Λm Λp i ω ≤ aWalk σ Λm Λp i ω := by
  rw [aWalk]; omega

omit [MeasurableSpace Ω] in
theorem aWalk_lt_bWalk_succ (σ : Ω → Ω) (Λm Λp : Set Ω) (i : ℕ) (ω : Ω) :
    aWalk σ Λm Λp i ω < bWalk σ Λm Λp (i + 1) ω := by
  have := rMinus_lt_rPlus σ Λm Λp (σ^[bWalk σ Λm Λp i ω] ω)
  rw [aWalk, bWalk]; omega

omit [MeasurableSpace Ω] in
theorem bWalk_strictMono (σ : Ω → Ω) (Λm Λp : Set Ω) (ω : Ω) :
    StrictMono (fun i => bWalk σ Λm Λp i ω) :=
  strictMono_nat_of_lt_succ (fun i => bWalk_lt_succ σ Λm Λp i ω)

omit [MeasurableSpace Ω] in
/-- The walk exhausts `ℕ`, which is what makes `t_n = max {t : b_t ≤ n}` well defined and
`t_n → ∞`. -/
theorem tendsto_bWalk (σ : Ω → Ω) (Λm Λp : Set Ω) (ω : Ω) :
    Tendsto (fun i => bWalk σ Λm Λp i ω) atTop atTop :=
  (bWalk_strictMono σ Λm Λp ω).tendsto_atTop

theorem measurable_rMinus {σ : Ω → Ω} (hσm : Measurable σ) {Λm : Set Ω}
    (hm : MeasurableSet Λm) : Measurable (rMinus σ Λm) := measurable_hitTime hσm hm

theorem measurable_rPlus {σ : Ω → Ω} (hσm : Measurable σ) {Λm Λp : Set Ω}
    (hm : MeasurableSet Λm) (hp : MeasurableSet Λp) : Measurable (rPlus σ Λm Λp) := by
  have h1 : Measurable (rMinus σ Λm) := measurable_rMinus hσm hm
  have h2 : Measurable (fun x => hitTime σ Λp (σ^[rMinus σ Λm x + 1] x)) := by
    refine measurable_to_countable' (fun n => ?_)
    have : (fun x => hitTime σ Λp (σ^[rMinus σ Λm x + 1] x)) ⁻¹' {n}
        = ⋃ m : ℕ, ((rMinus σ Λm) ⁻¹' {m}) ∩ ((fun x => hitTime σ Λp (σ^[m + 1] x)) ⁻¹' {n}) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h; exact ⟨rMinus σ Λm x, rfl, h⟩
      · rintro ⟨m, hm', hn⟩; rw [hm']; exact hn
    rw [this]
    refine MeasurableSet.iUnion (fun m => (h1 (measurableSet_singleton m)).inter ?_)
    exact (measurable_hitTime hσm hp).comp (hσm.iterate (m + 1)) (measurableSet_singleton n)
  exact (h1.add measurable_const).add h2

theorem measurable_bWalk {σ : Ω → Ω} (hσm : Measurable σ) {Λm Λp : Set Ω}
    (hm : MeasurableSet Λm) (hp : MeasurableSet Λp) (i : ℕ) :
    Measurable (bWalk σ Λm Λp i) := by
  induction i with
  | zero => simp [bWalk]
  | succ i ih =>
    have hcomp : Measurable (fun ω => rPlus σ Λm Λp (σ^[bWalk σ Λm Λp i ω] ω)) := by
      refine measurable_to_countable' (fun n => ?_)
      have : (fun ω => rPlus σ Λm Λp (σ^[bWalk σ Λm Λp i ω] ω)) ⁻¹' {n}
          = ⋃ m : ℕ, ((bWalk σ Λm Λp i) ⁻¹' {m})
              ∩ ((fun ω => rPlus σ Λm Λp (σ^[m] ω)) ⁻¹' {n}) := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff]
        constructor
        · intro h; exact ⟨bWalk σ Λm Λp i ω, rfl, h⟩
        · rintro ⟨m, hm', hn⟩; rw [hm']; exact hn
      rw [this]
      refine MeasurableSet.iUnion (fun m => (ih (measurableSet_singleton m)).inter ?_)
      exact ((measurable_rPlus hσm hm hp).comp (hσm.iterate m)) (measurableSet_singleton n)
    change Measurable (fun ω => bWalk σ Λm Λp i ω + rPlus σ Λm Λp (σ^[bWalk σ Λm Λp i ω] ω))
    exact ih.add hcomp

/-- **Subadditivity chained along the greedy walk** — the structural core of the paper's
`f_n(\omega) \le \sum f_{a_i \to b_i} + \sum f_{b_{i-1} \to a_i} + \cdots` display.

Each step of the walk contributes two pieces: the gap `[b_i, a_i)` before the next good window
opens, and the good block `[a_i, b_{i+1})` itself. The `f 0 ω` on the right is not slack that can
be dropped — subadditivity at `(0,0)` gives `f 0 ≤ 2 f 0`, i.e. `f 0 ≥ 0`, so the empty walk
genuinely costs `f 0 ω`. It is harmless downstream, vanishing when divided by `n`. -/
theorem SubadditiveFamily.le_sum_bWalk {σ : Ω → Ω} {f : ℕ → Ω → ℝ} (hf : SubadditiveFamily σ f)
    (Λm Λp : Set Ω) (t : ℕ) (ω : Ω) :
    f (bWalk σ Λm Λp t ω) ω ≤ f 0 ω +
      ∑ i ∈ Finset.range t,
        (f (aWalk σ Λm Λp i ω - bWalk σ Λm Λp i ω) (σ^[bWalk σ Λm Λp i ω] ω)
         + f (bWalk σ Λm Λp (i + 1) ω - aWalk σ Λm Λp i ω) (σ^[aWalk σ Λm Λp i ω] ω)) := by
  induction t with
  | zero => simp [bWalk]
  | succ t ih =>
    have hba : bWalk σ Λm Λp t ω ≤ aWalk σ Λm Λp t ω := bWalk_le_aWalk σ Λm Λp t ω
    have hab : aWalk σ Λm Λp t ω < bWalk σ Λm Λp (t + 1) ω := aWalk_lt_bWalk_succ σ Λm Λp t ω
    -- peel the whole step off the front of `[0, b_{t+1})`
    have h1 : f (bWalk σ Λm Λp (t + 1) ω) ω
        ≤ f (bWalk σ Λm Λp (t + 1) ω - bWalk σ Λm Λp t ω) (σ^[bWalk σ Λm Λp t ω] ω)
          + f (bWalk σ Λm Λp t ω) ω := by
      have h := hf.2 (bWalk σ Λm Λp (t + 1) ω - bWalk σ Λm Λp t ω) (bWalk σ Λm Λp t ω) ω
      rwa [Nat.sub_add_cancel (by omega)] at h
    -- and split that step into its gap and its good block
    have h2 : f (bWalk σ Λm Λp (t + 1) ω - bWalk σ Λm Λp t ω) (σ^[bWalk σ Λm Λp t ω] ω)
        ≤ f (bWalk σ Λm Λp (t + 1) ω - aWalk σ Λm Λp t ω) (σ^[aWalk σ Λm Λp t ω] ω)
          + f (aWalk σ Λm Λp t ω - bWalk σ Λm Λp t ω) (σ^[bWalk σ Λm Λp t ω] ω) := by
      have h := hf.2 (bWalk σ Λm Λp (t + 1) ω - aWalk σ Λm Λp t ω)
        (aWalk σ Λm Λp t ω - bWalk σ Λm Λp t ω) (σ^[bWalk σ Λm Λp t ω] ω)
      have harith : (bWalk σ Λm Λp (t + 1) ω - aWalk σ Λm Λp t ω)
          + (aWalk σ Λm Λp t ω - bWalk σ Λm Λp t ω)
          = bWalk σ Λm Λp (t + 1) ω - bWalk σ Λm Λp t ω := by omega
      have hpt : σ^[aWalk σ Λm Λp t ω - bWalk σ Λm Λp t ω] (σ^[bWalk σ Λm Λp t ω] ω)
          = σ^[aWalk σ Λm Λp t ω] ω := by
        rw [← Function.iterate_add_apply]
        congr 1
        omega
      rw [harith, hpt] at h
      exact h
    rw [Finset.sum_range_succ]
    linarith [ih]

omit [MeasurableSpace Ω] in
/-- The walk's window start really is a `Λ₋` point. -/
theorem iterate_aWalk_mem {σ : Ω → Ω} {Λm Λp : Set Ω} {ω : Ω} (i : ℕ)
    (hex : ∃ n, σ^[n] (σ^[bWalk σ Λm Λp i ω] ω) ∈ Λm) :
    σ^[aWalk σ Λm Λp i ω] ω ∈ Λm := by
  have h := hitTime_spec hex
  change σ^[bWalk σ Λm Λp i ω + rMinus σ Λm (σ^[bWalk σ Λm Λp i ω] ω)] ω ∈ Λm
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact h

/-- The number of completed good blocks by time `n`: the paper's `t_n = max {t : b_t ≤ n}`.

Well defined precisely because `bWalk` is strictly increasing, which forces `b_t ≥ t` and so
confines the candidate set to `[0, n]`. -/
noncomputable def blockCount (σ : Ω → Ω) (Λm Λp : Set Ω) (n : ℕ) (ω : Ω) : ℕ :=
  Nat.findGreatest (fun t => bWalk σ Λm Λp t ω ≤ n) n

omit [MeasurableSpace Ω] in
theorem self_le_bWalk (σ : Ω → Ω) (Λm Λp : Set Ω) (t : ℕ) (ω : Ω) :
    t ≤ bWalk σ Λm Λp t ω := (bWalk_strictMono σ Λm Λp ω).le_apply

omit [MeasurableSpace Ω] in
theorem bWalk_blockCount_le (σ : Ω → Ω) (Λm Λp : Set Ω) (n : ℕ) (ω : Ω) :
    bWalk σ Λm Λp (blockCount σ Λm Λp n ω) ω ≤ n := by
  have h0 : bWalk σ Λm Λp 0 ω ≤ n := by rw [bWalk]; exact Nat.zero_le n
  exact Nat.findGreatest_spec (P := fun t => bWalk σ Λm Λp t ω ≤ n) (Nat.zero_le n) h0

omit [MeasurableSpace Ω] in
theorem le_blockCount {σ : Ω → Ω} {Λm Λp : Set Ω} {t n : ℕ} (ω : Ω)
    (h : bWalk σ Λm Λp t ω ≤ n) : t ≤ blockCount σ Λm Λp n ω :=
  Nat.le_findGreatest (le_trans (self_le_bWalk σ Λm Λp t ω) h) h

omit [MeasurableSpace Ω] in
/-- `t_n → ∞`, which is what makes the two end segments of the decomposition negligible. -/
theorem tendsto_blockCount (σ : Ω → Ω) (Λm Λp : Set Ω) (ω : Ω) :
    Tendsto (fun n => blockCount σ Λm Λp n ω) atTop atTop :=
  tendsto_atTop_atTop.mpr fun t => ⟨bWalk σ Λm Λp t ω, fun _ hn => le_blockCount ω hn⟩

/-- The least `j ≥ k` satisfying `p ω`, falling back to `k` itself when there is none. -/
noncomputable def nextIndex (p : Ω → ℕ → Prop) (k : ℕ) (ω : Ω) : ℕ :=
  max k (sInf {j | k ≤ j ∧ p ω j})

omit [MeasurableSpace Ω] in
theorem le_nextIndex (p : Ω → ℕ → Prop) (k : ℕ) (ω : Ω) : k ≤ nextIndex p k ω := le_max_left _ _

omit [MeasurableSpace Ω] in
theorem nextIndex_spec {p : Ω → ℕ → Prop} {k : ℕ} {ω : Ω} (h : ∃ j, k ≤ j ∧ p ω j) :
    p ω (nextIndex p k ω) := by
  have hmem : sInf {j | k ≤ j ∧ p ω j} ∈ {j | k ≤ j ∧ p ω j} := Nat.sInf_mem h
  have hge : k ≤ sInf {j | k ≤ j ∧ p ω j} := hmem.1
  rw [nextIndex, max_eq_right hge]
  exact hmem.2

omit [MeasurableSpace Ω] in
/-- Whatever `p` does, the fallback keeps the enumeration diverging *pointwise* — which is what
`backwardVitali`'s `hjtop` demands (it quantifies over every `ω`, not a.e. `ω`). -/
theorem tendsto_nextIndex (p : Ω → ℕ → Prop) (ω : Ω) :
    Tendsto (fun k => nextIndex p k ω) atTop atTop :=
  tendsto_atTop_mono (fun k => le_nextIndex p k ω) tendsto_id

theorem measurable_nextIndex {p : Ω → ℕ → Prop} (hp : ∀ j, MeasurableSet {ω | p ω j}) (k : ℕ) :
    Measurable (nextIndex p k) := by
  classical
  refine measurable_to_countable' (fun n => ?_)
  rcases lt_or_ge n k with hnk | hkn
  · have : (nextIndex p k) ⁻¹' {n} = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      exact absurd (h ▸ le_nextIndex p k ω) (by omega)
    rw [this]; exact MeasurableSet.empty
  · have hchar : (nextIndex p k) ⁻¹' {n}
        = ({ω | p ω n} ∩ ⋂ j : ℕ, ⋂ _ : k ≤ j ∧ j < n, {ω | p ω j}ᶜ)
          ∪ (if n = k then {ω | ∀ j : ℕ, k ≤ j → ¬ p ω j} else ∅) := by
      ext ω
      have hset : ∀ m : ℕ, m ∈ {j | k ≤ j ∧ p ω j} ↔ (k ≤ m ∧ p ω m) := fun m => Iff.rfl
      constructor
      · intro h
        have h' : nextIndex p k ω = n := h
        by_cases hex : ∃ j, k ≤ j ∧ p ω j
        · have hmem : sInf {j | k ≤ j ∧ p ω j} ∈ {j | k ≤ j ∧ p ω j} := Nat.sInf_mem hex
          have hge : k ≤ sInf {j | k ≤ j ∧ p ω j} := hmem.1
          have hEq : sInf {j | k ≤ j ∧ p ω j} = n := by
            rw [nextIndex, max_eq_right hge] at h'; exact h'
          refine Or.inl ⟨by rw [← hEq]; exact hmem.2, ?_⟩
          simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_ofPred_eq]
          rintro j ⟨hkj, hjn⟩ hpj
          exact absurd (Nat.sInf_le ((hset j).mpr ⟨hkj, hpj⟩)) (by omega)
        · have hempty : {j | k ≤ j ∧ p ω j} = ∅ := by
            ext j
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
            exact fun hkj hpj => (not_exists.mp hex j) ⟨hkj, hpj⟩
          have hval : nextIndex p k ω = k := by rw [nextIndex, hempty]; simp
          have hnk' : n = k := by rw [← h', hval]
          refine Or.inr ?_
          rw [ite_eq_left hnk']
          simp only [Set.mem_ofPred_eq]
          exact fun j hkj hpj => (not_exists.mp hex j) ⟨hkj, hpj⟩
      · intro h
        change nextIndex p k ω = n
        rcases h with ⟨hpn, hmin⟩ | hnever
        · simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_ofPred_eq] at hmin
          have hex : ∃ j, k ≤ j ∧ p ω j := ⟨n, hkn, hpn⟩
          have hmem : sInf {j | k ≤ j ∧ p ω j} ∈ {j | k ≤ j ∧ p ω j} := Nat.sInf_mem hex
          have hge : k ≤ sInf {j | k ≤ j ∧ p ω j} := hmem.1
          rw [nextIndex, max_eq_right hge]
          refine le_antisymm (Nat.sInf_le ((hset n).mpr ⟨hkn, hpn⟩)) ?_
          by_contra hc
          rw [not_le] at hc
          exact hmin _ ⟨hge, hc⟩ hmem.2
        · by_cases hnk' : n = k
          · rw [ite_eq_left hnk'] at hnever
            simp only [Set.mem_ofPred_eq] at hnever
            have hempty : {j | k ≤ j ∧ p ω j} = ∅ := by
              ext j
              simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
              exact fun hkj hpj => hnever j hkj hpj
            rw [nextIndex, hempty]
            simp [hnk']
          · rw [ite_eq_right hnk'] at hnever
            exact absurd hnever (Set.notMem_empty ω)
    rw [hchar]
    refine MeasurableSet.union ((hp n).inter ?_) ?_
    · exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hp j).compl
    · by_cases hnk' : n = k
      · rw [ite_eq_left hnk']
        have : {ω | ∀ j : ℕ, k ≤ j → ¬ p ω j} = ⋂ j : ℕ, ⋂ _ : k ≤ j, {ω | p ω j}ᶜ := by
          ext ω; simp [Set.mem_iInter]
        rw [this]
        exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hp j).compl
      · rw [ite_eq_right hnk']; exact MeasurableSet.empty

/-- **The good-time windows for `balancedKingman_of_integrable`.** Feeding the enumeration above
into
`backwardVitali` produces disjoint two-sided windows covering all but `ε` of the space, whose
centres are a.e. genuine good times, i.e. times `j` with `f_{-j→j}(ω) < 2jq`.

This is the paper's "apply Backward Vitali to the `j_i`s and the `-j_i`s with parameter
`ε' = min{ε, δ}`" step. The one wrinkle formalization forces: `backwardVitali` needs
`j_k(ω) → ∞` for *every* `ω`, whereas the good times are only infinite almost everywhere, which
is why the enumeration falls back to `k` off the full-measure set. -/
theorem exists_good_windows [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (⇑σ) μ) (f : ℕ → Ω → ℝ)
    (hfm : ∀ n, Measurable (f n)) (q : ℝ) (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (hinf : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∃ j : ℕ, k ≤ j ∧ 1 ≤ j ∧
      f (2 * j) (zIter σ (-(j : ℤ)) ω) < 2 * j * q) :
    ∃ (A : Set Ω) (jω : Ω → ℕ), MeasurableSet A ∧ Measurable jω ∧
      (A.PairwiseDisjoint fun ω => (fun i => zIter σ i ω) '' Set.Icc (-(jω ω : ℤ)) (jω ω)) ∧
      ENNReal.ofReal (1 - ε) <
        μ (⋃ ω ∈ A, (fun i => zIter σ i ω) '' Set.Icc (-(jω ω : ℤ)) (jω ω)) ∧
      (∀ᵐ ω ∂μ, ω ∈ A → N ≤ jω ω ∧ 1 ≤ jω ω ∧
        f (2 * jω ω) (zIter σ (-(jω ω : ℤ)) ω) < 2 * (jω ω) * q) := by
  classical
  -- the radius lower bound `N` is what keeps `μ Λ₊ = μ A` small: the windows are disjoint and
  -- each holds `2j + 1 ≥ 2N + 1` points, so forcing `j ≥ N` forces `μ A ≲ 1/(2N+1)`.
  set p : Ω → ℕ → Prop :=
    fun ω j => N ≤ j ∧ 1 ≤ j ∧ f (2 * j) (zIter σ (-(j : ℤ)) ω) < 2 * j * q with hp
  have hpm : ∀ j, MeasurableSet {ω | p ω j} := by
    intro j
    have hmeas : Measurable (fun ω => f (2 * j) (zIter σ (-(j : ℤ)) ω)) := by
      have : (fun ω => f (2 * j) (zIter σ (-(j : ℤ)) ω))
          = fun ω => f (2 * j) ((σ.symm : Ω ≃ᵐ Ω)^[j] ω) := by
        funext ω; rw [zIter_neg_natCast]
      rw [this]
      exact (hfm (2 * j)).comp (σ.symm.measurable.iterate j)
    by_cases hj : N ≤ j ∧ 1 ≤ j
    · have : {ω | p ω j} = {ω | f (2 * j) (zIter σ (-(j : ℤ)) ω) < 2 * j * q} := by
        ext ω; simp [hp, hj.1, hj.2]
      rw [this]
      exact measurableSet_lt hmeas measurable_const
    · have : {ω | p ω j} = ∅ := by ext ω; simp [hp]; tauto
      rw [this]; exact MeasurableSet.empty
  obtain ⟨A, jω, hAm, hjωm, hjmem, hdisj, hcov⟩ :=
    backwardVitali μ σ hσ ε hε (fun k => nextIndex p k) (fun k => measurable_nextIndex hpm k)
      (fun ω => tendsto_nextIndex p ω)
  refine ⟨A, jω, hAm, hjωm, hdisj, hcov, ?_⟩
  filter_upwards [hinf] with ω hω hmem
  obtain ⟨k, hk⟩ := hjmem ω hmem
  have hex : ∃ j : ℕ, k ≤ j ∧ p ω j := by
    obtain ⟨j, hkj, hj1, hjq⟩ := hω (max k N)
    exact ⟨j, le_trans (le_max_left k N) hkj, le_trans (le_max_right k N) hkj, hj1, hjq⟩
  have := nextIndex_spec (p := p) (k := k) (ω := ω) hex
  rw [← hk] at this
  exact this

/-- `blockCount n` is measurable. `Nat.findGreatest` recurses on its *bound*, so fix the
threshold `N` and induct on the search depth: each step is a measurable `if`. -/
theorem measurable_blockCount {σ : Ω → Ω} (hσm : Measurable σ) {Λm Λp : Set Ω}
    (hm : MeasurableSet Λm) (hp : MeasurableSet Λp) (n : ℕ) :
    Measurable (blockCount σ Λm Λp n) := by
  classical
  have key : ∀ N t : ℕ,
      Measurable (fun ω => Nat.findGreatest (fun s => bWalk σ Λm Λp s ω ≤ N) t) := by
    intro N t
    induction t with
    | zero => simp
    | succ t ih =>
      have hset : MeasurableSet {ω | bWalk σ Λm Λp (t + 1) ω ≤ N} :=
        (measurable_bWalk hσm hm hp (t + 1)) measurableSet_Iic
      have hrw : (fun ω => Nat.findGreatest (fun s => bWalk σ Λm Λp s ω ≤ N) (t + 1))
          = fun ω => if bWalk σ Λm Λp (t + 1) ω ≤ N then t + 1
                     else Nat.findGreatest (fun s => bWalk σ Λm Λp s ω ≤ N) t := by
        funext ω
        exact Nat.findGreatest_succ _
      rw [hrw]
      exact Measurable.ite hset measurable_const ih
  exact key n n

/-- **The `t_n = 0` estimate.** `μ{t_n = 0} → 0`, the other half of the paper's cutoff choice.

`{t_n = 0}` is antitone in `n` (more time fits more blocks) with empty intersection: at
`n = b_1(ω)` the first block already fits, so `t_n ≥ 1`. -/
theorem tendsto_measure_blockCount_eq_zero (μ : Measure Ω) [IsFiniteMeasure μ] {σ : Ω → Ω}
    (hσm : Measurable σ) {Λm Λp : Set Ω} (hm : MeasurableSet Λm) (hp : MeasurableSet Λp) :
    Tendsto (fun n : ℕ => μ {ω | blockCount σ Λm Λp n ω = 0}) atTop (nhds 0) := by
  have hmeas : ∀ n : ℕ, NullMeasurableSet {ω | blockCount σ Λm Λp n ω = 0} μ := fun n =>
    ((measurable_blockCount hσm hm hp n) (measurableSet_singleton 0)).nullMeasurableSet
  have hmono : ∀ (a b : ℕ) (ω : Ω), a ≤ b →
      blockCount σ Λm Λp a ω ≤ blockCount σ Λm Λp b ω := by
    intro a b ω hab
    exact Nat.findGreatest_mono (fun t ht => le_trans ht hab) hab
  have hanti : Antitone (fun n : ℕ => {ω | blockCount σ Λm Λp n ω = 0}) := by
    intro a b hab ω hω
    have := hmono a b ω hab
    simp only [Set.mem_ofPred_eq] at hω ⊢
    omega
  have hempty : (⋂ n : ℕ, {ω | blockCount σ Λm Λp n ω = 0}) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    refine ⟨bWalk σ Λm Λp 1 ω, ?_⟩
    simp only [Set.mem_ofPred_eq]
    have h1 : 1 ≤ blockCount σ Λm Λp (bWalk σ Λm Λp 1 ω) ω := le_blockCount ω (le_refl _)
    omega
  have h := tendsto_measure_iInter_atTop (μ := μ) hmeas hanti ⟨0, measure_ne_top μ _⟩
  rwa [hempty, measure_empty] at h

/-- A gap contributes at most the Birkhoff sum of `f 1` over it. -/
theorem gap_le_sum {σ : Ω → Ω} {f : ℕ → Ω → ℝ} (hf : SubadditiveFamily σ f)
    (b m : ℕ) (hm : 1 ≤ m) (ω : Ω) :
    f m (σ^[b] ω) ≤ ∑ k ∈ Finset.range m, f 1 (σ^[b + k] ω) := by
  have h := hf.le_birkhoffSum m hm (σ^[b] ω)
  simp only [birkhoffSum] at h
  refine le_trans h (le_of_eq (Finset.sum_congr rfl (fun k _ => ?_)))
  rw [← Function.iterate_add_apply, Nat.add_comm]

omit [MeasurableSpace Ω] in
/-- The gaps and good blocks of the walk exactly partition `[0, b_t)`. -/
theorem sum_walk_lengths (σ : Ω → Ω) (Λm Λp : Set Ω) (t : ℕ) (ω : Ω) :
    ∑ i ∈ Finset.range t, ((aWalk σ Λm Λp i ω - bWalk σ Λm Λp i ω)
      + (bWalk σ Λm Λp (i + 1) ω - aWalk σ Λm Λp i ω)) = bWalk σ Λm Λp t ω := by
  induction t with
  | zero => simp [bWalk]
  | succ t ih =>
    have hba : bWalk σ Λm Λp t ω ≤ aWalk σ Λm Λp t ω := bWalk_le_aWalk σ Λm Λp t ω
    have hab : aWalk σ Λm Λp t ω < bWalk σ Λm Λp (t + 1) ω := aWalk_lt_bWalk_succ σ Λm Λp t ω
    rw [Finset.sum_range_succ, ih]
    omega

/-- **The chained bound, assembled.** Given a bound `G i` on each gap and `H i` on each good
block, the walk's chaining yields `f (b_t) ω ≤ f 0 ω + Σ (G i + H i)`.

Stated with the two bounds as hypotheses on purpose: it separates the *algebra* of the chaining
(this lemma) from the *analysis* that supplies the bounds (`gap_le_sum` for `G`,
`good_block_value` for `H`). The caller discharges them per index. -/
theorem chained_bound {σ : Ω → Ω} {f : ℕ → Ω → ℝ} (hf : SubadditiveFamily σ f)
    (Λm Λp : Set Ω) (t : ℕ) (ω : Ω) (G H : ℕ → ℝ)
    (hgap : ∀ i < t,
      f (aWalk σ Λm Λp i ω - bWalk σ Λm Λp i ω) (σ^[bWalk σ Λm Λp i ω] ω) ≤ G i)
    (hgood : ∀ i < t,
      f (bWalk σ Λm Λp (i + 1) ω - aWalk σ Λm Λp i ω) (σ^[aWalk σ Λm Λp i ω] ω) ≤ H i) :
    f (bWalk σ Λm Λp t ω) ω ≤ f 0 ω + ∑ i ∈ Finset.range t, (G i + H i) := by
  have hchain := hf.le_sum_bWalk Λm Λp t ω
  have hsum : ∑ i ∈ Finset.range t,
      (f (aWalk σ Λm Λp i ω - bWalk σ Λm Λp i ω) (σ^[bWalk σ Λm Λp i ω] ω)
        + f (bWalk σ Λm Λp (i + 1) ω - aWalk σ Λm Λp i ω) (σ^[aWalk σ Λm Λp i ω] ω))
      ≤ ∑ i ∈ Finset.range t, (G i + H i) :=
    Finset.sum_le_sum (fun i hi =>
      add_le_add (hgap i (Finset.mem_range.mp hi)) (hgood i (Finset.mem_range.mp hi)))
  linarith

/-- A right endpoint is never a left endpoint, so from one the next `Λ₋` hit is strictly later —
i.e. every gap of the walk is nonempty. The hit-existence hypothesis is needed because `hitTime`
returns the junk value `0` when the orbit never meets `Λ₋`. -/
theorem one_le_hitTime_leftEnd {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ} {x : Ω}
    (hdisj : A.PairwiseDisjoint fun y => (fun i => zIter σ i y) '' Set.Icc (-(jω y : ℤ)) (jω y))
    (hpos : ∀ ω' ∈ A, 1 ≤ jω ω')
    (hinj : ∀ ω' ∈ A, Function.Injective fun i : ℤ => zIter σ i ω')
    (hex : ∃ n, (σ : Ω → Ω)^[n] x ∈ leftEnd σ jω '' A)
    (hx : x ∈ rightEnd σ jω '' A) :
    1 ≤ hitTime (σ : Ω → Ω) (leftEnd σ jω '' A) x := by
  have hne : x ∉ leftEnd σ jω '' A := fun hmem =>
    Set.disjoint_left.mp (disjoint_leftEnd_rightEnd hdisj hpos hinj) hmem hx
  rcases Nat.eq_zero_or_pos (hitTime (σ : Ω → Ω) (leftEnd σ jω '' A) x) with h0 | h
  · exfalso
    have hspec := hitTime_spec hex
    rw [h0] at hspec
    simp only [Function.iterate_zero, id_eq] at hspec
    exact hne hspec
  · exact h

/-- **The indicator terms, integrated.** Along the orbit, a term supported on a small set costs
at most `n · ε`.

This is the step the paper describes as "the integration is what avoids Birkhoff": no pointwise
ergodic theorem is needed, only `∫ S_n g = n ∫ g`, which is pure measure preservation. Combined
with `exists_delta_setIntegral_abs_le` it bounds both the `1_B` gap terms and the `1_{Λ₊}`
correction terms that the paper's display drops. -/
theorem integral_birkhoffSum_indicator_le {μ : Measure Ω} {σ : Ω → Ω}
    (hmp : MeasurePreserving σ μ μ) {S : Set Ω} (hS : MeasurableSet S) {g : Ω → ℝ}
    (hg : Integrable g μ) {ε : ℝ} (hbound : ∫ ω in S, |g ω| ∂μ ≤ ε) (n : ℕ) :
    ∫ ω, birkhoffSum σ (S.indicator (fun x => |g x|)) n ω ∂μ ≤ n * ε := by
  rw [integral_birkhoffSum hmp _ ((hg.abs).indicator hS) n]
  have hEq : ∫ ω, S.indicator (fun x => |g x|) ω ∂μ = ∫ ω in S, |g ω| ∂μ :=
    integral_indicator hS
  rw [hEq]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact mul_le_mul_of_nonneg_left hbound hn

omit [MeasurableSpace Ω] in
/-- A pointwise term is dominated by its indicator version whenever the point lies in `S`;
this is how the gap sum (over uncovered positions only) is enlarged to a full Birkhoff sum. -/
theorem le_indicator_abs {S : Set Ω} {g : Ω → ℝ} {x : Ω} (hx : x ∈ S) :
    g x ≤ S.indicator (fun y => |g y|) x := by
  rw [Set.indicator_of_mem hx]
  exact le_abs_self _

omit [MeasurableSpace Ω] in
theorem indicator_abs_nonneg {S : Set Ω} {g : Ω → ℝ} (x : Ω) :
    0 ≤ S.indicator (fun y => |g y|) x := by
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]; exact abs_nonneg _
  · rw [Set.indicator_of_notMem hx]

/-- **The sign analysis.** `q` may be negative, so knowing only `L ≤ n` for the total good-block
length gives the wrong direction. Bracketing `L` between a lower bound `M` (the covered count)
and `n` gives a bound valid for either sign — this is what the paper's
`max{(C_hat+ε)(1-ε), C_hat+ε}` is doing. -/
theorem mul_le_max_of_bracket {q L M n : ℝ} (hML : M ≤ L) (hLn : L ≤ n) :
    q * L ≤ max (q * M) (q * n) := by
  rcases le_or_gt 0 q with hq | hq
  · exact le_max_of_le_right (mul_le_mul_of_nonneg_left hLn hq)
  · exact le_max_of_le_left (mul_le_mul_of_nonpos_left hML hq.le)

omit [MeasurableSpace Ω] in
/-- The total good-block length is bracketed: at most `b_t`, and at least `b_t` minus the total
gap length. Both follow from `sum_walk_lengths`, which says the two interleave to fill
`[0, b_t)`. -/
theorem good_length_bracket (σ : Ω → Ω) (Λm Λp : Set Ω) (t : ℕ) (ω : Ω) :
    ∑ i ∈ Finset.range t, (bWalk σ Λm Λp (i + 1) ω - aWalk σ Λm Λp i ω)
        ≤ bWalk σ Λm Λp t ω
      ∧ bWalk σ Λm Λp t ω
        ≤ (∑ i ∈ Finset.range t, (bWalk σ Λm Λp (i + 1) ω - aWalk σ Λm Λp i ω))
          + ∑ i ∈ Finset.range t, (aWalk σ Λm Λp i ω - bWalk σ Λm Λp i ω) := by
  have h := sum_walk_lengths σ Λm Λp t ω
  rw [Finset.sum_add_distrib] at h
  omega

omit [MeasurableSpace Ω] in
/-- The walk overshoots `n` at the very next step: `b_{t_n + 1} > n`. Immediate from maximality of
`t_n`, using `b_t ≥ t` to keep the index inside `findGreatest`'s search range. -/
theorem lt_bWalk_succ_blockCount (σ : Ω → Ω) (Λm Λp : Set Ω) (n : ℕ) (ω : Ω) :
    n < bWalk σ Λm Λp (blockCount σ Λm Λp n ω + 1) ω := by
  by_contra hc
  rw [not_lt] at hc
  have h := le_blockCount (σ := σ) (Λm := Λm) (Λp := Λp) ω hc
  omega

omit [MeasurableSpace Ω] in
/-- **The trailing segment is short.** `n - b_{t_n}` is bounded by the length of the block the
walk was in the middle of, i.e. by `r₊` at that point — which the cutoff estimate
`tendsto_measure_hitTime_ge` makes small outside a set of small measure. -/
theorem boundary_length_lt (σ : Ω → Ω) (Λm Λp : Set Ω) (n : ℕ) (ω : Ω) :
    n - bWalk σ Λm Λp (blockCount σ Λm Λp n ω) ω
      < rPlus σ Λm Λp (σ^[bWalk σ Λm Λp (blockCount σ Λm Λp n ω) ω] ω) := by
  have hover := lt_bWalk_succ_blockCount σ Λm Λp n ω
  have hle : bWalk σ Λm Λp (blockCount σ Λm Λp n ω) ω ≤ n :=
    bWalk_blockCount_le σ Λm Λp n ω
  have hstep : bWalk σ Λm Λp (blockCount σ Λm Λp n ω + 1) ω
      = bWalk σ Λm Λp (blockCount σ Λm Λp n ω) ω
        + rPlus σ Λm Λp (σ^[bWalk σ Λm Λp (blockCount σ Λm Λp n ω) ω] ω) := rfl
  omega

/-- The trailing segment, bounded pointwise by the `f 1` sum over it. -/
theorem boundary_le_sum {σ : Ω → Ω} {f : ℕ → Ω → ℝ} (hf : SubadditiveFamily σ f)
    (b n : ℕ) (hlt : b < n) (ω : Ω) :
    f (n - b) (σ^[b] ω) ≤ ∑ k ∈ Finset.range (n - b), f 1 (σ^[b + k] ω) :=
  gap_le_sum hf b (n - b) (by omega) ω

/-- Splitting `[0, n)` at the walk's last completed block. -/
theorem le_split_at_bWalk {σ : Ω → Ω} {f : ℕ → Ω → ℝ} (hf : SubadditiveFamily σ f)
    (b n : ℕ) (hbn : b ≤ n) (ω : Ω) :
    f n ω ≤ f (n - b) (σ^[b] ω) + f b ω := by
  have h := hf.2 (n - b) b ω
  rwa [Nat.sub_add_cancel hbn] at h

theorem zIter_natCast_fun (σ : Ω ≃ᵐ Ω) (k : ℕ) : zIter σ (k : ℤ) = (σ : Ω → Ω)^[k] :=
  funext (zIter_natCast σ k)

/-- Change of variables for a set integral along a measure-preserving bijection:
`∫_Λ h ∘ σ^k = ∫_{σ^k Λ} h`. -/
theorem setIntegral_comp_iterate {μ : Measure Ω} (σ : Ω ≃ᵐ Ω) (hmp : MeasurePreserving (⇑σ) μ μ)
    {Λ : Set Ω} (hΛ : MeasurableSet Λ) {h : Ω → ℝ} (hh : Integrable h μ) (k : ℕ) :
    ∫ ω in Λ, h ((σ : Ω → Ω)^[k] ω) ∂μ = ∫ y in (σ : Ω → Ω)^[k] '' Λ, h y ∂μ := by
  have hTm : Measurable ((σ : Ω → Ω)^[k]) := σ.measurable.iterate k
  have himg : MeasurableSet ((σ : Ω → Ω)^[k] '' Λ) := by
    have := measurableSet_zIter_image σ (k : ℤ) hΛ
    rwa [zIter_natCast_fun] at this
  -- pull the indicator across the map
  have hind : ∀ ω, Λ.indicator (fun x => h ((σ : Ω → Ω)^[k] x)) ω
      = ((σ : Ω → Ω)^[k] '' Λ).indicator h ((σ : Ω → Ω)^[k] ω) := by
    intro ω
    by_cases hω : ω ∈ Λ
    · have hmem : (σ : Ω → Ω)^[k] ω ∈ (σ : Ω → Ω)^[k] '' Λ := ⟨ω, hω, rfl⟩
      rw [Set.indicator_of_mem hω, Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem]
      rintro ⟨x, hx, hxe⟩
      exact hω ((σ.injective.iterate k) hxe ▸ hx)
  rw [← integral_indicator hΛ, ← integral_indicator himg]
  have hcomp : ∫ ω, Λ.indicator (fun x => h ((σ : Ω → Ω)^[k] x)) ω ∂μ
      = ∫ ω, ((σ : Ω → Ω)^[k] '' Λ).indicator h ((σ : Ω → Ω)^[k] ω) ∂μ := by
    exact integral_congr_ae (Filter.Eventually.of_forall hind)
  rw [hcomp]
  have hmap : Measure.map ((σ : Ω → Ω)^[k]) μ = μ := (hmp.iterate k).map_eq
  calc ∫ ω, ((σ : Ω → Ω)^[k] '' Λ).indicator h ((σ : Ω → Ω)^[k] ω) ∂μ
      = ∫ y, ((σ : Ω → Ω)^[k] '' Λ).indicator h y ∂(Measure.map ((σ : Ω → Ω)^[k]) μ) :=
        (integral_map hTm.aemeasurable
          (by rw [hmap]; exact (hh.indicator himg).aestronglyMeasurable)).symm
    _ = ∫ y, ((σ : Ω → Ω)^[k] '' Λ).indicator h y ∂μ := by rw [hmap]

/-- **The translate bound.** If `μ Λ` is small enough for absolute continuity to bite, then the
whole Birkhoff sum costs at most `n · ε` on `Λ` — because each translate `σ^k Λ` has the same
measure, so each of the `n` terms is separately small. This is the paper's
`(1/n) Σ_i ∫_{σ^i Λ} |f_1| ≤ ε` step. -/
theorem setIntegral_birkhoffSum_le {μ : Measure Ω} (σ : Ω ≃ᵐ Ω)
    (hmp : MeasurePreserving (⇑σ) μ μ) {Λ : Set Ω} (hΛ : MeasurableSet Λ) {g : Ω → ℝ}
    (hg : Integrable g μ) {δ ε : ℝ}
    (hac : ∀ S : Set Ω, MeasurableSet S → μ S ≤ ENNReal.ofReal δ → ∫ ω in S, |g ω| ∂μ ≤ ε)
    (hΛδ : μ Λ ≤ ENNReal.ofReal δ) (n : ℕ) :
    ∫ ω in Λ, birkhoffSum (σ : Ω → Ω) (fun x => |g x|) n ω ∂μ ≤ n * ε := by
  have hint : ∀ k : ℕ, IntegrableOn (fun ω => |g ((σ : Ω → Ω)^[k] ω)|) Λ μ := by
    intro k
    exact (((hmp.iterate k).integrable_comp_of_integrable hg).abs).integrableOn
  have hsplit : ∫ ω in Λ, birkhoffSum (σ : Ω → Ω) (fun x => |g x|) n ω ∂μ
      = ∑ k ∈ Finset.range n, ∫ ω in Λ, |g ((σ : Ω → Ω)^[k] ω)| ∂μ := by
    simp only [birkhoffSum]
    exact integral_finsetSum _ (fun k _ => hint k)
  rw [hsplit]
  have hterm : ∀ k ∈ Finset.range n, ∫ ω in Λ, |g ((σ : Ω → Ω)^[k] ω)| ∂μ ≤ ε := by
    intro k _
    rw [setIntegral_comp_iterate σ hmp hΛ hg.abs k]
    have himg : MeasurableSet ((σ : Ω → Ω)^[k] '' Λ) := by
      have := measurableSet_zIter_image σ (k : ℤ) hΛ
      rwa [zIter_natCast_fun] at this
    have hmeasure : μ ((σ : Ω → Ω)^[k] '' Λ) = μ Λ := by
      have := measure_zIter_image σ hmp (k : ℤ) hΛ
      rwa [zIter_natCast_fun] at this
    exact hac _ himg (by rw [hmeasure]; exact hΛδ)
  calc ∑ k ∈ Finset.range n, ∫ ω in Λ, |g ((σ : Ω → Ω)^[k] ω)| ∂μ
      ≤ ∑ _k ∈ Finset.range n, ε := Finset.sum_le_sum hterm
    _ = n * ε := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Recurrence from every position of the orbit.** The walk calls `hitTime_spec` at each `b_i`,
so it needs hit-existence not just at `ω` but at every forward iterate of it. Countably many
positions, each handled by pulling `ae_exists_mem_iterate` back along the measure-preserving
`σ^m`. -/
theorem ae_forall_exists_mem_iterate {μ : Measure Ω} [IsProbabilityMeasure μ] {σ : Ω → Ω}
    (hσ : Ergodic σ μ) {Λ : Set Ω} (hΛm : MeasurableSet Λ) (hΛ : μ Λ ≠ 0) :
    ∀ᵐ ω ∂μ, ∀ m : ℕ, ∃ n : ℕ, σ^[n] (σ^[m] ω) ∈ Λ := by
  refine ae_all_iff.mpr (fun m => ?_)
  exact ((hσ.toMeasurePreserving.iterate m).quasiMeasurePreserving).ae
    (ae_exists_mem_iterate hσ hΛm hΛ)

omit [MeasurableSpace Ω] in
/-- Each step of the walk lands on a `Λ₊` point — the right endpoint of the block just completed.
This is what lets `not_covered_of_gap` be applied at every `b_i`. -/
theorem iterate_bWalk_succ_mem {σ : Ω → Ω} {Λm Λp : Set Ω} {ω : Ω} (i : ℕ)
    (hex : ∃ n, σ^[n] (σ^[rMinus σ Λm (σ^[bWalk σ Λm Λp i ω] ω) + 1]
      (σ^[bWalk σ Λm Λp i ω] ω)) ∈ Λp) :
    σ^[bWalk σ Λm Λp (i + 1) ω] ω ∈ Λp := by
  have key : ∀ (b r h : ℕ) (y : Ω), σ^[b + (r + 1 + h)] y = σ^[h] (σ^[r + 1] (σ^[b] y)) := by
    intro b r h y
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
    congr 1
    omega
  change σ^[bWalk σ Λm Λp i ω + rPlus σ Λm Λp (σ^[bWalk σ Λm Λp i ω] ω)] ω ∈ Λp
  rw [rPlus, key]
  exact hitTime_spec hex

omit [MeasurableSpace Ω] in
/-- **The walk's good block is exactly the hitting time from its start.** This is the bridge that
lets `good_block_value` (stated at a `Λ₋` point, in terms of `hitTime`) be applied to the walk's
own block lengths.

The `+1`/`-1` shuffle is real: `rPlus` searches *strictly after* `rMinus`, so the walk's length is
`1 + hitTime` from one step on, and `hitTime_succ` converts that back — which is why
`σ^{a_i}ω ∉ Λ₊` (i.e. `disjoint_leftEnd_rightEnd`) is needed here. -/
theorem goodlen_eq_hitTime {σ : Ω → Ω} {Λm Λp : Set Ω} {ω : Ω} (i : ℕ)
    (hex : ∃ n, σ^[n] (σ^[aWalk σ Λm Λp i ω] ω) ∈ Λp)
    (hnot : σ^[aWalk σ Λm Λp i ω] ω ∉ Λp) :
    bWalk σ Λm Λp (i + 1) ω - aWalk σ Λm Λp i ω
      = hitTime σ Λp (σ^[aWalk σ Λm Λp i ω] ω) := by
  have hpt : σ^[rMinus σ Λm (σ^[bWalk σ Λm Λp i ω] ω) + 1] (σ^[bWalk σ Λm Λp i ω] ω)
      = σ (σ^[aWalk σ Λm Λp i ω] ω) := by
    rw [← Function.iterate_add_apply,
      ← Function.iterate_succ_apply' σ (aWalk σ Λm Λp i ω) ω]
    congr 1
    change rMinus σ Λm (σ^[bWalk σ Λm Λp i ω] ω) + 1 + bWalk σ Λm Λp i ω
      = bWalk σ Λm Λp i ω + rMinus σ Λm (σ^[bWalk σ Λm Λp i ω] ω) + 1
    omega
  have hsucc := hitTime_succ hex hnot
  have hb : bWalk σ Λm Λp (i + 1) ω
      = bWalk σ Λm Λp i ω + rPlus σ Λm Λp (σ^[bWalk σ Λm Λp i ω] ω) := rfl
  have ha : aWalk σ Λm Λp i ω
      = bWalk σ Λm Λp i ω + rMinus σ Λm (σ^[bWalk σ Λm Λp i ω] ω) := rfl
  have hr : rPlus σ Λm Λp (σ^[bWalk σ Λm Λp i ω] ω)
      = rMinus σ Λm (σ^[bWalk σ Λm Λp i ω] ω) + 1
        + hitTime σ Λp (σ (σ^[aWalk σ Λm Λp i ω] ω)) := by
    rw [rPlus, hpt]
  omega

/-- **Large radii force a small centre set.** If every window has radius at least `N`, the `2N+1`
translates of `A` over `Icc (-N) N` are pairwise disjoint, so `(2N+1) μ A ≤ 1`.

This is what makes the paper's dropped endpoint terms negligible: they live in `Λ₊`, which has
the same measure as `A`. -/
theorem measure_le_of_radius_ge {μ : Measure Ω} [IsProbabilityMeasure μ] (σ : Ω ≃ᵐ Ω)
    (hmp : MeasurePreserving (⇑σ) μ μ) {A : Set Ω} (hAm : MeasurableSet A) {jω : Ω → ℕ} (N : ℕ)
    (hdisj : A.PairwiseDisjoint fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hN : ∀ ω ∈ A, N ≤ jω ω)
    (hinj : ∀ ω ∈ A, Function.Injective fun i : ℤ => zIter σ i ω) :
    (2 * N + 1 : ℝ≥0∞) * μ A ≤ 1 := by
  have hdisjT : ∀ i ∈ Set.Icc (-(N : ℤ)) N, ∀ k ∈ Set.Icc (-(N : ℤ)) N, i ≠ k →
      Disjoint (zIter σ i '' A) (zIter σ k '' A) := by
    intro i hi k hk hik
    rw [Set.disjoint_left]
    rintro x ⟨ω, hωA, rfl⟩ ⟨ω', hω'A, hx'⟩
    have hNi : N ≤ jω ω := hN ω hωA
    have hNk : N ≤ jω ω' := hN ω' hω'A
    have hi1 : -(N : ℤ) ≤ i := hi.1
    have hi2 : i ≤ (N : ℤ) := hi.2
    have hk1 : -(N : ℤ) ≤ k := hk.1
    have hk2 : k ≤ (N : ℤ) := hk.2
    have hmem1 : zIter σ i ω ∈ (fun t => zIter σ t ω) '' Set.Icc (-(jω ω : ℤ)) (jω ω) :=
      ⟨i, ⟨by omega, by omega⟩, rfl⟩
    have hmem2 : zIter σ i ω ∈ (fun t => zIter σ t ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω') := by
      refine ⟨k, ⟨by omega, by omega⟩, hx'⟩
    have hωω : ω = ω' := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj hωA hω'A hne) hmem1 hmem2
    subst hωω
    exact hik (hinj ω hωA hx').symm
  have heq := measure_iUnion_zIter_window_eq σ hmp N hAm hdisjT
  have hle : μ (⋃ t ∈ Set.Icc (-(N : ℤ)) N, zIter σ t '' A) ≤ 1 := by
    calc μ (⋃ t ∈ Set.Icc (-(N : ℤ)) N, zIter σ t '' A) ≤ μ Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  rwa [heq] at hle

/-- **The endpoint set is small too.** Same counting as `measure_le_of_radius_ge`, but the range
must be *backward*: going forward from a right endpoint immediately leaves its window, whereas
stepping back `i ≤ 2j` stays inside. So it is the `2N+1` translates `σ^{-i} Λ₊`, `0 ≤ i ≤ 2N`,
that are disjoint. -/
theorem measure_rightEnd_le {μ : Measure Ω} [IsProbabilityMeasure μ] (σ : Ω ≃ᵐ Ω)
    (hmp : MeasurePreserving (⇑σ) μ μ) {A : Set Ω} {jω : Ω → ℕ} (N : ℕ)
    (hΛm : MeasurableSet (rightEnd σ jω '' A))
    (hdisj : A.PairwiseDisjoint fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hN : ∀ ω ∈ A, N ≤ jω ω)
    (hinj : ∀ ω ∈ A, Function.Injective fun i : ℤ => zIter σ i ω) :
    (2 * N + 1 : ℝ≥0∞) * μ (rightEnd σ jω '' A) ≤ 1 := by
  have hpd : (↑(Finset.range (2 * N + 1)) : Set ℕ).PairwiseDisjoint
      (fun i => zIter σ (-(i : ℤ)) '' (rightEnd σ jω '' A)) := by
    intro i hi k hk hik
    simp only [Finset.coe_range, Set.mem_Iio] at hi hk
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨y, ⟨ω, hωA, rfl⟩, rfl⟩ ⟨y', ⟨ω', hω'A, rfl⟩, hx'⟩
    have hNi : N ≤ jω ω := hN ω hωA
    have hNk : N ≤ jω ω' := hN ω' hω'A
    -- both points sit in their own windows
    have hcoord : ∀ (z : Ω) (m : ℕ), zIter σ (-(m : ℤ)) (rightEnd σ jω z)
        = zIter σ ((jω z : ℤ) - m) z := by
      intro z m
      rw [rightEnd, ← zIter_add]
      congr 1
      omega
    have hmem1 : zIter σ (-(i : ℤ)) (rightEnd σ jω ω)
        ∈ (fun t => zIter σ t ω) '' Set.Icc (-(jω ω : ℤ)) (jω ω) := by
      rw [hcoord]
      exact ⟨(jω ω : ℤ) - i, ⟨by omega, by omega⟩, rfl⟩
    have hmem2 : zIter σ (-(i : ℤ)) (rightEnd σ jω ω)
        ∈ (fun t => zIter σ t ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω') := by
      rw [← hx', hcoord]
      exact ⟨(jω ω' : ℤ) - k, ⟨by omega, by omega⟩, rfl⟩
    have hωω : ω = ω' := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj hωA hω'A hne) hmem1 hmem2
    subst hωω
    rw [hcoord, hcoord] at hx'
    have := hinj ω hωA hx'
    omega
  have hmeas : ∀ i : ℕ, MeasurableSet (zIter σ (-(i : ℤ)) '' (rightEnd σ jω '' A)) :=
    fun i => measurableSet_zIter_image σ (-(i : ℤ)) hΛm
  have hunion : μ (⋃ i ∈ Finset.range (2 * N + 1),
      zIter σ (-(i : ℤ)) '' (rightEnd σ jω '' A))
      = ∑ i ∈ Finset.range (2 * N + 1), μ (zIter σ (-(i : ℤ)) '' (rightEnd σ jω '' A)) :=
    measure_biUnion_finset hpd (fun i _ => hmeas i)
  have hsum : ∑ i ∈ Finset.range (2 * N + 1),
      μ (zIter σ (-(i : ℤ)) '' (rightEnd σ jω '' A))
      = (2 * N + 1 : ℝ≥0∞) * μ (rightEnd σ jω '' A) := by
    have hcongr : ∑ i ∈ Finset.range (2 * N + 1),
        μ (zIter σ (-(i : ℤ)) '' (rightEnd σ jω '' A))
        = ∑ _i ∈ Finset.range (2 * N + 1), μ (rightEnd σ jω '' A) :=
      Finset.sum_congr rfl (fun i _ => measure_zIter_image σ hmp (-(i : ℤ)) hΛm)
    rw [hcongr, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  calc (2 * N + 1 : ℝ≥0∞) * μ (rightEnd σ jω '' A)
      = μ (⋃ i ∈ Finset.range (2 * N + 1), zIter σ (-(i : ℤ)) '' (rightEnd σ jω '' A)) := by
        rw [hunion, hsum]
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

omit [MeasurableSpace Ω] in
/-- **Telescoping with slack.** If `bᵢ ≤ aᵢ ≤ b_{i+1}` and `S` is monotone, the increments of `S`
across the intervals `[bᵢ, aᵢ)` add up to at most the increment across `[b₀, b_t)`. This is how
the walk's *gap* contributions get bounded by a single Birkhoff sum. -/
theorem sum_sub_le_of_monotone {S : ℕ → ℝ} (hS : Monotone S) {b a : ℕ → ℕ}
    (hab : ∀ i, a i ≤ b (i + 1)) (t : ℕ) :
    ∑ i ∈ Finset.range t, (S (a i) - S (b i)) ≤ S (b t) - S (b 0) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ]
    have h1 : S (a t) ≤ S (b (t + 1)) := hS (hab t)
    linarith

omit [MeasurableSpace Ω] in
/-- A Birkhoff sum of a nonnegative function is monotone in the number of terms. -/
theorem birkhoffSum_mono_of_nonneg {σ : Ω → Ω} {g : Ω → ℝ} (hg : ∀ x, 0 ≤ g x) (ω : Ω) :
    Monotone (fun n => birkhoffSum σ g n ω) := by
  intro m n hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  change birkhoffSum σ g m ω ≤ birkhoffSum σ g (m + k) ω
  rw [birkhoffSum_add_right_apply]
  have : 0 ≤ birkhoffSum σ g k (σ^[m] ω) :=
    Finset.sum_nonneg (fun i _ => hg _)
  simpa using this

omit [MeasurableSpace Ω] in
/-- A Birkhoff sum over a sub-block, written as a difference of Birkhoff sums from the origin. -/
theorem birkhoffSum_shift_eq {σ : Ω → Ω} (g : Ω → ℝ) (b m : ℕ) (ω : Ω) :
    birkhoffSum σ g m (σ^[b] ω) = birkhoffSum σ g (b + m) ω - birkhoffSum σ g b ω := by
  rw [birkhoffSum_add_right_apply]; ring

/-- Right endpoints lie in their own windows, so `Λ₊` is covered. -/
theorem rightEnd_mem_iUnion_windows {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ} {x : Ω}
    (hx : x ∈ rightEnd σ jω '' A) :
    x ∈ ⋃ ω' ∈ A, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω') := by
  obtain ⟨ω', hω', rfl⟩ := hx
  exact Set.mem_biUnion hω' ⟨(jω ω' : ℤ), ⟨by omega, le_refl _⟩, rfl⟩

/-- The complement of the union of the good windows — the paper's `B`. -/
def uncovered (σ : Ω ≃ᵐ Ω) (jω : Ω → ℕ) (A : Set Ω) : Set Ω :=
  (⋃ ω' ∈ A, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω'))ᶜ

/-- The majorant of `f₁` along the walk's gaps: `|f₁|` on the uncovered set together with `|f₁|`
on `Λ₊`. The second summand is the repair of the paper's off-by-one — the left end of each gap is
a *right endpoint*, hence covered, so `1_B |f₁|` alone does not dominate there. -/
noncomputable def gapMaj (σ : Ω ≃ᵐ Ω) (jω : Ω → ℕ) (A : Set Ω) (f : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun x => (uncovered σ jω A).indicator (fun y => |f 1 y|) x
    + (rightEnd σ jω '' A).indicator (fun y => |f 1 y|) x

/-- The same majorant for *lengths* rather than values: at least `1` at every gap point. -/
noncomputable def gapCount (σ : Ω ≃ᵐ Ω) (jω : Ω → ℕ) (A : Set Ω) : Ω → ℝ :=
  fun x => (uncovered σ jω A).indicator (fun _ => (1 : ℝ)) x
    + (rightEnd σ jω '' A).indicator (fun _ => (1 : ℝ)) x

/-- The last completed block start `b_{t_n}`. -/
noncomputable def lastBlock (σ : Ω ≃ᵐ Ω) (jω : Ω → ℕ) (A : Set Ω) (n : ℕ) (ω : Ω) : ℕ :=
  bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A)
    (blockCount (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) n ω) ω

/-- The length of the initial gap `[0, a₀)`, truncated at `n`. -/
noncomputable def firstGap (σ : Ω ≃ᵐ Ω) (jω : Ω → ℕ) (A : Set Ω) (n : ℕ) (ω : Ω) : ℕ :=
  min (aWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) 0 ω) n

theorem gapMaj_nonneg (σ : Ω ≃ᵐ Ω) (jω : Ω → ℕ) (A : Set Ω) (f : ℕ → Ω → ℝ) (x : Ω) :
    0 ≤ gapMaj σ jω A f x :=
  add_nonneg (Set.indicator_nonneg (fun _ _ => abs_nonneg _) _)
    (Set.indicator_nonneg (fun _ _ => abs_nonneg _) _)

theorem gapCount_nonneg (σ : Ω ≃ᵐ Ω) (jω : Ω → ℕ) (A : Set Ω) (x : Ω) :
    0 ≤ gapCount σ jω A x :=
  add_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

/-- **Gap points are either uncovered or right endpoints.** The left end of a gap is the right
endpoint of the block just finished; every later point of the gap is uncovered. -/
theorem gap_point_mem {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ} {ω : Ω}
    (hdisj : A.PairwiseDisjoint fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hinj : ∀ ω' ∈ A, Function.Injective fun i : ℤ => zIter σ i ω') {bb k : ℕ}
    (hb : (σ : Ω → Ω)^[bb] ω ∈ rightEnd σ jω '' A)
    (hk : k < rMinus (σ : Ω → Ω) (leftEnd σ jω '' A) ((σ : Ω → Ω)^[bb] ω)) :
    (σ : Ω → Ω)^[bb + k] ω ∈ uncovered σ jω A ∨
      (σ : Ω → Ω)^[bb + k] ω ∈ rightEnd σ jω '' A := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact Or.inr (by simpa using hb)
  · refine Or.inl ?_
    rw [uncovered, Set.mem_compl_iff]
    exact not_covered_of_gap hdisj hinj hb (by omega) (by rw [rMinus] at hk; omega)

theorem le_gapMaj {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ} {f : ℕ → Ω → ℝ} {x : Ω}
    (hx : x ∈ uncovered σ jω A ∨ x ∈ rightEnd σ jω '' A) :
    f 1 x ≤ gapMaj σ jω A f x := by
  rcases hx with h | h
  · have h1 : (uncovered σ jω A).indicator (fun y => |f 1 y|) x = |f 1 x| :=
      Set.indicator_of_mem h _
    have h2 : 0 ≤ (rightEnd σ jω '' A).indicator (fun y => |f 1 y|) x :=
      Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
    have h3 : f 1 x ≤ |f 1 x| := le_abs_self _
    rw [gapMaj, h1]
    linarith
  · have h1 : (rightEnd σ jω '' A).indicator (fun y => |f 1 y|) x = |f 1 x| :=
      Set.indicator_of_mem h _
    have h2 : 0 ≤ (uncovered σ jω A).indicator (fun y => |f 1 y|) x :=
      Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
    have h3 : f 1 x ≤ |f 1 x| := le_abs_self _
    rw [gapMaj, h1]
    linarith

theorem one_le_gapCount {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ} {x : Ω}
    (hx : x ∈ uncovered σ jω A ∨ x ∈ rightEnd σ jω '' A) :
    1 ≤ gapCount σ jω A x := by
  rcases hx with h | h
  · have h1 : (uncovered σ jω A).indicator (fun _ => (1 : ℝ)) x = 1 := Set.indicator_of_mem h _
    have h2 : 0 ≤ (rightEnd σ jω '' A).indicator (fun _ => (1 : ℝ)) x :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    rw [gapCount, h1]; linarith
  · have h1 : (rightEnd σ jω '' A).indicator (fun _ => (1 : ℝ)) x = 1 := Set.indicator_of_mem h _
    have h2 : 0 ≤ (uncovered σ jω A).indicator (fun _ => (1 : ℝ)) x :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    rw [gapCount, h1]; linarith

/-- Stepping back `k ≤ n` times from `σⁿω`. -/
theorem symm_iterate_iterate (σ : Ω ≃ᵐ Ω) {k n : ℕ} (hk : k ≤ n) (ω : Ω) :
    (σ.symm : Ω → Ω)^[k] ((σ : Ω → Ω)^[n] ω) = (σ : Ω → Ω)^[n - k] ω := by
  rw [← zIter_neg_natCast σ k, ← zIter_natCast σ n, ← zIter_add, ← zIter_natCast σ (n - k)]
  congr 1
  omega

/-- **No right endpoint strictly inside a walk step.** Between `b_i` and `b_{i+1}` the orbit
passes through the gap `(b_i, a_i)` — uncovered, hence disjoint from `Λ₊` — then the left endpoint
`a_i` — which is in `Λ₋`, disjoint from `Λ₊` — and then a stretch strictly before the first
return to `Λ₊`.

This is what makes `b_{t_n}` the *last* `Λ₊` time in `[0, n]`, and hence lets the trailing segment
`[b_{t_n}, n)` be controlled by a backward hitting time. -/
theorem not_mem_rightEnd_of_between {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ} {ω : Ω}
    (hdisj : A.PairwiseDisjoint fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hpos : ∀ ω' ∈ A, 1 ≤ jω ω')
    (hinj : ∀ ω' ∈ A, Function.Injective fun i : ℤ => zIter σ i ω') {i j : ℕ}
    (hbi : (σ : Ω → Ω)^[bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) i ω] ω
      ∈ rightEnd σ jω '' A)
    (h1 : bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) i ω < j)
    (h2 : j < bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) (i + 1) ω) :
    (σ : Ω → Ω)^[j] ω ∉ rightEnd σ jω '' A := by
  classical
  have hstep : bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) (i + 1) ω
      = bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) i ω
        + (hitTime (σ : Ω → Ω) (leftEnd σ jω '' A)
            ((σ : Ω → Ω)^[bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) i ω] ω)
          + 1
          + hitTime (σ : Ω → Ω) (rightEnd σ jω '' A)
              ((σ : Ω → Ω)^[hitTime (σ : Ω → Ω) (leftEnd σ jω '' A)
                ((σ : Ω → Ω)^[bWalk (σ : Ω → Ω) (leftEnd σ jω '' A)
                  (rightEnd σ jω '' A) i ω] ω) + 1]
                ((σ : Ω → Ω)^[bWalk (σ : Ω → Ω) (leftEnd σ jω '' A)
                  (rightEnd σ jω '' A) i ω] ω))) := by
    rw [bWalk, rPlus, rMinus]
  intro hj
  rcases lt_trichotomy j (bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) i ω
      + hitTime (σ : Ω → Ω) (leftEnd σ jω '' A)
        ((σ : Ω → Ω)^[bWalk (σ : Ω → Ω) (leftEnd σ jω '' A)
          (rightEnd σ jω '' A) i ω] ω)) with hlt | heq | hgt
  · exact not_covered_of_gap hdisj hinj hbi h1 hlt (rightEnd_mem_iUnion_windows hj)
  · -- exactly the left endpoint `a_i`, which lies in `Λ₋`
    have hr1 : 1 ≤ hitTime (σ : Ω → Ω) (leftEnd σ jω '' A)
        ((σ : Ω → Ω)^[bWalk (σ : Ω → Ω) (leftEnd σ jω '' A)
          (rightEnd σ jω '' A) i ω] ω) := by omega
    have hex : ∃ m, (σ : Ω → Ω)^[m]
        ((σ : Ω → Ω)^[bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) i ω] ω)
          ∈ leftEnd σ jω '' A := by
      by_contra hno
      have hempty : {m : ℕ | (σ : Ω → Ω)^[m]
          ((σ : Ω → Ω)^[bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) i ω] ω)
            ∈ leftEnd σ jω '' A} = ∅ := by
        ext m
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hm => hno ⟨m, hm⟩
      rw [hitTime, hempty, Nat.sInf_empty] at hr1
      omega
    have hmem := hitTime_spec hex
    rw [← Function.iterate_add_apply] at hmem
    rw [show hitTime (σ : Ω → Ω) (leftEnd σ jω '' A)
        ((σ : Ω → Ω)^[bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) i ω] ω)
        + bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) i ω = j from by omega]
      at hmem
    exact Set.disjoint_left.mp (disjoint_leftEnd_rightEnd hdisj hpos hinj) hmem hj
  · -- past the left endpoint: `hitTime` minimality
    rw [show (σ : Ω → Ω)^[j] ω
        = (σ : Ω → Ω)^[j - (bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) i ω
            + hitTime (σ : Ω → Ω) (leftEnd σ jω '' A)
              ((σ : Ω → Ω)^[bWalk (σ : Ω → Ω) (leftEnd σ jω '' A)
                (rightEnd σ jω '' A) i ω] ω) + 1)]
          ((σ : Ω → Ω)^[hitTime (σ : Ω → Ω) (leftEnd σ jω '' A)
            ((σ : Ω → Ω)^[bWalk (σ : Ω → Ω) (leftEnd σ jω '' A)
              (rightEnd σ jω '' A) i ω] ω) + 1]
            ((σ : Ω → Ω)^[bWalk (σ : Ω → Ω) (leftEnd σ jω '' A)
              (rightEnd σ jω '' A) i ω] ω)) from by
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
        congr 1
        omega] at hj
    have := hitTime_min (σ := (σ : Ω → Ω)) (Λ := rightEnd σ jω '' A) hj
    omega

omit [MeasurableSpace Ω] in
/-- Recurrence from every orbit position makes every `b_{i+1}` a `Λ₊` point. -/
theorem bWalk_succ_mem_of_recur {σ : Ω → Ω} {Λm Λp : Set Ω} {ω : Ω}
    (hex : ∀ m : ℕ, ∃ k, σ^[k] (σ^[m] ω) ∈ Λp) (i : ℕ) :
    σ^[bWalk σ Λm Λp (i + 1) ω] ω ∈ Λp := by
  refine iterate_bWalk_succ_mem i ?_
  obtain ⟨k, hk⟩ :=
    hex (rMinus σ Λm (σ^[bWalk σ Λm Λp i ω] ω) + 1 + bWalk σ Λm Λp i ω)
  exact ⟨k, by rwa [Function.iterate_add_apply] at hk⟩

omit [MeasurableSpace Ω] in
/-- **Telescoping the walk's gaps into one Birkhoff sum.** Indexed from `i = 1`, since the very
first gap `[0, a₀)` starts at a point that need not be a right endpoint and so carries no
covering information.

Applied twice: with `u` a majorant of `|f₁|` on the gap points, to bound the gap *values*; and
with `u ≥ 1` there, to bound the gap *lengths*. -/
theorem sum_shifted_gaps_le {σ : Ω → Ω} {Λm Λp : Set Ω} {u : Ω → ℝ} (hu : ∀ x, 0 ≤ u x)
    (ω : Ω) (w : ℕ → ℝ) (t : ℕ)
    (hw : ∀ i < t, w i ≤ birkhoffSum σ u
      (aWalk σ Λm Λp (i + 1) ω - bWalk σ Λm Λp (i + 1) ω)
      (σ^[bWalk σ Λm Λp (i + 1) ω] ω))
    (n : ℕ) (hn : bWalk σ Λm Λp (t + 1) ω ≤ n) :
    ∑ i ∈ Finset.range t, w i ≤ birkhoffSum σ u n ω := by
  set S : ℕ → ℝ := fun k => birkhoffSum σ u k ω with hSdef
  have hSmono : Monotone S := birkhoffSum_mono_of_nonneg hu ω
  have hstep : ∀ i < t, w i ≤ S (aWalk σ Λm Λp (i + 1) ω) - S (bWalk σ Λm Λp (i + 1) ω) := by
    intro i hi
    have h := hw i hi
    rw [birkhoffSum_shift_eq, Nat.add_sub_cancel' (bWalk_le_aWalk σ Λm Λp (i + 1) ω)] at h
    exact h
  have hsum : ∑ i ∈ Finset.range t, w i
      ≤ ∑ i ∈ Finset.range t,
        (S (aWalk σ Λm Λp (i + 1) ω) - S (bWalk σ Λm Λp (i + 1) ω)) :=
    Finset.sum_le_sum (fun i hi => hstep i (Finset.mem_range.mp hi))
  have htel := sum_sub_le_of_monotone hSmono
    (b := fun i => bWalk σ Λm Λp (i + 1) ω) (a := fun i => aWalk σ Λm Λp (i + 1) ω)
    (fun i => le_of_lt (aWalk_lt_bWalk_succ σ Λm Λp (i + 1) ω)) t
  have hS0 : 0 ≤ S (bWalk σ Λm Λp 1 ω) := by
    have := hSmono (Nat.zero_le (bWalk σ Λm Λp 1 ω))
    simpa [hSdef, birkhoffSum_zero] using this
  have hSn : S (bWalk σ Λm Λp (t + 1) ω) ≤ S n := hSmono hn
  linarith

/-- **The trailing segment is a backward hitting time.** Once at least one full block has been
completed, `b_{t_n}` is the last `Λ₊` time in `[0, n]`, so `n - b_{t_n}` is exactly how far one
must step *back* from `σⁿω` to meet `Λ₊`.

This is the honest form of the paper's `r_-(σⁿω) = n - b_{t_n}`: the relevant hitting time is
backward, not forward. It converts a quantity that depends on `n` into one fixed function
evaluated at `σⁿω`, whose distribution is `n`-independent — which is what makes the cutoff
`ℙ(n - b_{t_n} ≥ M) < ε` uniform in `n`. -/
theorem sub_bWalk_le_hitBack {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ} {ω : Ω}
    (hdisj : A.PairwiseDisjoint fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hpos : ∀ ω' ∈ A, 1 ≤ jω ω')
    (hinj : ∀ ω' ∈ A, Function.Injective fun i : ℤ => zIter σ i ω')
    (hrec : ∀ m : ℕ, ∃ k, (σ : Ω → Ω)^[k] ((σ : Ω → Ω)^[m] ω) ∈ rightEnd σ jω '' A)
    {t n : ℕ}
    (hbn : bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) (t + 1) ω ≤ n)
    (hover : n < bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) (t + 1 + 1) ω) :
    n - bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) (t + 1) ω
      ≤ hitTime (σ.symm : Ω → Ω) (rightEnd σ jω '' A) ((σ : Ω → Ω)^[n] ω) := by
  have hbmem : (σ : Ω → Ω)^[bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A)
      (t + 1) ω] ω ∈ rightEnd σ jω '' A := bWalk_succ_mem_of_recur hrec t
  have hex : ∃ k, (σ.symm : Ω → Ω)^[k] ((σ : Ω → Ω)^[n] ω) ∈ rightEnd σ jω '' A := by
    refine ⟨n - bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) (t + 1) ω, ?_⟩
    rw [symm_iterate_iterate σ (by omega),
      show n - (n - bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) (t + 1) ω)
        = bWalk (σ : Ω → Ω) (leftEnd σ jω '' A) (rightEnd σ jω '' A) (t + 1) ω from by omega]
    exact hbmem
  by_contra hc
  rw [not_le] at hc
  have hmem := hitTime_spec hex
  rw [symm_iterate_iterate σ (by omega)] at hmem
  exact not_mem_rightEnd_of_between hdisj hpos hinj (i := t + 1) hbmem (by omega) (by omega) hmem

end MultiplicativeErgodic
