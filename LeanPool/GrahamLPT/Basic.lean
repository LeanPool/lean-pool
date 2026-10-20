/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

module

public import LeanPool.GrahamLPT.Defs
public import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Positivity.Finset

/-!
# Basic

Loads, makespans, the existence of list and LPT schedules, the attained optimum, relabeling.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- No job has index below `0`. -/
theorem bs_loadBefore_zero {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (i : Fin m) :
    loadBefore p σ 0 i = 0 := by
  simp [loadBefore]

/-- Adding the job `k`. -/
theorem bs_loadBefore_succ {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (k : Fin n) (i : Fin m) :
    loadBefore p σ (k + 1) i = loadBefore p σ k i + if σ k = i then p k else 0 := by
  unfold loadBefore
  rw [Finset.sum_filter, Finset.sum_filter]
  have e : (if σ k = i then p k else 0) =
      ∑ j : Fin n, if j = k then (if σ j = i then p j else 0) else 0 := by
    rw [Finset.sum_ite_eq']
    simp
  rw [e, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hjk : j = k
  · subst hjk
    simp
  · have hne : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
    by_cases h1 : (j : ℕ) < k
    · have h2 : (j : ℕ) < k + 1 := by omega
      simp [hjk, h1, h2]
    · have h2 : ¬ (j : ℕ) < k + 1 := by omega
      simp [hjk, h1, h2]

/-- At or beyond the last index, `loadBefore` is the load. -/
theorem bs_loadBefore_of_le {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (k : ℕ) (hk : n ≤ k) (i
  : Fin m) :
    loadBefore p σ k i = load p σ i := by
  unfold loadBefore load
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have := j.isLt
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

/-- Restricting a job vector and assignment preserves every load in the retained prefix. -/
theorem loadBefore_restrict {m n N : ℕ} (h : n ≤ N) (p : Fin N → ℝ)
    (σ : Fin N → Fin m) (k : ℕ) (hk : k ≤ n) (i : Fin m) :
    loadBefore (p ∘ Fin.castLE h) (σ ∘ Fin.castLE h) k i = loadBefore p σ k i := by
  unfold loadBefore
  refine Finset.sum_bij (fun j _ => Fin.castLE h j) ?_ ?_ ?_ ?_
  · intro j hj
    simpa only [mem_filter, mem_univ, true_and, Function.comp_apply, Fin.val_castLE] using hj
  · intro a _ b _ hab
    apply Fin.ext
    simpa only [Fin.val_castLE] using congrArg (fun j : Fin N => (j : ℕ)) hab
  · intro j hj
    have hj' := (mem_filter.mp hj).2
    have hcast : Fin.castLE h (⟨j, lt_of_lt_of_le hj'.1 hk⟩ : Fin n) = j := by
      apply Fin.ext
      simp only [Fin.val_castLE]
    refine ⟨⟨j, lt_of_lt_of_le hj'.1 hk⟩, ?_, hcast⟩
    simpa only [mem_filter, mem_univ, true_and, Function.comp_apply, hcast] using hj'
  · intro j _
    rfl

/-- A list schedule restricts to a list schedule of any initial segment of the jobs. -/
theorem IsListSchedule.restrict {m n N : ℕ} (h : n ≤ N) (p : Fin N → ℝ)
    (σ : Fin N → Fin m) (hσ : IsListSchedule p σ) :
    IsListSchedule (p ∘ Fin.castLE h) (σ ∘ Fin.castLE h) := by
  intro k i
  rw [loadBefore_restrict h p σ k k.isLt.le,
    loadBefore_restrict h p σ k k.isLt.le]
  simpa only [Fin.val_castLE, Function.comp_apply] using hσ (Fin.castLE h k) i

/-- The loads before `k` sum to the lengths of the jobs before `k`. -/
theorem bs_sum_loadBefore {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (k : ℕ) :
    ∑ i, loadBefore p σ k i = ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k), p j := by
  unfold loadBefore
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ite_and]
  by_cases h : (j : ℕ) < k
  · simp [h, Finset.sum_ite_eq]
  · simp [h]

/-- The loads sum to the total length. -/
theorem bs_sum_load {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) : ∑ i, load p σ i = ∑ j, p j := by
  unfold load
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Finset.sum_ite_eq]

/-- The lengths of the jobs before `k`, plus `p k`, are at most the total (nonnegative lengths). -/
theorem bs_sum_filter_add_le {n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (k : Fin n) :
    ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k), p j + p k ≤ ∑ j, p j := by
  have hk : k ∉ univ.filter (fun j : Fin n => (j : ℕ) < k) := by simp
  rw [add_comm, ← Finset.sum_insert hk]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hp j)

theorem bs_loadBefore_mono {m n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : Fin n → Fin m) {k k'
  : ℕ}
    (h : k ≤ k') (i : Fin m) : loadBefore p σ k i ≤ loadBefore p σ k' i := by
  unfold loadBefore
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hp j)
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact ⟨by omega, hj.2⟩

theorem bs_loadBefore_le_load {m n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : Fin n → Fin m) (k
  : ℕ)
    (i : Fin m) : loadBefore p σ k i ≤ load p σ i := by
  unfold loadBefore load
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hp j)
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact hj.2

/-- The load of a machine with no job is `0`. -/
theorem bs_load_eq_zero {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (i : Fin m) (h : ∀ j, σ j ≠
  i) :
    load p σ i = 0 := by
  unfold load
  refine Finset.sum_eq_zero fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact absurd hj (h j)

/-- With a cutoff `c`: a machine with a job of index below `c` has a last such job. -/
theorem bs_exists_last_job_before {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (c : ℕ) (i : Fin m)
    (h : ∃ j : Fin n, (j : ℕ) < c ∧ σ j = i) :
    ∃ k : Fin n, (k : ℕ) < c ∧ σ k = i ∧ loadBefore p σ c i = loadBefore p σ k i + p k := by
  obtain ⟨j0, hj0c, hj0⟩ := h
  have hne : (univ.filter (fun j : Fin n => (j : ℕ) < c ∧ σ j = i)).Nonempty :=
    ⟨j0, by simp [hj0c, hj0]⟩
  obtain ⟨k, hkS, hkmax⟩ := Finset.exists_max_image _ (fun j : Fin n => (j : ℕ)) hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hkS
  refine ⟨k, hkS.1, hkS.2, ?_⟩
  have e : loadBefore p σ c i = loadBefore p σ ((k : ℕ) + 1) i := by
    unfold loadBefore
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : (j : ℕ) ≤ k := hkmax j (by simp [h1, h2])
      exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h2⟩
  rw [e, bs_loadBefore_succ]
  simp [hkS.2]

/-- A machine with a job has a last job `k`, and its load is the load before `k` plus `p k`. -/
theorem bs_exists_last_job {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (i : Fin m) (h : ∃ j, σ j
  = i) :
    ∃ k : Fin n, σ k = i ∧ load p σ i = loadBefore p σ k i + p k := by
  obtain ⟨j, hj⟩ := h
  obtain ⟨k, -, hk, he⟩ := bs_exists_last_job_before p σ n i ⟨j, j.isLt, hj⟩
  exact ⟨k, hk, by rw [← bs_loadBefore_of_le p σ n le_rfl i, he]⟩

/-- A machine with no job of index below `c` has load `0` before `c`. -/
theorem bs_loadBefore_eq_zero {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (c : ℕ) (i : Fin m)
    (h : ∀ j : Fin n, (j : ℕ) < c → σ j ≠ i) : loadBefore p σ c i = 0 := by
  unfold loadBefore
  refine Finset.sum_eq_zero fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact absurd hj.2 (h j hj.1)

/-- In a list schedule, `m` times the least load before `k` is at most the total length of the
jobs before `k`. -/
theorem bs_mul_loadBefore_le {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (hσ : IsListSchedule p σ)
    (k : Fin n) : (m : ℝ) * loadBefore p σ k (σ k) ≤ ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) <
      k), p j := by
  have h : ∑ _i : Fin m, loadBefore p σ k (σ k) ≤ ∑ i, loadBefore p σ k i :=
    Finset.sum_le_sum fun i _ => hσ k i
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    bs_sum_loadBefore] using h

theorem bs_makespan_le_iff {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) (c : ℝ) :
    makespan p σ ≤ c ↔ ∀ i, load p σ i ≤ c := by
  unfold makespan
  rw [Finset.sup'_le_iff]
  simp

theorem bs_exists_load_eq_makespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) :
    ∃ i, load p σ i = makespan p σ := by
  obtain ⟨i, -, h⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := Fin m)) (load p σ)
  exact ⟨i, h.symm⟩

/-- Every machine load is at most the makespan. -/
theorem load_le_makespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) (i : Fin m) :
    load p σ i ≤ makespan p σ :=
  Finset.le_sup' (load p σ) (mem_univ i)

theorem bs_makespan_nonneg {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : Fin n →
  Fin m) :
    0 ≤ makespan p σ :=
  le_trans (Finset.sum_nonneg fun j _ => hp j) (load_le_makespan p σ 0)

/-- Relabeling the jobs by a permutation changes no load. -/
theorem bs_load_comp {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (π : Equiv.Perm (Fin n)) (i :
  Fin m) :
    load (p ∘ π) (σ ∘ π) i = load p σ i := by
  unfold load
  rw [Finset.sum_filter, Finset.sum_filter]
  exact Equiv.sum_comp π (fun j => if σ j = i then p j else 0)

/-- The total length is at most `m` times the makespan. -/
theorem sum_le_mul_makespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) :
    ∑ j, p j ≤ (m : ℝ) * makespan p σ := by
  rw [← bs_sum_load p σ]
  have h : ∑ i, load p σ i ≤ ∑ _i : Fin m, makespan p σ :=
    Finset.sum_le_sum fun i _ => load_le_makespan p σ i
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

/-- The optimal makespan is attained. -/
theorem exists_makespan_eq_optMakespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) :
    ∃ τ : Fin n → Fin m, makespan p τ = optMakespan m p := by
  obtain ⟨τ, -, h⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := Fin n → Fin m))
    (fun σ : Fin n → Fin m => makespan p σ)
  exact ⟨τ, h.symm⟩

/-- A least-loaded machine of a load vector (the greedy choice). -/
noncomputable def leastLoadedMachine {m : ℕ} [NeZero m] (L : Fin m → ℝ) : Fin m :=
  Classical.choose (Finset.exists_min_image univ L univ_nonempty)

theorem bs_argmin_le {m : ℕ} [NeZero m] (L : Fin m → ℝ) (i : Fin m) : L (leastLoadedMachine L) ≤ L
    i :=
  (Classical.choose_spec (Finset.exists_min_image univ L univ_nonempty)).2 i (mem_univ i)

/-- The greedy loads after the first `k` jobs. -/
noncomputable def greedyLoads {m n : ℕ} [NeZero m] (p : Fin n → ℝ) : ℕ → Fin m → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun i => greedyLoads p k i +
      if i = leastLoadedMachine (greedyLoads p k) then (if h : k < n then p ⟨k, h⟩ else 0) else 0

theorem bs_loadBefore_greedy {m n : ℕ} [NeZero m] (p : Fin n → ℝ) :
    ∀ k : ℕ, k ≤ n → ∀ i : Fin m, loadBefore p (fun j : Fin n => leastLoadedMachine (greedyLoads p
        (j : ℕ)))
      k i =
      greedyLoads p k i := by
  intro k
  induction k with
  | zero =>
    intro _ i
    rw [bs_loadBefore_zero]
    rfl
  | succ k ih =>
    intro hk i
    have hkn : k < n := by omega
    have e := bs_loadBefore_succ p (fun j : Fin n => leastLoadedMachine (greedyLoads p (j : ℕ)))
        ⟨k, hkn⟩ i
    simp only at e
    rw [e, ih (by omega) i]
    simp only [greedyLoads, hkn, ↓reduceDIte]
    by_cases hi : i = leastLoadedMachine (greedyLoads p k)
    · simp [hi]
    · have hi' : ¬ leastLoadedMachine (greedyLoads p k) = i := fun h => hi h.symm
      simp [hi, hi']

/-- A list schedule exists. -/
theorem exists_isListSchedule {m n : ℕ} [NeZero m] (p : Fin n → ℝ) :
    ∃ σ : Fin n → Fin m, IsListSchedule p σ := by
  refine ⟨fun j : Fin n => leastLoadedMachine (greedyLoads p (j : ℕ)), fun k i => ?_⟩
  rw [bs_loadBefore_greedy p k k.isLt.le, bs_loadBefore_greedy p k k.isLt.le]
  exact bs_argmin_le _ i

/-- An LPT schedule exists. -/
theorem exists_isLPTSchedule {m n : ℕ} [NeZero m] (p : Fin n → ℝ) :
    ∃ σ : Fin n → Fin m, IsLPTSchedule p σ := by
  set π := Tuple.sort (fun j => -p j) with hπ
  have hanti : Antitone (p ∘ π) := by
    intro a b hab
    have := Tuple.monotone_sort (fun j => -p j) hab
    simp only [Function.comp] at this ⊢
    linarith
  obtain ⟨σ', hσ'⟩ := exists_isListSchedule (m := m) (p ∘ π)
  refine ⟨σ' ∘ π.symm, π, hanti, ?_⟩
  have e : (σ' ∘ ⇑π.symm) ∘ ⇑π = σ' := by
    funext j
    simp
  rw [e]
  exact hσ'

/-- The optimal makespan is at most the makespan of every assignment. -/
theorem optMakespan_le {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (τ : Fin n → Fin m) :
    optMakespan m p ≤ makespan p τ :=
  Finset.inf'_le (fun σ : Fin n → Fin m => makespan p σ) (mem_univ τ)

/-- For nonnegative lengths every job is at most the makespan. -/
theorem le_makespan_of_nonneg {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (j : Fin n) : p j ≤ makespan p σ := by
  refine le_trans ?_ (load_le_makespan p σ (σ j))
  exact Finset.single_le_sum (fun j _ => hp j) (by simp : j ∈ univ.filter (fun j' : Fin n => σ j'
    = σ j))

/-- Relabeling the jobs by a permutation does not change the makespan. -/
theorem makespan_comp {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (σ : Fin n → Fin m) (π :
  Equiv.Perm (Fin n)) :
    makespan (p ∘ π) (σ ∘ π) = makespan p σ := by
  have h : load (p ∘ π) (σ ∘ π) = load p σ := funext (bs_load_comp p σ π)
  unfold makespan
  rw [h]

end GrahamLPT
