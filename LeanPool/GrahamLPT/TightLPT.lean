/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

module

public import LeanPool.GrahamLPT.Defs
import LeanPool.GrahamLPT.Basic
import LeanPool.GrahamLPT.Key
import LeanPool.GrahamLPT.LPTBound
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity.Finset

/-!
# TightLPT

Graham's family: optimum `3m`, LPT makespan `4m − 1`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

theorem tg_grahamJobs_apply_lt (m : ℕ) (j : Fin (2 * m + 1)) (h : (j : ℕ) < 2 * m) :
    grahamJobs m j = 2 * (m : ℝ) - 1 - (((j : ℕ) / 2 : ℕ) : ℝ) := by
  unfold grahamJobs
  exact ite_eq_left h

theorem tg_grahamJobs_apply_last (m : ℕ) (j : Fin (2 * m + 1)) (h : 2 * m ≤ (j : ℕ)) : grahamJobs
  m j = m := by
  unfold grahamJobs
  exact ite_eq_right (by omega)

theorem tg_le_grahamJobs (m : ℕ) (j : Fin (2 * m + 1)) : (m : ℝ) ≤ grahamJobs m j := by
  by_cases h : (j : ℕ) < 2 * m
  · rw [tg_grahamJobs_apply_lt m j h]
    have h1 : (j : ℕ) / 2 + 1 ≤ m := by omega
    have h2 : (((j : ℕ) / 2 : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h1
    linarith
  · rw [tg_grahamJobs_apply_last m j (by omega)]

theorem tg_grahamJobs_nonneg (m : ℕ) (j : Fin (2 * m + 1)) : 0 ≤ grahamJobs m j :=
  le_trans (Nat.cast_nonneg m) (tg_le_grahamJobs m j)

/-- `Σ_{j < 2k} (c − ⌊j/2⌋) = 2kc − k(k − 1)`. -/
theorem tg_sum_range_aux (c : ℝ) (k : ℕ) :
    ∑ j ∈ range (2 * k), (c - ((j / 2 : ℕ) : ℝ)) = 2 * (k : ℝ) * c - (k : ℝ) * ((k : ℝ) - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      show (2 * k) / 2 = k by omega, show (2 * k + 1) / 2 = k by omega]
    push_cast
    ring

theorem tg_grahamJobs_sum (m : ℕ) : ∑ j, grahamJobs m j = 3 * (m : ℝ) ^ 2 := by
  have h1 : ∑ j, grahamJobs m j = ∑ j ∈ range (2 * m + 1),
      (if j < 2 * m then 2 * (m : ℝ) - 1 - ((j / 2 : ℕ) : ℝ) else (m : ℝ)) :=
    Fin.sum_univ_eq_sum_range (fun j => if j < 2 * m then 2 * (m : ℝ) - 1 - ((j / 2 : ℕ) : ℝ) else
      (m : ℝ))
      (2 * m + 1)
  have h2 : ∑ j ∈ range (2 * m),
      (if j < 2 * m then 2 * (m : ℝ) - 1 - ((j / 2 : ℕ) : ℝ) else (m : ℝ)) =
      ∑ j ∈ range (2 * m), (2 * (m : ℝ) - 1 - ((j / 2 : ℕ) : ℝ)) :=
    sum_congr rfl fun j hj => ite_eq_left (mem_range.1 hj)
  rw [h1, sum_range_succ, ite_eq_right (lt_irrefl _), h2, tg_sum_range_aux]
  ring

/-- The pairs `j, 2m − 1 − j` of the first `2m` jobs sum to `3m − 1`. -/
theorem tg_pair (m : ℕ) (j : Fin (2 * m + 1)) (h : (j : ℕ) < 2 * m) :
    grahamJobs m j + grahamJobs m ⟨2 * m - 1 - j, by omega⟩ = 3 * m - 1 := by
  have key : ∀ a b : ℕ, a + b + 1 = m →
      2 * (m : ℝ) - 1 - (a : ℝ) + (2 * (m : ℝ) - 1 - (b : ℝ)) = 3 * m - 1 := by
    intro a b hab
    have : (a : ℝ) + b + 1 = m := by exact_mod_cast hab
    linarith
  rw [tg_grahamJobs_apply_lt m j h, tg_grahamJobs_apply_lt m ⟨2 * m - 1 - j, by omega⟩
    (by dsimp only; omega)]
  exact key _ _ (by dsimp only; omega)

/-- The pairs `j, 2m − 3 − j` of the first `2m − 2` jobs sum to `3m`. -/
theorem tg_pair' (m : ℕ) (j : Fin (2 * m + 1)) (h : (j : ℕ) < 2 * m - 2) :
    grahamJobs m j + grahamJobs m ⟨2 * m - 3 - j, by omega⟩ = 3 * m := by
  have key : ∀ a b : ℕ, a + b + 2 = m →
      2 * (m : ℝ) - 1 - (a : ℝ) + (2 * (m : ℝ) - 1 - (b : ℝ)) = 3 * m := by
    intro a b hab
    have : (a : ℝ) + b + 2 = m := by exact_mod_cast hab
    linarith
  rw [tg_grahamJobs_apply_lt m j (by omega),
    tg_grahamJobs_apply_lt m ⟨2 * m - 3 - j, by omega⟩ (by dsimp only; omega)]
  exact key _ _ (by dsimp only; omega)

/-- The pairing `τ₀` (`j ↦ min (j, 2m − 3 − j)` for `j < 2m − 2`, the three jobs of length `m` on
the last machine)
has every load `3m`. -/
theorem tg_exists_opt (m : ℕ) [NeZero m] :
    ∃ τ : Fin (2 * m + 1) → Fin m, ∀ i, load (grahamJobs m) τ i = 3 * m := by
  have hm : 0 < m := NeZero.pos m
  refine ⟨fun j => if h : (j : ℕ) < 2 * m - 2 then ⟨min (j : ℕ) (2 * m - 3 - j), by omega⟩
    else ⟨m - 1, by omega⟩, fun i => ?_⟩
  have hi := i.isLt
  unfold load
  by_cases hlt : (i : ℕ) < m - 1
  · have hfib : univ.filter (fun j : Fin (2 * m + 1) =>
        (if h : (j : ℕ) < 2 * m - 2 then (⟨min (j : ℕ) (2 * m - 3 - j), by omega⟩ : Fin m)
          else ⟨m - 1, by omega⟩) = i) =
        {(⟨i, by omega⟩ : Fin (2 * m + 1)), ⟨2 * m - 3 - i, by omega⟩} := by
      ext j
      have hj := j.isLt
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Fin.ext_iff]
      split_ifs with h1 <;> dsimp only <;> omega
    rw [hfib, sum_pair (by rw [Ne, Fin.ext_iff]; dsimp only; omega)]
    exact tg_pair' m ⟨i, by omega⟩ (by dsimp only; omega)
  · have hfib : univ.filter (fun j : Fin (2 * m + 1) =>
        (if h : (j : ℕ) < 2 * m - 2 then (⟨min (j : ℕ) (2 * m - 3 - j), by omega⟩ : Fin m)
          else ⟨m - 1, by omega⟩) = i) =
        {(⟨2 * m - 2, by omega⟩ : Fin (2 * m + 1)), ⟨2 * m - 1, by omega⟩, ⟨2 * m, by omega⟩} := by
      ext j
      have hj := j.isLt
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Fin.ext_iff]
      split_ifs with h1 <;> dsimp only <;> omega
    rw [hfib, sum_insert (by simp only [mem_insert, mem_singleton, Fin.ext_iff]; omega),
      sum_pair (by rw [Ne, Fin.ext_iff]; dsimp only; omega),
      tg_grahamJobs_apply_lt m ⟨2 * m - 2, by omega⟩ (by dsimp only; omega),
      tg_grahamJobs_apply_lt m ⟨2 * m - 1, by omega⟩ (by dsimp only; omega),
      tg_grahamJobs_apply_last m ⟨2 * m, by omega⟩ (by dsimp only; omega)]
    have key : ∀ a b : ℕ, a + 1 = m → b + 1 = m →
        2 * (m : ℝ) - 1 - (a : ℝ) + (2 * (m : ℝ) - 1 - (b : ℝ) + m) = 3 * m := by
      intro a b ha hb
      have h1 : (a : ℝ) + 1 = m := by exact_mod_cast ha
      have h2 : (b : ℝ) + 1 = m := by exact_mod_cast hb
      linarith
    exact key _ _ (by dsimp only; omega) (by dsimp only; omega)

theorem tg_le_makespan (m : ℕ) [NeZero m] (τ : Fin (2 * m + 1) → Fin m) :
    3 * (m : ℝ) ≤ makespan (grahamJobs m) τ := by
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have h := sum_le_mul_makespan (grahamJobs m) τ
  rw [tg_grahamJobs_sum] at h
  have h' : (m : ℝ) * (3 * m) ≤ (m : ℝ) * makespan (grahamJobs m) τ := by linarith
  exact le_of_mul_le_mul_left h' hm

/-- The pairing `τ'` (`j ↦ min (j, 2m − 1 − j)`) of the first `2m` jobs has every load `3m − 1`
before index `2m`. -/
theorem tg_exists_prefix_pairing (m : ℕ) [NeZero m] :
    ∃ τ : Fin (2 * m + 1) → Fin m, ∀ i, loadBefore (grahamJobs m) τ (2 * m) i = 3 * m - 1 := by
  have hm : 0 < m := NeZero.pos m
  refine ⟨fun j => if h : (j : ℕ) < 2 * m then ⟨min (j : ℕ) (2 * m - 1 - j), by omega⟩
    else ⟨0, hm⟩, fun i => ?_⟩
  have hi := i.isLt
  unfold loadBefore
  have hfib : univ.filter (fun j : Fin (2 * m + 1) => (j : ℕ) < 2 * m ∧
      (if h : (j : ℕ) < 2 * m then (⟨min (j : ℕ) (2 * m - 1 - j), by omega⟩ : Fin m) else ⟨0, hm⟩)
        = i) =
      {(⟨i, by omega⟩ : Fin (2 * m + 1)), ⟨2 * m - 1 - i, by omega⟩} := by
    ext j
    have hj := j.isLt
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Fin.ext_iff]
    split_ifs with h1 <;> dsimp only <;> omega
  rw [hfib, sum_pair (by rw [Ne, Fin.ext_iff]; dsimp only; omega)]
  exact tg_pair m ⟨i, by omega⟩ (by dsimp only; omega)

/-- Graham's instance is listed in nonincreasing order. -/
theorem grahamJobs_antitone (m : ℕ) : Antitone (grahamJobs m) := by
  intro a b hab
  have hab' : (a : ℕ) ≤ b := hab
  by_cases hb : (b : ℕ) < 2 * m
  · have ha : (a : ℕ) < 2 * m := by omega
    rw [tg_grahamJobs_apply_lt m a ha, tg_grahamJobs_apply_lt m b hb]
    have h1 : (a : ℕ) / 2 ≤ (b : ℕ) / 2 := Nat.div_le_div_right hab'
    have h2 : (((a : ℕ) / 2 : ℕ) : ℝ) ≤ (((b : ℕ) / 2 : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  · rw [tg_grahamJobs_apply_last m b (by omega)]
    exact tg_le_grahamJobs m a

/-- Every list schedule of Graham's instance in its own order has every load `3m − 1` after the
first `2m` jobs
(the key lemma at `T = 3m − 1`, then the sum `m(3m − 1)`). -/
theorem tg_loadBefore_two_mul (m : ℕ) [NeZero m] (σ : Fin (2 * m + 1) → Fin m)
    (hσ : IsListSchedule (grahamJobs m) σ) (i : Fin m) :
    loadBefore (grahamJobs m) σ (2 * m) i = 3 * m - 1 := by
  have hm : 0 < m := NeZero.pos m
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : ∀ j, 0 ≤ grahamJobs m j := tg_grahamJobs_nonneg m
  obtain ⟨τ, hτ⟩ := tg_exists_prefix_pairing m
  have hle : ∀ i', loadBefore (grahamJobs m) σ (2 * m) i' ≤ 3 * m - 1 := by
    intro i'
    by_cases hex : ∃ j : Fin (2 * m + 1), (j : ℕ) < 2 * m ∧ σ j = i'
    · obtain ⟨k, hk, hσk, heq⟩ := bs_exists_last_job_before (grahamJobs m) σ (2 * m) i' hex
      rw [heq, ← hσk]
      apply key_lemma (grahamJobs m) hp (grahamJobs_antitone m) σ hσ k τ (3 * m - 1)
      · intro i''
        rw [← hτ i'']
        exact bs_loadBefore_mono _ hp τ (by omega) i''
      · have := tg_le_grahamJobs m k
        linarith
    · push Not at hex
      rw [bs_loadBefore_eq_zero _ σ _ i' hex]
      linarith
  have hlast : univ.filter (fun j : Fin (2 * m + 1) => ¬ (j : ℕ) < 2 * m) =
      {(⟨2 * m, by omega⟩ : Fin (2 * m + 1))} := by
    ext j
    have hj := j.isLt
    simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]
    omega
  have htot := tg_grahamJobs_sum m
  rw [← sum_filter_add_sum_filter_not univ (fun j : Fin (2 * m + 1) => (j : ℕ) < 2 * m), hlast,
    sum_singleton, tg_grahamJobs_apply_last m ⟨2 * m, by omega⟩ (by dsimp only; omega)] at htot
  have hsum := bs_sum_loadBefore (grahamJobs m) σ (2 * m)
  by_contra hne
  have hlt : loadBefore (grahamJobs m) σ (2 * m) i < 3 * m - 1 := lt_of_le_of_ne (hle i) hne
  have hs : ∑ i', loadBefore (grahamJobs m) σ (2 * m) i' < ∑ _i' : Fin m, (3 * (m : ℝ) - 1) :=
    sum_lt_sum (fun i' _ => hle i') ⟨i, mem_univ _, hlt⟩
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  nlinarith

/-- Every list schedule of Graham's instance in its own order has makespan `4m − 1`. -/
theorem tg_listSchedule_makespan (m : ℕ) [NeZero m] (σ : Fin (2 * m + 1) → Fin m)
    (hσ : IsListSchedule (grahamJobs m) σ) : makespan (grahamJobs m) σ = 4 * m - 1 := by
  have hm : 0 < m := NeZero.pos m
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply le_antisymm
  · obtain ⟨τ, hτ⟩ := tg_exists_opt m
    have h1 := lpt_bound (grahamJobs m) (tg_grahamJobs_nonneg m) σ
      ⟨1, by simpa using grahamJobs_antitone m, by simpa using hσ⟩ τ
    have h2 : makespan (grahamJobs m) τ = 3 * m :=
      le_antisymm ((bs_makespan_le_iff _ _ _).2 (fun i => (hτ i).le)) (tg_le_makespan m τ)
    rw [h2] at h1
    have h3 : (3 * (m : ℝ)) * makespan (grahamJobs m) σ ≤ (3 * (m : ℝ)) * (4 * m - 1) := by linarith
    exact le_of_mul_le_mul_left h3 (by linarith)
  · have h1 := tg_loadBefore_two_mul m σ hσ (σ ⟨2 * m, by omega⟩)
    have h2 : loadBefore (grahamJobs m) σ (2 * m + 1) (σ ⟨2 * m, by omega⟩) =
        loadBefore (grahamJobs m) σ (2 * m) (σ ⟨2 * m, by omega⟩) + grahamJobs m ⟨2 * m, by omega⟩
          := by
      have := bs_loadBefore_succ (grahamJobs m) σ ⟨2 * m, by omega⟩ (σ ⟨2 * m, by omega⟩)
      rw [ite_eq_left rfl] at this
      exact this
    have h3 := bs_loadBefore_of_le (grahamJobs m) σ (2 * m + 1) le_rfl (σ ⟨2 * m, by omega⟩)
    have h4 := load_le_makespan (grahamJobs m) σ (σ ⟨2 * m, by omega⟩)
    have h5 := tg_grahamJobs_apply_last m ⟨2 * m, by omega⟩ (by dsimp only; omega)
    linarith

/-- An antitone relabeling of Graham's instance leaves the lengths unchanged
(`Tuple.unique_antitone`). -/
theorem tg_comp_eq (m : ℕ) (π : Equiv.Perm (Fin (2 * m + 1))) (h : Antitone (grahamJobs m ∘ π)) :
    grahamJobs m ∘ π = grahamJobs m := by
  have h1 : Antitone (grahamJobs m ∘ ⇑(1 : Equiv.Perm (Fin (2 * m + 1)))) := by
    simpa using grahamJobs_antitone m
  have h2 := Tuple.unique_antitone h h1
  simpa using h2

/-- Graham's instance has optimal makespan `3m`. -/
theorem grahamJobs_optMakespan (m : ℕ) [NeZero m] : optMakespan m (grahamJobs m) = 3 * m
  := by
  obtain ⟨τ, hτ⟩ := tg_exists_opt m
  apply le_antisymm
  · calc optMakespan m (grahamJobs m) ≤ makespan (grahamJobs m) τ := optMakespan_le _ τ
      _ ≤ 3 * m := (bs_makespan_le_iff _ _ _).2 (fun i => (hτ i).le)
  · obtain ⟨τ', hτ'⟩ := exists_makespan_eq_optMakespan (m := m) (grahamJobs m)
    rw [← hτ']
    exact tg_le_makespan m τ'

/-- Every LPT schedule of Graham's instance has makespan `4m − 1`: the bound `4/3 − 1/(3m)` is
attained for every `m`. -/
theorem grahamJobs_lpt_makespan (m : ℕ) [NeZero m] (σ : Fin (2 * m + 1) → Fin m)
    (hσ : IsLPTSchedule (grahamJobs m) σ) : makespan (grahamJobs m) σ = 4 * m - 1 := by
  obtain ⟨π, hanti, hls⟩ := hσ
  have hc := tg_comp_eq m π hanti
  rw [hc] at hls
  have h1 := tg_listSchedule_makespan m (σ ∘ π) hls
  rw [← makespan_comp (grahamJobs m) σ π, hc, h1]

end GrahamLPT
