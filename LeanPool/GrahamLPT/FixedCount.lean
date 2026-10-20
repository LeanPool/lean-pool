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
import LeanPool.GrahamLPT.TightLPT
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity.Finset

/-!
# FixedCount

The supremum of the LPT ratio for a fixed number `n ≥ 2m + 1` of jobs: Graham's jobs followed by
small jobs. Helpers carry the prefix `fc_`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- The lengths by index: Graham's `2m + 1` jobs (`2m − 1, 2m − 1, …, m, m, m`), then `ε`. -/
noncomputable def paddedJobLength (m : ℕ) (ε : ℝ) (j : ℕ) : ℝ :=
  if j < 2 * m then 2 * (m : ℝ) - 1 - ((j / 2 : ℕ) : ℝ) else if j = 2 * m then (m : ℝ) else ε

/-- Graham's `2m + 1` jobs followed by `n − 2m − 1` jobs of length `ε`. -/
noncomputable def paddedJobs (m n : ℕ) (ε : ℝ) : Fin n → ℝ := fun j => paddedJobLength m ε j

theorem fc_len_lt (m : ℕ) (ε : ℝ) (j : ℕ) (h : j < 2 * m) :
    paddedJobLength m ε j = 2 * (m : ℝ) - 1 - ((j / 2 : ℕ) : ℝ) := by
  unfold paddedJobLength
  exact ite_eq_left h

theorem fc_len_two_mul (m : ℕ) (ε : ℝ) : paddedJobLength m ε (2 * m) = m := by
  unfold paddedJobLength
  rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]

theorem fc_len_gt (m : ℕ) (ε : ℝ) (j : ℕ) (h : 2 * m < j) : paddedJobLength m ε j = ε := by
  have h1 : ¬ j < 2 * m := by omega
  have h2 : ¬ j = 2 * m := by omega
  unfold paddedJobLength
  rw [ite_eq_right h1, ite_eq_right h2]

/-- Each of Graham's jobs is at least `m`. -/
theorem fc_le_len (m : ℕ) (ε : ℝ) (j : ℕ) (h : j ≤ 2 * m) : (m : ℝ) ≤ paddedJobLength m ε j := by
  rcases Nat.lt_or_ge j (2 * m) with h1 | h1
  · rw [fc_len_lt m ε j h1]
    have h2 : j / 2 + 1 ≤ m := by omega
    have h3 : ((j / 2 : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h2
    linarith
  · have h2 : j = 2 * m := by omega
    rw [h2]
    exact (fc_len_two_mul m ε).ge

theorem fc_len_pos (m : ℕ) (ε : ℝ) (hm : 0 < m) (hε : 0 < ε) (j : ℕ) : 0 < paddedJobLength m ε j
    := by
  rcases Nat.lt_or_ge (2 * m) j with h | h
  · rw [fc_len_gt m ε j h]
    exact hε
  · have h1 := fc_le_len m ε j h
    have h2 : (0 : ℝ) < m := by exact_mod_cast hm
    linarith

theorem fc_jobs_pos (m n : ℕ) (ε : ℝ) (hm : 0 < m) (hε : 0 < ε) (j : Fin n) : 0 < paddedJobs m n ε
    j :=
  fc_len_pos m ε hm hε j

/-- For `ε ≤ m` the family is listed in nonincreasing order. -/
theorem fc_antitone (m n : ℕ) (ε : ℝ) (hε : ε ≤ m) : Antitone (paddedJobs m n ε) := by
  intro a b hab
  have hab' : (a : ℕ) ≤ b := hab
  change paddedJobLength m ε b ≤ paddedJobLength m ε a
  rcases Nat.lt_or_ge (b : ℕ) (2 * m) with hb | hb
  · rw [fc_len_lt m ε b hb, fc_len_lt m ε a (by omega)]
    have h1 : (a : ℕ) / 2 ≤ (b : ℕ) / 2 := Nat.div_le_div_right hab'
    have h2 : (((a : ℕ) / 2 : ℕ) : ℝ) ≤ (((b : ℕ) / 2 : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  · rcases Nat.lt_or_ge (a : ℕ) (2 * m + 1) with ha | ha
    · have h1 := fc_le_len m ε a (by omega)
      rcases Nat.lt_or_ge (2 * m) (b : ℕ) with hb' | hb'
      · rw [fc_len_gt m ε b hb']
        linarith
      · have h2 : (b : ℕ) = 2 * m := by omega
        rw [h2, fc_len_two_mul]
        exact h1
    · simp only [fc_len_gt m ε a (by omega), fc_len_gt m ε b (by omega), le_refl]

/-- The unpadded jobs agree with Graham's original instance. -/
theorem paddedJobLength_eq_grahamJobs (m : ℕ) (ε : ℝ) (j : Fin (2 * m + 1)) :
    paddedJobLength m ε j = grahamJobs m j := by
  by_cases h : (j : ℕ) < 2 * m
  · simp only [paddedJobLength, grahamJobs, h, ite_true]
  · have hj : (j : ℕ) = 2 * m := by omega
    simp only [paddedJobLength, grahamJobs, hj, ite_true]

/-- Restriction to the original job count removes the small-job tail. -/
theorem paddedJobs_restrict (m n : ℕ) (ε : ℝ) (hn : 2 * m + 1 ≤ n) :
    paddedJobs m n ε ∘ Fin.castLE hn = grahamJobs m := by
  funext j
  exact paddedJobLength_eq_grahamJobs m ε j

/-- The pairs `j, 2m − 1 − j` among the original jobs sum to `3m − 1`. -/
theorem fc_pair (m : ℕ) (ε : ℝ) (j : ℕ) (h : j < 2 * m) :
    paddedJobLength m ε j + paddedJobLength m ε (2 * m - 1 - j) = 3 * m - 1 := by
  simpa only [← paddedJobLength_eq_grahamJobs m ε] using
    tg_pair m ⟨j, by omega⟩ h

/-- The optimal pairs `j, 2m − 3 − j` among the original jobs sum to `3m`. -/
theorem fc_pair' (m : ℕ) (ε : ℝ) (j : ℕ) (h : j < 2 * m - 2) :
    paddedJobLength m ε j + paddedJobLength m ε (2 * m - 3 - j) = 3 * m := by
  simpa only [← paddedJobLength_eq_grahamJobs m ε] using
    tg_pair' m ⟨j, by omega⟩ h

/-- The first `2m` jobs sum to `3m² − m`. -/
theorem fc_sum_lt (m n : ℕ) (ε : ℝ) (hn : 2 * m ≤ n) :
    ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < 2 * m), paddedJobs m n ε j = 3 * (m : ℝ) ^ 2 - m
        :=
      by
  rw [sum_filter]
  have h1 : ∑ j : Fin n, (if (j : ℕ) < 2 * m then paddedJobs m n ε j else 0) =
      ∑ j ∈ (range n).filter (fun j => j < 2 * m), paddedJobLength m ε j :=
    (Fin.sum_univ_eq_sum_range (fun j => if j < 2 * m then paddedJobLength m ε j else 0) n).trans
      (sum_filter (fun j => j < 2 * m) (paddedJobLength m ε)).symm
  have h2 : (range n).filter (fun j => j < 2 * m) = range (2 * m) := by
    ext j
    simp only [mem_filter, mem_range]
    omega
  have h3 : ∑ j ∈ range (2 * m), paddedJobLength m ε j =
      ∑ j ∈ range (2 * m), (2 * (m : ℝ) - 1 - ((j / 2 : ℕ) : ℝ)) :=
    sum_congr rfl fun j hj => fc_len_lt m ε j (mem_range.1 hj)
  rw [h1, h2, h3, tg_sum_range_aux]
  ring

/-- The pairing `j ↦ min (j, 2m − 1 − j)` of the first `2m` jobs has every load `3m − 1` before
index `2m`. -/
theorem fc_exists_prefix_pairing (m n : ℕ) [NeZero m] (ε : ℝ) (hn : 2 * m ≤ n) :
    ∃ τ : Fin n → Fin m, ∀ i, loadBefore (paddedJobs m n ε) τ (2 * m) i = 3 * m - 1 := by
  obtain ⟨ρ, hρ⟩ := tg_exists_prefix_pairing m
  let τ : Fin n → Fin m := fun j =>
    if hj : (j : ℕ) < 2 * m then ρ ⟨j, by omega⟩ else 0
  have hsmall : 2 * m ≤ 2 * m + 1 := by omega
  have hp : paddedJobs m n ε ∘ Fin.castLE hn = grahamJobs m ∘ Fin.castLE hsmall := by
    funext j
    exact paddedJobLength_eq_grahamJobs m ε (Fin.castLE hsmall j)
  have hτ : τ ∘ Fin.castLE hn = ρ ∘ Fin.castLE hsmall := by
    funext j
    simp only [τ, Function.comp_apply, Fin.val_castLE, j.isLt, ↓reduceDIte]
    congr 1
  refine ⟨τ, fun i => ?_⟩
  rw [← loadBefore_restrict hn _ τ (2 * m) le_rfl i, hp, hτ,
    loadBefore_restrict hsmall _ ρ (2 * m) le_rfl i, hρ i]

/-- The original prefix loads are unaffected by the lengths of later jobs. -/
theorem fc_loadBefore_two_mul (m n : ℕ) [NeZero m] (ε : ℝ)
    (hn : 2 * m + 1 ≤ n) (σ : Fin n → Fin m) (hσ : IsListSchedule (paddedJobs m n ε) σ)
    (i : Fin m) : loadBefore (paddedJobs m n ε) σ (2 * m) i = 3 * m - 1 := by
  have hrestricted := IsListSchedule.restrict hn (paddedJobs m n ε) σ hσ
  rw [paddedJobs_restrict m n ε hn] at hrestricted
  have hload := tg_loadBefore_two_mul m (σ ∘ Fin.castLE hn) hrestricted i
  rw [← paddedJobs_restrict m n ε hn,
    loadBefore_restrict hn (paddedJobs m n ε) σ (2 * m) (by omega) i] at hload
  exact hload

/-- Every list schedule of the family in its own order has makespan at least `4m − 1`: the job
`2m`, of length
`m`, lands on a machine of load `3m − 1`. -/
theorem fc_le_makespan_listSchedule (m n : ℕ) [NeZero m] (ε : ℝ) (hε0 : 0 < ε)
    (hn : 2 * m + 1 ≤ n) (σ : Fin n → Fin m) (hσ : IsListSchedule (paddedJobs m n ε) σ) :
    4 * (m : ℝ) - 1 ≤ makespan (paddedJobs m n ε) σ := by
  have hm : 0 < m := NeZero.pos m
  have hp : ∀ j, 0 ≤ paddedJobs m n ε j := fun j => (fc_jobs_pos m n ε hm hε0 j).le
  obtain ⟨k, hk⟩ : ∃ k : Fin n, (k : ℕ) = 2 * m := ⟨⟨2 * m, by omega⟩, rfl⟩
  have h1 := fc_loadBefore_two_mul m n ε hn σ hσ (σ k)
  have h2 := bs_loadBefore_succ (paddedJobs m n ε) σ k (σ k)
  rw [hk, ite_eq_left rfl] at h2
  have h3 := bs_loadBefore_le_load (paddedJobs m n ε) hp σ (2 * m + 1) (σ k)
  have h4 := load_le_makespan (paddedJobs m n ε) σ (σ k)
  have h5 : paddedJobs m n ε k = m := by
    change paddedJobLength m ε k = m
    rw [hk]
    exact fc_len_two_mul m ε
  linarith

/-- An antitone relabeling of the family leaves the lengths unchanged (`Tuple.unique_antitone`). -/
theorem fc_comp_eq (m n : ℕ) (ε : ℝ) (hε1 : ε ≤ m) (π : Equiv.Perm (Fin n))
    (h : Antitone (paddedJobs m n ε ∘ π)) : paddedJobs m n ε ∘ π = paddedJobs m n ε := by
  have h1 : Antitone (paddedJobs m n ε ∘ ⇑(1 : Equiv.Perm (Fin n))) := by
    simpa using fc_antitone m n ε hε1
  have h2 := Tuple.unique_antitone h h1
  simpa using h2

/-- Every LPT schedule of the family has makespan at least `4m − 1`. -/
theorem fc_le_makespan_lpt (m n : ℕ) [NeZero m] (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ m)
    (hn : 2 * m + 1 ≤ n) (σ : Fin n → Fin m) (hσ : IsLPTSchedule (paddedJobs m n ε) σ) :
    4 * (m : ℝ) - 1 ≤ makespan (paddedJobs m n ε) σ := by
  obtain ⟨π, hanti, hls⟩ := hσ
  have hc := fc_comp_eq m n ε hε1 π hanti
  rw [hc] at hls
  have h1 := fc_le_makespan_listSchedule m n ε hε0 hn (σ ∘ π) hls
  rw [← makespan_comp (paddedJobs m n ε) σ π, hc]
  exact h1

/-- The pairing `j ↦ min (j, 2m − 3 − j)` of the first `2m − 2` jobs, the three jobs of length `m`
and every
small job on the last machine: every load is at most `3m + nε`. -/
theorem fc_exists_opt (m n : ℕ) [NeZero m] (ε : ℝ) (hε0 : 0 ≤ ε) (hn : 2 * m + 1 ≤ n) :
    ∃ τ : Fin n → Fin m, ∀ i, load (paddedJobs m n ε) τ i ≤ 3 * m + n * ε := by
  have hm : 0 < m := NeZero.pos m
  refine ⟨fun j => if h : (j : ℕ) < 2 * m - 2 then ⟨min (j : ℕ) (2 * m - 3 - j), by omega⟩
    else ⟨m - 1, by omega⟩, fun i => ?_⟩
  have hi := i.isLt
  have hnε : 0 ≤ (n : ℝ) * ε := mul_nonneg (Nat.cast_nonneg n) hε0
  unfold load
  by_cases hlt : (i : ℕ) < m - 1
  · have hfib : univ.filter (fun j : Fin n =>
        (if h : (j : ℕ) < 2 * m - 2 then (⟨min (j : ℕ) (2 * m - 3 - j), by omega⟩ : Fin m)
          else ⟨m - 1, by omega⟩) = i) =
        {(⟨i, by omega⟩ : Fin n), ⟨2 * m - 3 - i, by omega⟩} := by
      ext j
      have hj := j.isLt
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Fin.ext_iff]
      split_ifs with h1 <;> dsimp only <;> omega
    rw [hfib, sum_pair (by rw [Ne, Fin.ext_iff]; dsimp only; omega)]
    have := fc_pair' m ε i (by omega)
    change paddedJobLength m ε i + paddedJobLength m ε (2 * m - 3 - i) ≤ 3 * m + n * ε
    linarith only [this, hnε]
  · have hfib : univ.filter (fun j : Fin n =>
        (if h : (j : ℕ) < 2 * m - 2 then (⟨min (j : ℕ) (2 * m - 3 - j), by omega⟩ : Fin m)
          else ⟨m - 1, by omega⟩) = i) =
        univ.filter (fun j : Fin n => 2 * m - 2 ≤ (j : ℕ)) := by
      ext j
      have hj := j.isLt
      simp only [mem_filter, mem_univ, true_and, Fin.ext_iff]
      split_ifs with h1 <;> dsimp only <;> omega
    rw [hfib, ← sum_filter_add_sum_filter_not (univ.filter (fun j : Fin n => 2 * m - 2 ≤ (j : ℕ)))
      (fun j : Fin n => (j : ℕ) < 2 * m + 1)]
    have hA : (univ.filter (fun j : Fin n => 2 * m - 2 ≤ (j : ℕ))).filter
        (fun j : Fin n => (j : ℕ) < 2 * m + 1) =
        {(⟨2 * m - 2, by omega⟩ : Fin n), ⟨2 * m - 1, by omega⟩, ⟨2 * m, by omega⟩} := by
      ext j
      have hj := j.isLt
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Fin.ext_iff]
      omega
    have hB : ∑ j ∈ (univ.filter (fun j : Fin n => 2 * m - 2 ≤ (j : ℕ))).filter
        (fun j : Fin n => ¬ (j : ℕ) < 2 * m + 1), paddedJobs m n ε j ≤ n * ε := by
      calc ∑ j ∈ (univ.filter (fun j : Fin n => 2 * m - 2 ≤ (j : ℕ))).filter
            (fun j : Fin n => ¬ (j : ℕ) < 2 * m + 1), paddedJobs m n ε j
          = ∑ _j ∈ (univ.filter (fun j : Fin n => 2 * m - 2 ≤ (j : ℕ))).filter
            (fun j : Fin n => ¬ (j : ℕ) < 2 * m + 1), ε := by
            refine sum_congr rfl fun j hj => ?_
            simp only [mem_filter, mem_univ, true_and] at hj
            exact fc_len_gt m ε j (by omega)
        _ = (((univ.filter (fun j : Fin n => 2 * m - 2 ≤ (j : ℕ))).filter
            (fun j : Fin n => ¬ (j : ℕ) < 2 * m + 1)).card : ℝ) * ε := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ n * ε := by
            apply mul_le_mul_of_nonneg_right _ hε0
            have := card_le_univ ((univ.filter (fun j : Fin n => 2 * m - 2 ≤ (j : ℕ))).filter
              (fun j : Fin n => ¬ (j : ℕ) < 2 * m + 1))
            rw [Fintype.card_fin] at this
            exact_mod_cast this
    rw [hA, sum_insert (by simp only [mem_insert, mem_singleton, Fin.ext_iff]; omega),
      sum_pair (by rw [Ne, Fin.ext_iff]; dsimp only; omega)]
    have e1 : paddedJobs m n ε ⟨2 * m - 2, by omega⟩ = m := by
      change paddedJobLength m ε (2 * m - 2) = m
      rw [fc_len_lt m ε (2 * m - 2) (by omega)]
      have h : (2 * m - 2) / 2 + 1 = m := by omega
      have h' : (((2 * m - 2) / 2 : ℕ) : ℝ) + 1 = m := by exact_mod_cast h
      linarith only [h']
    have e2 : paddedJobs m n ε ⟨2 * m - 1, by omega⟩ = m := by
      change paddedJobLength m ε (2 * m - 1) = m
      rw [fc_len_lt m ε (2 * m - 1) (by omega)]
      have h : (2 * m - 1) / 2 + 1 = m := by omega
      have h' : (((2 * m - 1) / 2 : ℕ) : ℝ) + 1 = m := by exact_mod_cast h
      linarith only [h']
    have e3 : paddedJobs m n ε ⟨2 * m, by omega⟩ = m := fc_len_two_mul m ε
    rw [e1, e2, e3]
    linarith only [hB]

/-- The optimum of the family is at most `3m + nε`. -/
theorem fc_optMakespan_le (m n : ℕ) [NeZero m] (ε : ℝ) (hε0 : 0 ≤ ε) (hn : 2 * m + 1 ≤ n) :
    optMakespan m (paddedJobs m n ε) ≤ 3 * m + n * ε := by
  obtain ⟨τ, hτ⟩ := fc_exists_opt m n ε hε0 hn
  exact (optMakespan_le _ τ).trans ((bs_makespan_le_iff _ _ _).2 hτ)

/-- A positive instance with a job has a positive optimum. -/
theorem fc_optMakespan_pos {m n : ℕ} [NeZero m] (hn : 0 < n) (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) :
    0 < optMakespan m p := by
  obtain ⟨τ, hτ⟩ := exists_makespan_eq_optMakespan (m := m) p
  rw [← hτ]
  exact lt_of_lt_of_le (hp ⟨0, hn⟩) (le_makespan_of_nonneg p (fun j => (hp j).le) τ ⟨0,
    hn⟩)

/-- For every fixed number `n ≥ 2m + 1` of jobs, Graham's constant `4/3 − 1/(3m)` is still the
supremum of
`C(σ)/optMakespan` over the LPT schedules of the positive instances with `n` jobs (for `m ≥ 2` it
is attained only at
`n = 2m + 1`, `lpt_lt_bound_of_card_ne`). -/
theorem isLUB_lpt_ratio_of_card {m n : ℕ} [NeZero m] (hn : 2 * m + 1 ≤ n) :
    IsLUB {r : ℝ | ∃ (p : Fin n → ℝ) (σ : Fin n → Fin m), (∀ j, 0 < p j) ∧ IsLPTSchedule p σ ∧
      r = makespan p σ / optMakespan m p} (4 / 3 - 1 / (3 * m)) := by
  have hm : 0 < m := NeZero.pos m
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm3 : (0 : ℝ) < 3 * m := by linarith
  have hc : (4 : ℝ) / 3 - 1 / (3 * m) = (4 * m - 1) / (3 * m) := by field_simp
  have hn0 : 0 < n := by omega
  refine ⟨?_, ?_⟩
  · rw [mem_upperBounds]
    rintro r ⟨p, σ, hp, hσ, rfl⟩
    have hopt := fc_optMakespan_pos (m := m) hn0 p hp
    rw [div_le_iff₀ hopt]
    exact lpt_le_optMakespan p (fun j => (hp j).le) σ hσ
  · rw [mem_lowerBounds]
    intro b hb
    rw [mem_upperBounds] at hb
    by_contra hlt
    have hlt' : b < 4 / 3 - 1 / (3 * m) := lt_of_not_ge hlt
    rw [hc, lt_div_iff₀ hm3] at hlt'
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 4 * m - 1 - 3 * m * b := ⟨_, rfl⟩
    have hDpos : 0 < D := by rw [hD]; linarith
    have hbn : 0 ≤ |b| * n := mul_nonneg (abs_nonneg b) (Nat.cast_nonneg n)
    have hden : 0 < D + |b| * n + 1 := by linarith only [hDpos, hbn]
    obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = D / (D + |b| * n + 1) := ⟨_, rfl⟩
    have hε0 : 0 < ε := by rw [hε]; exact div_pos hDpos hden
    have hε1 : ε ≤ 1 := by rw [hε, div_le_one hden]; linarith only [hbn]
    have hεm : ε ≤ m := by linarith only [hε1, hmR]
    have hεeq : ε * (D + |b| * n + 1) = D := by rw [hε]; exact div_mul_cancel₀ D hden.ne'
    obtain ⟨σ, hσ⟩ := exists_isLPTSchedule (m := m) (paddedJobs m n ε)
    have hpos : ∀ j, 0 < paddedJobs m n ε j := fc_jobs_pos m n ε hm hε0
    have hmem := hb _ ⟨paddedJobs m n ε, σ, hpos, hσ, rfl⟩
    have hopt := fc_optMakespan_pos (m := m) hn0 _ hpos
    have hC := fc_le_makespan_lpt m n ε hε0 hεm hn σ hσ
    have hoptle := fc_optMakespan_le m n ε hε0.le hn
    rw [div_le_iff₀ hopt] at hmem
    have hkey : b * optMakespan m (paddedJobs m n ε) < 4 * m - 1 := by
      rcases le_or_gt b 0 with hb0 | hb0
      · have h1 : b * optMakespan m (paddedJobs m n ε) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hb0 hopt.le
        linarith only [h1, hmR]
      · have h1 : b * optMakespan m (paddedJobs m n ε) ≤ b * (3 * m + n * ε) :=
          mul_le_mul_of_nonneg_left hoptle hb0.le
        have h2 : |b| = b := abs_of_pos hb0
        rw [h2] at hεeq
        have h3 : b * n * ε < D := by
          nlinarith only [hεeq, hε0, mul_pos hε0 hDpos]
        rw [hD] at h3
        nlinarith only [h1, h3]
    linarith only [hC, hmem, hkey]

end GrahamLPT
