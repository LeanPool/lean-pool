/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

module

public import LeanPool.GrahamLPT.Defs
import LeanPool.GrahamLPT.Basic
import LeanPool.GrahamLPT.ListBound
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Positivity.Finset

/-!
# TightList

The unit-job family: optimum `m`, list-schedule makespan `2m − 1`.
Helpers carry the prefix `tl_`; the `_internal` twins of the Challenge theorems are closed in
`Contracts.lean`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

theorem tl_unitJobs_apply_lt (m : ℕ) (j : Fin (m * (m - 1) + 1)) (h : (j : ℕ) < m * (m - 1)) :
    unitJobs m j = 1 := by
  simp [unitJobs, h]

theorem tl_unitJobs_apply_last (m : ℕ) (j : Fin (m * (m - 1) + 1)) (h : m * (m - 1) ≤ (j : ℕ)) :
    unitJobs m j = m := by
  simp [unitJobs, not_lt.mpr h]

theorem tl_unitJobs_nonneg (m : ℕ) (j : Fin (m * (m - 1) + 1)) : 0 ≤ unitJobs m j := by
  unfold unitJobs
  split_ifs <;> positivity

/-- Before the long job, the load of a machine is the number of its jobs. -/
theorem tl_loadBefore_eq_card (m : ℕ) (σ : Fin (m * (m - 1) + 1) → Fin m) (k : ℕ) (hk : k ≤ m * (m
  - 1))
    (i : Fin m) :
    loadBefore (unitJobs m) σ k i =
      ((univ.filter (fun j : Fin (m * (m - 1) + 1) => (j : ℕ) < k ∧ σ j = i)).card : ℝ) := by
  unfold loadBefore
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) (fun j hj => tl_unitJobs_apply_lt m j
    (lt_of_lt_of_le (Finset.mem_filter.mp hj).2.1 hk))]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The jobs before `k ≤ m(m − 1)` have total length `k`. -/
theorem tl_sum_filter_lt (m : ℕ) (k : ℕ) (hk : k ≤ m * (m - 1)) :
    ∑ j ∈ univ.filter (fun j : Fin (m * (m - 1) + 1) => (j : ℕ) < k), unitJobs m j = k := by
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) (fun j hj => tl_unitJobs_apply_lt m j
    (lt_of_lt_of_le (Finset.mem_filter.mp hj).2 hk))]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Fin.card_filter_val_lt, min_eq_right (by omega)]

theorem tl_nat_le (m c : ℕ) (hm : 1 ≤ m) (h : m * c ≤ m * (m - 1) + (m - 1)) : c ≤ m - 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h ⊢
  by_contra hc
  have hc' : q + 1 ≤ c := by omega
  nlinarith

theorem tl_div_lt (m j : ℕ) (hm : 0 < m) (h : j < m * (m - 1)) : j / m < m - 1 := by
  rw [Nat.div_lt_iff_lt_mul hm, Nat.mul_comm]
  exact h

/-- The invariant of a list schedule of the unit jobs: `m · loadBefore k i ≤ k + m − 1` for `k ≤
m(m − 1)`. -/
theorem tl_loadBefore_le (m : ℕ) [NeZero m] (σ : Fin (m * (m - 1) + 1) → Fin m)
    (hσ : IsListSchedule (unitJobs m) σ) (k : ℕ) (hk : k ≤ m * (m - 1)) (i : Fin m) :
    (m : ℝ) * loadBefore (unitJobs m) σ k i ≤ k + m - 1 := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (NeZero.one_le : 1 ≤ m)
  induction k with
  | zero =>
    rw [bs_loadBefore_zero]
    push_cast
    linarith
  | succ k ih =>
    have hk' : k < m * (m - 1) := by omega
    have hk1 : k < m * (m - 1) + 1 := by omega
    have ih' := ih (by omega)
    have h := bs_loadBefore_succ (unitJobs m) σ ⟨k, hk1⟩ i
    rw [h, tl_unitJobs_apply_lt m ⟨k, hk1⟩ hk']
    push_cast
    by_cases hi : σ ⟨k, hk1⟩ = i
    · rw [ite_eq_left hi]
      have h2 := bs_mul_loadBefore_le (unitJobs m) σ hσ ⟨k, hk1⟩
      rw [tl_sum_filter_lt m k hk'.le, hi] at h2
      linarith
    · rw [ite_eq_right hi]
      linarith

/-- Every load after the unit jobs is `m − 1`. -/
theorem tl_loadBefore_units (m : ℕ) [NeZero m] (σ : Fin (m * (m - 1) + 1) → Fin m)
    (hσ : IsListSchedule (unitJobs m) σ) (i : Fin m) :
    loadBefore (unitJobs m) σ (m * (m - 1)) i = m - 1 := by
  have hm : 1 ≤ m := NeZero.one_le
  have hle : ∀ i' : Fin m, loadBefore (unitJobs m) σ (m * (m - 1)) i' ≤ (m : ℝ) - 1 := by
    intro i'
    have h1 := tl_loadBefore_le m σ hσ (m * (m - 1)) le_rfl i'
    obtain ⟨c, hc⟩ : ∃ c : ℕ, loadBefore (unitJobs m) σ (m * (m - 1)) i' = c :=
      ⟨_, tl_loadBefore_eq_card m σ (m * (m - 1)) le_rfl i'⟩
    rw [hc] at h1 ⊢
    have h2 : ((m * c : ℕ) : ℝ) ≤ ((m * (m - 1) + (m - 1) : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hm] at h1 ⊢
      linarith
    have h3 := tl_nat_le m c hm (by exact_mod_cast h2)
    have h4 : ((c : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast h3
    rw [Nat.cast_sub hm] at h4
    simpa using h4
  have hsum : ∑ i', loadBefore (unitJobs m) σ (m * (m - 1)) i' = ∑ _i' : Fin m, ((m : ℝ) - 1) := by
    rw [bs_sum_loadBefore, tl_sum_filter_lt m (m * (m - 1)) le_rfl, Finset.sum_const,
      Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast [Nat.cast_sub hm]
    ring
  exact (Finset.sum_eq_sum_iff_of_le (fun i' _ => hle i')).1 hsum i (Finset.mem_univ _)

theorem tl_le_makespan (m : ℕ) [NeZero m] (τ : Fin (m * (m - 1) + 1) → Fin m) :
    (m : ℝ) ≤ makespan (unitJobs m) τ := by
  have h := le_makespan_of_nonneg_internal (unitJobs m) (tl_unitJobs_nonneg m) τ (Fin.last _)
  rwa [tl_unitJobs_apply_last m _ (by simp)] at h

/-- An assignment of makespan `m`: the unit jobs spread `m` per machine over `m − 1` machines, the
long job alone. -/
theorem tl_exists_makespan_eq (m : ℕ) [NeZero m] :
    ∃ τ : Fin (m * (m - 1) + 1) → Fin m, makespan (unitJobs m) τ = m := by
  have hm : 0 < m := NeZero.pos m
  let τ : Fin (m * (m - 1) + 1) → Fin m := fun j =>
    if h : (j : ℕ) < m * (m - 1) then ⟨(j : ℕ) / m, by have := tl_div_lt m j hm h; omega⟩
    else ⟨m - 1, by omega⟩
  have hτ : ∀ j : Fin (m * (m - 1) + 1),
      ((τ j : Fin m) : ℕ) = if (j : ℕ) < m * (m - 1) then (j : ℕ) / m else m - 1 := by
    intro j
    by_cases h : (j : ℕ) < m * (m - 1) <;> simp [τ, h]
  refine ⟨τ, le_antisymm ?_ (tl_le_makespan m τ)⟩
  rw [bs_makespan_le_iff]
  intro i
  unfold load
  by_cases hi : (i : ℕ) = m - 1
  · calc ∑ j ∈ univ.filter (fun j => τ j = i), unitJobs m j
          ≤ ∑ j ∈ ({Fin.last _} : Finset (Fin (m * (m - 1) + 1))), unitJobs m j := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              rw [Finset.mem_singleton]
              by_contra hne
              have hj' : (j : ℕ) < m * (m - 1) := by
                have := Fin.val_lt_last hne
                simpa using this
              have h1 := hτ j
              rw [hj, ite_eq_left hj'] at h1
              have := tl_div_lt m j hm hj'
              omega
            · intro j _ _
              exact tl_unitJobs_nonneg m j
      _ = m := by rw [Finset.sum_singleton, tl_unitJobs_apply_last m _ (by simp)]
  · have hunit : ∀ j ∈ univ.filter (fun j => τ j = i), unitJobs m j = 1 := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      apply tl_unitJobs_apply_lt
      by_contra hj'
      have h1 := hτ j
      rw [hj, ite_eq_right hj'] at h1
      exact hi h1
    rw [Finset.sum_congr rfl hunit, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : (univ.filter (fun j => τ j = i)).card ≤ m := by
      rw [← Finset.card_map Fin.valEmbedding]
      calc ((univ.filter (fun j => τ j = i)).map Fin.valEmbedding).card
          ≤ (Finset.Ico (m * (i : ℕ)) (m * (i : ℕ) + m)).card := by
            apply Finset.card_le_card
            intro x hx
            simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
              Fin.valEmbedding_apply] at hx
            obtain ⟨j, hj, rfl⟩ := hx
            have hj' : (j : ℕ) < m * (m - 1) := by
              by_contra hj'
              have h1 := hτ j
              rw [hj, ite_eq_right hj'] at h1
              exact hi h1
            have h1 := hτ j
            rw [hj, ite_eq_left hj'] at h1
            have h2 := Nat.div_add_mod (j : ℕ) m
            have h3 := Nat.mod_lt (j : ℕ) hm
            rw [← h1] at h2
            rw [Finset.mem_Ico]
            omega
        _ = m := by rw [Nat.card_Ico]; omega
    exact_mod_cast hcard

/-- The `m(m − 1)` unit jobs with one job of length `m` have optimal makespan `m`. -/
theorem unitJobs_optMakespan_internal (m : ℕ) [NeZero m] : optMakespan m (unitJobs m) = m := by
  apply le_antisymm
  · obtain ⟨τ, hτ⟩ := tl_exists_makespan_eq m
    rw [← hτ]
    exact optMakespan_le_internal _ τ
  · obtain ⟨τ, hτ⟩ := exists_makespan_eq_optMakespan_internal (m := m) (unitJobs m)
    rw [← hτ]
    exact tl_le_makespan m τ

/-- Every list schedule of the unit jobs followed by the job of length `m` has makespan `2m − 1`. -/
theorem unitJobs_listSchedule_makespan_internal (m : ℕ) [NeZero m] (σ : Fin (m * (m - 1) + 1) →
  Fin m)
    (hσ : IsListSchedule (unitJobs m) σ) : makespan (unitJobs m) σ = 2 * m - 1 := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (NeZero.one_le : 1 ≤ m)
  obtain ⟨τ, hτ⟩ := tl_exists_makespan_eq m
  apply le_antisymm
  · have h := listSchedule_bound_internal (unitJobs m) (tl_unitJobs_nonneg m) σ hσ τ
    rw [hτ] at h
    exact le_of_mul_le_mul_left (a := (m : ℝ)) (by linarith) (by linarith)
  · have h1 := bs_loadBefore_succ (unitJobs m) σ (Fin.last _) (σ (Fin.last _))
    rw [ite_eq_left rfl, tl_unitJobs_apply_last m _ (by simp)] at h1
    simp only [Fin.val_last] at h1
    rw [bs_loadBefore_of_le (unitJobs m) σ (m * (m - 1) + 1) le_rfl, tl_loadBefore_units m σ hσ]
      at h1
    have h2 := load_le_makespan_internal (unitJobs m) σ (σ (Fin.last _))
    linarith

end GrahamLPT
