/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

module

public import LeanPool.GrahamLPT.Defs
import LeanPool.GrahamLPT.Basic
import LeanPool.GrahamLPT.TightLPT
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Positivity.Finset

/-!
# GrahamScaled

Scaling and relabeling of instances, and the sufficiency half of Dósa's theorem: every positive
multiple of Graham's instance in any order attains the bound. Helpers carry the prefix `gs_`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- Scaling the lengths by `a ≥ 0` scales the loads before `k`. -/
theorem gs_loadBefore_smul {m n : ℕ} (p : Fin n → ℝ) (a : ℝ) (σ : Fin n → Fin m) (k : ℕ) (i : Fin
  m) :
    loadBefore (fun j => a * p j) σ k i = a * loadBefore p σ k i := by
  unfold loadBefore
  rw [Finset.mul_sum]

/-- Scaling the lengths by `a` scales every load. -/
theorem gs_load_smul {m n : ℕ} (p : Fin n → ℝ) (a : ℝ) (σ : Fin n → Fin m) (i : Fin m) :
    load (fun j => a * p j) σ i = a * load p σ i := by
  unfold load
  rw [Finset.mul_sum]

/-- Scaling the lengths by `a ≥ 0` scales the makespan. -/
theorem gs_makespan_smul {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (a : ℝ) (ha : 0 ≤ a) (σ : Fin n →
  Fin m) :
    makespan (fun j => a * p j) σ = a * makespan p σ := by
  apply le_antisymm
  · rw [bs_makespan_le_iff]
    intro i
    rw [gs_load_smul]
    exact mul_le_mul_of_nonneg_left (load_le_makespan p σ i) ha
  · obtain ⟨i, hi⟩ := bs_exists_load_eq_makespan p σ
    rw [← hi, ← gs_load_smul p a σ i]
    exact load_le_makespan _ σ i

/-- Scaling the lengths by `a ≥ 0` scales the optimal makespan. -/
theorem gs_optMakespan_smul {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (a : ℝ) (ha : 0 ≤ a) :
    optMakespan m (fun j => a * p j) = a * optMakespan m p := by
  apply le_antisymm
  · obtain ⟨τ, hτ⟩ := exists_makespan_eq_optMakespan (m := m) p
    rw [← hτ, ← gs_makespan_smul p a ha τ]
    exact optMakespan_le _ τ
  · obtain ⟨τ, hτ⟩ := exists_makespan_eq_optMakespan (m := m) (fun j => a * p j)
    rw [← hτ, gs_makespan_smul p a ha τ]
    exact mul_le_mul_of_nonneg_left (optMakespan_le p τ) ha

/-- A list schedule of `p` is a list schedule of `a · p` for `a > 0`, and conversely. -/
theorem gs_isListSchedule_smul_iff {m n : ℕ} (p : Fin n → ℝ) (a : ℝ) (ha : 0 < a) (σ : Fin n → Fin
  m) :
    IsListSchedule (fun j => a * p j) σ ↔ IsListSchedule p σ := by
  unfold IsListSchedule
  constructor
  · intro h k i
    have hki := h k i
    rw [gs_loadBefore_smul, gs_loadBefore_smul] at hki
    exact le_of_mul_le_mul_left hki ha
  · intro h k i
    rw [gs_loadBefore_smul, gs_loadBefore_smul]
    exact mul_le_mul_of_nonneg_left (h k i) ha.le

/-- Relabeling the jobs by a permutation preserves the optimal makespan. -/
theorem gs_optMakespan_comp {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    optMakespan m (p ∘ π) = optMakespan m p := by
  apply le_antisymm
  · obtain ⟨τ, hτ⟩ := exists_makespan_eq_optMakespan (m := m) p
    rw [← hτ, ← makespan_comp p τ π]
    exact optMakespan_le _ (τ ∘ π)
  · obtain ⟨τ, hτ⟩ := exists_makespan_eq_optMakespan (m := m) (p ∘ π)
    have hp : (p ∘ π) ∘ π.symm = p := by
      funext j
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    have h := makespan_comp (p ∘ π) τ π.symm
    rw [hp] at h
    rw [← hτ, ← h]
    exact optMakespan_le _ (τ ∘ π.symm)

/-- Every positive multiple of Graham's instance, in any order, attains the bound: every LPT
schedule `σ` satisfies
`3m · C(σ) = (4m − 1) · optMakespan`. -/
theorem lpt_eq_bound_of_graham {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (a : ℝ) (ha : 0 < a)
    (e : Fin n ≃ Fin (2 * m + 1)) (he : ∀ j, p j = a * grahamJobs m (e j)) (σ : Fin n → Fin m)
    (hσ : IsLPTSchedule p σ) : 3 * m * makespan p σ = (4 * m - 1) * optMakespan m p := by
  have hn : n = 2 * m + 1 := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_fin] using h
  subst hn
  obtain ⟨π, hanti, hls⟩ := hσ
  have hpe : p = fun j => a * (grahamJobs m ∘ e) j := funext he
  have hpπ : p ∘ π = fun j => a * (grahamJobs m ∘ (π.trans e)) j := by
    funext j
    simp only [Function.comp_apply, Equiv.trans_apply, he]
  have hanti' : Antitone (grahamJobs m ∘ (π.trans e)) := by
    intro x y hxy
    have h := hanti hxy
    rw [hpπ] at h
    exact le_of_mul_le_mul_left h ha
  have hls' : IsListSchedule (grahamJobs m ∘ (π.trans e)) (σ ∘ π) := by
    rw [hpπ] at hls
    exact (gs_isListSchedule_smul_iff _ a ha _).1 hls
  have hcomp : (σ ∘ e.symm) ∘ (π.trans e) = σ ∘ π := by
    funext j
    simp only [Function.comp_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
  have hlpt : IsLPTSchedule (grahamJobs m) (σ ∘ e.symm) :=
    ⟨π.trans e, hanti', by rw [hcomp]; exact hls'⟩
  have h1 : makespan (grahamJobs m) (σ ∘ e.symm) = 4 * m - 1 :=
    grahamJobs_lpt_makespan m _ hlpt
  have h2 : makespan p σ = a * makespan (grahamJobs m) (σ ∘ e.symm) := by
    have hσe : (σ ∘ e.symm) ∘ e = σ := by
      funext j
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [hpe, gs_makespan_smul (grahamJobs m ∘ e) a ha.le σ,
      ← makespan_comp (grahamJobs m) (σ ∘ e.symm) e, hσe]
  have h3 : optMakespan m p = a * (3 * m) := by
    rw [hpe, gs_optMakespan_smul (grahamJobs m ∘ e) a ha.le, gs_optMakespan_comp (grahamJobs m) e,
      grahamJobs_optMakespan]
  rw [h2, h3, h1]
  ring

end GrahamLPT
