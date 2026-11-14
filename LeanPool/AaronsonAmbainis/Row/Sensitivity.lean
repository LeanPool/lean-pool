/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.Row.Extension

/-!
# The sensitivity lemma

Lemma 6.3 (Sensitivity) of the paper, `Row.sum_abs_sub_unit_le`: if `G` on a cube is bounded by
`1` and has degree at most `D`, then `∑_b |G(0) - G(e_b)| ≤ 4 D²`. Here `0 = Row.zero β` and
`e_b = Row.unit b` are the points `(1,…,1)` and `(1,…,1)^b` of the paper. Markov's inequality at
an endpoint enters as the hypothesis `MarkovEndpoint`, which is proved in `Row/Markov.lean`.
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Row

open Finset Polynomial

/-- If every partial sum of `d` is bounded by `K` in absolute value, then `∑ |d| ≤ 2 K`. -/
lemma sum_abs_le_of_abs_sum_le {β : Type*} [Fintype β] (d : β → ℝ) (K : ℝ)
    (h : ∀ R : Finset β, |∑ b ∈ R, d b| ≤ K) : ∑ b, |d b| ≤ 2 * K := by
  have hA : ∑ b ∈ univ.filter (fun b => 0 ≤ d b), |d b|
      = ∑ b ∈ univ.filter (fun b => 0 ≤ d b), d b :=
    Finset.sum_congr rfl (fun b hb => abs_of_nonneg (Finset.mem_filter.mp hb).2)
  have hB : ∑ b ∈ univ.filter (fun b => ¬ 0 ≤ d b), |d b|
      = -∑ b ∈ univ.filter (fun b => ¬ 0 ≤ d b), d b := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun b hb => abs_of_neg (not_le.mp (Finset.mem_filter.mp hb).2))
  have hsplit := Finset.sum_filter_add_sum_filter_not univ (fun b => 0 ≤ d b) (fun b => |d b|)
  have h1 := (abs_le.mp (h (univ.filter (fun b => 0 ≤ d b)))).2
  have h2 := (abs_le.mp (h (univ.filter (fun b => ¬ 0 ≤ d b)))).1
  linarith

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The restriction polynomial `φ_R(s) = ∑_U g_U (1 - s)^{|U ∩ R|}`. -/
noncomputable def phi (g : Finset β → ℝ) (R : Finset β) : ℝ[X] :=
  ∑ U : Finset β, C (g U) * (1 - X) ^ (U ∩ R).card

lemma natDegree_phi_le (g : Finset β → ℝ) (R : Finset β) (D : ℕ)
    (hg : ∀ U : Finset β, D < U.card → g U = 0) : (phi g R).natDegree ≤ D := by
  refine natDegree_sum_le_of_forall_le _ _ (fun U _ => ?_)
  by_cases hU : U.card ≤ D
  · have h1X : (1 - X : ℝ[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
    calc (C (g U) * (1 - X) ^ (U ∩ R).card).natDegree
        ≤ ((1 - X : ℝ[X]) ^ (U ∩ R).card).natDegree := natDegree_C_mul_le _ _
      _ ≤ (U ∩ R).card * (1 - X : ℝ[X]).natDegree := natDegree_pow_le
      _ ≤ (U ∩ R).card * 1 := Nat.mul_le_mul_left _ h1X
      _ ≤ D := by
          rw [mul_one]
          exact (Finset.card_le_card Finset.inter_subset_left).trans hU
  · rw [hg U (not_le.mp hU)]
    simp

lemma eval_phi (g : Finset β → ℝ) (R : Finset β) (s : ℝ) :
    (phi g R).eval s = ∑ U : Finset β, g U * ∏ b ∈ U, (if b ∈ R then 1 - s else 1) := by
  unfold phi
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  rw [eval_mul, eval_C, eval_pow, eval_sub, eval_one, eval_X, Finset.prod_ite_mem,
    Finset.prod_const]

lemma derivative_phi_eval_zero (g : Finset β → ℝ) (R : Finset β) :
    (phi g R).derivative.eval 0 = -∑ U : Finset β, g U * ((U ∩ R).card : ℝ) := by
  unfold phi
  rw [derivative_sum, eval_finsetSum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  rw [derivative_C_mul, derivative_pow, derivative_sub, derivative_one, derivative_X]
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_one, eval_X, eval_zero, sub_zero,
    one_pow]
  ring

/-- `∑_{b ∈ R} (G(0) - G(e_b)) = 2 ∑_U g_U |U ∩ R|` for `G = ∑_U g_U chi_U`. -/
lemma sum_sub_unit (g : Finset β → ℝ) (R : Finset β) :
    ∑ b ∈ R, ((∑ U : Finset β, g U * chi U (zero β)) - ∑ U : Finset β, g U * chi U (unit b))
      = 2 * ∑ U : Finset β, g U * ((U ∩ R).card : ℝ) := by
  have h1 : ∀ b : β,
      (∑ U : Finset β, g U * chi U (zero β)) - ∑ U : Finset β, g U * chi U (unit b)
        = ∑ U : Finset β, g U * (if b ∈ U then 2 else 0) := by
    intro b
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun U _ => ?_)
    rw [chi_zero, chi_unit]
    split_ifs <;> ring
  have h2 : ∀ U : Finset β, ∑ b ∈ R, (if b ∈ U then (2 : ℝ) else 0) = 2 * ((U ∩ R).card : ℝ) := by
    intro U
    rw [Finset.sum_ite_mem, Finset.sum_const, Finset.inter_comm, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun b _ => h1 b), Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  rw [← Finset.mul_sum, h2 U]
  ring

/-- For every set `R` of coordinates, `|∑_{b ∈ R} (G(0) - G(e_b))| ≤ 2 D²`. -/
lemma abs_sum_sub_unit_le (hM : MarkovEndpoint) (G : Cube β → ℝ) (D : ℕ)
    (hG : ∀ w, |G w| ≤ 1) (hdeg : HasDegreeLE G D) (R : Finset β) :
    |∑ b ∈ R, (G (zero β) - G (unit b))| ≤ 2 * (D : ℝ) ^ 2 := by
  obtain ⟨g, hg, hGg⟩ := hdeg
  have hbound : ∀ s : ℝ, 0 ≤ s → s ≤ 2 → |(phi g R).eval s| ≤ 1 := by
    intro s hs0 hs2
    rw [eval_phi]
    refine abs_multilinear_le_one g (fun z => ?_) (fun b => if b ∈ R then 1 - s else 1)
      (fun b => ?_)
    · rw [← hGg z]
      exact hG z
    · split_ifs
      · rw [abs_le]
        constructor <;> linarith
      · simp
  have hmark := hM D (phi g R) (natDegree_phi_le g R D hg) hbound
  rw [derivative_phi_eval_zero, abs_neg] at hmark
  have hsum : ∑ b ∈ R, (G (zero β) - G (unit b))
      = 2 * ∑ U : Finset β, g U * ((U ∩ R).card : ℝ) := by
    rw [← sum_sub_unit g R]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hGg (zero β), hGg (unit b)]
  rw [hsum, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- The sensitivity lemma (Lemma 6.3 of the paper), given Markov's inequality at an endpoint. -/
theorem sum_abs_sub_unit_le (hM : MarkovEndpoint) (G : Cube β → ℝ) (D : ℕ)
    (hG : ∀ w, |G w| ≤ 1) (hdeg : HasDegreeLE G D) :
    ∑ b, |G (zero β) - G (unit b)| ≤ 4 * (D : ℝ) ^ 2 := by
  have h := sum_abs_le_of_abs_sum_le (fun b => G (zero β) - G (unit b)) (2 * (D : ℝ) ^ 2)
    (fun R => abs_sum_sub_unit_le hM G D hG hdeg R)
  linarith

end Row
end AaronsonAmbainis
