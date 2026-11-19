/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/
module

public import LeanPool.CographDistance.Definitions
public import LeanPool.CographDistance.Family

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.IntermediateValue

/-!
# A distance eigenvalue of `G_m` in `(-2 - 1/(2m), -2)`

The partition {centre}, {ends of the copies of `K₂`}, {isolated vertex} of `G_m` is equitable for
the distance matrix, with quotient matrix `[[0, 2m, 1], [1, 4m-3, 2], [1, 4m, 0]]` and
characteristic polynomial `p_m(x) = x³ + 3x² - x - 3 - m(4x² + 10x + 4)`. A root `λ` of `p_m`
lifts to the eigenvector equal to `α` on the centre, `1` on the ends of the copies of `K₂` and
`γ` on the isolated vertex, where `α = 2m(λ+2)/(λ²-1)` and `γ = λα - 2m`.
-/

@[expose] public section

namespace CographDist

open Finset

/-- The cubic `p_m`. -/
def cubic (m : ℝ) (x : ℝ) : ℝ := x ^ 3 + 3 * x ^ 2 - x - 3 - m * (4 * x ^ 2 + 10 * x + 4)

theorem cubic_neg_two (m : ℝ) : cubic m (-2) = 3 := by
  unfold cubic; ring

theorem cubic_left (m : ℝ) (hm : 0 < m) :
    cubic m (-2 - 1 / (2 * m)) = -(4 * m ^ 2 + 6 * m + 1) / (8 * m ^ 3) := by
  unfold cubic
  field_simp
  ring

/-- `p_m` has a root in the open interval `(-2 - 1/(2m), -2)`. -/
theorem cubic_root (m : ℝ) (hm : 0 < m) :
    ∃ x : ℝ, -2 - 1 / (2 * m) < x ∧ x < -2 ∧ cubic m x = 0 := by
  have hab : -2 - 1 / (2 * m) ≤ -2 := by
    have : 0 < 1 / (2 * m) := by positivity
    linarith
  have hcont : ContinuousOn (cubic m) (Set.Icc (-2 - 1 / (2 * m)) (-2)) := by
    unfold cubic; fun_prop
  have hl : cubic m (-2 - 1 / (2 * m)) < 0 := by
    rw [cubic_left m hm]
    have : 0 < (4 * m ^ 2 + 6 * m + 1) / (8 * m ^ 3) := by positivity
    rw [neg_div]; linarith
  have h0 : (0 : ℝ) ∈ Set.Ioo (cubic m (-2 - 1 / (2 * m))) (cubic m (-2)) := by
    rw [cubic_neg_two]
    exact ⟨hl, by norm_num⟩
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := intermediate_value_Ioo hab hcont h0
  exact ⟨x, hx1, hx2, hx⟩

/-- The coefficient of the dominating vertex in the lifted eigenvector. -/
noncomputable def centerCoefficient (m : ℕ) (l : ℝ) : ℝ :=
  2 * m * (l + 2) / (l ^ 2 - 1)

/-- The eigenvector of `D(G_m)` attached to a root `l` of `p_m`. -/
noncomputable def eigvec (m : ℕ) (l : ℝ) : W m → ℝ
  | none => centerCoefficient m l
  | some none => l * centerCoefficient m l - 2 * m
  | some (some _) => 1

private theorem sum_const_matching_dist {m : ℕ} (v : W m) (d : ℕ)
    (hd : ∀ q : Fin m × Bool, (fam m).dist v (some (some q)) = d) :
    ∑ q : Fin m × Bool, ((fam m).dist v (some (some q)) : ℝ) = 2 * m * d := by
  simp only [hd, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- Row sums of the distances from an end of a copy of `K₂` to the ends of all copies. -/
theorem pair_row_sum {m : ℕ} (p : Fin m × Bool) :
    ∑ q : Fin m × Bool, ((fam m).dist (some (some p)) (some (some q)) : ℝ) = 4 * m - 3 := by
  classical
  have hmate : p ≠ (p.1, !p.2) := by
    intro h
    have hb : p.2 = !p.2 := congrArg Prod.snd h
    cases hbit : p.2 <;> rw [hbit] at hb <;> contradiction
  have hd (q : Fin m × Bool) :
      ((fam m).dist (some (some p)) (some (some q)) : ℝ) =
        2 - (if q = p then 2 else 0) - (if q = (p.1, !p.2) then 1 else 0) := by
    rw [fam_dist, fam_adj_pair_iff_eq_mate]
    by_cases hp : q = p
    · subst q
      norm_num [hmate]
    · by_cases hq : q = (p.1, !p.2) <;> norm_num [hp, Ne.symm hp, hq, hmate, Ne.symm hmate]
  simp only [hd, Finset.sum_sub_distrib]
  simp [Fintype.card_prod]
  ring

theorem eigvec_spec (m : ℕ) (hm : 1 ≤ m) (l : ℝ) (hl : l < -2) (hroot : cubic m l = 0) :
    eigvec m l ≠ 0 ∧ (distMatrix (fam m)).mulVec (eigvec m l) = l • eigvec m l := by
  classical
  have hden : l ^ 2 - 1 ≠ 0 := by nlinarith
  let α := centerCoefficient m l
  have hαeq : α * (l ^ 2 - 1) = 2 * m * (l + 2) := by
    dsimp [α, centerCoefficient]
    field_simp
  refine ⟨?_, ?_⟩
  · intro h
    have := congrFun h (some (some (⟨0, hm⟩, true)))
    simp [eigvec] at this
  · funext v
    simp only [Matrix.mulVec, dotProduct, distMatrix, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_option, Fintype.sum_option]
    rcases v with _ | _ | p
    · -- the centre
      have hd (q : Fin m × Bool) : (fam m).dist none (some (some q)) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr (fam_adj_none_some m _)
      simp only [eigvec, mul_one]
      rw [sum_const_matching_dist none 1 hd]
      simp only [SimpleGraph.dist_self, Nat.cast_zero, zero_mul, fam_dist,
        reduceCtorEq, ↓reduceIte, fam_adj_none_some, Nat.cast_one, one_mul, mul_one, zero_add]
      ring
    · -- the isolated vertex
      have hd (q : Fin m × Bool) : (fam m).dist (some none) (some (some q)) = 2 := by
        simp [fam_dist]
      simp only [eigvec, mul_one]
      rw [sum_const_matching_dist (some none) 2 hd]
      simp only [fam_dist, reduceCtorEq, ↓reduceIte, fam_adj_some_none, Nat.cast_one, one_mul,
        SimpleGraph.dist_self, Nat.cast_zero, zero_mul, Nat.cast_ofNat, zero_add]
      change α + 2 * m * 2 = l * (l * α - 2 * m)
      nlinarith [hαeq]
    · -- an end of a copy of `K₂`
      have hs := pair_row_sum p
      simp only [eigvec, mul_one]
      rw [hs]
      simp only [fam_dist, reduceCtorEq, ↓reduceIte, fam_adj_some_none, Nat.cast_one,
        one_mul, Option.some.injEq, fam_not_adj_to_z, Nat.cast_ofNat]
      have hc : cubic m l = 0 := hroot
      unfold cubic at hc
      have key : α * (1 + 2 * l) = l + 3 := by
        have h1 : α * (1 + 2 * l) * (l ^ 2 - 1) = (l + 3) * (l ^ 2 - 1) := by
          rw [mul_right_comm, hαeq]; nlinarith [hc]
        exact mul_right_cancel₀ hden h1
      change α + (2 * (l * α - 2 * m) + (4 * m - 3)) = l
      linarith

/-- For every `m ≥ 1`, `G_m` has a distance eigenvalue in `(-2 - 1/(2m), -2)`. -/
theorem fam_eigenvalue (m : ℕ) (hm : 1 ≤ m) :
    ∃ l : ℝ, -2 - 1 / (2 * (m : ℝ)) < l ∧ l < -2 ∧ IsDistEigenvalue (fam m) l := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨l, h1, h2, h3⟩ := cubic_root m hm'
  obtain ⟨hne, heigen⟩ := eigvec_spec m hm l h2 h3
  exact ⟨l, h1, h2, eigvec m l, hne, heigen⟩

end CographDist
