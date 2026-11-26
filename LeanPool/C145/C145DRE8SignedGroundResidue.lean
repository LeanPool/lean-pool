/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145DRE8ActualFrame

/-! Source §4.2 signed-ground calibration directly from ordinary H2. We evaluate
the already verified cleared numerator identity at the ground input pole and
a fixed positive second variable. No equality of totalized H2 values at poles
is used. Additive resonances remain permitted. -/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators
open C145.H2 C145.ThreePlane
variable {n : ℕ}

theorem signed_ground_from_actual_H2
    (μ : ℝ) (hμ : 0 < μ) (rates : Fin (n + 1) → ℝ)
    (hRates : Function.Injective rates) (hPos : ∀ i, 0 < rates i)
    (hGroundRate : rates 0 = μ)
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ) (a : Fin (n + 1) → ℝ)
    (c0 c1 : ℝ) (hU : C145PhysicalFrame.ColumnOrthonormal U)
    (hV : C145PhysicalFrame.ColumnOrthonormal V)
    (hGU : ∀ v, U v 0 = c0) (hGV : ∀ v, V v 0 = c1)
    (ha : ∀ i, 0 < a i)
    (hH : SamePositive rates (C145PhysicalFrame.T U a) (C145PhysicalFrame.T V a)) :
    c0 = c1 := by
  classical
  have hPlane := (samePositive_iff_plane rates hPos _ _).mp hH
  have hEval := congrArg (MvPolynomial.eval ![-μ,μ]) hPlane
  rw [eval_rhoZ] at hEval
  simp only [neg_add_cancel, map_zero] at hEval
  have hNode (i : Fin (n + 1)) : (Li rates i).eval (-μ) = if i = 0 then di rates 0 else 0 := by
    rw [← hGroundRate]
    exact eval_Li_grid rates i 0
  have hSummand (j k : Fin (n + 1)) :
      (C145PhysicalFrame.T U a 0 j k-C145PhysicalFrame.T V a 0 j k) * di rates 0*
        (Li rates j).eval μ * (Li rates k).eval 0 =
      if j = k then
        (c0 - c1) * a 0 * di rates 0 * (a j ^ 2 * (Li rates j).eval μ * (Li rates j).eval 0)
      else 0 :=
        by
    rw [C145PhysicalFrame.ground_slice U a c0 hU hGU,
      C145PhysicalFrame.ground_slice V a c1 hV hGV]
    by_cases hjk : j = k
    · subst k; simp only [ite_true, mul_one]; ring
    · simp only [hjk, ite_false, mul_zero, sub_self, zero_mul]
  have hExpansion :
      MvPolynomial.eval ![0,-μ,μ]
          (numerator rates (C145PhysicalFrame.T U a-C145PhysicalFrame.T V a)) =
        (c0-c1) * a 0 * di rates 0*
          (∑ j, a j ^ 2 * (Li rates j).eval μ * (Li rates j).eval 0) := by
    simp only [numerator, map_sum, map_mul, MvPolynomial.eval_C, eval_L]
    change (∑ i, ∑ j, ∑ k,
      (C145PhysicalFrame.T U a i j k-C145PhysicalFrame.T V a i j k)*
      (Li rates i).eval (-μ) * (Li rates j).eval μ * (Li rates k).eval 0) = _
    simp_rw [hNode]
    rw [Fin.sum_univ_succ]
    simp only [ite_true, Fin.succ_ne_zero, ite_false, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero]
    simp_rw [hSummand]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Finset.mul_sum]
  rw [hExpansion] at hEval
  have hLiPos (j : Fin (n + 1)) (s : ℝ) (hs : 0 ≤ s) : 0 < (Li rates j).eval s := by
    simp only [Li, Polynomial.eval_prod, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
    apply Finset.prod_pos
    intro i hi
    exact add_pos_of_nonneg_of_pos hs (hPos i)
  have hSum : 0 < (∑ j, a j ^ 2 * (Li rates j).eval μ * (Li rates j).eval 0) := by
    apply Finset.sum_pos
    · intro j hj
      exact mul_pos (mul_pos (sq_pos_of_ne_zero (ne_of_gt (ha j)))
        (hLiPos j μ hμ.le)) (hLiPos j 0 le_rfl)
    · exact ⟨0,Finset.mem_univ 0⟩
  have hFactor : a 0 * di rates 0*
      (∑ j, a j ^ 2 * (Li rates j).eval μ * (Li rates j).eval 0) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ne_of_gt (ha 0)) (di_ne_zero rates hRates 0)) (ne_of_gt hSum)
  have hProduct : (c0-c1) * (a 0 * di rates 0*
      (∑ j, a j ^ 2 * (Li rates j).eval μ * (Li rates j).eval 0)) = 0 := by
    convert hEval using 1
    ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp hProduct).resolve_right hFactor)

end C145DRE8

end
