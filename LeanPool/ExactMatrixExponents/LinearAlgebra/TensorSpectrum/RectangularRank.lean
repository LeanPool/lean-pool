/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorCharacterPowers
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Bounds

/-!
# Rank and character bounds for products of three dot tensors

The singleton legs implement the cyclic identification of the matrix
coordinates. The rounded side lengths give the corresponding price bound.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation
open MatrixMultiplicationAllFields.MatrixExponent.Rectangle

namespace MatrixMultiplicationAllFields.TensorSpectrum.TensorClass

variable {K : Type*} [CommSemiring K]

/-- The quantity computed by `dotX j * dotY i * dotZ k`. -/
def dots (i j k : ℕ) : TensorClass K := dotX j * dotY i * dotZ k

theorem dots_power (i j k t : ℕ) : dots (K := K) (i ^ t) (j ^ t) (k ^ t) = (dots i j k) ^ t := by
  induction t with
  | zero => simp [dots]
  | succ t ih =>
    rw [pow_succ, pow_succ, pow_succ, pow_succ, ← ih]
    simp only [dots, ← dotX_mul, ← dotY_mul, ← dotZ_mul]
    exact (congrArg (· * _) (mul_mul_mul_comm _ _ _ _)).trans (mul_mul_mul_comm _ _ _ _)

theorem rank_of_dots {i j k r : ℕ} (h : dots i j k ≤ (r : TensorClass K)) :
    Tensor.RankAtMost
      (fun (x : Fin i × Fin k) (y : Fin k × Fin j) (z : Fin i × Fin j) =>
        if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then (1 : K) else 0) r := by
  have hr := (TensorClass.rank_mono h).trans (show TensorClass.rank (r : TensorClass K) ≤ r by
    rw [natCast_eq_ofTensor_natTensor, rank_ofTensor]
    exact (CoefficientTensor.rank_le_iff _ _).mpr (CoefficientTensor.rankAtMost_natTensor r))
  rw [dots, dotX, dotY, dotZ, ofTensor_mul, ofTensor_mul, rank_ofTensor] at hr
  obtain ⟨a, b, c, he⟩ := (CoefficientTensor.rank_le_iff _ _).mp hr
  refine ⟨fun l x => a l (((), x.1), x.2), fun l y => b l ((y.2, ()), y.1),
    fun l z => c l ((z.2, z.1), ()), ?_⟩
  funext x y z
  symm
  have hh := congrFun (congrFun (congrFun he (((), x.1), x.2)) ((y.2, ()), y.1)) ((z.2, z.1), ())
  refine hh.symm.trans ?_
  simp [Tensor.product, CoefficientTensor.dotXCoeff,
    CoefficientTensor.dotYCoeff, CoefficientTensor.dotZCoeff, ite_and]
  grind

theorem price_dots (f : Character K) {n : ℕ} (hn : 0 < n) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (f (dots (side n a) (side n b) (side n c)) : ℝ) ≤
      8 * (n : ℝ) ^ (b * f.pX + a * f.pY + c * f.pZ) := by
  simp only [dots, Character.map_mul, NNReal.coe_mul]
  change f.dotXValue _ * f.dotYValue _ * f.dotZValue _ ≤ _
  rw [f.dotXValue_eq_rpow _ (side_pos hn b), f.dotYValue_eq_rpow _ (side_pos hn a),
    f.dotZValue_eq_rpow _ (side_pos hn c)]
  have hn₀ : 0 < (n : ℝ) := by positivity
  calc
    _ ≤ (2 * (n : ℝ) ^ (b * f.pX)) * (2 * (n : ℝ) ^ (a * f.pY)) *
        (2 * (n : ℝ) ^ (c * f.pZ)) := by
      gcongr
      · exact rounded_dot hn hb f.pX_nonneg f.pX_le_one
      · exact rounded_dot hn ha f.pY_nonneg f.pY_le_one
      · exact rounded_dot hn hc f.pZ_nonneg f.pZ_le_one
    _ = _ := by rw [Real.rpow_add hn₀, Real.rpow_add hn₀]; ring

end MatrixMultiplicationAllFields.TensorSpectrum.TensorClass
