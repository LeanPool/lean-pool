/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.OUJointRegularity
public import LeanPool.EhrhardGaussian.Ehrhard.OUTimeDependent
public import LeanPool.EhrhardGaussian.Ehrhard.GaussianLinearAverageBounds

/-! # Bounds for space and time derivatives of bounded smooth OU inputs -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open EhrhardGaussian.Gaussian (coordinateDerivative standardGaussianMeasure)

namespace EhrhardGaussian.Ehrhard

/-- Ornstein–Uhlenbeck averaging preserves a uniform absolute bound. -/
theorem abs_ouAverage_le {n : ℕ} {F : (Fin n → ℝ) → ℝ} {B : ℝ}
    (hF : ∀ y, |F y| ≤ B) (x : Fin n → ℝ) (t : ℝ) : |ouAverage F x t| ≤ B :=
  abs_gaussianLinearAverage_le
    (fun z y => Real.exp (-t) • y + Real.sqrt (1 - Real.exp (-2 * t)) • z) hF x

/-- Ornstein–Uhlenbeck averaging preserves a uniform gradient norm bound. -/
theorem norm_fderiv_ouAverage_le {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F) {G : ℝ}
    (hgrad : ∀ y, ‖fderiv ℝ F y‖ ≤ G) (x : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (fun y => ouAverage F y t) x‖ ≤ G := by
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have hInt : ‖∫ z, fderiv ℝ F
      (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-2 * t)) • z)
      ∂standardGaussianMeasure n‖ ≤ G := by
    have h := norm_integral_le_of_norm_le_const
      (f := fun z => fderiv ℝ F (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-2 * t)) • z))
      (ae_of_all (standardGaussianMeasure n) fun z => hgrad _)
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using h
  rw [(hasFDerivAt_ouAverage_center hF x t).fderiv, norm_smul,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul he hInt (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- Gradient and second derivative bounds control the time derivative of an Ornstein–Uhlenbeck
average. -/
theorem abs_deriv_ouAverage_le {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F) {G H : ℝ}
    (hgrad : ∀ y, ‖fderiv ℝ F y‖ ≤ G)
    (hsecond : ∀ i y, |coordinateDerivative (coordinateDerivative F i) i y| ≤ H)
    (x : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    |deriv (ouAverage F x) t| ≤ (n : ℝ) * H + G * ‖x‖ := by
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [ht])
  have he2 : Real.exp (-t) ^ 2 ≤ 1 := pow_le_one₀ (Real.exp_pos _).le he
  have hLap (y : Fin n → ℝ) : |∑ i, coordinateDerivative (coordinateDerivative F i) i y| ≤ n * H :=
    by
    calc
      |∑ i, coordinateDerivative (coordinateDerivative F i) i y| ≤
          ∑ i, |coordinateDerivative (coordinateDerivative F i) i y| := Finset.abs_sum_le_sum_abs _
            _
      _ ≤ ∑ _i : Fin n, H := Finset.sum_le_sum fun i _ => hsecond i y
      _ = n * H := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hx (y : Fin n → ℝ) : |fderiv ℝ F y x| ≤ G * ‖x‖ :=
    ((fderiv ℝ F y).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hgrad y) (norm_nonneg _))
  have ha := abs_ouAverage_le hLap x t
  have hb := abs_ouAverage_le hx x t
  rw [(hasDerivAt_ouAverage_laplacian hF x ht).deriv]
  calc
    _ ≤ |Real.exp (-t) ^ 2 * ouAverage
        (fun y => ∑ i, coordinateDerivative (coordinateDerivative F i) i y) x t| +
        |Real.exp (-t) * ouAverage (fun y => fderiv ℝ F y x) x t| := by
      rw [sub_eq_add_neg]
      apply (abs_add_le _ _).trans_eq
      rw [abs_neg]
    _ = Real.exp (-t) ^ 2 * |ouAverage
        (fun y => ∑ i, coordinateDerivative (coordinateDerivative F i) i y) x t| +
        Real.exp (-t) * |ouAverage (fun y => fderiv ℝ F y x) x t| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ 1 * (n * H) + 1 * (G * ‖x‖) :=
      add_le_add (mul_le_mul he2 ha (abs_nonneg _) zero_le_one)
        (mul_le_mul he hb (abs_nonneg _) zero_le_one)
    _ = _ := by ring

/-- The full derivative norm is bounded by the sum of time and space derivative bounds. -/
theorem norm_fderiv_spaceTime_le {n : ℕ} {F : ℝ × (Fin n → ℝ) → ℝ}
    {t : ℝ} {x : Fin n → ℝ} (hF : DifferentiableAt ℝ F (t, x))
    {T G : ℝ} (hT : 0 ≤ T) (hG : 0 ≤ G)
    (hdt : |deriv (fun s => F (s, x)) t| ≤ T)
    (hdx : ‖fderiv ℝ (fun y => F (t, y)) x‖ ≤ G) :
    ‖fderiv ℝ F (t, x)‖ ≤ T + G := by
  have hspace := hF.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  dsimp only [Function.comp_def] at hspace
  have hspace_apply (v : Fin n → ℝ) := congrArg
    (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L v) hspace.fderiv
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at hspace_apply
  have hdt' : |fderiv ℝ F (t, x) (1, 0)| ≤ T := by
    rw [← deriv_spaceTime_left hF]
    exact hdt
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg hT hG)
  intro v
  have hv : v = v.1 • (((1 : ℝ), (0 : Fin n → ℝ))) + (0, v.2) := by ext <;> simp
  have hsplit : fderiv ℝ F (t, x) v = v.1 * fderiv ℝ F (t, x) (1, 0) +
      fderiv ℝ (fun y => F (t, y)) x v.2 := by
    calc
      _ = fderiv ℝ F (t, x) (v.1 • (((1 : ℝ), (0 : Fin n → ℝ))) + (0, v.2)) :=
        congrArg (fderiv ℝ F (t, x)) hv
      _ = _ := by rw [map_add, map_smul, smul_eq_mul, ← hspace_apply]
  rw [hsplit, Real.norm_eq_abs]
  calc
    _ ≤ |v.1| * |fderiv ℝ F (t, x) (1, 0)| +
        |fderiv ℝ (fun y => F (t, y)) x v.2| := by
      simpa only [abs_mul] using abs_add_le (v.1 * fderiv ℝ F (t, x) (1, 0))
        (fderiv ℝ (fun y => F (t, y)) x v.2)
    _ ≤ ‖v‖ * T + G * ‖v‖ := by
      apply add_le_add
      · exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_fst_le v)
          hdt' (abs_nonneg _) (norm_nonneg _)
      · exact ((fderiv ℝ (fun y => F (t, y)) x).le_opNorm v.2).trans
          (mul_le_mul hdx (norm_snd_le v) (norm_nonneg _) hG)
    _ = (T + G) * ‖v‖ := by ring

/-- A bounded smooth input with bounded first and second derivatives gives
a uniform linear space-time bound for its OU average at positive times. -/
theorem ouAverage_spaceTime_linear_bound {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F) {B G H : ℝ}
    (hB : 0 ≤ B) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hvalue : ∀ y, |F y| ≤ B) (hgrad : ∀ y, ‖fderiv ℝ F y‖ ≤ G)
    (hsecond : ∀ i y, |coordinateDerivative (coordinateDerivative F i) i y| ≤ H)
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    |ouAverage F x t| + ‖fderiv ℝ (fun p : ℝ × (Fin n → ℝ) => ouAverage F p.2 p.1) (t, x)‖ ≤
      (B + (n : ℝ) * H + G) * (1 + ‖x‖) := by
  have hF₁ := hasPolynomiallyBoundedCoordinateDerivatives_of_second hF
  have hpoint : (t, x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (Fin n → ℝ)) := ⟨ht, mem_univ _⟩
  have hdiff := ((contDiffOn_ouAverage_spaceTime hF₁).contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds hpoint)).differentiableAt_one
  have hd := norm_fderiv_spaceTime_le hdiff
    (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hH) (mul_nonneg hG (norm_nonneg _))) hG
    (abs_deriv_ouAverage_le hF hgrad hsecond x ht)
    (norm_fderiv_ouAverage_le hF₁ hgrad x ht.le)
  calc
    _ ≤ B + ((n : ℝ) * H + G * ‖x‖ + G) := add_le_add (abs_ouAverage_le hvalue x t) hd
    _ ≤ (B + (n : ℝ) * H + G) * (1 + ‖x‖) := by
      have hextra := mul_nonneg (add_nonneg hB (mul_nonneg (Nat.cast_nonneg n) hH))
        (norm_nonneg x)
      nlinarith only [hextra]

end EhrhardGaussian.Ehrhard

end
