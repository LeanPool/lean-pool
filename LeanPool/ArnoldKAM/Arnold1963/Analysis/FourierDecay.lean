/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Analysis.MultiContourShift
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.FourierCoefficients
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Exponential decay of actual Fourier coefficients, using contour shifts in each coordinate.
-/

@[expose] public section
noncomputable section
open Complex MeasureTheory
open scoped NNReal
namespace KamProject.Arnold1963

/-- Complex linear scaling from unit-period coordinates to angles with period `2π`. -/
def angleScale (n : ℕ) : ComplexSpace n →L[ℂ] ComplexSpace n :=
  (2 * (Real.pi : ℂ)) • ContinuousLinearMap.id ℂ _

@[simp] theorem angleScale_apply {n : ℕ} (q : ComplexSpace n) (j : Fin n) :
    angleScale n q j = 2 * (Real.pi : ℂ) * q j := rfl

theorem scaledAngle_eq_angleScale {n : ℕ} (t : RealSpace n) :
    scaledAngle t = angleScale n (complexify t) := by
  ext j
  simp [scaledAngle, complexify]

/-- The strip width after converting angles to unit-period coordinates. -/
def normalizedWidth (ρ : ℝ≥0) : ℝ≥0 := ⟨ρ / (2 * Real.pi), by positivity⟩

theorem angleScale_mem_strip {n : ℕ} {ρ : ℝ≥0} {q : ComplexSpace n}
    (hq : q ∈ angleStrip n (normalizedWidth ρ)) : angleScale n q ∈ angleStrip n ρ := by
  apply (mem_angleStrip_iff _ _).mpr
  intro j
  have h := (mem_angleStrip_iff _ _).mp hq j
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  change |(q j).im| ≤ (ρ : ℝ) / (2 * Real.pi) at h
  have hb := (le_div_iff₀ hT).mp h
  simpa [abs_mul, abs_of_pos hT, abs_of_pos Real.pi_pos, mul_comm] using hb

/-- The negative-frequency exponential weight for normalized Fourier integration. -/
def unitFourierWeight {n : ℕ} (k : FourierIndex n) (q : ComplexSpace n) : ℂ :=
  exp (-I * (2 * (Real.pi : ℂ)) * indexPairing k q)

theorem analyticAt_unitFourierWeight {n : ℕ} (k : FourierIndex n) (q : ComplexSpace n) :
    AnalyticAt ℂ (unitFourierWeight k) q := by
  apply AnalyticAt.cexp'
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_sum
  intro j hj
  apply analyticAt_const.mul
  convert (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).analyticAt q
    using 1
  rfl

theorem indexPairing_update_one {n : ℕ} (k : FourierIndex n) (q : ComplexSpace n) (j : Fin n) :
    indexPairing k (Function.update q j (q j + 1)) = indexPairing k q + k j := by
  classical
  have he : (fun l => (k l : ℂ) * Function.update q j (q j + 1) l) =
      (fun l => (k l : ℂ) * q l + (Pi.single j (k j : ℂ) : ComplexSpace n) l) := by
    ext l
    by_cases h : l = j
    · subst l; simp [mul_add]
    · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
  unfold indexPairing
  rw [he, Finset.sum_add_distrib]
  simp

theorem unitFourierWeight_periodic {n : ℕ} (k : FourierIndex n) (q : ComplexSpace n)
    (j : Fin n) : unitFourierWeight k (Function.update q j (q j + 1)) =
      unitFourierWeight k q := by
  unfold unitFourierWeight
  rw [indexPairing_update_one, mul_add, exp_add]
  have he : -I * (2 * (Real.pi : ℂ)) * k j = (-k j : ℤ) * (2 * Real.pi * I) := by
    push_cast
    ring
  rw [he, exp_int_mul_two_pi_mul_I, mul_one]

theorem unitFourierWeight_real {n : ℕ} (k : FourierIndex n) (x : RealSpace n) :
    unitFourierWeight k (complexify x) = fourierMonomial (-k) (scaledAngle x) := by
  unfold unitFourierWeight fourierMonomial indexPairing
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.neg_apply, Int.cast_neg, scaledAngle, complexify,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

theorem norm_unitFourierWeight_shift {n : ℕ} (k : FourierIndex n) (y x : RealSpace n) :
    ‖unitFourierWeight k (complexShift y x)‖ =
      Real.exp ((2 * Real.pi) * ∑ j, (k j : ℝ) * y j) := by
  rw [unitFourierWeight, norm_exp]
  congr 1
  simp [indexPairing, complexShift, mul_re, mul_im]

theorem angleScale_update_one {n : ℕ} (q : ComplexSpace n) (j : Fin n) :
    angleScale n (Function.update q j (q j + 1)) =
      angleScale n q + angleShift (Pi.single j (1 : ℤ)) := by
  classical
  ext l
  by_cases h : l = j
  · subst l; simp [angleShift, complexify, mul_add]
  · simp [Function.update_of_ne h, Pi.single_eq_of_ne h, angleShift, complexify]

namespace AnalyticPhaseFunction

theorem fourierCoeff_eq_unitCubeIntegral {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) {p : ComplexSpace n} (hp : p ∈ G) (k : FourierIndex n) :
    f.fourierCoeff p k = unitCubeIntegral
      (fun x => f.toFun (p, angleScale n (complexify x)) * unitFourierWeight k (complexify x)) := by
  rw [f.fourierCoeff_eq_cubeIntegral hp]
  unfold unitCubeIntegral
  rw [unitCubeMeasure_eq_restrict_Ioc]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [mFourier_eq_fourierMonomial, ← scaledAngle_eq_angleScale, unitFourierWeight_real, mul_comm]

theorem norm_fourierCoeff_le_exp {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) {p : ComplexSpace n} (hp : p ∈ G) (k : FourierIndex n) :
    ‖f.fourierCoeff p k‖ ≤ f.uniformNorm * Real.exp (-(indexLength k * ρ)) := by
  let r := normalizedWidth ρ
  let F : ComplexSpace n → ℂ := fun q => f.toFun (p, angleScale n q) * unitFourierWeight k q
  have hF : AnalyticOnNhd ℂ F (angleStrip n r) := by
    intro q hq
    have hpair : AnalyticAt ℂ (fun z : ComplexSpace n => (p, angleScale n z)) q :=
      analyticAt_const.prod ((angleScale n).analyticAt q)
    have hfq := f.analytic (p, angleScale n q) ⟨hp, angleScale_mem_strip (ρ := ρ) hq⟩
    exact (hfq.comp (f := fun z : ComplexSpace n => (p, angleScale n z)) hpair).mul
      (analyticAt_unitFourierWeight k q)
  have hperiod : ∀ q ∈ angleStrip n r, ∀ j, F (Function.update q j (q j + 1)) = F q := by
    intro q hq j
    dsimp only [F]
    rw [angleScale_update_one, f.periodic p hp _ (angleScale_mem_strip hq),
      unitFourierWeight_periodic]
  let y : RealSpace n := fun j => if 0 ≤ k j then -(r : ℝ) else r
  have hy : ∀ j, |y j| ≤ r := by
    intro j
    dsimp [y]
    split_ifs <;> simp
  have hky (j : Fin n) : (k j : ℝ) * y j = -|(k j : ℝ)| * r := by
    dsimp [y]
    split_ifs with hk
    · rw [abs_of_nonneg (by exact_mod_cast hk)]; ring
    · rw [abs_of_neg (by exact_mod_cast (lt_of_not_ge hk))]; ring
  have he : (2 * Real.pi) * ∑ j, (k j : ℝ) * y j = -(indexLength k * ρ) := by
    simp_rw [hky]
    rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    change (2 * Real.pi) * (-(∑ j, |(k j : ℝ)|) * ((ρ : ℝ) / (2 * Real.pi))) =
      -((∑ j, |(k j : ℝ)|) * (ρ : ℝ))
    have hT : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp
  rw [f.fourierCoeff_eq_unitCubeIntegral hp]
  change ‖unitCubeIntegral (fun x => F (complexify x))‖ ≤ _
  rw [← unitCubeIntegral_shift_eq hF hperiod y hy]
  apply norm_unitCubeIntegral_le
  intro x hx
  dsimp only [F]
  rw [norm_mul, norm_unitFourierWeight_shift, he]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact (f.norm_le_iff.mp le_rfl).norm_le
    ⟨hp, angleScale_mem_strip (complexShift_mem_strip _ _ hy)⟩

end AnalyticPhaseFunction
end KamProject.Arnold1963
