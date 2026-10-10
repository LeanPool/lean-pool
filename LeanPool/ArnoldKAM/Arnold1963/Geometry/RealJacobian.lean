/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Basic.Measure
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
Real-slice Jacobian estimates. The maximum-norm unit cube gives the sharp C ^ n determinant
bound without an additional dimension factor.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace KamProject.Arnold1963

/-- Coordinatewise complexification as a real continuous linear map. -/
def complexifyCLM (n : ℕ) : RealSpace n →L[ℝ] ComplexSpace n :=
  ContinuousLinearMap.pi fun j => Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)

/-- Coordinatewise real-part projection as a real continuous linear map. -/
def realPartCLM (n : ℕ) : ComplexSpace n →L[ℝ] RealSpace n :=
  ContinuousLinearMap.pi fun j => Complex.reCLM.comp (ContinuousLinearMap.proj j)

@[simp] theorem complexifyCLM_apply {n} (x : RealSpace n) : complexifyCLM n x = complexify x := rfl
@[simp] theorem realPartCLM_apply {n} (z : ComplexSpace n) : realPartCLM n z = realPart z := rfl

theorem norm_realPart_le {n} (z : ComplexSpace n) : ‖realPart z‖ ≤ ‖z‖ := by
  apply (real_norm_le_iff _ (norm_nonneg _)).mpr
  intro j
  exact (Complex.abs_re_le_norm (z j)).trans (norm_le_pi_norm z j)

/-- Restriction of a complex action map to real input and output coordinates. -/
def realRestriction {n} (f : ComplexSpace n → ComplexSpace n) : RealSpace n → RealSpace n :=
  realPart ∘ f ∘ complexify

/-- The real continuous linear map induced by restricting a complex derivative. -/
def realDerivative {n} (L : ComplexSpace n →L[ℂ] ComplexSpace n) :
    RealSpace n →L[ℝ] RealSpace n :=
  (realPartCLM n).comp ((L.restrictScalars ℝ).comp (complexifyCLM n))

theorem hasFDerivAt_realRestriction {n} {f : ComplexSpace n → ComplexSpace n}
    {x : RealSpace n} (hf : DifferentiableAt ℂ f (complexify x)) :
    HasFDerivAt (realRestriction f) (realDerivative (fderiv ℂ f (complexify x))) x := by
  exact (realPartCLM n).hasFDerivAt.comp x
    ((hf.hasFDerivAt.restrictScalars ℝ).comp x (complexifyCLM n).hasFDerivAt)

theorem norm_realDerivative_le {n} (L : ComplexSpace n →L[ℂ] ComplexSpace n) :
    ‖realDerivative L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro x
  exact (norm_realPart_le _).trans (by simpa using L.le_opNorm (complexify x))

theorem abs_det_le_pow_of_opNorm_le {n : ℕ} (L : RealSpace n →L[ℝ] RealSpace n)
    {C : ℝ} (hC : 0 ≤ C) (hL : ‖L‖ ≤ C) : |(L : RealSpace n →ₗ[ℝ] RealSpace n).det| ≤ C ^ n := by
  have him : L '' closedBall (0 : RealSpace n) 1 ⊆ closedBall 0 C := by
    rintro y ⟨x, hx, rfl⟩
    simp only [mem_closedBall, dist_zero_right] at hx ⊢
    exact (L.le_opNorm x).trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg x)).trans
      (by simpa using mul_le_mul_of_nonneg_left hx hC))
  have hm := measure_mono (μ := (volume : Measure (RealSpace n))) him
  rw [Measure.addHaar_image_continuousLinearMap,
    Real.volume_pi_closedBall _ (by norm_num : (0 : ℝ) ≤ 1),
    Real.volume_pi_closedBall _ hC] at hm
  simp only [Fintype.card_fin, mul_one] at hm
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 ^ n),
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (2 * C) ^ n), mul_pow] at ht
  exact (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < 2 ^ n)).mp (by
    simpa only [mul_comm] using ht)

theorem real_image_measure_le {n} {f : RealSpace n → RealSpace n}
    {s : Set (RealSpace n)} {C : ℝ} (hs : MeasurableSet s) (hC : 0 ≤ C)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) (hd : ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ C) :
    volume (f '' s) ≤ ENNReal.ofReal (C ^ n) * volume s := by
  calc
    _ ≤ ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).toLinearMap.det| ∂volume :=
      addHaar_image_le_lintegral_abs_det_fderiv volume hs
        (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt)
    _ ≤ ∫⁻ _ in s, ENNReal.ofReal (C ^ n) ∂volume := by
      apply setLIntegral_mono' hs
      intro x hx
      exact ENNReal.ofReal_le_ofReal (abs_det_le_pow_of_opNorm_le _ hC (hd x hx))
    _ = _ := by simp

end KamProject.Arnold1963
