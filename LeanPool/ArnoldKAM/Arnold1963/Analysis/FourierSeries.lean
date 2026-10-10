/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Analysis.FourierCoefficients
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.FourierKernel

/-!
Normally convergent Fourier series on narrower complex strips and reconstruction on real angles.
-/

@[expose] public section
noncomputable section
open scoped NNReal
namespace KamProject.Arnold1963

theorem continuous_fourierMonomial {n : ℕ} (k : FourierIndex n) :
    Continuous (fourierMonomial k) := by
  unfold fourierMonomial indexPairing
  fun_prop

/-- A bounded continuous Fourier summand on a closed complex angle strip. -/
def fourierTermOnStrip {n : ℕ} (a : FourierIndex n → ℂ) (σ : ℝ≥0)
    (k : FourierIndex n) : BoundedOnDomain (F := ℂ) (angleStrip n σ) :=
  boundedRestriction (fun q => a k * fourierMonomial k q) (angleStrip n σ)
    (continuous_const.mul (continuous_fourierMonomial k)).continuousOn
    (‖a k‖ * Real.exp (indexLength k * σ))
    ⟨by positivity, fun q hq => by
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_fourierMonomial_le k q).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hq (indexLength_nonneg k)))⟩

theorem norm_fourierTermOnStrip_le_of_decay {n : ℕ} {a : FourierIndex n → ℂ}
    {M ρ δ : ℝ} {σ : ℝ≥0} (hM : 0 ≤ M) (hσ : (σ : ℝ) ≤ ρ - δ)
    (ha : ∀ k, ‖a k‖ ≤ M * Real.exp (-(indexLength k * ρ))) (k : FourierIndex n) :
    ‖fourierTermOnStrip a σ k‖ ≤ M * Real.exp (-δ * indexLength k) := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro q
  change ‖a k * fourierMonomial k q‖ ≤ M * Real.exp (-δ * indexLength k)
  simpa only [neg_mul, mul_comm] using
    norm_fourierTerm_le hM ha (q.property.trans hσ) k

theorem summable_fourierTerms_of_decay {n : ℕ} {a : FourierIndex n → ℂ}
    {M ρ δ : ℝ} {σ : ℝ≥0} (hM : 0 ≤ M) (hδ : 0 < δ) (hσ : (σ : ℝ) ≤ ρ - δ)
    (ha : ∀ k, ‖a k‖ ≤ M * Real.exp (-(indexLength k * ρ))) :
    Summable (fourierTermOnStrip a σ) :=
  ((summable_exp_indexLength n hδ).mul_left M).of_norm_bounded
    (norm_fourierTermOnStrip_le_of_decay hM hσ ha)

theorem norm_tsum_fourierTerms_le_of_decay {n : ℕ} {a : FourierIndex n → ℂ}
    {M ρ δ : ℝ} {σ : ℝ≥0} (hM : 0 ≤ M) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hσ : (σ : ℝ) ≤ ρ - δ)
    (ha : ∀ k, ‖a k‖ ≤ M * Real.exp (-(indexLength k * ρ))) :
    ‖∑' k, fourierTermOnStrip a σ k‖ ≤ M * (4 / δ) ^ n := by
  have h := tsum_of_norm_bounded ((hasSum_exp_indexLength n hδ).mul_left M)
    (norm_fourierTermOnStrip_le_of_decay hM hσ ha)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hM
  simpa only [(hasSum_exp_indexLength n hδ).tsum_eq] using
    tsum_exp_indexLength_le n hδ hδ1

namespace AnalyticPhaseFunction
variable {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}

theorem hasSum_fourier_real_of_summable (f : AnalyticPhaseFunction n G ρ)
    {p : ComplexSpace n} (hp : p ∈ G) (h : Summable (f.fourierCoeff p)) (t : RealSpace n) :
    HasSum (fun k => f.fourierCoeff p k * fourierMonomial k (scaledAngle t))
      (f.toFun (p, scaledAngle t)) := by
  have hs := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (f := f.onUnitTorus ⟨p, hp⟩) h (fun j => (t j : UnitAddCircle))
  simpa only [onUnitTorus, ContinuousMap.coe_mk, smul_eq_mul, fourierCoeff,
    mFourier_eq_fourierMonomial, f.torusValue_coe hp] using hs

theorem summable_fourierCoeff_of_decay (f : AnalyticPhaseFunction n G ρ)
    (p : ComplexSpace n) {M : ℝ} (hρ : 0 < ρ)
    (h : ∀ k, ‖f.fourierCoeff p k‖ ≤ M * Real.exp (-(indexLength k * ρ))) :
    Summable (f.fourierCoeff p) := by
  apply ((summable_exp_indexLength n (show (0 : ℝ) < ρ from hρ)).mul_left M).of_norm_bounded
  intro k
  simpa only [neg_mul, mul_comm] using h k

end AnalyticPhaseFunction
end KamProject.Arnold1963
