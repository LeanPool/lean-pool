/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Analysis.FourierCoefficients
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.FourierKernel
public import LeanPool.ArnoldKAM.Arnold1963.Arithmetic.Parameters
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
Integration, Fourier normalization, threshold positivity, and a nonconstant cosine example.
-/

@[expose] public section
noncomputable section
open KamProject.Arnold1963 MeasureTheory
open scoped NNReal
namespace KamProject.Arnold1963.Audit

/-- Normalized Haar measure for the explicit Fourier examples. -/
local instance auditFourierMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example (k : FourierIndex 2) :
    UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier k) k = (1 : ℂ) := by
  have h := (orthonormal_iff_ite.mp UnitAddTorus.orthonormal_mFourier) k k
  simpa only [ite_true, eq_self, ContinuousMap.inner_toLp, ← UnitAddTorus.mFourier_neg,
    UnitAddTorus.mFourierCoeff, smul_eq_mul, mul_comm] using h

example : indexLength (![1, 1] : FourierIndex 2) = 2 := by norm_num [indexLength]
example : (![1, 1] : FourierIndex 2) ∉ fourierModes 2 2 := by norm_num [indexLength]
example : (![1, 1] : FourierIndex 2) ∈ fourierModes 2 (5 / 2) := by
  norm_num [indexLength]
example : ‖(fun _ : Fin 2 => (1 : ℂ))‖ = 1 := by simp
example (M : ℝ) : NormBoundOn (fun _ : ℝ => (0 : ℂ)) ∅ M ↔ 0 ≤ M := by simp

private theorem norm_cos_le_exp_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos, norm_div]
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have h := norm_add_le (Complex.exp (z * Complex.I)) (Complex.exp (-z * Complex.I))
  rw [Complex.norm_exp, Complex.norm_exp] at h
  have ha : (z * Complex.I).re ≤ |z.im| := by simpa using neg_le_abs z.im
  have hb : (-z * Complex.I).re ≤ |z.im| := by simpa using le_abs_self z.im
  exact h.trans (by nlinarith [Real.exp_le_exp.mpr ha, Real.exp_le_exp.mpr hb])

/-- The cosine of the first angle, packaged with analyticity, periodicity and boundedness. -/
def cosineExample (ρ : ℝ≥0) : AnalyticPhaseFunction 1 Set.univ ρ where
  toFun z := Complex.cos (z.2 0)
  domain_conj := by intro z hz; trivial
  analytic := by
    intro z hz
    let L : ComplexPhaseSpace 1 →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj (0 : Fin 1)).comp (ContinuousLinearMap.snd ℂ _ _)
    exact Complex.analyticAt_cos.comp (f := L) (L.analyticAt z)
  periodic := by
    intro p hp q hq k
    simpa [angleShift, complexify, mul_comm, mul_assoc] using
      Complex.cos_add_int_mul_two_pi (q 0) (k 0)
  conj_compatible := by
    intro z hz
    simpa only [conjPhase, conjVec, starRingEnd_apply] using Complex.cos_conj (z.2 0)
  bounded := by
    refine ⟨Real.exp ρ, (Real.exp_pos _).le, fun z hz => ?_⟩
    exact (norm_cos_le_exp_im _).trans
      (Real.exp_le_exp.mpr ((mem_angleStrip_iff _ _).mp hz.2 0))

example (ρ : ℝ≥0) : (cosineExample ρ).toFun (0, 0) = 1 := by
  simp [cosineExample]
example (ρ : ℝ≥0) :
    (cosineExample ρ).toFun (0, fun _ => (Real.pi : ℂ)) = -1 := by
  simp [cosineExample]

example (ρ : ℝ≥0) (k : FourierIndex 1) :
    ‖(cosineExample ρ).fourierCoeff 0 k‖ ≤ (cosineExample ρ).uniformNorm :=
  (cosineExample ρ).norm_fourierCoeff_le (Set.mem_univ _) k
example (ρ : ℝ≥0) :
    ‖(cosineExample ρ).toFun (0, 0) - (cosineExample ρ).angleAverage 0‖ ≤
      2 * (cosineExample ρ).uniformNorm :=
  (cosineExample ρ).norm_sub_angleAverage_le (Set.mem_univ _)
    (by simpa using complexify_mem_angleStrip (0 : RealSpace 1) ρ)

example {δ : ℝ} (hδ : 0 < δ) :
    HasSum (fun k : FourierIndex 0 => Real.exp (-δ * indexLength k)) 1 := by
  simpa using hasSum_exp_indexLength 0 hδ

example {n : ℕ} (hn : 0 < n) {θ Θ ρ κ D : ℝ}
    (hθ : 0 < θ) (hΘ : 0 < Θ) (hρ : 0 < ρ) (hκ : 0 < κ) (hD : 0 < D) :
    0 < initialPerturbationThreshold n θ Θ ρ κ D :=
  initialPerturbationThreshold_pos hn hθ hΘ hρ hκ hD

end KamProject.Arnold1963.Audit
