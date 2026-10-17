/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.HarmonicReplacement
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.CoefficientBounds
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.AnalyticInequalities

/-!
# WeakTesting

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Weak testing for the small-contrast harmonic comparison

This file supplies the measure-theoretic part of `e.harmapprox.Schauder`.
The public chain uses coefficient measurability and the a.e. operator-norm
distance directly.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport HCPolySupport.Book.Ch02
open HCPolySupport.Book.Ch05.Section53.JUpperBoundWeakNorms

noncomputable section

variable {d : ℕ}

/-- Squared Euclidean magnitude is integrable for a vector `L²` field. -/
theorem integrableOn_vecNormSq_of_memVectorL2
    {W : Set (Vec d)} {F : Vec d → Vec d} (hF : MemVectorL2 W F) :
    IntegrableOn (fun x => vecNormSq (F x)) W := by
  simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hF hF

private theorem memLp_euclideanNorm_of_memVectorL2
    {W : Set (Vec d)} {F : Vec d → Vec d} (hF : MemVectorL2 W F) :
    MemLp (fun x => euclideanNorm (F x)) 2 (volume.restrict W) := by
  have hh := (memHilbertVectorL2_hilbertifyVecField hF).norm
  simpa [hilbertifyVecField, euclideanNorm_eq_norm_ofVec] using hh

private theorem vecNorm_eq_euclideanNorm (v : Vec d) :
    vecNorm v = euclideanNorm v := by
  rw [← sq_eq_sq₀ (vecNorm_nonneg v) (euclideanNorm_nonneg v),
    vecNorm_sq_eq_vecNormSq, euclideanNorm_sq]

/-- Euclidean Cauchy--Schwarz for two vector `L²` fields, expressed in the
square-energy language used by the harmonic comparison. -/
theorem abs_integral_vecDot_le_sqrt_energy_mul_sqrt_energy
    {W : Set (Vec d)} {F G : Vec d → Vec d}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hF : MemVectorL2 W F) (hG : MemVectorL2 W G) :
    |∫ x in W, vecDot (F x) (G x) ∂volume| ≤
      Real.sqrt (∫ x in W, vecNormSq (F x) ∂volume) *
        Real.sqrt (∫ x in W, vecNormSq (G x) ∂volume) := by
  let X : Vec d → ℝ := fun x => euclideanNorm (F x)
  let Y : Vec d → ℝ := fun x => euclideanNorm (G x)
  have hX : MemLp X 2 (volume.restrict W) := by
    simpa [X] using memLp_euclideanNorm_of_memVectorL2 hF
  have hY : MemLp Y 2 (volume.restrict W) := by
    simpa [Y] using memLp_euclideanNorm_of_memVectorL2 hG
  have hdot : IntegrableOn (fun x => vecDot (F x) (G x)) W :=
    integrableOn_vecDot_of_memVectorL2 hF hG
  have hXY : IntegrableOn (fun x => X x * Y x) W := by
    have hmem : MemLp (fun x => X x * Y x) 1 (volume.restrict W) :=
      hX.fun_mul (r := 1) hY
    exact hmem.integrable (by norm_num)
  have habs :
      |∫ x in W, vecDot (F x) (G x) ∂volume| ≤
        ∫ x in W, X x * Y x ∂volume := by
    calc
      |∫ x in W, vecDot (F x) (G x) ∂volume| ≤
          ∫ x in W, |vecDot (F x) (G x)| ∂volume := abs_integral_le_integral_abs
      _ ≤ ∫ x in W, X x * Y x ∂volume := by
        apply setIntegral_mono_ae hdot.abs hXY
        filter_upwards with x
        simpa [X, Y, ← vecNorm_eq_euclideanNorm] using!
          abs_vecDot_le_vecNorm_mul_vecNorm (F x) (G x)
  have hcs :=
    integral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq_of_ae_nonneg
      (μ := volume.restrict W)
      hX.integrable_sq hY.integrable_sq
      (Filter.Eventually.of_forall fun x => euclideanNorm_nonneg (F x))
      (Filter.Eventually.of_forall fun x => euclideanNorm_nonneg (G x))
  have hXsq : (fun x => X x ^ 2) = fun x => vecNormSq (F x) := by
    funext x
    dsimp [X]
    rw [euclideanNorm_sq]
  have hYsq : (fun x => Y x ^ 2) = fun x => vecNormSq (G x) := by
    funext x
    dsimp [Y]
    rw [euclideanNorm_sq]
  rw [hXsq, hYsq] at hcs
  exact habs.trans hcs

/-- Measurable-coefficient form of the perturbation-field estimate. -/
theorem integral_vecNormSq_coefficientSubIdentity_mul_le_of_measurable
    {W : Set (Vec d)} {a : CoeffField d} {H : Vec d → Vec d} {delta : ℝ}
    (hmeas : Measurable a)
    (ha : CoefficientIdentityDistanceLE W a delta)
    (hH : MemVectorL2 W H) :
    ∫ x in W, vecNormSq (matVecMul (a x - 1) (H x)) ∂volume ≤
      delta ^ 2 * ∫ x in W, vecNormSq (H x) ∂volume := by
  let P : Vec d → Vec d := fun x => matVecMul (a x - 1) (H x)
  have hP : MemVectorL2 W P := by
    simpa only [P] using
      memVectorL2_coefficientSubIdentity_mul hmeas.aemeasurable ha hH
  have hleft := integrableOn_vecNormSq_of_memVectorL2 hP
  have hright :=
    (integrableOn_vecNormSq_of_memVectorL2 hH).const_mul (delta ^ 2)
  calc
    ∫ x in W, vecNormSq (matVecMul (a x - 1) (H x)) ∂volume =
        ∫ x in W, vecNormSq (P x) ∂volume := rfl
    _ ≤ ∫ x in W, delta ^ 2 * vecNormSq (H x) ∂volume := by
      apply integral_mono_ae hleft hright
      filter_upwards [ha] with x hx
      exact (vecNormSq_matVecMul_le_applyMat_opNorm_sq_mul
        (a x - 1) (H x)).trans
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀
            (norm_nonneg (HilbertVec.applyMat (a x - 1))) hx 2)
            (vecNormSq_nonneg (H x)))
    _ = delta ^ 2 * ∫ x in W, vecNormSq (H x) ∂volume :=
      integral_const_mul _ _

/-- Square-root measurable-coefficient form of the perturbation estimate. -/
theorem sqrt_integral_vecNormSq_coefficientSubIdentity_mul_le_of_measurable
    {W : Set (Vec d)} {a : CoeffField d} {H : Vec d → Vec d} {delta : ℝ}
    (hmeas : Measurable a)
    (ha : CoefficientIdentityDistanceLE W a delta)
    (hdelta : 0 ≤ delta) (hH : MemVectorL2 W H) :
    Real.sqrt (∫ x in W, vecNormSq (matVecMul (a x - 1) (H x)) ∂volume) ≤
      delta * Real.sqrt (∫ x in W, vecNormSq (H x) ∂volume) := by
  have h := Real.sqrt_le_sqrt
    (integral_vecNormSq_coefficientSubIdentity_mul_le_of_measurable hmeas ha hH)
  rw [Real.sqrt_mul (sq_nonneg delta), Real.sqrt_sq hdelta] at h
  exact h
end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
