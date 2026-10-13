/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.Arithmetic
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.Carrier

/-!
# CoefficientBounds

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Pointwise consequences of small contrast

The source informally replaces `||a-Id|| <= delta` by `Id <= a`.  The latter
does not follow.  The correct consequence is coercivity at `1-delta`; combined
with `delta < 1/2`, it gives the same factor `2` in the harmonic-comparison
estimate printed in the proof.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport
open HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ}

instance matMeasurableSpace : MeasurableSpace (Mat d) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))

instance matBorelSpace : BorelSpace (Mat d) :=
  inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))

instance hilbertVecOperatorMeasurableSpace :
    MeasurableSpace (HilbertVec d →L[ℝ] HilbertVec d) :=
  borel (HilbertVec d →L[ℝ] HilbertVec d)

instance hilbertVecOperatorBorelSpace :
    BorelSpace (HilbertVec d →L[ℝ] HilbertVec d) :=
  ⟨rfl⟩

noncomputable def matrixToHilbertOperatorLinear :
    Mat d →ₗ[ℝ] (HilbertVec d →L[ℝ] HilbertVec d) where
  toFun := HilbertVec.applyMat
  map_add' := by
    intro A B
    ext x i
    simp [HilbertVec.applyMat_apply, matVecMul, Finset.sum_add_distrib, add_mul]
  map_smul' := by
    intro c A
    ext x i
    simp [HilbertVec.applyMat_apply, matVecMul, Finset.mul_sum, mul_assoc]

noncomputable def matrixToHilbertOperator :
    Mat d →L[ℝ] (HilbertVec d →L[ℝ] HilbertVec d) :=
  ⟨matrixToHilbertOperatorLinear,
    matrixToHilbertOperatorLinear.continuous_of_finiteDimensional⟩

/-- A measurable coefficient satisfying the a.e. small-contrast bound maps
an `L²` vector field through `a - Id` into `L²`; no pointwise ellipticity
certificate is needed. -/
theorem memVectorL2_coefficientSubIdentity_mul
    {W : Set (Vec d)} {a : CoeffField d} {H : Vec d → Vec d} {delta : ℝ}
    (hmeas : AEMeasurable a (volume.restrict W))
    (ha : CoefficientIdentityDistanceLE W a delta)
    (hH : MemVectorL2 W H) :
    MemVectorL2 W (fun x ↦ matVecMul (a x - 1) (H x)) := by
  let evalCLM :
      (HilbertVec d →L[ℝ] HilbertVec d) →L[ℝ]
        HilbertVec d →L[ℝ] HilbertVec d :=
    ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ (HilbertVec d))
  have hoperator : AEMeasurable (fun x ↦ HilbertVec.applyMat (a x - 1))
      (volume.restrict W) := by
    have hsub : AEMeasurable (fun x ↦ a x - 1) (volume.restrict W) := by
      refine aemeasurable_pi_iff.mpr fun i ↦ aemeasurable_pi_iff.mpr fun j ↦ ?_
      exact ((aemeasurable_pi_iff.mp
        ((aemeasurable_pi_iff.mp hmeas) i)) j).sub aemeasurable_const
    exact matrixToHilbertOperator.continuous.measurable.comp_aemeasurable hsub
  have hHHilbert : MemLp (fun x ↦ HilbertVec.ofVec (H x)) 2
      (volumeMeasureOn W) :=
    memHilbertVectorL2_hilbertifyVecField hH
  have hstrong : AEStronglyMeasurable
      (fun x ↦ HilbertVec.applyMat (a x - 1) (HilbertVec.ofVec (H x)))
      (volumeMeasureOn W) := by
    simpa only [evalCLM] using!
      ContinuousLinearMap.aestronglyMeasurable_comp₂ (L := evalCLM)
        hoperator.aestronglyMeasurable hHHilbert.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂volumeMeasureOn W,
      ‖HilbertVec.applyMat (a x - 1) (HilbertVec.ofVec (H x))‖ ≤
        delta * ‖HilbertVec.ofVec (H x)‖ := by
    filter_upwards [ha] with x hx
    exact (HilbertVec.applyMat (a x - 1)).le_opNorm _ |>.trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hPHilbert : MemLp
      (fun x ↦ HilbertVec.applyMat (a x - 1) (HilbertVec.ofVec (H x))) 2
      (volumeMeasureOn W) :=
    MemLp.of_le_mul hHHilbert hstrong hbound
  let toVecCLM : HilbertVec d →L[ℝ] Vec d :=
    (HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap
  simpa only [HilbertVec.applyMat_apply, HilbertVec.toVec_ofVec] using!
    toVecCLM.comp_memLp' hPHilbert

/-- The same hypotheses give `L²` integrability of the full coefficient
action. -/
theorem memVectorL2_coefficient_mul
    {W : Set (Vec d)} {a : CoeffField d} {H : Vec d → Vec d} {delta : ℝ}
    (hmeas : AEMeasurable a (volume.restrict W))
    (ha : CoefficientIdentityDistanceLE W a delta)
    (hH : MemVectorL2 W H) :
    MemVectorL2 W (fun x ↦ matVecMul (a x) (H x)) := by
  have hP := memVectorL2_coefficientSubIdentity_mul hmeas ha hH
  have heq : (fun x ↦ matVecMul (a x) (H x)) =
      fun x ↦ H x + matVecMul (a x - 1) (H x) := by
    funext x
    classical
    change (a x).mulVec (H x) = H x + (a x - 1).mulVec (H x)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [heq]
  exact hH.add hP

private theorem matVecMul_sub_one (A : Mat d) (v : Vec d) :
    matVecMul (A - 1) v = matVecMul A v - v := by
  classical
  funext i
  simp only [matVecMul, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  simp [Matrix.one_apply]
  rfl

private theorem vecDot_self_eq_vecNormSq (v : Vec d) :
    vecDot v v = vecNormSq v := rfl

/-- The ruled Hilbert-space operator norm controls the squared Euclidean
magnitude of matrix action. -/
theorem vecNormSq_matVecMul_le_applyMat_opNorm_sq_mul (A : Mat d) (v : Vec d) :
    vecNormSq (matVecMul A v) ≤
      ‖HilbertVec.applyMat A‖ ^ 2 * vecNormSq v := by
  have hop := (HilbertVec.applyMat A).le_opNorm (HilbertVec.ofVec v)
  calc
    vecNormSq (matVecMul A v) =
        ‖HilbertVec.applyMat A (HilbertVec.ofVec v)‖ ^ 2 := by
      rw [HilbertVec.norm_sq_applyMat]
      rfl
    _ ≤ (‖HilbertVec.applyMat A‖ * ‖HilbertVec.ofVec v‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hop 2
    _ = ‖HilbertVec.applyMat A‖ ^ 2 * vecNormSq v := by
      rw [mul_pow, HilbertVec.norm_sq_ofVec]
      rfl

/-- Operator-norm closeness controls the perturbative quadratic form. -/
theorem abs_vecDot_coefficient_sub_identity_le {A : Mat d} {delta : ℝ}
    (hA : ‖HilbertVec.applyMat (A - 1)‖ ≤ delta) (v : Vec d) :
    |vecDot v (matVecMul (A - 1) v)| ≤ delta * vecNormSq v := by
  have hop : ‖HilbertVec.applyMat (A - 1) (HilbertVec.ofVec v)‖ ≤
      delta * ‖HilbertVec.ofVec v‖ := by
    exact ((HilbertVec.applyMat (A - 1)).le_opNorm (HilbertVec.ofVec v)).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  calc
    |vecDot v (matVecMul (A - 1) v)| =
        |inner ℝ (HilbertVec.ofVec v)
          (HilbertVec.applyMat (A - 1) (HilbertVec.ofVec v))| := by
            rw [HilbertVec.inner_ofVec_applyMat]
    _ ≤ ‖HilbertVec.ofVec v‖ *
        ‖HilbertVec.applyMat (A - 1) (HilbertVec.ofVec v)‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖HilbertVec.ofVec v‖ * (delta * ‖HilbertVec.ofVec v‖) :=
      mul_le_mul_of_nonneg_left hop (norm_nonneg _)
    _ = delta * vecNormSq v := by
      change ‖HilbertVec.ofVec v‖ * (delta * ‖HilbertVec.ofVec v‖) =
        delta * vecDot v v
      rw [← HilbertVec.norm_sq_ofVec]
      ring

/-- The honest lower ellipticity bound supplied by small contrast. -/
theorem one_sub_mul_vecNormSq_le_vecDot_coefficient {A : Mat d} {delta : ℝ}
    (hA : ‖HilbertVec.applyMat (A - 1)‖ ≤ delta) (v : Vec d) :
    (1 - delta) * vecNormSq v ≤ vecDot v (matVecMul A v) := by
  have hdev := abs_vecDot_coefficient_sub_identity_le hA v
  have hlow : -delta * vecNormSq v ≤ vecDot v (matVecMul (A - 1) v) := by
    simpa only [neg_mul] using neg_le_of_abs_le hdev
  have hsplit : vecDot v (matVecMul A v) =
      vecNormSq v + vecDot v (matVecMul (A - 1) v) := by
    have hv : matVecMul A v = v + matVecMul (A - 1) v := by
      rw [matVecMul_sub_one]
      abel
    rw [hv, vecDot_add_right, vecDot_self_eq_vecNormSq]
  rw [hsplit]
  linarith only [hlow]

/-- The printed smallness assumption supplies the honest half-coercivity used
in the corrected energy test. -/
theorem half_mul_vecNormSq_le_vecDot_coefficient_of_smallContrast
    {A : Mat d} {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hA : ‖HilbertVec.applyMat (A - 1)‖ ≤ smallContrastThreshold d alpha)
    (v : Vec d) :
    (1 / 2 : ℝ) * vecNormSq v ≤ vecDot v (matVecMul A v) := by
  have hbase := one_sub_mul_vecNormSq_le_vecDot_coefficient hA v
  have hsmall := smallContrastThreshold_lt_half d halpha0 halpha1
  have hnorm := vecNormSq_nonneg v
  calc
    (1 / 2 : ℝ) * vecNormSq v ≤
        (1 - smallContrastThreshold d alpha) * vecNormSq v := by
      gcongr
      linarith only [hsmall]
    _ ≤ vecDot v (matVecMul A v) := hbase

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
