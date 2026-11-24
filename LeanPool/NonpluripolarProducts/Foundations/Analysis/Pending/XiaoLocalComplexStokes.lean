/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.XiaoComplexDifferential
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.XiaoLocalStokes
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.StandardHermitianTwoForm

/-!
# Genuine local complex Stokes and the actual top density

Multiplication by `I` has real determinant one. The actual top-density Jacobian
law therefore removes the outer complex twist in normalized `dᶜ`, reducing its
local Stokes identity to the actual exterior derivative identity.
-/

@[expose] public section

open MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.XiaoLocalComplexStokes

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms TopDegreeDensity
  ConstantFormProducts XiaoComplexDifferential XiaoLocalStokes

noncomputable section

variable {n k : ℕ}

/-- The actual model complex structure preserves the real orientation and volume. -/
theorem modelComplexStructure_real_det_eq_one (n : ℕ) :
    LinearMap.det (modelComplexStructure n).toLinearMap = 1 := by
  change LinearMap.det
    ((Complex.I • LinearMap.id : ComplexModel n →ₗ[ℂ] ComplexModel n).restrictScalars ℝ) = 1
  rw [normSq_det_eq_realDet]
  simp [LinearMap.det_smul]

/-- The complex structure preserves the existing actual real top density. -/
theorem topDensity_comp_modelComplexStructure (A : RealForm n (2 * n)) :
    topDensity (A.compContinuousLinearMap (modelComplexStructure n)) = topDensity A := by
  rw [topDensity_compContinuousLinearMap, modelComplexStructure_real_det_eq_one, one_mul]

/-- The actual chart formula for the normalized complex differential in degree `k`. -/
def localDc (a : ComplexModel n → RealForm n k) (z : ComplexModel n) : RealForm n (k + 1) :=
  ((-1 : ℝ) ^ (k + 1) / (4 * Real.pi)) •
    (extDeriv (fun y => (a y).compContinuousLinearMap (modelComplexStructure n))
      z).compContinuousLinearMap
      (modelComplexStructure n)

/-- The local construction is precisely the existing actual global coefficient. -/
theorem localDc_eq_dc_coeff {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (a : SmoothRealForm n M k) (e : ComplexChart n M) (z : ComplexModel n) :
    localDc (a.coeff e) z = (dc a).coeff e z := rfl

/-- The normalized local complex differential has integrable top density and zero integral. -/
theorem integrable_and_integral_topDensity_localDc_eq_zero
    {a : ComplexModel n → RealForm n k} (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a)
    (h : k + 1 = 2 * n) :
    Integrable (fun z => topDensity (castForm h (localDc a z))) ∧
      (∫ z, topDensity (castForm h (localDc a z))) = 0 := by
  let L : RealForm n k →L[ℝ] RealForm n k :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM (modelComplexStructure n)
  have htw : ContDiff ℝ 1 (fun z => (a z).compContinuousLinearMap (modelComplexStructure n)) :=
    L.contDiff.comp ha
  have hctw : HasCompactSupport
      (fun z => (a z).compContinuousLinearMap (modelComplexStructure n)) :=
    hc.comp_left (g := L) L.map_zero
  obtain ⟨hi, hz⟩ := integrable_and_integral_topDensity_extDeriv_eq_zero htw hctw h
  have heq : (fun z => topDensity (castForm h (localDc a z))) =
      fun z => ((-1 : ℝ) ^ (k + 1) / (4 * Real.pi)) *
        topDensity (castForm h
          (extDeriv (fun y => (a y).compContinuousLinearMap (modelComplexStructure n)) z)) := by
    funext z
    simp only [localDc, map_smul, topDensity_smul, ← castForm_compContinuousLinearMap,
      topDensity_comp_modelComplexStructure]
  rw [heq]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul, hz, mul_zero]

end

end SGPT.Foundations.Analysis.Pending.XiaoLocalComplexStokes
