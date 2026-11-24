/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.XiaoCovectorProducts
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.XiaoLocalComplexStokes
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicMixedDensity

/-! # Normalized local differentials of scalar times constant type forms -/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.ConstantFormLocalDdc

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms ConstantFormProducts
  ClosedProductCurrents LocalProductCurrents XiaoCovectorProducts XiaoLocalComplexStokes

/-- The genuine normalized first identity only needs pointwise differentiability. -/
theorem localDc_smul_const_form_at {n q : ℕ}
    {f : ComplexModel n → ℝ} {x : ComplexModel n}
    (hf : DifferentiableAt ℝ f x) (γ : formSpan n q) :
    localDc (fun y => f y • (γ : RealForm n (2 * q))) x =
      oneWedge ((-1 / (4 * Real.pi) : ℝ) •
        (fderiv ℝ f x).comp (modelComplexStructure n)) (γ : RealForm n (2 * q)) := by
  have hJ : complexJ n = modelComplexStructure n := by
    ext v
    rfl
  have hγ : (γ : RealForm n (2 * q)).compContinuousLinearMap
      (modelComplexStructure n) = γ := by
    rw [← hJ]
    exact (mem_jInvariant_iff _).mp (formSpan_le_jInvariant q γ.property)
  have hfield : (fun y => (f y • (γ : RealForm n (2 * q))).compContinuousLinearMap
      (modelComplexStructure n)) = fun y => f y • (γ : RealForm n (2 * q)) := by
    funext y
    ext v
    simpa only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.smul_apply] using
      congrArg (fun A : RealForm n (2 * q) => f y • A v) hγ
  have hc : extDeriv (fun _ : ComplexModel n => (γ : RealForm n (2 * q))) x = 0 := by
    ext v
    simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  have hs : ((-1 : ℝ) ^ (2 * q + 1) / (4 * Real.pi)) = -1 / (4 * Real.pi) := by
    simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul]
  rw [localDc, hfield, extDeriv_smul_eq hf (differentiableAt_const _), hc,
    smul_zero, add_zero, oneWedge_compContinuousLinearMap, hγ, hs]
  simpa only [covectorWedgeCLM_apply, smul_apply] using
    congrArg (fun L : RealForm n (2 * q) →L[ℝ] RealForm n (2 * q + 1) => L γ)
      ((covectorWedgeCLM n (2 * q)).map_smul (-1 / (4 * Real.pi))
        ((fderiv ℝ f x).comp (modelComplexStructure n))).symm

/-- A genuine second-order germ produces the full normalized second identity. -/
theorem localDdc_smul_const_form_at {n q : ℕ}
    {f : ComplexModel n → ℝ} {x : ComplexModel n}
    (hf : ContDiffAt ℝ 2 f x) (γ : formSpan n q) :
    extDeriv (fun y => localDc
      (fun z => f z • (γ : RealForm n (2 * q))) y) x =
      wedgeTo (by omega : 2 + 2 * q = 2 * q + 1 + 1)
        (smoothDDC f x) (γ : RealForm n (2 * q)) := by
  let L : ComplexModel n → (ComplexModel n →L[ℝ] ℝ) :=
    fun y => (-1 / (4 * Real.pi) : ℝ) •
      (fderiv ℝ f y).comp (modelComplexStructure n)
  have heq : (fun y => localDc (fun z => f z • (γ : RealForm n (2 * q))) y)
      =ᶠ[𝓝 x] fun y => oneWedge (L y) (γ : RealForm n (2 * q)) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact localDc_smul_const_form_at (hy.differentiableAt (by norm_num)) γ
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hL : DifferentiableAt ℝ L x := by
    dsimp only [L]
    fun_prop
  have hc : extDeriv (fun _ : ComplexModel n => (γ : RealForm n (2 * q))) x = 0 := by
    ext v
    simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  have hz : oneWedge (L x) (0 : RealForm n (2 * q + 1)) = 0 := by
    simpa only [covectorWedgeCLM_apply] using (covectorWedgeCLM n (2 * q + 1) (L x)).map_zero
  rw [heq.extDeriv_eq, extDeriv_oneWedge_eq hL (differentiableAt_const _), hc, hz, sub_zero]
  rfl

/-- The identity needs smoothness only on the actual open set. -/
theorem localDdc_smul_const_form_on {n q : ℕ}
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ 2 f U)
    (γ : formSpan n q) {x : ComplexModel n} (hx : x ∈ U) :
    extDeriv (fun y => localDc
      (fun z => f z • (γ : RealForm n (2 * q))) y) x =
      wedgeTo (by omega : 2 + 2 * q = 2 * q + 1 + 1)
        (smoothDDC f x) (γ : RealForm n (2 * q)) :=
  localDdc_smul_const_form_at ((hf x hx).contDiffAt (hU.mem_nhds hx)) γ

/-- Actual finite-sum exterior differentiation, including the empty family. -/
theorem extDeriv_fintype_sum_at {n k : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → ComplexModel n → RealForm n k) {x : ComplexModel n}
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) :
    extDeriv (fun y => ∑ i, a i y) x = ∑ i, extDeriv (a i) x := by
  simp only [extDeriv]
  rw [fderiv_fun_sum (fun i _ => ha i)]
  exact map_sum (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ) _ _

end SGPT.Foundations.Analysis.Pending.ConstantFormLocalDdc
