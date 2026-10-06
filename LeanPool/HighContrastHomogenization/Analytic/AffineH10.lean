/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineH10Norm

/-!
# High-contrast homogenization: Analytic.AffineH10

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Affine transport of zero-boundary Sobolev functions

Composition with an invertible matrix transports compactly supported smooth
approximants, including their scalar and gradient convergence.  This gives the
corresponding transport of affine Dirichlet data.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- An invertible linear pullback sends an actual `H¹₀` witness to the
inverse-image domain with the transpose-transformed gradient. -/
theorem exists_h10Function_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (u : H10Function U) :
    ∃ uL : H10Function (matImage L⁻¹ U),
      uL.toH1Function.toFun =
          (fun y ↦ u.toH1Function.toFun (matVecMul L y)) ∧
        uL.toH1Function.grad =
          (fun y ↦ matVecMul (matTranspose L)
            (u.toH1Function.grad (matVecMul L y))) := by
  let V : Set (Vec d) := matImage L⁻¹ U
  let T : Vec d → Vec d := matVecMul L
  let C : ℝ≥0∞ :=
    ENNReal.ofReal (|L.det|⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal)
  have hC_ne_top : C ≠ ⊤ := by simp [C]
  obtain ⟨uL, huLfun, huLgrad⟩ :=
    exists_h1Function_affinePullback hL hU u.toH1Function
  let e : Vec d ≃ₜ Vec d :=
    { toFun := matVecMul L
      invFun := matVecMul L⁻¹
      left_inv := fun x ↦ by
        rw [matVecMul_mul, Matrix.nonsing_inv_mul L hL, matVecMul_one]
      right_inv := fun x ↦ by
        rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one]
      continuous_toFun := continuous_matVecMul L
      continuous_invFun := continuous_matVecMul L⁻¹ }
  let w : H10Function V :=
    { toH1Function := uL
      approx := fun n y ↦ u.approx n (T y)
      approx_smooth := fun n ↦ by
        simpa [T, Function.comp_def] using!
          (u.approx_smooth n).comp
            (LinearMap.toContinuousLinearMap (Matrix.mulVecLin L)).contDiff
      approx_hasCompactSupport := fun n ↦ by
        show HasCompactSupport (u.approx n ∘ e)
        simpa [e, T, Function.comp_def] using
          (u.approx_hasCompactSupport n).comp_homeomorph e
      approx_support_subset := fun n y hy ↦ by
        have hy' : matVecMul L y ∈ tsupport (u.approx n) := by
          rw [show (fun z ↦ u.approx n (T z)) = u.approx n ∘ e by rfl,
            tsupport_comp_eq_preimage (u.approx n) e] at hy
          exact hy
        change y ∈ matImage L⁻¹ U
        rw [matImage_inv_eq_preimage hL]
        exact u.approx_support_subset n hy'
      tendsto_approx := by
        have heq :
            (fun n ↦ eLpNorm
              (fun y ↦ u.approx n (T y) - uL.toFun y) 2
              (volume.restrict V)) =
              fun n ↦ C * eLpNorm
                (fun x ↦ u.approx n x - u.toH1Function.toFun x) 2
                (volume.restrict U) := by
          funext n
          have hmeas : AEStronglyMeasurable
              (fun x ↦ u.approx n x - u.toH1Function.toFun x)
              (volume.restrict U) :=
            (u.approx_smooth n).continuous.aestronglyMeasurable.sub
              u.toH1Function.memL2.aestronglyMeasurable
          rw [show (fun y ↦ u.approx n (T y) - uL.toFun y) =
              fun y ↦ (u.approx n (matVecMul L y) -
                u.toH1Function.toFun (matVecMul L y)) by
            funext y
            rw [huLfun]]
          simpa [C, V] using eLpNorm_affinePullback hL hU hmeas
        rw [heq]
        simpa using
          ENNReal.Tendsto.const_mul u.tendsto_approx (Or.inr hC_ne_top)
      tendsto_approx_grad := fun i ↦ by
        let sourceError : ℕ → Fin d → Vec d → ℝ :=
          fun n j x ↦ smoothGrad (u.approx n) x j - u.toH1Function.grad x j
        have hsourceMem : ∀ n j,
            MemL2On U (sourceError n j) := by
          intro n j
          exact (((u.approx_smooth n).continuous_fderiv (by simp)).clm_apply
              continuous_const |>.memLp_of_hasCompactSupport
                ((u.approx_hasCompactSupport n).fderiv_apply
                  (𝕜 := ℝ) (basisVec j)) |>.restrict U).sub
            (u.toH1Function.gradMemL2 j)
        have hpoint : ∀ n y,
            (fderiv ℝ (fun z ↦ u.approx n (T z)) y) (basisVec i) -
                uL.grad y i =
              ∑ j, L j i * sourceError n j (matVecMul L y) := by
          intro n y
          rw [← smoothGrad, smoothGrad_comp_matVecMul L (u.approx_smooth n),
            huLgrad]
          simp only [sourceError, matVecMul, matTranspose, Matrix.transpose_apply]
          calc
            ∑ j, L j i * smoothGrad (u.approx n) (matVecMul L y) j -
                ∑ j, L j i * u.grad (matVecMul L y) j =
              ∑ j, (L j i * smoothGrad (u.approx n) (matVecMul L y) j -
                L j i * u.grad (matVecMul L y) j) :=
                by rw [Finset.sum_sub_distrib]
            _ = ∑ j, L j i * (smoothGrad (u.approx n) (matVecMul L y) j -
                u.grad (matVecMul L y) j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
        let pulledError : ℕ → Fin d → Vec d → ℝ :=
          fun n j y ↦ L j i * sourceError n j (matVecMul L y)
        have hpulledMeas : ∀ n j, AEStronglyMeasurable
            (pulledError n j) (volume.restrict V) := by
          intro n j
          have hj := ((memL2On_affinePullback hL hU
            (hsourceMem n j)).const_mul (L j i)).aestronglyMeasurable
          simpa only [pulledError, Pi.smul_apply, smul_eq_mul] using hj
        have hpulledTend : ∀ j, _root_.Filter.Tendsto
            (fun n ↦ eLpNorm (pulledError n j) 2 (volume.restrict V))
            _root_.Filter.atTop (nhds 0) := by
          intro j
          have heq :
              (fun n ↦ eLpNorm (pulledError n j) 2 (volume.restrict V)) =
                fun n ↦ ‖L j i‖ₑ * C *
                  eLpNorm (sourceError n j) 2 (volume.restrict U) := by
            funext n
            calc
              eLpNorm (pulledError n j) 2 (volume.restrict V) =
                  ‖L j i‖ₑ * eLpNorm
                    (fun y ↦ sourceError n j (matVecMul L y)) 2
                    (volume.restrict V) := by
                simpa only [pulledError, Pi.smul_apply, smul_eq_mul] using!
                  eLpNorm_const_smul (L j i)
                    (fun y ↦ sourceError n j (matVecMul L y)) 2
                    (volume.restrict V)
              _ = ‖L j i‖ₑ * C *
                  eLpNorm (sourceError n j) 2 (volume.restrict U) := by
                rw [eLpNorm_affinePullback hL hU
                  (hsourceMem n j).aestronglyMeasurable]
                simp only [C, mul_assoc]
          rw [heq]
          have hconst : ‖L j i‖ₑ * C ≠ ⊤ :=
            ENNReal.mul_ne_top (by simp) hC_ne_top
          simpa using! ENNReal.Tendsto.const_mul (u.tendsto_approx_grad j)
            (Or.inr hconst)
        have hsum := tendsto_eLpNorm_finset_sum_zero pulledError
          (volume.restrict V) hpulledMeas hpulledTend
        convert hsum using 1
        funext n
        congr 2
        funext y
        simpa only [pulledError, Finset.sum_apply] using hpoint n y }
  exact ⟨w, huLfun, huLgrad⟩

/-- Affine Dirichlet membership transports with constructed pullbacks of both
the boundary datum and the solution. -/
theorem exists_memAffineH10_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (g₀ h : H1Function U)
    (haff : MemAffineH10 U g₀ h) :
    ∃ g₀L hL : H1Function (matImage L⁻¹ U),
      g₀L.toFun = (fun y ↦ g₀.toFun (matVecMul L y)) ∧
      g₀L.grad = (fun y ↦ matVecMul (matTranspose L)
        (g₀.grad (matVecMul L y))) ∧
      hL.toFun = (fun y ↦ h.toFun (matVecMul L y)) ∧
      hL.grad = (fun y ↦ matVecMul (matTranspose L)
        (h.grad (matVecMul L y))) ∧
      MemAffineH10 (matImage L⁻¹ U) g₀L hL := by
  obtain ⟨g₀L, hg₀fun, hg₀grad⟩ := exists_h1Function_affinePullback hL hU g₀
  obtain ⟨hPulled, hhfun, hhgrad⟩ :=
    exists_h1Function_affinePullback hL hU h
  rcases haff with ⟨w, hwfun, hwgrad⟩
  obtain ⟨wL, hwLfun, hwLgrad⟩ := exists_h10Function_affinePullback hL hU w
  have hmap := map_restrict_volume_affinePullback hL hU
  have hTmeas : AEMeasurable (matVecMul L : Vec d → Vec d)
      (volume.restrict (matImage L⁻¹ U)) :=
    (continuous_matVecMul L).aemeasurable
  have hwfunMap : w.toH1Function.toFun =ᵐ[
      Measure.map (matVecMul L) (volume.restrict (matImage L⁻¹ U))]
      (fun x ↦ h.toFun x - g₀.toFun x) := by
    rw [hmap]
    exact Measure.smul_absolutelyContinuous.ae_eq hwfun
  have hwgradMap : w.toH1Function.grad =ᵐ[
      Measure.map (matVecMul L) (volume.restrict (matImage L⁻¹ U))]
      (fun x ↦ h.grad x - g₀.grad x) := by
    rw [hmap]
    exact Measure.smul_absolutelyContinuous.ae_eq hwgrad
  refine ⟨g₀L, hPulled, hg₀fun, hg₀grad, hhfun, hhgrad, wL, ?_, ?_⟩
  · have hpull := ae_eq_comp hTmeas hwfunMap
    rw [hwLfun, hhfun, hg₀fun]
    simpa [Function.comp_def] using hpull
  · have hpull := ae_eq_comp hTmeas hwgradMap
    rw [hwLgrad, hhgrad, hg₀grad]
    filter_upwards [hpull] with y hy
    simp only [Function.comp_apply] at hy
    rw [hy]
    ext i
    simp only [matVecMul, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

end

end HighContrast
end HCPolySupport
