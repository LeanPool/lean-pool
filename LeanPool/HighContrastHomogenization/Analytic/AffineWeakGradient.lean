/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineGeometry
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.BasicLemmas
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# High-contrast homogenization: Analytic.AffineWeakGradient

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Affine transport of weak gradients

An invertible matrix pulls a scalar Sobolev function back by composition and
transports its weak gradient by the transpose matrix.  This file records the
weak-gradient and `H¹` parts of that change of variables.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The inverse image domain of a measurable set under an invertible matrix is measurable. -/
theorem measurableSet_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) :
    MeasurableSet (matImage L⁻¹ U) := by
  rw [matImage_inv_eq_preimage hL]
  exact hU.preimage (continuous_matVecMul L).measurable

/-- Restricted volume on an affine pullback has the inverse-determinant Jacobian. -/
theorem map_restrict_volume_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) :
    Measure.map (matVecMul L) (volume.restrict (matImage L⁻¹ U)) =
      ENNReal.ofReal (|L.det|⁻¹) • volume.restrict U := by
  have hV := measurableSet_affinePullback hL hU
  rw [map_restrict_volume_matVecMul hL hV, matImage_matImage_inv hL]

/-- Pullback by an invertible matrix preserves local square integrability. -/
theorem memL2On_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) {f : Vec d → ℝ}
    (hf : MemL2On U f) :
    MemL2On (matImage L⁻¹ U) (fun y => f (matVecMul L y)) := by
  let T : Vec d → Vec d := matVecMul L
  have hmap := map_restrict_volume_affinePullback hL hU
  have hfmap : MemLp f 2
      (Measure.map T (volume.restrict (matImage L⁻¹ U))) := by
    rw [hmap]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hfmap.comp_of_map (continuous_matVecMul L).aemeasurable

private theorem gradMemL2On_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) {Du : Vec d → Vec d}
    (hDu : GradMemL2On U Du) :
    GradMemL2On (matImage L⁻¹ U)
      (fun y => matVecMul (matTranspose L) (Du (matVecMul L y))) := by
  intro i
  change MemL2On (matImage L⁻¹ U)
    (fun y => ∑ j, L j i * Du (matVecMul L y) j)
  exact memLp_finsetSum Finset.univ fun j _ =>
    (memL2On_affinePullback hL hU (hDu j)).const_mul (L j i)

private theorem contDiff_matVecMul_top (L : Mat d) :
    ContDiff ℝ (⊤ : ℕ∞) (matVecMul L) := by
  let T : Vec d →L[ℝ] Vec d :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin L)
  change ContDiff ℝ (⊤ : ℕ∞) T
  exact T.contDiff

/-- The smooth gradient obeys the transpose chain rule under a matrix map. -/
theorem smoothGrad_comp_matVecMul (L : Mat d) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec d) :
    smoothGrad (fun y => f (matVecMul L y)) x =
      matVecMul (matTranspose L) (smoothGrad f (matVecMul L x)) := by
  let T : Vec d →L[ℝ] Vec d :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin L)
  have hderiv :
      fderiv ℝ (fun y => f (matVecMul L y)) x =
        (fderiv ℝ f (matVecMul L x)).comp T := by
    calc
      fderiv ℝ (fun y => f (matVecMul L y)) x =
          (fderiv ℝ f (matVecMul L x)).comp (fderiv ℝ (matVecMul L) x) := by
        exact fderiv_comp (x := x) (hf.differentiable (by simp) (matVecMul L x))
          T.differentiableAt
      _ = (fderiv ℝ f (matVecMul L x)).comp T := by
        have hT : fderiv ℝ (matVecMul L) x = T := T.fderiv
        rw [hT]
  ext i
  change (fderiv ℝ (fun y => f (matVecMul L y)) x) (basisVec i) = _
  rw [hderiv]
  simp only [ContinuousLinearMap.comp_apply]
  change (fderiv ℝ f (matVecMul L x)) (matVecMul L (basisVec i)) = _
  rw [show matVecMul L (basisVec i) = fun j => L j i by
    change Matrix.mulVec L (Pi.single i 1) = L.col i
    exact Matrix.mulVec_single_one L i]
  change (fderiv ℝ f (matVecMul L x)) (fun j => L j i) =
    ∑ j, L j i * (fderiv ℝ f (matVecMul L x)) (basisVec j)
  rw [pi_eq_sum_univ' (fun j => L j i), map_sum]
  simp only [map_smul, smul_eq_mul, basisVec]

/-- A local test pulls back from the inverse-image domain to the original domain. -/
theorem isLocalTest_comp_matVecMul_inv {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : IsLocalTest (matImage L⁻¹ U) f) :
    IsLocalTest U (fun x => f (matVecMul L⁻¹ x)) := by
  let e : Vec d ≃ₜ Vec d :=
    { toFun := matVecMul L⁻¹
      invFun := matVecMul L
      left_inv := fun x => by
        rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one]
      right_inv := fun x => by
        rw [matVecMul_mul, Matrix.nonsing_inv_mul L hL, matVecMul_one]
      continuous_toFun := continuous_matVecMul L⁻¹
      continuous_invFun := continuous_matVecMul L }
  refine ⟨?_, ?_, ?_⟩
  · simpa [Function.comp_def] using hf.contDiff.comp (contDiff_matVecMul_top L⁻¹)
  · change HasCompactSupport (f ∘ e)
    simpa [e, Function.comp_def] using hf.hasCompactSupport.comp_homeomorph e
  · intro x hx
    have hx' : matVecMul L⁻¹ x ∈ tsupport f := by
      rw [show (fun y => f (matVecMul L⁻¹ y)) = f ∘ e by rfl,
        tsupport_comp_eq_preimage f e] at hx
      exact hx
    have hpre := hf.tsupport_subset hx'
    rw [matImage_inv_eq_preimage hL] at hpre
    simpa [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one] using hpre

/-- A local test on the original domain pulls back to the inverse-image domain. -/
theorem isLocalTest_comp_matVecMul {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} {f : Vec d → ℝ} (hf : IsLocalTest U f) :
    IsLocalTest (matImage L⁻¹ U) (fun y => f (matVecMul L y)) := by
  let e : Vec d ≃ₜ Vec d :=
    { toFun := matVecMul L
      invFun := matVecMul L⁻¹
      left_inv := fun x => by
        rw [matVecMul_mul, Matrix.nonsing_inv_mul L hL, matVecMul_one]
      right_inv := fun x => by
        rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one]
      continuous_toFun := continuous_matVecMul L
      continuous_invFun := continuous_matVecMul L⁻¹ }
  refine ⟨?_, ?_, ?_⟩
  · simpa [Function.comp_def] using hf.contDiff.comp (contDiff_matVecMul_top L)
  · change HasCompactSupport (f ∘ e)
    simpa [e, Function.comp_def] using hf.hasCompactSupport.comp_homeomorph e
  · intro y hy
    have hy' : matVecMul L y ∈ tsupport f := by
      rw [show (fun x => f (matVecMul L x)) = f ∘ e by rfl,
        tsupport_comp_eq_preimage f e] at hy
      exact hy
    rw [matImage_inv_eq_preimage hL]
    exact hf.tsupport_subset hy'

/-- An `L²` weak-gradient pair pulls back along every invertible matrix. -/
theorem hasWeakGradientOn_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) {u : Vec d → ℝ}
    {Du : Vec d → Vec d} (hu : MemL2On U u) (hDu : GradMemL2On U Du)
    (hweak : HasWeakGradientOn U u Du) :
    HasWeakGradientOn (matImage L⁻¹ U) (fun y => u (matVecMul L y))
      (fun y => matVecMul (matTranspose L) (Du (matVecMul L y))) := by
  let V : Set (Vec d) := matImage L⁻¹ U
  have hV : MeasurableSet V := measurableSet_affinePullback hL hU
  intro i φ hφsmooth hφcompact hφsub
  let ψ : Vec d → ℝ := fun x => φ (matVecMul L⁻¹ x)
  have hψ : IsLocalTest U ψ :=
    isLocalTest_comp_matVecMul_inv hL ⟨hφsmooth, hφcompact, hφsub⟩
  have hweakj := fun j => hweak j ψ hψ.contDiff hψ.hasCompactSupport hψ.tsupport_subset
  have hψderiv : ∀ j, MemL2On U (fun x => (fderiv ℝ ψ x) (basisVec j)) := by
    intro j
    have hc : Continuous (fun x => (fderiv ℝ ψ x) (basisVec j)) :=
      (hψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
    exact (hc.memLp_of_hasCompactSupport
      (hψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec j))).restrict U
  have hψmem : MemL2On U ψ :=
    (hψ.contDiff.continuous.memLp_of_hasCompactSupport hψ.hasCompactSupport).restrict U
  have hleftInt : ∀ j, IntegrableOn
      (fun x => L j i * (u x * (fderiv ℝ ψ x) (basisVec j))) U volume := by
    intro j
    exact (hu.integrable_mul (hψderiv j)).const_mul (L j i)
  have hrightInt : ∀ j, IntegrableOn
      (fun x => L j i * (Du x j * ψ x)) U volume := by
    intro j
    exact ((hDu j).integrable_mul hψmem).const_mul (L j i)
  have hsum :
      ∑ j, ∫ x in U, L j i * (u x * (fderiv ℝ ψ x) (basisVec j)) ∂volume =
        -∑ j, ∫ x in U, L j i * (Du x j * ψ x) ∂volume := by
    calc
      ∑ j, ∫ x in U, L j i * (u x * (fderiv ℝ ψ x) (basisVec j)) ∂volume =
          ∑ j, L j i * ∫ x in U, u x * (fderiv ℝ ψ x) (basisVec j) ∂volume := by
        apply Finset.sum_congr rfl
        intro j _
        rw [integral_const_mul]
      _ = ∑ j, L j i * (-∫ x in U, Du x j * ψ x ∂volume) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hweakj j]
      _ = -∑ j, L j i * ∫ x in U, Du x j * ψ x ∂volume := by
        simp only [mul_neg, Finset.sum_neg_distrib]
      _ = -∑ j, ∫ x in U, L j i * (Du x j * ψ x) ∂volume := by
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [integral_const_mul]
  have hgradInv : ∀ x,
      matVecMul (matTranspose L) (smoothGrad ψ x) =
        smoothGrad φ (matVecMul L⁻¹ x) := by
    intro x
    rw [smoothGrad_comp_matVecMul L⁻¹ hφsmooth]
    have hLT : IsUnit (matTranspose L).det := by
      simpa [matTranspose] using Matrix.isUnit_det_transpose L hL
    have hinvT : matTranspose L⁻¹ = (matTranspose L)⁻¹ := by
      simpa [matTranspose] using Matrix.transpose_nonsing_inv (A := L)
    rw [hinvT, matVecMul_mul, Matrix.mul_nonsing_inv _ hLT, matVecMul_one]
  have hcore :
      ∫ x in U, u x * smoothGrad φ (matVecMul L⁻¹ x) i ∂volume =
        -∫ x in U,
          matVecMul (matTranspose L) (Du x) i * φ (matVecMul L⁻¹ x) ∂volume := by
    calc
      ∫ x in U, u x * smoothGrad φ (matVecMul L⁻¹ x) i ∂volume =
          ∫ x in U, ∑ j, L j i * (u x * (fderiv ℝ ψ x) (basisVec j))
            ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        rw [← hgradInv x]
        simp only [smoothGrad, matVecMul, matTranspose, Matrix.transpose_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ j, ∫ x in U, L j i * (u x * (fderiv ℝ ψ x) (basisVec j))
            ∂volume := integral_finsetSum Finset.univ (fun j _ => hleftInt j)
      _ = -∑ j, ∫ x in U, L j i * (Du x j * ψ x) ∂volume := hsum
      _ = -∫ x in U, ∑ j, L j i * (Du x j * ψ x) ∂volume := by
        rw [integral_finsetSum Finset.univ (fun j _ => hrightInt j)]
      _ = -∫ x in U,
          matVecMul (matTranspose L) (Du x) i * φ (matVecMul L⁻¹ x) ∂volume := by
        apply congrArg Neg.neg
        apply integral_congr_ae
        filter_upwards with x
        simp only [ψ, matVecMul, matTranspose, Matrix.transpose_apply]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hleftChange := setIntegral_matImage hL hV
    (fun x => u x * smoothGrad φ (matVecMul L⁻¹ x) i)
  have hrightChange := setIntegral_matImage hL hV
    (fun x => matVecMul (matTranspose L) (Du x) i * φ (matVecMul L⁻¹ x))
  rw [matImage_matImage_inv hL] at hleftChange hrightChange
  simp only [matVecMul_mul, Matrix.nonsing_inv_mul L hL, matVecMul_one,
    smul_eq_mul] at hleftChange hrightChange
  rw [hleftChange, hrightChange] at hcore
  apply mul_left_cancel₀ (abs_ne_zero.mpr hL.ne_zero)
  calc
    |L.det| * ∫ x in V, u (matVecMul L x) * smoothGrad φ x i ∂volume =
        -(|L.det| * ∫ x in V,
          matVecMul (matTranspose L) (Du (matVecMul L x)) i * φ x ∂volume) := hcore
    _ = |L.det| *
        (-∫ x in V, matVecMul (matTranspose L) (Du (matVecMul L x)) i * φ x
          ∂volume) := by ring

/-- Every `H¹` witness has the exact transpose-gradient affine pullback. -/
theorem exists_h1Function_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (u : H1Function U) :
    ∃ uL : H1Function (matImage L⁻¹ U),
      uL.toFun = (fun y => u.toFun (matVecMul L y)) ∧
      uL.grad = (fun y => matVecMul (matTranspose L) (u.grad (matVecMul L y))) := by
  let uL : H1Function (matImage L⁻¹ U) :=
    { toFun := fun y => u.toFun (matVecMul L y)
      grad := fun y => matVecMul (matTranspose L) (u.grad (matVecMul L y))
      memL2 := memL2On_affinePullback hL hU u.memL2
      gradMemL2 := gradMemL2On_affinePullback hL hU u.gradMemL2
      hasWeakGradient := hasWeakGradientOn_affinePullback hL hU u.memL2
        u.gradMemL2 u.hasWeakGradient }
  exact ⟨uL, rfl, rfl⟩

end

end HighContrast
end HCPolySupport
