/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffinePairing
public import LeanPool.HighContrastHomogenization.Analytic.AffineWeakGradient

/-!
# High-contrast homogenization: Analytic.AffineH1a0Pairing

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Affine transport for coefficient-weighted zero-trace data

The inverse-image convention for an invertible linear change of variables
transports measurable gradient pairs, weak gradients with locally integrable
components, and the unnormalized symmetric energy with its exact Jacobian.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- An unnormalized nonnegative integral on an affine pullback carries the
inverse-determinant Jacobian, without a measurability assumption on the
integrand. -/
theorem lintegral_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (f : Vec d → ℝ≥0∞) :
    (∫⁻ y in matImage L⁻¹ U, f (matVecMul L y) ∂volume) =
      ENNReal.ofReal |L.det|⁻¹ * ∫⁻ x in U, f x ∂volume := by
  have hmap := map_restrict_volume_affinePullback hL hU
  calc
    (∫⁻ y in matImage L⁻¹ U, f (matVecMul L y) ∂volume) =
        ∫⁻ x, f x ∂Measure.map (matVecMul L)
          (volume.restrict (matImage L⁻¹ U)) :=
      (measurableEmbedding_matVecMul hL).lintegral_map f |>.symm
    _ = ENNReal.ofReal |L.det|⁻¹ * ∫⁻ x in U, f x ∂volume := by
      rw [hmap, lintegral_smul_measure]
      rfl

/-- Measurability of a function-gradient pair is preserved by the affine
pullback and the transpose action on its gradient. -/
theorem isMeasurableGradientPair_affinePullback {L : Mat d}
    (hL : IsUnit L.det) {U : Set (Vec d)} (hU : MeasurableSet U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hpair : IsMeasurableGradientPair (volume.restrict U) u Du) :
    IsMeasurableGradientPair (volume.restrict (matImage L⁻¹ U))
      (fun y ↦ u (matVecMul L y))
      (fun y ↦ matVecMul (matTranspose L) (Du (matVecMul L y))) := by
  have hq : Measure.QuasiMeasurePreserving (matVecMul L)
      (volume.restrict (matImage L⁻¹ U)) (volume.restrict U) := by
    refine ⟨(continuous_matVecMul L).measurable, ?_⟩
    rw [map_restrict_volume_affinePullback hL hU]
    exact Measure.AbsolutelyContinuous.rfl.smul_left _
  refine ⟨hpair.1.comp_quasiMeasurePreserving hq, fun i ↦ ?_⟩
  change AEStronglyMeasurable
    (fun y ↦ ∑ j, L j i * Du (matVecMul L y) j)
      (volume.restrict (matImage L⁻¹ U))
  exact Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ ↦
    ((hpair.2 j).comp_quasiMeasurePreserving hq).const_mul (L j i)

/-- An affine pullback preserves a weak gradient when the function and every
gradient component are integrable on the source domain. -/
theorem hasWeakGradientOn_affinePullback_of_integrable {L : Mat d}
    (hL : IsUnit L.det) {U : Set (Vec d)} (hU : MeasurableSet U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : IntegrableOn u U volume)
    (hDu : ∀ i, IntegrableOn (fun x ↦ Du x i) U volume)
    (hweak : HasWeakGradientOn U u Du) :
    HasWeakGradientOn (matImage L⁻¹ U) (fun y ↦ u (matVecMul L y))
      (fun y ↦ matVecMul (matTranspose L) (Du (matVecMul L y))) := by
  let V : Set (Vec d) := matImage L⁻¹ U
  have hV : MeasurableSet V := measurableSet_affinePullback hL hU
  intro i φ hφsmooth hφcompact hφsub
  let ψ : Vec d → ℝ := fun x ↦ φ (matVecMul L⁻¹ x)
  have hψ : IsLocalTest U ψ :=
    isLocalTest_comp_matVecMul_inv hL ⟨hφsmooth, hφcompact, hφsub⟩
  have hweakj := fun j ↦ hweak j ψ hψ.contDiff hψ.hasCompactSupport hψ.tsupport_subset
  have hψderiv : ∀ j, MemLp (fun x ↦ (fderiv ℝ ψ x) (basisVec j)) ∞
      (volume.restrict U) := by
    intro j
    have hc : Continuous (fun x ↦ (fderiv ℝ ψ x) (basisVec j)) :=
      (hψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
    exact (hc.memLp_of_hasCompactSupport
      (hψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec j))).restrict U
  have hψmem : MemLp ψ ∞ (volume.restrict U) :=
    (hψ.contDiff.continuous.memLp_of_hasCompactSupport hψ.hasCompactSupport).restrict U
  have hleftInt : ∀ j, IntegrableOn
      (fun x ↦ L j i * (u x * (fderiv ℝ ψ x) (basisVec j))) U volume := by
    intro j
    exact (hu.mul_of_top_left (hψderiv j)).const_mul (L j i)
  have hrightInt : ∀ j, IntegrableOn
      (fun x ↦ L j i * (Du x j * ψ x)) U volume := by
    intro j
    exact ((hDu j).mul_of_top_left hψmem).const_mul (L j i)
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
            ∂volume := integral_finsetSum Finset.univ (fun j _ ↦ hleftInt j)
      _ = -∑ j, ∫ x in U, L j i * (Du x j * ψ x) ∂volume := hsum
      _ = -∫ x in U, ∑ j, L j i * (Du x j * ψ x) ∂volume := by
        rw [integral_finsetSum Finset.univ (fun j _ ↦ hrightInt j)]
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
    (fun x ↦ u x * smoothGrad φ (matVecMul L⁻¹ x) i)
  have hrightChange := setIntegral_matImage hL hV
    (fun x ↦ matVecMul (matTranspose L) (Du x) i * φ (matVecMul L⁻¹ x))
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

/-- The symmetric energy of a transpose-transformed field has the exact
inverse-determinant Jacobian on the affine pullback domain. -/
theorem sEnergyOn_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (b : CoeffField d)
    (F : Vec d → Vec d) :
    sEnergyOn (affineCoefficient L hL b) (matImage L⁻¹ U)
        (fun y ↦ matVecMul (matTranspose L) (F (matVecMul L y))) =
      ENNReal.ofReal |L.det|⁻¹ * sEnergyOn b U F := by
  unfold sEnergyOn
  calc
    (∫⁻ y in matImage L⁻¹ U,
        ENNReal.ofReal
          (vecDot (matVecMul (matTranspose L) (F (matVecMul L y)))
            (matVecMul (symmPart (affineCoefficient L hL b y))
              (matVecMul (matTranspose L) (F (matVecMul L y))))) ∂volume) =
        ∫⁻ y in matImage L⁻¹ U,
          ENNReal.ofReal
            (vecDot (F (matVecMul L y))
              (matVecMul (symmPart (b (matVecMul L y))) (F (matVecMul L y))))
            ∂volume := by
      apply lintegral_congr
      intro y
      rw [affineCoefficient_symmetric_energy hL]
    _ = ENNReal.ofReal |L.det|⁻¹ *
        ∫⁻ x in U,
          ENNReal.ofReal
            (vecDot (F x) (matVecMul (symmPart (b x)) (F x))) ∂volume :=
      lintegral_affinePullback hL hU
        (fun x ↦ ENNReal.ofReal
          (vecDot (F x) (matVecMul (symmPart (b x)) (F x))))

/-- The full symmetric Sobolev quantity obeys the sharp two-term Jacobian
formula under affine pullback. -/
theorem h1sNormSqOn_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (b : CoeffField d)
    (u : Vec d → ℝ) (Du : Vec d → Vec d) :
    h1sNormSqOn (affineCoefficient L hL b) (matImage L⁻¹ U)
        (fun y ↦ u (matVecMul L y))
        (fun y ↦ matVecMul (matTranspose L) (Du (matVecMul L y))) =
      (ENNReal.ofReal |L.det|⁻¹ *
          ∫⁻ x in U, ENNReal.ofReal |u x| ∂volume) ^ 2 +
        ENNReal.ofReal |L.det|⁻¹ * sEnergyOn b U Du := by
  unfold h1sNormSqOn
  change ((∫⁻ y in matImage L⁻¹ U,
      ENNReal.ofReal |u (matVecMul L y)| ∂volume) ^ 2 +
      sEnergyOn (affineCoefficient L hL b) (matImage L⁻¹ U)
        (fun y ↦ matVecMul (matTranspose L) (Du (matVecMul L y)))) = _
  have huL := lintegral_affinePullback hL hU
    (fun x ↦ ENNReal.ofReal |u x|)
  rw [huL, sEnergyOn_affinePullback hL hU]

/-- A single finite determinant factor controls both terms of the transported
coefficient-weighted Sobolev quantity. -/
theorem h1sNormSqOn_affinePullback_le {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (b : CoeffField d)
    (u : Vec d → ℝ) (Du : Vec d → Vec d) :
    h1sNormSqOn (affineCoefficient L hL b) (matImage L⁻¹ U)
        (fun y ↦ u (matVecMul L y))
        (fun y ↦ matVecMul (matTranspose L) (Du (matVecMul L y))) ≤
      max ((ENNReal.ofReal |L.det|⁻¹) ^ 2) (ENNReal.ofReal |L.det|⁻¹) *
        h1sNormSqOn b U u Du := by
  rw [h1sNormSqOn_affinePullback hL hU]
  unfold h1sNormSqOn
  let q : ℝ≥0∞ := ENNReal.ofReal |L.det|⁻¹
  let A : ℝ≥0∞ := ∫⁻ x in U, ENNReal.ofReal |u x| ∂volume
  let B : ℝ≥0∞ := sEnergyOn b U Du
  change (q * A) ^ 2 + q * B ≤ max (q ^ 2) q * (A ^ 2 + B)
  rw [mul_pow, mul_add]
  exact add_le_add
    (by gcongr; exact le_max_left (q ^ 2) q)
    (by gcongr; exact le_max_right (q ^ 2) q)

end

end HighContrast
end HCPolySupport
