/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineH1a0Pairing
public import LeanPool.HighContrastHomogenization.Analytic.AffineFractionalKernel
public import LeanPool.HighContrastHomogenization.Analytic.ClassHonesty
public import LeanPool.HighContrastHomogenization.Analytic.ClosureH1a
public import LeanPool.HighContrastHomogenization.Analytic.LocalIntegrability
public import LeanPool.HighContrastHomogenization.Analytic.NormEquivalence
public import LeanPool.HighContrastHomogenization.Analytic.WeakGradientClosure
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorNormalizedL2Bridge
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.AffineLiouvilleLocal

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local Sobolev transport under an invertible linear map

Centered balls are enlarged by a fixed matrix factor before the exact affine
change of variables is applied.  The determinant factor in the transported
energy is independent of the radius.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set _root_.Filter
open scoped ENNReal Topology

noncomputable section

variable {d : ℕ}

/-- A positive coefficient controlling the Euclidean distortion of a fixed
matrix. -/
@[expose]
noncomputable def affineBallFactor (L : Mat d) : ℝ :=
  max 1 (Book.Ch02.matrixFrobeniusNormSq L)

theorem one_le_affineBallFactor (L : Mat d) :
    1 ≤ affineBallFactor L :=
  le_max_left _ _

theorem matVecMul_euclideanBall_subset_scaled
    (L : Mat d) (R : ℝ) :
    (fun y ↦ matVecMul L y) '' euclideanBall d R ⊆
      euclideanBall d (affineBallFactor L * R) := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : vecNormSq y < R ^ 2 := by
    simpa only [euclideanBall, euclideanBallAt, sub_zero] using! hy
  have hlinear :=
    Book.Ch02.vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq L y
  have hnorm : Book.Ch02.matrixFrobeniusNormSq L ≤ affineBallFactor L :=
    le_max_right _ _
  have hq : 1 ≤ affineBallFactor L := one_le_affineBallFactor L
  have hsquares : Book.Ch02.matrixFrobeniusNormSq L ≤ affineBallFactor L ^ 2 := by
    have hnonneg := Book.Ch02.matrixFrobeniusNormSq_nonneg L
    nlinarith only [hnonneg, hnorm, hq]
  simp only [euclideanBall, euclideanBallAt, sub_zero]
  exact hlinear.trans_lt ((mul_le_mul_of_nonneg_right hsquares
    (vecNormSq_nonneg y)).trans_lt (by
      simpa only [mul_pow] using
        (mul_lt_mul_of_pos_left hy'
          (sq_pos_of_pos (zero_lt_one.trans_le hq)))))

theorem euclideanBall_subset_affinePullback_scaled
    {L : Mat d} (hL : IsUnit L.det) (R : ℝ) :
    euclideanBall d R ⊆
      matImage L⁻¹ (euclideanBall d (affineBallFactor L * R)) := by
  rw [matImage_inv_eq_preimage hL]
  intro y hy
  exact matVecMul_euclideanBall_subset_scaled L R ⟨y, hy, rfl⟩

private theorem h1sNormSqOn_mono_set
    (b : CoeffField d) {U V : Set (Vec d)} (hUV : U ⊆ V)
    (u : Vec d → ℝ) (Du : Vec d → Vec d) :
    h1sNormSqOn b U u Du ≤ h1sNormSqOn b V u Du := by
  unfold h1sNormSqOn sEnergyOn
  apply add_le_add
  · gcongr
  · exact lintegral_mono_set hUV

private theorem contDiff_matVecMul_top (L : Mat d) :
    ContDiff ℝ (⊤ : ℕ∞) (matVecMul L) := by
  let T : Vec d →L[ℝ] Vec d :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin L)
  change ContDiff ℝ (⊤ : ℕ∞) T
  exact T.contDiff

/-- The local coefficient-weighted Sobolev class is preserved by an
invertible affine pullback. -/
theorem memH1sLoc_affinePullback
    {L : Mat d} (hL : IsUnit L.det)
    {b : CoeffField d} (hb : IsAELocallyUniformlyElliptic b)
    {v : Vec d → ℝ} {Dv : Vec d → Vec d}
    (hv : MemH1sLoc b v Dv) :
    MemH1sLoc (affineCoefficient L hL b)
      (fun y ↦ v (matVecMul L y))
      (fun y ↦ matVecMul (matTranspose L) (Dv (matVecMul L y))) := by
  constructor
  · have hpair := isMeasurableGradientPair_affinePullback hL
      (U := Set.univ) MeasurableSet.univ
      (by simpa only [Measure.restrict_univ] using hv.1)
    simpa only [matImage_inv_eq_preimage hL, preimage_univ,
      Measure.restrict_univ] using hpair
  · intro R hR
    let q := affineBallFactor L
    let U := euclideanBall d (q * R)
    let V := matImage L⁻¹ U
    have hq : 0 < q := zero_lt_one.trans_le (one_le_affineBallFactor L)
    have hqR : 0 < q * R := mul_pos hq hR
    have hU : MeasurableSet U := (isOpen_euclideanBall d (q * R)).measurableSet
    have hVU : euclideanBall d R ⊆ V := by
      simpa only [q, U, V] using euclideanBall_subset_affinePullback_scaled hL R
    obtain ⟨hweak, w, hw, htend⟩ := hv.2 (q * R) hqR
    have hu := integrableOn_of_memH1sLoc_class hv hqR
    have hDu := fun i ↦ integrableOn_grad_of_memH1sLoc_class hb hv hqR i
    have hweakV := hasWeakGradientOn_affinePullback_of_integrable
      hL hU hu hDu hweak
    refine ⟨hweakV.restrict (isOpen_euclideanBall d R) hVU, ?_⟩
    let wL : ℕ → Vec d → ℝ := fun n y ↦ w n (matVecMul L y)
    refine ⟨wL, ?_, ?_⟩
    · intro n
      simpa only [wL, Function.comp_def] using
        (hw n).comp (contDiff_matVecMul_top L)
    · let K : ℝ≥0∞ :=
        max ((ENNReal.ofReal |L.det|⁻¹) ^ 2) (ENNReal.ofReal |L.det|⁻¹)
      apply tendsto_zero_of_le_of_tendsto_zero
        (g := fun n ↦ K * h1sNormSqOn b U
          (fun x ↦ w n x - v x)
          (fun x ↦ smoothGrad (w n) x - Dv x))
      · intro n
        have hfull := h1sNormSqOn_affinePullback_le hL hU b
          (fun x ↦ w n x - v x)
          (fun x ↦ smoothGrad (w n) x - Dv x)
        have hgrad :
            (fun y ↦ smoothGrad (wL n) y -
              matVecMul (matTranspose L) (Dv (matVecMul L y))) =
            fun y ↦ matVecMul (matTranspose L)
              (smoothGrad (w n) (matVecMul L y) - Dv (matVecMul L y)) := by
          funext y
          rw [smoothGrad_comp_matVecMul L (hw n)]
          exact (Matrix.mulVec_sub _ _ _).symm
        have hmono := h1sNormSqOn_mono_set
          (affineCoefficient L hL b) hVU
          (fun y ↦ wL n y - v (matVecMul L y))
          (fun y ↦ smoothGrad (wL n) y -
            matVecMul (matTranspose L) (Dv (matVecMul L y)))
        rw [hgrad] at hmono
        rw [hgrad]
        exact hmono.trans (by simpa only [K, U, V, wL] using hfull)
      · have hKtop : K ≠ ⊤ := by
          dsimp only [K]
          exact max_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
            ENNReal.ofReal_ne_top
        simpa only [U, mul_zero] using
          (ENNReal.Tendsto.const_mul htend (Or.inr hKtop))

end

end Root
end HighContrast
end HCPolySupport
