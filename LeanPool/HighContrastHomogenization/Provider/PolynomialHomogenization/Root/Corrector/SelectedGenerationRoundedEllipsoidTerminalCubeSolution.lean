/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedAnalyticGeometry
public import LeanPool.HighContrastHomogenization.Analytic.EllipsoidGeometry
public import LeanPool.HighContrastHomogenization.Provider.Regularity.H1aOpenSubsetGradientRealization
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleCubeRestriction
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedEllipsoidTriadicGeometry
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedWeakSolutionPullback
public import LeanPool.HighContrastHomogenization.Support.Probability.LocalEllipticitySlices
public import LeanPool.HighContrastHomogenization.Analytic.CoefficientLocality

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector
.SelectedGenerationRoundedEllipsoidTerminalCubeSolution

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Terminal ellipsoid solution at a selected rounded generation

The printed-order recurrence selects a rounded generation after its analytic
constant is known.  This file transports a physical weak solution through
that selected matrix and packages the terminal origin-cube solution used by
the finite recurrence.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set
open scoped Matrix MatrixOrder

noncomputable section


variable {d : ℕ} [NeZero d]

/-- The inverse image of a physical ellipsoid under a selected rounded grid. -/
@[expose]
def selectedRoundedPullbackEllipsoid
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (r : ℝ) : Set (Vec d) :=
  matImage (geom.grid (symmPart abar))⁻¹ (ellipsoid abar r)

/-- The physical image of an origin cube under a selected rounded grid. -/
@[expose]
def selectedRoundedPhysicalCube
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (m : ℤ) : Set (Vec d) :=
  matImage (geom.grid (symmPart abar)) (openCubeSet (originCube d m))

omit [NeZero d] in
private theorem vecDot_matVecMul_smul_one_selected
    (c : ℝ) (x : Vec d) :
    vecDot x (matVecMul (c • (1 : Mat d)) x) = c * vecNormSq x := by
  have hone : matVecMul (1 : Mat d) x = x := by
    funext i
    simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  rw [smul_matVecMul, hone, vecDot_smul_right]
  rfl

omit [NeZero d] in
private theorem vecDot_matVecMul_le_of_matrix_le_selected
    {A B : Mat d} (h : A ≤ B) (x : Vec d) :
    vecDot x (matVecMul A x) ≤ vecDot x (matVecMul B x) := by
  have hdiff : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hx := hdiff.dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, dotProduct_sub] at hx
  change x ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ B *ᵥ x
  simp only [star_trivial] at hx
  linarith only [hx]

private theorem selectedRoundedReferenceMatrix_inv_le
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    (geom.referenceMatrix abar hS)⁻¹ ≤
      (100 / 99 : ℝ) • (1 : Mat d) := by
  have hlower := geom.reference_lower abar hS
  have hB : (geom.referenceMatrix abar hS).PosDef :=
    geom.reference_posDef abar hS
  have hscalar : ((99 / 100 : ℝ) • (1 : Mat d)).PosDef :=
    Matrix.PosDef.one.smul (by norm_num)
  have h := inv_le_inv_of_le hscalar hB hlower
  rw [inv_smul_of_isUnit (by norm_num : (99 / 100 : ℝ) ≠ 0)
    (by simp : IsUnit (1 : Mat d).det), inv_one] at h
  norm_num at h ⊢
  exact h

private theorem vecDot_selectedRoundedReferenceMatrix_inv_grid_inv
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) (x : Vec d) :
    vecDot
        (matVecMul (geom.grid (symmPart abar))⁻¹ x)
        (matVecMul (geom.referenceMatrix abar hS)⁻¹
          (matVecMul (geom.grid (symmPart abar))⁻¹ x)) =
      (specBound ((symmPart abar)⁻¹))⁻¹ *
        vecDot x (matVecMul (symmPart abar)⁻¹ x) := by
  let Q : Mat d := geom.grid (symmPart abar)
  let S : Mat d := symmPart abar
  let mu : ℝ := specBound S⁻¹
  let B : Mat d := geom.referenceMatrix abar hS
  have hQ : IsUnit Q.det := by
    simpa only [Q] using geom.grid_det_isUnit hS
  have hSdet : IsUnit S.det := isUnit_det_of_posDef hS
  have hmu : mu ≠ 0 :=
    (specBound_inv_symmPart_pos (NeZero.pos d) hS).ne'
  have hQT : matTranspose Q = Q := by
    simpa only [Q] using geom.grid_transpose hS
  have hQinvT : matTranspose Q⁻¹ = Q⁻¹ := by
    have hQherm : Qᴴ = Q := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, matTranspose]
        using hQT
    have hQinvHerm : (Q⁻¹)ᴴ = Q⁻¹ := by
      rw [Matrix.conjTranspose_nonsing_inv, hQherm]
    simpa only [matTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hQinvHerm
  have hBform : B = Q⁻¹ * (mu • S) * Q⁻¹ := by
    dsimp only [B, RoundedGenerationAnalyticGeometry.referenceMatrix,
      roundedReferenceMatrixAtGeneration]
    have hQinvT' :
        matTranspose (roundedGrid geom.generation (symmPart abar))⁻¹ =
          (roundedGrid geom.generation (symmPart abar))⁻¹ := by
      simpa only [Q, RoundedGenerationAnalyticGeometry.grid] using hQinvT
    rw [hQinvT']
    rfl
  have hscaledInv : (mu • S)⁻¹ = mu⁻¹ • S⁻¹ :=
    inv_smul_of_isUnit hmu hSdet
  have hBinv : B⁻¹ = Q * (mu⁻¹ • S⁻¹) * Q := by
    rw [hBform, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv Q hQ, hscaledInv]
    noncomm_ring
  change
    vecDot (matVecMul Q⁻¹ x)
        (matVecMul B⁻¹ (matVecMul Q⁻¹ x)) =
      mu⁻¹ * vecDot x (matVecMul S⁻¹ x)
  rw [hBinv]
  have hmatrix :
      (Q * (mu⁻¹ • S⁻¹) * Q) * Q⁻¹ =
        Q * (mu⁻¹ • S⁻¹) := by
    noncomm_ring [Matrix.mul_nonsing_inv Q hQ]
  have haction :
      matVecMul (Q * (mu⁻¹ • S⁻¹) * Q) (matVecMul Q⁻¹ x) =
        matVecMul Q (matVecMul (mu⁻¹ • S⁻¹) x) := by
    rw [matVecMul_mul, matVecMul_mul, hmatrix]
  rw [haction]
  calc
    vecDot (matVecMul Q⁻¹ x)
        (matVecMul Q (matVecMul (mu⁻¹ • S⁻¹) x)) =
        vecDot (matVecMul Q⁻¹ x)
          (matVecMul (matTranspose Q)
            (matVecMul (mu⁻¹ • S⁻¹) x)) := by rw [hQT]
    _ = vecDot (matVecMul Q (matVecMul Q⁻¹ x))
          (matVecMul (mu⁻¹ • S⁻¹) x) :=
      vecDot_matVecMul_transpose _ _ Q
    _ = vecDot x (matVecMul (mu⁻¹ • S⁻¹) x) := by
      rw [matVecMul_mul, Matrix.mul_nonsing_inv Q hQ, matVecMul_one]
    _ = mu⁻¹ * vecDot x (matVecMul S⁻¹ x) := by
      rw [smul_matVecMul, vecDot_smul_right]

/-- The selected rounded pullback has the exact quadratic sublevel-set form. -/
theorem selectedRoundedPullbackEllipsoid_eq
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) (r : ℝ) :
    selectedRoundedPullbackEllipsoid geom abar r =
      {y : Vec d |
        vecDot y (matVecMul (geom.referenceMatrix abar hS)⁻¹ y) ≤ r ^ 2} := by
  let Q : Mat d := geom.grid (symmPart abar)
  have hQ : IsUnit Q.det := geom.grid_det_isUnit hS
  rw [selectedRoundedPullbackEllipsoid, matImage_inv_eq_preimage hQ]
  ext y
  change
    vecDot (matVecMul Q y)
          (matVecMul (symmPart abar)⁻¹ (matVecMul Q y)) ≤
        specBound ((symmPart abar)⁻¹) * r ^ 2 ↔
      vecDot y (matVecMul (geom.referenceMatrix abar hS)⁻¹ y) ≤ r ^ 2
  have hmu : 0 < specBound ((symmPart abar)⁻¹) :=
    specBound_inv_symmPart_pos (NeZero.pos d) hS
  have hform :=
    vecDot_selectedRoundedReferenceMatrix_inv_grid_inv geom abar hS
      (matVecMul Q y)
  change
    vecDot (matVecMul Q⁻¹ (matVecMul Q y))
        (matVecMul (geom.referenceMatrix abar hS)⁻¹
          (matVecMul Q⁻¹ (matVecMul Q y))) =
      (specBound ((symmPart abar)⁻¹))⁻¹ *
        vecDot (matVecMul Q y)
          (matVecMul (symmPart abar)⁻¹ (matVecMul Q y)) at hform
  have hcancel : matVecMul Q⁻¹ (matVecMul Q y) = y := by
    rw [matVecMul_mul, Matrix.nonsing_inv_mul Q hQ, matVecMul_one]
  rw [hcancel] at hform
  rw [hform]
  constructor
  · intro h
    calc
      (specBound ((symmPart abar)⁻¹))⁻¹ *
          vecDot (matVecMul Q y)
            (matVecMul (symmPart abar)⁻¹ (matVecMul Q y)) ≤
          (specBound ((symmPart abar)⁻¹))⁻¹ *
            (specBound ((symmPart abar)⁻¹) * r ^ 2) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hmu.le)
      _ = r ^ 2 := by field_simp [hmu.ne']
  · intro h
    calc
      vecDot (matVecMul Q y)
          (matVecMul (symmPart abar)⁻¹ (matVecMul Q y)) =
          specBound ((symmPart abar)⁻¹) *
            ((specBound ((symmPart abar)⁻¹))⁻¹ *
              vecDot (matVecMul Q y)
                (matVecMul (symmPart abar)⁻¹ (matVecMul Q y))) := by
        field_simp [hmu.ne']
      _ ≤ specBound ((symmPart abar)⁻¹) * r ^ 2 :=
        mul_le_mul_of_nonneg_left h hmu.le

/-- The standard interior terminal cube lies inside the selected-generation
pullback ellipsoid. -/
theorem openCube_terminalGeneration_subset_selectedRoundedPullbackEllipsoid
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {R : ℝ} (hR : 0 < R) :
    openCubeSet (originCube d
      (roundedEllipsoidTerminalGeneration (d := d) R hR)) ⊆
      selectedRoundedPullbackEllipsoid geom abar R := by
  rw [selectedRoundedPullbackEllipsoid_eq geom abar hS R]
  let m : ℤ := roundedEllipsoidTerminalGeneration (d := d) R hR
  have hdNat : 0 < d := NeZero.pos d
  have hd : (0 : ℝ) < d := by exact_mod_cast hdNat
  have hscale : (3 : ℝ) ^ m < 3 * (R / (100 * (d : ℝ))) := by
    simpa only [m, roundedEllipsoidTerminalGeneration] using
      outerTriadicGeneration_scale_lt_three_mul
        (show 0 < R / (100 * (d : ℝ)) by positivity)
  intro y hy
  have hcenter : cubeCenter (originCube d m) = (0 : Vec d) := by
    funext i
    simp only [cubeCenter, originCube, Pi.zero_apply, Int.cast_zero, zero_mul]
  have hmetric :
      y ∈ Metric.ball (0 : Vec d) (cubeRadius (originCube d m)) := by
    rw [← hcenter, ball_cubeCenter_eq_openCubeSet]
    exact hy
  have hnorm := vecNormSq_sub_le_of_mem_metricBall hmetric
  have hnorm' :
      vecNormSq y ≤ (d : ℝ) * ((1 / 2 : ℝ) * (3 : ℝ) ^ m) ^ 2 := by
    simpa only [sub_zero, cubeRadius, cubeScaleFactor_originCube] using hnorm
  have hquad := vecDot_matVecMul_le_of_matrix_le_selected
    (selectedRoundedReferenceMatrix_inv_le geom abar hS) y
  rw [vecDot_matVecMul_smul_one_selected] at hquad
  have hmScale : 0 ≤ (3 : ℝ) ^ m := by positivity
  have hscaleSq :
      ((3 : ℝ) ^ m) ^ 2 <
        (3 * (R / (100 * (d : ℝ)))) ^ 2 := by
    simpa only [pow_two] using mul_self_lt_mul_self hmScale hscale
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hdNat
  have hdiv : R ^ 2 / (d : ℝ) ≤ R ^ 2 :=
    div_le_self (sq_nonneg R) hdOne
  have hnormBound : vecNormSq y < (99 / 100 : ℝ) * R ^ 2 := by
    calc
      vecNormSq y ≤
          (d : ℝ) * ((1 / 2 : ℝ) * (3 : ℝ) ^ m) ^ 2 := hnorm'
      _ = (d : ℝ) * (1 / 4 : ℝ) * (((3 : ℝ) ^ m) ^ 2) := by ring
      _ < (d : ℝ) * (1 / 4 : ℝ) *
          (3 * (R / (100 * (d : ℝ)))) ^ 2 :=
        mul_lt_mul_of_pos_left hscaleSq (by positivity)
      _ = (9 / 40000 : ℝ) * (R ^ 2 / (d : ℝ)) := by
        field_simp [ne_of_gt hd]
        ring
      _ ≤ (9 / 40000 : ℝ) * R ^ 2 :=
        mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ < (99 / 100 : ℝ) * R ^ 2 :=
        mul_lt_mul_of_pos_right (by norm_num) (sq_pos_of_pos hR)
  exact (calc
      vecDot y (matVecMul (geom.referenceMatrix abar hS)⁻¹ y) ≤
          (100 / 99 : ℝ) * vecNormSq y := hquad
      _ < (100 / 99 : ℝ) * ((99 / 100 : ℝ) * R ^ 2) :=
        mul_lt_mul_of_pos_left hnormBound (by norm_num)
      _ = R ^ 2 := by ring).le

/-- The selected terminal physical cube lies in the original ellipsoid. -/
theorem selectedRoundedPhysicalCube_terminalGeneration_subset_ellipsoid
    (geom : RoundedGenerationAnalyticGeometry d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {R : ℝ} (hR : 0 < R) :
    selectedRoundedPhysicalCube geom abar
        (roundedEllipsoidTerminalGeneration (d := d) R hR) ⊆
      ellipsoid abar R := by
  let Q : Mat d := geom.grid (symmPart abar)
  let m : ℤ := roundedEllipsoidTerminalGeneration (d := d) R hR
  have hQ : IsUnit Q.det := geom.grid_det_isUnit hS
  have hpre :=
    openCube_terminalGeneration_subset_selectedRoundedPullbackEllipsoid
      geom abar hS hR
  change openCubeSet (originCube d m) ⊆ matImage Q⁻¹ (ellipsoid abar R)
    at hpre
  rw [matImage_inv_eq_preimage hQ] at hpre
  rintro x ⟨y, hy, rfl⟩
  exact hpre hy

private theorem isWeakSolutionOn_selectedRoundedCenteredPullback_iff
    (geom : RoundedGenerationAnalyticGeometry d)
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {U : Set (Vec d)}
    (hU : IsOpen U) (a : CoeffField d) {u : Vec d → ℝ}
    {Du : Vec d → Vec d} (hu : MemScalarL2 U u)
    (hDu : ∀ i, MemScalarL2 U fun x ↦ Du x i)
    (hweak : HasWeakGradientOn U u Du) :
    IsWeakSolutionOn a U Du ↔
      IsWeakSolutionOn
        (roundedCenteredCoefficientAtGeneration
          geom.generation geom.admissible abar hS a)
        (matImage (geom.grid (symmPart abar))⁻¹ U)
        (fun y ↦ matVecMul (geom.grid (symmPart abar))
          (Du (matVecMul (geom.grid (symmPart abar)) y))) := by
  let Q : Mat d := geom.grid (symmPart abar)
  let b : CoeffField d := fun x ↦ a x - skewPart abar
  let mu : ℝ := specBound ((symmPart abar)⁻¹)
  have hQ : IsUnit Q.det := geom.grid_det_isUnit hS
  have hmu : mu ≠ 0 :=
    (specBound_inv_symmPart_pos (NeZero.pos d) hS).ne'
  have hk : IsSkewMat (skewPart abar) := matTranspose_skewPart abar
  have hfield : (fun x ↦ b x + skewPart abar) = a := by
    funext x
    simp only [b, sub_add_cancel]
  have hgauge :=
    isWeakSolutionOn_add_constSkew_iff hU b hu hDu hweak
      (skewPart abar) hk
  rw [hfield] at hgauge
  have hscale :=
    (isWeakSolutionOn_smul_coefficient_iff (U := U) b Du hmu).symm
  have haffine := isWeakSolutionOn_affinePullback_iff
    hQ hU.measurableSet (fun x ↦ mu • b x) Du
  have hchain := hgauge.trans (hscale.trans haffine)
  have htranspose : matTranspose Q = Q := geom.grid_transpose hS
  rw [htranspose] at hchain
  simpa only [b, mu, Q, roundedCenteredCoefficientAtGeneration,
    RoundedGenerationAnalyticGeometry.grid] using hchain

/-- A physical weak solution gives the terminal Chapter 3 cube solution at
the selected rounded generation. -/
theorem exists_roundedEllipsoidTerminalCubeSolutionAtGeneration
    (geom : RoundedGenerationAnalyticGeometry d)
    (a : CoeffSpace d) (abar : Mat d) (hS : (symmPart abar).PosDef)
    (aRounded : Book.Ch03.CoeffFamily d)
    (hRoundedAE : ∀ Q : TriadicCube d,
      (aRounded.coeffOn Q).toCoeffField =ᵐ[volume]
        roundedCenteredCoefficientAtGeneration
          geom.generation geom.admissible abar hS (⇑a.1))
    {R : ℝ} (hR : 0 < R)
    (u : Vec d → ℝ) (Du : Vec d → Vec d)
    (hu : MemH1a (⇑a.1 : CoeffField d) (ellipsoid abar R) u Du)
    (hweak : IsWeakSolutionOn (⇑a.1 : CoeffField d)
      (ellipsoid abar R) Du) :
    ∃ w : Book.Ch03.CubeSolution
        (originCube d
          (roundedEllipsoidTerminalGeneration (d := d) R hR)) aRounded,
      w.toH1.grad =
        fun y ↦ matVecMul (geom.grid (symmPart abar))
          (Du (matVecMul (geom.grid (symmPart abar)) y)) := by
  let Qmat : Mat d := geom.grid (symmPart abar)
  let m : ℤ := roundedEllipsoidTerminalGeneration (d := d) R hR
  let Q : TriadicCube d := originCube d m
  let U : Set (Vec d) := selectedRoundedPhysicalCube geom abar m
  have hQmat : IsUnit Qmat.det := geom.grid_det_isUnit hS
  have hUform : U = matImage Qmat (openCubeSet Q) := rfl
  have hUdomain : IsOpenBoundedConvexDomain U := by
    rw [hUform]
    exact isOpenBoundedConvexDomain_matImage hQmat
      (isOpenBoundedConvexDomain_openCubeSet Q)
  let : IsFiniteMeasure (volumeMeasureOn U) :=
    hUdomain.isFiniteMeasure_restrict_volume
  have hUsub : U ⊆ ellipsoid abar R := by
    simpa only [U, m] using
      selectedRoundedPhysicalCube_terminalGeneration_subset_ellipsoid
        geom abar hS hR
  obtain ⟨lam, Lam, c, hlam, _hlamLam, hell, hac⟩ :=
    a.2.exists_ae_isEllipticMatrix_ae_eq_restrict (isBounded_ellipsoid hS R)
  obtain ⟨uPhysical, huPhysicalGrad⟩ :=
    isPotentialOn_grad_on_openSubset_of_memH1a hUdomain hUsub
      (isBounded_ellipsoid hS R) hlam hell ((memH1a_congr_coeff hac u Du).mp hu)
  have hweakU : IsWeakSolutionOn (⇑a.1 : CoeffField d) U uPhysical.grad := by
    have hrestricted := hweak.mono hUsub
    simpa only [huPhysicalGrad] using hrestricted
  have hdomain : matImage Qmat⁻¹ U = openCubeSet Q := by
    rw [hUform]
    exact matImage_inv_matImage hQmat (openCubeSet Q)
  have hweakPullRaw :=
    (isWeakSolutionOn_selectedRoundedCenteredPullback_iff
      geom hS hUdomain.isOpen (⇑a.1 : CoeffField d)
      uPhysical.memL2 uPhysical.gradMemL2
      uPhysical.hasWeakGradient).mp hweakU
  have hPullbackRaw :
      ∃ uRounded : H1Function (matImage Qmat⁻¹ U),
        uRounded.toFun =
            (fun y ↦ uPhysical.toFun (matVecMul Qmat y)) ∧
          uRounded.grad =
            (fun y ↦ matVecMul (matTranspose Qmat)
              (uPhysical.grad (matVecMul Qmat y))) :=
    exists_h1Function_affinePullback hQmat
      hUdomain.isOpen.measurableSet uPhysical
  rw [hdomain] at hPullbackRaw
  obtain ⟨uRounded, _huRoundedFun, huRoundedGradRaw⟩ := hPullbackRaw
  have htranspose : matTranspose Qmat = Qmat := geom.grid_transpose hS
  have huRoundedGrad : uRounded.grad =
      fun y ↦ matVecMul Qmat (Du (matVecMul Qmat y)) := by
    rw [huRoundedGradRaw, htranspose, huPhysicalGrad]
  have hweakRoundedRaw :
      IsWeakSolutionOn
        (roundedCenteredCoefficientAtGeneration
          geom.generation geom.admissible abar hS (⇑a.1))
        (openCubeSet Q) uRounded.grad := by
    rw [huRoundedGrad]
    simpa only [Qmat, hdomain, huPhysicalGrad] using hweakPullRaw
  have hcoeffAE :
      roundedCenteredCoefficientAtGeneration
          geom.generation geom.admissible abar hS (⇑a.1) =ᵐ[
        volume.restrict (openCubeSet Q)]
          (aRounded.coeffOn Q).toCoeffField :=
    ae_restrict_of_ae (hRoundedAE Q).symm
  have hweakRounded :
      IsWeakSolutionOn (aRounded.coeffOn Q).toCoeffField
        (openCubeSet Q) uRounded.grad :=
    hweakRoundedRaw.congr_ae hcoeffAE _root_.Filter.EventuallyEq.rfl
  have hEll : IsAEEllipticFieldOn
      (aRounded.coeffOn Q).lam (aRounded.coeffOn Q).Lam
      (openCubeSet Q) (aRounded.coeffOn Q).toCoeffField := by
    refine ⟨measurableSet_openCubeSet Q, ?_, ?_⟩
    · intro i j
      simpa only [Book.Ch02.cubeDomain_coe] using
        (aRounded.coeffOn Q).aeStronglyMeasurable i j
    · simpa only [Book.Ch02.cubeDomain_coe] using
        (aRounded.coeffOn Q).aeElliptic
  have hflux : MemVectorL2 (openCubeSet Q)
      (fun x ↦ matVecMul ((aRounded.coeffOn Q).toCoeffField x)
        (uRounded.grad x)) :=
    hEll.memVectorL2_matVecMul uRounded.grad_memVectorL2
  have hsolenoidal : IsSolenoidalOn (openCubeSet Q)
      (fun x ↦ matVecMul ((aRounded.coeffOn Q).toCoeffField x)
        (uRounded.grad x)) := by
    apply IsSolenoidalOn.of_test_of_contDiff_of_memVectorL2
      hflux (isOpen_openCubeSet Q)
    intro psi hsmooth hcompact hsupport
    have hzero := (hweakRounded psi ⟨hsmooth, hcompact, hsupport⟩).2
    change ∫ x in openCubeSet Q,
      vecDot (matVecMul ((aRounded.coeffOn Q).toCoeffField x)
          (uRounded.grad x)) (smoothGrad psi x) ∂volume = 0
    simpa only [vecDot_comm] using hzero
  let w : Book.Ch03.CubeSolution Q aRounded :=
    { toH1 := uRounded
      isHarmonic := ⟨uRounded.isPotentialOn, hsolenoidal⟩ }
  exact ⟨w, by simpa only [w, Qmat] using huRoundedGrad⟩

end

end Root
end HighContrast
end HCPolySupport
