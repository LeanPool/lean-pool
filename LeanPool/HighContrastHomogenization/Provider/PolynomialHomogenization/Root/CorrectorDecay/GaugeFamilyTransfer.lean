/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.CanonicalGaugeSpine
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.JointNegOnePower
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.GaugeAffineFactor
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.AEEq
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedCenteredCoeffSpace
public import LeanPool.HighContrastHomogenization.Analytic.AffineFields
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorRealRadiusBallGeometry
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.CorrectorDecayRestrictionComposition
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1EquivariantPullbackEliminator
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1NormalizedRootEllipsoidGeometry

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.GaugeFamilyTransfer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Projective normalization cancels between the two inverse affine factors
and the centered coefficient. -/
theorem normalizedRoot_centered_conjugation
    {d : ℕ} [NeZero d] {abar A : Mat d}
    (hS : (symmPart abar).PosDef) :
    (Selection.normalizedRoot (symmPart abar))⁻¹ *
          (specBound ((symmPart abar)⁻¹) • A) *
        matTranspose (Selection.normalizedRoot (symmPart abar))⁻¹ =
      (matSqrt (symmPart abar))⁻¹ * A *
        matTranspose (matSqrt (symmPart abar))⁻¹ := by
  let S : Mat d := symmPart abar
  let mu : ℝ := specBound S⁻¹
  let c : ℝ := Real.sqrt mu
  let L : Mat d := matSqrt S
  have hmu : 0 < mu := by
    simpa only [mu, S] using normalizedRootScale_pos hS
  have hc : 0 < c := Real.sqrt_pos.mpr hmu
  have hcSq : c * c = mu := Real.mul_self_sqrt hmu.le
  have hInv : (Selection.normalizedRoot S)⁻¹ = c⁻¹ • L⁻¹ := by
    dsimp only [c, mu, L]
    rw [Selection.normalizedRoot_eq]
    exact nonsing_inv_smul _ hc.ne' (isUnit_det_matSqrt hS)
  have hcoef : c⁻¹ * mu * c⁻¹ = 1 := by
    rw [← hcSq]
    field_simp [hc.ne']
  have htranspose : matTranspose (c⁻¹ • L⁻¹) =
      c⁻¹ • matTranspose L⁻¹ := by
    simpa only [matTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.transpose_smul c⁻¹ L⁻¹
  rw [hInv, htranspose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show c⁻¹ * (mu * c⁻¹) = c⁻¹ * mu * c⁻¹ by ring, hcoef,
    one_smul]

/-- The certificate family in normalized-root coordinates is the literal
square-root-gauge coefficient almost everywhere. -/
theorem exactGaugeCoeff_ae
    {d : ℕ} [NeZero d] {a : CoeffSpace d} {abar : Mat d}
    (hS : (symmPart abar).PosDef) (Q : TriadicCube d)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ R : TriadicCube d,
      (aRef.coeffOn R).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ⇑(normalizedCenteredCoeff a abar hS).1) :
    (aRef.coeffOn Q).toCoeffField =ᵐ[volume]
      fun y ↦
        (matSqrt (symmPart abar))⁻¹ *
          ((a.1 (matVecMul (Selection.normalizedRoot (symmPart abar)) y) : Mat d) -
            skewPart abar) *
          matTranspose (matSqrt (symmPart abar))⁻¹ := by
  let q : Mat d := Selection.normalizedRoot (symmPart abar)
  let hq : IsUnit q.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (normalizedRoot_posDef_of_posDef hS).isUnit
  have hcenter := normalizedCenteredCoeff_ae a abar hS
  have hpull := affineCoefficient_congr_ae q hq hcenter
  rw [haRef Q]
  refine hpull.trans ?_
  filter_upwards [] with y
  rw [affineCoefficient_apply]
  simpa only [q] using normalizedRoot_centered_conjugation
    (abar := abar)
    (A := (a.1 (matVecMul q y) : Mat d) - skewPart abar) hS

/-- Homogeneity of the canonical joint limit cancels the projective scalar
in the physical-gradient pullback. -/
theorem matSqrt_physicalGradient_pullback_ae
    {d : ℕ} [NeZero d] {a : CoeffSpace d} {abar : Mat d}
    (hS : (symmPart abar).PosDef)
    (aRef : Book.Ch03.CoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy aRef)
    (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d)
    (e : Vec d)
    (hpullback :
      (fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar))
        (e + gradPhi e a
          (matVecMul (Selection.normalizedRoot (symmPart abar)) y))) =ᵐ[volume]
        fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar)) e +
          (finiteAffineCorrectionJointLocalLimit aRef hCauchy
            (matVecMul (Selection.normalizedRoot (symmPart abar))
              e)).globalGradientRepresentative y) :
    (fun y ↦ matVecMul (matSqrt (symmPart abar))
      (gradPhi e a
        (matVecMul (Selection.normalizedRoot (symmPart abar)) y))) =ᵐ[volume]
      (finiteAffineCorrectionJointLocalLimit aRef hCauchy
        (matVecMul (matSqrt (symmPart abar)) e)).globalGradientRepresentative := by
  let mu : ℝ := specBound ((symmPart abar)⁻¹)
  let c : ℝ := Real.sqrt mu
  let L : Mat d := matSqrt (symmPart abar)
  let q : Mat d := Selection.normalizedRoot (symmPart abar)
  let eRef : Vec d := matVecMul L e
  let PhiRef : Vec d → NormalizedLocalH1Carrier d :=
    finiteAffineCorrectionJointLocalLimit aRef hCauchy
  have hmu : 0 < mu := by
    simpa only [mu] using normalizedRootScale_pos hS
  have hc : 0 < c := Real.sqrt_pos.mpr hmu
  have hqe : matVecMul q e = c • eRef := by
    simp only [q, c, mu, L, eRef, Selection.normalizedRoot_eq,
      smul_matVecMul]
  have hPhiScale :
      (PhiRef (matVecMul q e)).globalGradientRepresentative =ᵐ[volume]
        fun y ↦ c • (PhiRef eRef).globalGradientRepresentative y := by
    rw [hqe]
    have hcarrier := finiteAffineCorrectionJointLocalLimit_smul
      aRef hCauchy c eRef
    rw [show PhiRef (c • eRef) =
        NormalizedLocalH1Carrier.smulCarrier c (PhiRef eRef) by
      simpa only [PhiRef] using hcarrier]
    exact Root.NormalizedLocalH1Carrier.globalGradientRepresentative_smulCarrier
      c (PhiRef eRef)
  filter_upwards [hpullback, hPhiScale] with y hy hscale
  ext i
  have hi := congrFun hy i
  rw [hscale] at hi
  have hi' :
      c * (matVecMul L e i +
          matVecMul L
            (gradPhi e a (matVecMul q y)) i) =
        c * (matVecMul L e i +
          (PhiRef eRef).globalGradientRepresentative y i) := by
    simpa only [q, c, mu, L, eRef, PhiRef,
      Selection.normalizedRoot_eq, smul_matVecMul, matVecMul_add,
      Pi.smul_apply, Pi.add_apply, mul_add] using! hi
  exact add_left_cancel (mul_left_cancel₀ hc.ne' hi')

/-- The physical skew-centered flux row pulls back to the identity-reference
flux row of the same canonical joint corrector. -/
theorem physicalFlux_pullback_ae
    {d : ℕ} [NeZero d] {a : CoeffSpace d} {abar : Mat d}
    (hS : (symmPart abar).PosDef) (Q : TriadicCube d)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ R : TriadicCube d,
      (aRef.coeffOn R).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ⇑(normalizedCenteredCoeff a abar hS).1)
    (hCauchy : FiniteAffineCorrectionLocalCauchy aRef)
    (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d)
    (e : Vec d)
    (hpullback :
      (fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar))
        (e + gradPhi e a
          (matVecMul (Selection.normalizedRoot (symmPart abar)) y))) =ᵐ[volume]
        fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar)) e +
          (finiteAffineCorrectionJointLocalLimit aRef hCauchy
            (matVecMul (Selection.normalizedRoot (symmPart abar))
              e)).globalGradientRepresentative y) :
    (fun y ↦ matVecMul (matSqrt (symmPart abar))⁻¹
      (matVecMul
          ((a.1 (matVecMul (Selection.normalizedRoot (symmPart abar)) y) : Mat d) -
            skewPart abar)
          (e + gradPhi e a
            (matVecMul (Selection.normalizedRoot (symmPart abar)) y)) -
        matVecMul (symmPart abar) e)) =ᵐ[volume]
      fun y ↦
        matVecMul ((aRef.coeffOn Q).toCoeffField y)
            (matVecMul (matSqrt (symmPart abar)) e +
              (finiteAffineCorrectionJointLocalLimit aRef hCauchy
                (matVecMul (matSqrt (symmPart abar)) e)).globalGradientRepresentative y) -
          matVecMul (matSqrt (symmPart abar)) e := by
  have hgrad := matSqrt_physicalGradient_pullback_ae hS aRef hCauchy
    gradPhi e hpullback
  have hcoeff := exactGaugeCoeff_ae hS Q aRef haRef
  filter_upwards [hgrad, hcoeff] with y hgradY hcoeffY
  let F : Vec d := e + gradPhi e a
    (matVecMul (Selection.normalizedRoot (symmPart abar)) y)
  have hbank := matSqrt_inv_skewCentered_flux_difference_eq
    (abar := abar)
    (A := (a.1 (matVecMul (Selection.normalizedRoot (symmPart abar)) y) : Mat d))
    hS F e
  calc
    matVecMul (matSqrt (symmPart abar))⁻¹
          (matVecMul
              ((a.1 (matVecMul (Selection.normalizedRoot (symmPart abar)) y) : Mat d) -
                skewPart abar) F -
            matVecMul (symmPart abar) e) =
        matVecMul
            ((matSqrt (symmPart abar))⁻¹ *
              ((a.1 (matVecMul (Selection.normalizedRoot (symmPart abar)) y) : Mat d) -
                skewPart abar) *
              matTranspose (matSqrt (symmPart abar))⁻¹)
            (matVecMul (matSqrt (symmPart abar)) F) -
          matVecMul (matSqrt (symmPart abar)) e := hbank.symm
    _ = matVecMul ((aRef.coeffOn Q).toCoeffField y)
            (matVecMul (matSqrt (symmPart abar)) e +
              (finiteAffineCorrectionJointLocalLimit aRef hCauchy
                (matVecMul (matSqrt (symmPart abar)) e)).globalGradientRepresentative y) -
          matVecMul (matSqrt (symmPart abar)) e := by
      rw [← hcoeffY]
      congr 2
      dsimp only [F]
      rw [matVecMul_add, hgradY]

/-- The exact normalized-root inverse image of the physical ellipsoid. -/
@[expose]
def closedEuclideanBall (d : ℕ) (r : ℝ) : Set (Vec d) :=
  {y | vecNormSq y ≤ r ^ 2}

theorem measurableSet_closedEuclideanBall (d : ℕ) (r : ℝ) :
    MeasurableSet (closedEuclideanBall d r) := by
  exact (isClosed_le continuous_vecNormSq continuous_const).measurableSet

theorem euclideanBall_subset_closedEuclideanBall
    {d : ℕ} {r : ℝ} :
    euclideanBall d r ⊆ closedEuclideanBall d r := by
  intro y hy
  exact le_of_lt (by
    simpa only [euclideanBall, euclideanBallAt, sub_zero, mem_ofPred_eq]
      using hy)

theorem closedEuclideanBall_subset_euclideanBall_two_mul
    {d : ℕ} {r : ℝ} (hr : 0 < r) :
    closedEuclideanBall d r ⊆ euclideanBall d (2 * r) := by
  intro y hy
  have hsq : vecNormSq y < (2 * r) ^ 2 := by
    dsimp only [closedEuclideanBall] at hy
    exact hy.trans_lt (by nlinarith only [hr])
  simpa only [euclideanBall, euclideanBallAt, sub_zero, mem_ofPred_eq]
    using hsq

theorem closedEuclideanBall_subset_outerCube
    {d : ℕ} {r : ℝ} (hr : 0 < r) :
    closedEuclideanBall d r ⊆
      openCubeSet (originCube d
        (outerTriadicGeneration (4 * r) (by positivity))) := by
  exact (closedEuclideanBall_subset_euclideanBall_two_mul hr).trans
    (by
      simpa only [show 2 * (2 * r) = 4 * r by ring] using
        (euclideanBall_subset_openCubeSet_originCube_outerTriadicGeneration
          (d := d) (r := 2 * r) (by positivity)))

theorem volume_closedEuclideanBall_pos
    {d : ℕ} [NeZero d] {r : ℝ} (hr : 0 < r) :
    0 < volume (closedEuclideanBall d r) := by
  exact lt_of_lt_of_le
    (volume_pos_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_euclideanBallAt (0 : Vec d) hr)
      ⟨0, center_mem_euclideanBallAt (0 : Vec d) hr⟩)
    (measure_mono euclideanBall_subset_closedEuclideanBall)

theorem volume_closedEuclideanBall_lt_top
    {d : ℕ} {r : ℝ} (hr : 0 < r) :
    volume (closedEuclideanBall d r) < ∞ := by
  exact (measure_mono
    (closedEuclideanBall_subset_euclideanBall_two_mul hr)).trans_lt
      (isOpenBoundedConvexDomain_euclideanBallAt
        (0 : Vec d) (by positivity : 0 < 2 * r)).volume_lt_top

theorem outerCube_volume_ratio_lt_closedBall
    {d : ℕ} [NeZero d] {r : ℝ} (hr : 0 < r) :
    (volume (openCubeSet (originCube d
        (outerTriadicGeneration (4 * r) (by positivity))))).toReal /
        (volume (closedEuclideanBall d r)).toReal <
      (6 * Real.sqrt d) ^ d := by
  let m : ℤ := outerTriadicGeneration (4 * r) (by positivity)
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have hinnerpos : 0 < (2 * (r / Real.sqrt d)) ^ d := by positivity
  have hopenLower :=
    two_mul_div_sqrt_pow_le_volume_euclideanBall_toReal (d := d) hr
  have hclosedTop : volume (closedEuclideanBall d r) ≠ ∞ :=
    (volume_closedEuclideanBall_lt_top (d := d) hr).ne
  have hopenMono : volume (euclideanBall d r) ≤
      volume (closedEuclideanBall d r) :=
    measure_mono euclideanBall_subset_closedEuclideanBall
  have hclosedLower : (2 * (r / Real.sqrt d)) ^ d ≤
      (volume (closedEuclideanBall d r)).toReal :=
    hopenLower.trans (ENNReal.toReal_mono hclosedTop hopenMono)
  have hdenpos : 0 < (volume (closedEuclideanBall d r)).toReal :=
    hinnerpos.trans_le hclosedLower
  have hscale : (3 : ℝ) ^ m < 12 * r := by
    have h := outerTriadicGeneration_scale_lt_three_mul
      (by positivity : 0 < 4 * r)
    have h' : (3 : ℝ) ^ m < 3 * (4 * r) := by
      simpa only [m] using h
    nlinarith only [h']
  have hscaleNonneg : 0 ≤ (3 : ℝ) ^ m :=
    (zpow_pos (by norm_num : (0 : ℝ) < 3) m).le
  have hnum :
      (volume (openCubeSet (originCube d m))).toReal < (12 * r) ^ d := by
    rw [volume_openCubeSet_toReal, cubeVolume_eq_scaleFactor_pow,
      cubeScaleFactor_originCube]
    exact pow_lt_pow_left₀ hscale hscaleNonneg (NeZero.ne d)
  have hA : 0 ≤ (12 * r) ^ d := by positivity
  calc
    (volume (openCubeSet (originCube d m))).toReal /
          (volume (closedEuclideanBall d r)).toReal <
        (12 * r) ^ d /
          (volume (closedEuclideanBall d r)).toReal :=
      div_lt_div_of_pos_right hnum hdenpos
    _ ≤ (12 * r) ^ d / (2 * (r / Real.sqrt d)) ^ d :=
      div_le_div_of_nonneg_left hA hinnerpos hclosedLower
    _ = (6 * Real.sqrt d) ^ d := by
      rw [← div_pow]
      congr 1
      field_simp
      ring

@[expose]
def closedBallScaledNegOneConstant (d : ℕ) : ℝ :=
  12 * Real.sqrt ((6 * Real.sqrt d) ^ d)

theorem closedBallScaledNegOneConstant_pos
    (d : ℕ) [NeZero d] : 0 < closedBallScaledNegOneConstant d := by
  unfold closedBallScaledNegOneConstant
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr (NeZero.pos d)
  positivity

theorem closedBall_scale_prefactor_le
    {d : ℕ} [NeZero d] {r : ℝ} (hr : 0 < r) :
    r⁻¹ * Real.sqrt
        ((volume (openCubeSet (originCube d
          (outerTriadicGeneration (4 * r) (by positivity))))).toReal /
          (volume (closedEuclideanBall d r)).toReal) ≤
      closedBallScaledNegOneConstant d *
        (((3 : ℝ) ^ outerTriadicGeneration
          (4 * r) (by positivity))⁻¹) := by
  let m : ℤ := outerTriadicGeneration (4 * r) (by positivity)
  let L : ℝ := (3 : ℝ) ^ m
  let K : ℝ := (6 * Real.sqrt d) ^ d
  have hL : 0 < L := by dsimp only [L]; positivity
  have hscale : L < 12 * r := by
    have hscale0 : (3 : ℝ) ^ m < 3 * (4 * r) := by
      simpa only [m] using
        outerTriadicGeneration_scale_lt_three_mul
          (by positivity : 0 < 4 * r)
    dsimp only [L]
    calc
      (3 : ℝ) ^ m < 3 * (4 * r) := hscale0
      _ = 12 * r := by ring
  have hinv : (12 * r)⁻¹ < L⁻¹ :=
    (inv_lt_inv₀ (mul_pos (by norm_num) hr) hL).2 hscale
  have hrInv : r⁻¹ ≤ 12 * L⁻¹ := by
    calc
      r⁻¹ = (1 : ℝ) * r⁻¹ := by rw [one_mul]
      _ = (12 * 12⁻¹) * r⁻¹ := by norm_num
      _ = 12 * (12⁻¹ * r⁻¹) := by rw [mul_assoc]
      _ = 12 * (12 * r)⁻¹ := by rw [mul_inv]
      _ ≤ 12 * L⁻¹ := mul_le_mul_of_nonneg_left hinv.le (by norm_num)
  have hratio :
      (volume (openCubeSet (originCube d m))).toReal /
          (volume (closedEuclideanBall d r)).toReal < K := by
    simpa only [m, K] using
      outerCube_volume_ratio_lt_closedBall (d := d) hr
  have hsqrt : Real.sqrt
      ((volume (openCubeSet (originCube d m))).toReal /
        (volume (closedEuclideanBall d r)).toReal) ≤ Real.sqrt K :=
    Real.sqrt_le_sqrt hratio.le
  calc
    r⁻¹ * Real.sqrt
          ((volume (openCubeSet (originCube d m))).toReal /
            (volume (closedEuclideanBall d r)).toReal) ≤
        (12 * L⁻¹) * Real.sqrt K :=
      mul_le_mul hrInv hsqrt (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num) (inv_nonneg.mpr hL.le))
    _ = closedBallScaledNegOneConstant d * L⁻¹ := by
      unfold closedBallScaledNegOneConstant
      dsimp only [K]
      ac_rfl
    _ = closedBallScaledNegOneConstant d *
        (((3 : ℝ) ^ outerTriadicGeneration
          (4 * r) (by positivity))⁻¹) := rfl

theorem closedBallScaled_negOne_pair_le_originCube
    {d : ℕ} [NeZero d] {r : ℝ} (hr : 0 < r)
    (m : ℤ)
    (hm : m = outerTriadicGeneration (4 * r) (by positivity))
    (F G : Vec d → Vec d)
    (hF : MemVectorL2 (openCubeSet (originCube d m)) F)
    (hG : MemVectorL2 (openCubeSet (originCube d m)) G) :
    ENNReal.ofReal r⁻¹ *
        (negOneNorm (closedEuclideanBall d r) F +
          negOneNorm (closedEuclideanBall d r) G) ≤
      ENNReal.ofReal (closedBallScaledNegOneConstant d) *
        (ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹) *
          (negOneNorm (openCubeSet (originCube d m)) F +
            negOneNorm (openCubeSet (originCube d m)) G)) := by
  let U : Set (Vec d) := closedEuclideanBall d r
  let V : Set (Vec d) := openCubeSet (originCube d m)
  have hUV : U ⊆ V := by
    simpa only [U, V, hm] using closedEuclideanBall_subset_outerCube
      (d := d) hr
  have hU0 : volume U ≠ 0 := by
    exact (volume_closedEuclideanBall_pos (d := d) hr).ne'
  have hUtop : volume U ≠ ∞ := by
    exact (volume_closedEuclideanBall_lt_top (d := d) hr).ne
  have hV0 : volume V ≠ 0 := by
    intro hz
    have hp : 0 < (volume V).toReal := by
      dsimp only [V]
      rw [volume_openCubeSet_toReal]
      exact cubeVolume_pos _
    rw [hz, ENNReal.toReal_zero] at hp
    exact lt_irrefl 0 hp
  have hVtop : volume V ≠ ∞ :=
    (volume_openCubeSet_lt_top (originCube d m)).ne
  have hpair := negOneNorm_pair_le_sqrt_volumeRatio_of_subset
    hUV hU0 hUtop hV0 hVtop F G
      (by simpa only [V] using hF) (by simpa only [V] using hG)
  have hpref := closedBall_scale_prefactor_le (d := d) hr
  calc
    ENNReal.ofReal r⁻¹ *
          (negOneNorm U F + negOneNorm U G) ≤
        ENNReal.ofReal r⁻¹ *
          (ENNReal.ofReal
              (Real.sqrt ((volume V).toReal / (volume U).toReal)) *
            (negOneNorm V F + negOneNorm V G)) :=
      mul_le_mul_right hpair _
    _ = ENNReal.ofReal
          (r⁻¹ * Real.sqrt ((volume V).toReal / (volume U).toReal)) *
            (negOneNorm V F + negOneNorm V G) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
    _ ≤ ENNReal.ofReal
          (closedBallScaledNegOneConstant d * ((3 : ℝ) ^ m)⁻¹) *
            (negOneNorm V F + negOneNorm V G) :=
      (by
        have hp : ENNReal.ofReal
              (r⁻¹ * Real.sqrt ((volume V).toReal / (volume U).toReal)) ≤
            ENNReal.ofReal
              (closedBallScaledNegOneConstant d * ((3 : ℝ) ^ m)⁻¹) :=
          ENNReal.ofReal_le_ofReal (by
            simpa only [U, V, ← hm] using hpref)
        calc
          ENNReal.ofReal
                (r⁻¹ * Real.sqrt ((volume V).toReal / (volume U).toReal)) *
              (negOneNorm V F + negOneNorm V G) =
            (negOneNorm V F + negOneNorm V G) * ENNReal.ofReal
                (r⁻¹ * Real.sqrt ((volume V).toReal / (volume U).toReal)) :=
              mul_comm _ _
          _ ≤ (negOneNorm V F + negOneNorm V G) * ENNReal.ofReal
                (closedBallScaledNegOneConstant d * ((3 : ℝ) ^ m)⁻¹) :=
              mul_le_mul_right hp _
          _ = ENNReal.ofReal
                (closedBallScaledNegOneConstant d * ((3 : ℝ) ^ m)⁻¹) *
              (negOneNorm V F + negOneNorm V G) := mul_comm _ _)
    _ = ENNReal.ofReal (closedBallScaledNegOneConstant d) *
        (ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹) *
          (negOneNorm V F + negOneNorm V G)) := by
      rw [ENNReal.ofReal_mul (closedBallScaledNegOneConstant_pos d).le]
      ac_rfl
    _ = _ := by simp only [V]

/-- The normalized-root image of the exact closed gauge ball is the physical
ellipsoid. -/
theorem matImage_closedBall_eq_ellipsoid
    {d : ℕ} [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) (r : ℝ) :
    matImage (Selection.normalizedRoot (symmPart abar))
        (closedEuclideanBall d r) = ellipsoid abar r := by
  let q : Mat d := Selection.normalizedRoot (symmPart abar)
  let hq : IsUnit q.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (normalizedRoot_posDef_of_posDef hS).isUnit
  have hgeom := Root.matImage_normalizedRoot_inv_ellipsoid_eq hS r
  change matImage q {y : Vec d | vecNormSq y ≤ r ^ 2} = ellipsoid abar r
  rw [← hgeom]
  exact matImage_matImage_inv hq (ellipsoid abar r)

/-- Exact affine transport followed by closed-ball restriction converts a
physical inverse-radius pair to the inverse-triadic-scale gauge pair. -/
theorem physicalScaledPair_le_gaugeOriginCube
    {d : ℕ} [NeZero d] {abar : Mat d} {r : ℝ}
    (hS : (symmPart abar).PosDef) (hr : 0 < r)
    (m : ℤ) (hm : m = outerTriadicGeneration (4 * r) (by positivity))
    (P₁ P₂ F G : Vec d → Vec d)
    (h₁ : (fun y ↦ P₁ (matVecMul
      (Selection.normalizedRoot (symmPart abar)) y)) =ᵐ[volume] F)
    (h₂ : (fun y ↦ P₂ (matVecMul
      (Selection.normalizedRoot (symmPart abar)) y)) =ᵐ[volume] G)
    (hF : MemVectorL2 (openCubeSet (originCube d m)) F)
    (hG : MemVectorL2 (openCubeSet (originCube d m)) G) :
    ENNReal.ofReal r⁻¹ * negOneNorm (ellipsoid abar r) P₁ +
        ENNReal.ofReal r⁻¹ * negOneNorm (ellipsoid abar r) P₂ ≤
      ENNReal.ofReal
          (Real.sqrt (h1AffineFactor
              (Selection.normalizedRoot (symmPart abar))) *
            closedBallScaledNegOneConstant d) *
        (ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹) *
          (negOneNorm (openCubeSet (originCube d m)) F +
            negOneNorm (openCubeSet (originCube d m)) G)) := by
  let q : Mat d := Selection.normalizedRoot (symmPart abar)
  let U : Set (Vec d) := closedEuclideanBall d r
  let V : Set (Vec d) := openCubeSet (originCube d m)
  let A : ℝ := Real.sqrt (h1AffineFactor q)
  let B : ℝ := closedBallScaledNegOneConstant d
  let hq : IsUnit q.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (normalizedRoot_posDef_of_posDef hS).isUnit
  have hU : MeasurableSet U := measurableSet_closedEuclideanBall d r
  have hU0 : volume U ≠ 0 :=
    (volume_closedEuclideanBall_pos (d := d) hr).ne'
  have hgrad := negOneNorm_matImage_le hq hU hU0 P₁
  have hflux := negOneNorm_matImage_le hq hU hU0 P₂
  have himage : matImage q U = ellipsoid abar r := by
    simpa only [q, U] using matImage_closedBall_eq_ellipsoid hS r
  have h₁U : (fun y ↦ P₁ (matVecMul q y))
      =ᵐ[volume.restrict U] F := by
    exact ae_restrict_of_ae (by simpa only [q] using! h₁)
  have h₂U : (fun y ↦ P₂ (matVecMul q y))
      =ᵐ[volume.restrict U] G := by
    exact ae_restrict_of_ae (by simpa only [q] using! h₂)
  have hpair : negOneNorm (ellipsoid abar r) P₁ +
      negOneNorm (ellipsoid abar r) P₂ ≤
        ENNReal.ofReal A * (negOneNorm U F + negOneNorm U G) := by
    rw [← himage]
    have hsum := add_le_add hgrad hflux
    rw [negOneNorm_eq_of_ae_eq_on h₁U,
      negOneNorm_eq_of_ae_eq_on h₂U] at hsum
    simpa only [A, q, mul_add] using hsum
  have hclosed := closedBallScaled_negOne_pair_le_originCube
    hr m hm F G (by simpa only [V] using hF) (by simpa only [V] using hG)
  calc
    ENNReal.ofReal r⁻¹ * negOneNorm (ellipsoid abar r) P₁ +
          ENNReal.ofReal r⁻¹ * negOneNorm (ellipsoid abar r) P₂ =
        ENNReal.ofReal r⁻¹ *
          (negOneNorm (ellipsoid abar r) P₁ +
            negOneNorm (ellipsoid abar r) P₂) := by rw [mul_add]
    _ ≤ ENNReal.ofReal r⁻¹ *
        (ENNReal.ofReal A * (negOneNorm U F + negOneNorm U G)) :=
      (by
        simpa only [mul_comm] using
          (mul_le_mul_right hpair (ENNReal.ofReal r⁻¹)))
    _ = ENNReal.ofReal A *
        (ENNReal.ofReal r⁻¹ *
          (negOneNorm U F + negOneNorm U G)) := by ac_rfl
    _ ≤ ENNReal.ofReal A *
        (ENNReal.ofReal B *
          (ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹) *
            (negOneNorm V F + negOneNorm V G))) :=
      (by
        have hmul := mul_le_mul_right
          (by simpa only [U, V, B] using hclosed) (ENNReal.ofReal A)
        simpa only [mul_comm, mul_left_comm, mul_assoc] using hmul)
    _ = _ := by
      dsimp only [A, B, q]
      simp only [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      ac_rfl

end

end HighContrast
end HCPolySupport
