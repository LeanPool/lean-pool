/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorClassEnergy
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorIntrinsicSlopeGoodTail
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitz

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorIntrinsicGrowthGoodTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Sub-exponential growth of the canonical corrector

A sufficiently small scalar good tail gives a scale-uniform weighted-gradient
bound for the canonical affine-plus-corrector limit.  Consequently that full
gradient has sub-`eta` growth for every positive `eta`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem weightedGradNorm_congr_coeff_ae
    {d : ℕ} {U : Set (Vec d)} {b b' : CoeffField d}
    (f : Vec d → Vec d)
    (hbb' : b =ᵐ[volumeMeasureOn U] b') :
    weightedGradNorm b U f = weightedGradNorm b' U f := by
  unfold weightedGradNorm eVolumeAverage
  congr 2
  apply lintegral_congr_ae
  filter_upwards [hbb'] with x hx
  simp only [hx]

@[expose]
public noncomputable def finiteAffineGrowthApproximation
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q k : ℕ) : H1Function (localGradientCube d q) :=
  (show H1Function (localGradientCube d q) from by
    simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using
      finiteAffineBoundaryH1 (q : ℤ) e) +
    normalizedLocalH1 (finiteAffineCorrectionLocalSequence a e) q k

private theorem finiteAffineGrowthApproximation_grad_eq
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q k : ℕ) :
    (finiteAffineGrowthApproximation a e q k).grad =
      (finiteAffineSolution a ((q + k : ℕ) : ℤ) e).toH1.grad := by
  funext x
  change
    (finiteAffineBoundaryH1 (q : ℤ) e).grad x +
        (normalizeOnUnitCube
          (finiteAffineCorrectionLocalSequence a e (q + k))).grad x =
      (finiteAffineSolution a ((q + k : ℕ) : ℤ) e).toH1.grad x
  rw [finiteAffineSolution_toH1]
  change
    (finiteAffineBoundaryH1 (q : ℤ) e).grad x +
        (normalizeOnUnitCube
          (finiteAffineCorrectionLocalSequence a e (q + k))).grad x =
      (finiteAffineBoundaryH1 ((q + k : ℕ) : ℤ) e).grad x +
        (finiteAffineCorrection a ((q + k : ℕ) : ℤ) e).toH1Function.grad x
  rw [finiteAffineBoundaryH1_grad, finiteAffineBoundaryH1_grad]
  change e +
      (normalizeOnUnitCube
        (finiteAffineCorrectionLocalSequence a e (q + k))).grad x =
    e + (finiteAffineCorrectionLocalSequence a e (q + k)).grad x
  rw [normalizeOnUnitCube_grad]

private theorem finiteAffineGrowthApproximation_tendsto
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (e : Vec d) (q : ℕ) :
    _root_.Filter.Tendsto
      (fun k =>
        (finiteAffineGrowthApproximation a e q k).gradToHilbertVectorL2)
      _root_.Filter.atTop
      (nhds
        (finiteAffineCorrectionJointLocalH1 a hCauchy e q).gradToHilbertVectorL2) := by
  let g0 : LocalGradientL2 d q :=
    (show H1Function (localGradientCube d q) from by
      simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using
        finiteAffineBoundaryH1 (q : ℤ) e).gradToHilbertVectorL2
  have hlimit :
      _root_.Filter.Tendsto
        (fun k =>
          (normalizedLocalPair
            (finiteAffineCorrectionLocalSequence a e) q k).2)
        _root_.Filter.atTop
        (nhds
          ((finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent q)) :=
    (finiteAffineCorrectionJointLocalLimit_isLimit a hCauchy e q).snd_nhds
  have hsum :
      _root_.Filter.Tendsto
        (fun k =>
          g0 +
            (normalizedLocalPair
              (finiteAffineCorrectionLocalSequence a e) q k).2)
        _root_.Filter.atTop
        (nhds
          (g0 +
            (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent q)) :=
    tendsto_const_nhds.add hlimit
  have hsource :
      (fun k =>
        (finiteAffineGrowthApproximation a e q k).gradToHilbertVectorL2) =
        fun k =>
          g0 +
            (normalizedLocalPair
              (finiteAffineCorrectionLocalSequence a e) q k).2 := by
    funext k
    rw [finiteAffineGrowthApproximation,
      H1Function.gradToHilbertVectorL2_add]
    rfl
  have htarget :
      (finiteAffineCorrectionJointLocalH1 a hCauchy e q).gradToHilbertVectorL2 =
        g0 +
          (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent q := by
    rw [finiteAffineCorrectionJointLocalH1_gradToHilbertVectorL2]
    dsimp only [g0]
    rfl
  rw [hsource, htarget]
  exact hsum

private theorem finiteAffineGrowthApproximation_weightedGradNorm_le
    {d : ℕ} [NeZero d] {s C c Cenergy : ℝ}
    (hC : 1 ≤ C) (hclt : c < 1)
    (hLipschitz :
      ∀ (a : Book.Ch02.TriadicCoeffFamily d)
        (n m : ℤ), n < m →
        ScalarIdentityGoodTailOnInterval a s c n m →
        ∀ u : Book.Ch03.CubeSolution (originCube d m) a,
          weightedGradNorm
              (a.coeffOn (originCube d n)).toCoeffField
              (openCubeSet (originCube d n)) u.toH1.grad ≤
            ENNReal.ofReal C *
              weightedGradNorm
                (a.coeffOn (originCube d m)).toCoeffField
                (openCubeSet (originCube d m)) u.toH1.grad)
    (hCenergy : 0 < Cenergy)
    (henergy :
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d),
        Book.Ch03.h1EnergyNormOnCube (originCube d m) a
            (finiteAffineSolution a m e).toH1 ≤
          Cenergy * (1 + scalarIdentityWeakError a s m) * euclideanNorm e)
    {a : Book.Ch02.TriadicCoeffFamily d} {delta : ℝ} {n : ℤ}
    (hdelta : delta ∈ Set.Ioc (0 : ℝ) c)
    (hgood : ScalarIdentityGoodTail a s delta n)
    (e : Vec d) (q k : ℕ) (hnq : n ≤ (q : ℤ)) :
    weightedGradNorm
        (a.coeffOn (originCube d (q : ℤ))).toCoeffField
        (localGradientCube d q)
        (finiteAffineGrowthApproximation a e q k).grad ≤
      ENNReal.ofReal (C * (2 * Cenergy * euclideanNorm e)) := by
  have hdelta_c : delta ≤ c := hdelta.2
  have hdelta_one : delta ≤ 1 := hdelta.2.trans hclt.le
  have hweak : scalarIdentityWeakError a s ((q + k : ℕ) : ℤ) ≤ 1 :=
    (hgood.weakError_le (by omega)).trans hdelta_one
  have henergyReal :
      Book.Ch03.h1EnergyNormOnCube (originCube d ((q + k : ℕ) : ℤ)) a
          (finiteAffineSolution a ((q + k : ℕ) : ℤ) e).toH1 ≤
        2 * Cenergy * euclideanNorm e := by
    calc
      _ ≤ Cenergy *
          (1 + scalarIdentityWeakError a s ((q + k : ℕ) : ℤ)) *
            euclideanNorm e := henergy a _ e
      _ ≤ Cenergy * 2 * euclideanNorm e := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith only [hweak]) hCenergy.le)
          (euclideanNorm_nonneg e)
      _ = 2 * Cenergy * euclideanNorm e := by ring
  have houter :
      weightedGradNorm
          (a.coeffOn (originCube d ((q + k : ℕ) : ℤ))).toCoeffField
          (openCubeSet (originCube d ((q + k : ℕ) : ℤ)))
          (finiteAffineSolution a ((q + k : ℕ) : ℤ) e).toH1.grad ≤
        ENNReal.ofReal (2 * Cenergy * euclideanNorm e) := by
    rw [weightedGradNorm_eq_ofReal_h1EnergyNormOnCube]
    exact ENNReal.ofReal_le_ofReal henergyReal
  rw [finiteAffineGrowthApproximation_grad_eq]
  by_cases hk : k = 0
  · subst k
    simp only [Nat.add_zero, localGradientCube]
    calc
      _ ≤ ENNReal.ofReal (2 * Cenergy * euclideanNorm e) := houter
      _ ≤ ENNReal.ofReal C *
          ENNReal.ofReal (2 * Cenergy * euclideanNorm e) := by
        calc
          _ = 1 * ENNReal.ofReal (2 * Cenergy * euclideanNorm e) := by simp
          _ ≤ ENNReal.ofReal C *
              ENNReal.ofReal (2 * Cenergy * euclideanNorm e) := by
            gcongr
            simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hC
      _ = ENNReal.ofReal (C * (2 * Cenergy * euclideanNorm e)) := by
        rw [← ENNReal.ofReal_mul (zero_le_one.trans hC)]
  · have hqk : (q : ℤ) < ((q + k : ℕ) : ℤ) := by omega
    have hinterval : ScalarIdentityGoodTailOnInterval a s c
        (q : ℤ) ((q + k : ℕ) : ℤ) :=
      (hgood.interval (by omega)).mono_start hnq |>.mono hdelta_c
    let u : Book.Ch03.CubeSolution (originCube d ((q + k : ℕ) : ℤ)) a :=
      finiteAffineCubeSolution a ((q + k : ℕ) : ℤ) e
    calc
      weightedGradNorm
          (a.coeffOn (originCube d (q : ℤ))).toCoeffField
          (openCubeSet (originCube d (q : ℤ)))
          (finiteAffineSolution a ((q + k : ℕ) : ℤ) e).toH1.grad ≤
        ENNReal.ofReal C *
          weightedGradNorm
            (a.coeffOn (originCube d ((q + k : ℕ) : ℤ))).toCoeffField
            (openCubeSet (originCube d ((q + k : ℕ) : ℤ)))
            (finiteAffineSolution a ((q + k : ℕ) : ℤ) e).toH1.grad := by
              simpa only [u, finiteAffineCubeSolution] using
                hLipschitz a (q : ℤ) ((q + k : ℕ) : ℤ) hqk hinterval u
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal
          (2 * Cenergy * euclideanNorm e) := by
        gcongr
      _ = ENNReal.ofReal (C * (2 * Cenergy * euclideanNorm e)) := by
        rw [← ENNReal.ofReal_mul (zero_le_one.trans hC)]

/-- A sufficiently small scalar good tail gives a scale-uniform weighted
gradient bound for the canonical affine-plus-corrector limit beyond the
starting scale. -/
theorem exists_scalarIdentityGoodTailJointWeightedGradientBoundConstant
    (d : ℕ) [NeZero d] (s : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ B c : ℝ, 0 < B ∧ c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        ∀ (hCauchy : FiniteAffineCorrectionLocalCauchy a)
          (e : Vec d) (q : ℕ), n ≤ (q : ℤ) →
          weightedGradNorm
              (a.coeffOn (originCube d (q : ℤ))).toCoeffField
              (localGradientCube d q)
              (finiteAffineCorrectionJointLocalH1 a hCauchy e q).grad ≤
            ENNReal.ofReal (B * euclideanNorm e) := by
  obtain ⟨C, c, hC, hc, hLipschitz⟩ :=
    exists_scalarIdentityFiniteLipschitzConstant d s hs hs_lt
  obtain ⟨Cenergy, hCenergy, henergy⟩ :=
    exists_finiteAffineSolutionEnergyEstimateConstant d s hs
      (hs_lt.trans (by norm_num))
  let B : ℝ := 2 * C * Cenergy
  have hB : 0 < B := by
    dsimp only [B]
    exact mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hC)) hCenergy
  refine ⟨B, c, hB, hc, ?_⟩
  intro a delta n hdelta hgood hCauchy e q hnq
  let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
    (originCube d (q : ℤ)) a
  let A : ℕ → HilbertVectorL2 (localGradientCube d q) := fun k =>
    (finiteAffineGrowthApproximation a e q k).gradToHilbertVectorL2
  let L : HilbertVectorL2 (localGradientCube d q) :=
    (finiteAffineCorrectionJointLocalH1 a hCauchy e q).gradToHilbertVectorL2
  have hAL : _root_.Filter.Tendsto A _root_.Filter.atTop (nhds L) := by
    simpa only [A, L] using
      finiteAffineGrowthApproximation_tendsto a hCauchy e q
  have hEnergyTendsto :
      _root_.Filter.Tendsto
        (fun k => normalizedLocalSymmetricEnergy hEll (A k))
        _root_.Filter.atTop
        (nhds (normalizedLocalSymmetricEnergy hEll L)) :=
    (continuous_normalizedLocalSymmetricEnergy hEll).continuousAt.tendsto.comp hAL
  have hBform : C * (2 * Cenergy * euclideanNorm e) =
      B * euclideanNorm e := by
    dsimp only [B]
    ring
  have hBoundApprox : ∀ k,
      weightedGradNorm
          (a.coeffOn (originCube d (q : ℤ))).toCoeffField
          (localGradientCube d q)
          (finiteAffineGrowthApproximation a e q k).grad ≤
        ENNReal.ofReal (B * euclideanNorm e) := by
    intro k
    rw [← hBform]
    exact finiteAffineGrowthApproximation_weightedGradNorm_le
      hC hc.2 hLipschitz hCenergy henergy hdelta hgood e q k hnq
  have hEnergyApprox : ∀ k,
      normalizedLocalSymmetricEnergy hEll (A k) ≤
        (B * euclideanNorm e) ^ 2 := by
    intro k
    have hbridge :=
      ofReal_normalizedLocalSymmetricEnergy_eq_weightedGradNorm_sq
        hEll (finiteAffineGrowthApproximation a e q k).grad_memVectorL2
    have hbridgeLocal :
        ENNReal.ofReal
            (normalizedLocalSymmetricEnergy hEll
              (finiteAffineGrowthApproximation a e q k).gradToHilbertVectorL2) =
          weightedGradNorm
              (Book.Ch03.publicCoeffField (originCube d (q : ℤ)) a)
              (localGradientCube d q)
              (finiteAffineGrowthApproximation a e q k).grad ^ 2 := by
      simpa only [localGradientCube, H1Function.gradToHilbertVectorL2] using hbridge
    have hcoeff :
        weightedGradNorm
            (Book.Ch03.publicCoeffField (originCube d (q : ℤ)) a)
            (localGradientCube d q)
            (finiteAffineGrowthApproximation a e q k).grad =
          weightedGradNorm
            (a.coeffOn (originCube d (q : ℤ))).toCoeffField
            (localGradientCube d q)
            (finiteAffineGrowthApproximation a e q k).grad := by
      apply weightedGradNorm_congr_coeff_ae
      simpa only [localGradientCube] using
        Book.Ch03.publicCoeffField_ae_eq_openCubeSet
          (originCube d (q : ℤ)) a
    have hsq := ENNReal.pow_le_pow_left (hBoundApprox k :
      weightedGradNorm
          (a.coeffOn (originCube d (q : ℤ))).toCoeffField
          (localGradientCube d q)
          (finiteAffineGrowthApproximation a e q k).grad ≤
        ENNReal.ofReal (B * euclideanNorm e)) (n := 2)
    have hBnonneg : 0 ≤ B * euclideanNorm e :=
      mul_nonneg hB.le (euclideanNorm_nonneg e)
    rw [← ENNReal.ofReal_pow hBnonneg] at hsq
    rw [← hcoeff, ← hbridgeLocal] at hsq
    simpa only [A, H1Function.gradToHilbertVectorL2] using
      (ENNReal.ofReal_le_ofReal_iff (sq_nonneg (B * euclideanNorm e))).1 hsq
  have hEnergyLimit :
      normalizedLocalSymmetricEnergy hEll L ≤
        (B * euclideanNorm e) ^ 2 :=
    le_of_tendsto hEnergyTendsto (_root_.Filter.Eventually.of_forall hEnergyApprox)
  have hLimitBridge :=
    ofReal_normalizedLocalSymmetricEnergy_eq_weightedGradNorm_sq hEll
      (finiteAffineCorrectionJointLocalH1 a hCauchy e q).grad_memVectorL2
  have hLimitBridgeLocal :
      ENNReal.ofReal
          (normalizedLocalSymmetricEnergy hEll
            (finiteAffineCorrectionJointLocalH1 a hCauchy e q).gradToHilbertVectorL2) =
        weightedGradNorm
            (Book.Ch03.publicCoeffField (originCube d (q : ℤ)) a)
            (localGradientCube d q)
            (finiteAffineCorrectionJointLocalH1 a hCauchy e q).grad ^ 2 := by
    simpa only [localGradientCube, H1Function.gradToHilbertVectorL2] using hLimitBridge
  have hLimitCoeff :
      weightedGradNorm
          (Book.Ch03.publicCoeffField (originCube d (q : ℤ)) a)
          (localGradientCube d q)
          (finiteAffineCorrectionJointLocalH1 a hCauchy e q).grad =
        weightedGradNorm
          (a.coeffOn (originCube d (q : ℤ))).toCoeffField
          (localGradientCube d q)
          (finiteAffineCorrectionJointLocalH1 a hCauchy e q).grad := by
    apply weightedGradNorm_congr_coeff_ae
    simpa only [localGradientCube] using
      Book.Ch03.publicCoeffField_ae_eq_openCubeSet
        (originCube d (q : ℤ)) a
  have hEnergyLimitENN :
      ENNReal.ofReal (normalizedLocalSymmetricEnergy hEll L) ≤
        ENNReal.ofReal ((B * euclideanNorm e) ^ 2) :=
    ENNReal.ofReal_le_ofReal hEnergyLimit
  have hsqLimit :
      weightedGradNorm
          (a.coeffOn (originCube d (q : ℤ))).toCoeffField
          (localGradientCube d q)
          (finiteAffineCorrectionJointLocalH1 a hCauchy e q).grad ^ 2 ≤
        ENNReal.ofReal (B * euclideanNorm e) ^ 2 := by
    rw [← ENNReal.ofReal_pow
      (mul_nonneg hB.le (euclideanNorm_nonneg e))]
    rw [← hLimitCoeff, ← hLimitBridgeLocal]
    simpa only [L, H1Function.gradToHilbertVectorL2] using hEnergyLimitENN
  exact (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).1 hsqLimit

end

end HighContrast
end HCPolySupport
