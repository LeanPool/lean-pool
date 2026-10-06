/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1QuantitativeCorrectorTail
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1ReparameterizationCore

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1WeightedProjectionCloseness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Near-identity estimate for the weighted finite-corrector projection

Coefficient-energy minimality and the scalar good-tail average coercivity
turn the quantitative finite-corrector tail into a near-identity bound for
the canonical linear slope projection.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory

noncomputable section

/-- Normalized symmetric coefficient energy on the harmonic-gradient space
of an origin cube. -/
@[expose]
noncomputable def localHarmonicEnergy
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d) (q : ℕ)
    (F : AHarmonicGradientHilbert.Space
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (localGradientCube d q))
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
        (originCube d (q : ℤ)) a)) : ℝ :=
  normalizedLocalSymmetricEnergy
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d (q : ℤ)) a) (F : LocalGradientL2 d q)

private theorem normalizedLocalSymmetricEnergy_neg
    {d : ℕ} {U : Set (Vec d)} {b : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U b) (F : HilbertVectorL2 U) :
    normalizedLocalSymmetricEnergy hEll (-F) =
      normalizedLocalSymmetricEnergy hEll F := by
  unfold normalizedLocalSymmetricEnergy
  rw [map_neg, inner_neg_left, inner_neg_right]
  ring

private theorem sqrt_normalizedEnergy_grad_eq_h1EnergyNormOnCube_restriction
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k : ℤ) (u : H1Function (openCubeSet (originCube d k))) :
    Real.sqrt (normalizedLocalSymmetricEnergy
        (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
          (originCube d k) a) u.gradToHilbertVectorL2) =
      Book.Ch03.h1EnergyNormOnCube (originCube d k) a u := by
  rw [sqrt_normalizedEnergy_grad_eq_weightedGradNorm_toReal]
  rw [weightedGradNorm_congr_coeff_ae_on _
    (Book.Ch03.publicCoeffField_ae_eq_openCubeSet (originCube d k) a)]
  erw [weightedGradNorm_eq_ofReal_h1EnergyNormOnCube]
  rw [ENNReal.toReal_ofReal]
  unfold Book.Ch03.h1EnergyNormOnCube
  exact Real.sqrt_nonneg _

private theorem finiteCorrectorWeightedProjection_energy_le
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    {q m : ℕ} (hqm : q ≤ m)
    (hT : Function.Injective (finiteTrialHarmonicGradientLinearMap a hqm))
    (e : Vec d) :
    let T := finiteTrialHarmonicGradientLinearMap a hqm
    let J := jointTargetHarmonicGradientLinearMap a hCauchy q
    let P := finiteCorrectorWeightedProjection a hCauchy hqm hT
    localHarmonicEnergy a q (J e - T (P e)) ≤
      localHarmonicEnergy a q (J e - T e) := by
  dsimp only
  have hmin := finiteCorrectorWeightedProjection_minimizes
    a hCauchy hqm hT e e
  let B := AHarmonicGradientHilbert.symmCoeffBilin
    (PotentialSolenoidalL2Data.ofSubmoduleClosures (localGradientCube d q))
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d (q : ℤ)) a)
  have hbilin : B
      ((jointTargetHarmonicGradientLinearMap a hCauchy q) e -
        (finiteTrialHarmonicGradientLinearMap a hqm)
          ((finiteCorrectorWeightedProjection a hCauchy hqm hT) e))
      ((jointTargetHarmonicGradientLinearMap a hCauchy q) e -
        (finiteTrialHarmonicGradientLinearMap a hqm)
          ((finiteCorrectorWeightedProjection a hCauchy hqm hT) e)) ≤
      B
      ((jointTargetHarmonicGradientLinearMap a hCauchy q) e -
        (finiteTrialHarmonicGradientLinearMap a hqm) e)
      ((jointTargetHarmonicGradientLinearMap a hCauchy q) e -
        (finiteTrialHarmonicGradientLinearMap a hqm) e) := by
    unfold quadraticEnergy at hmin
    dsimp only [B]
    nlinarith only [hmin]
  unfold localHarmonicEnergy normalizedLocalSymmetricEnergy
  exact mul_le_mul_of_nonneg_left hbilin (inv_nonneg.mpr ENNReal.toReal_nonneg)

/-- The canonical coefficient-weighted projection is quantitatively close
to the identity whenever the joint-to-finite tail is small. -/
theorem finiteCorrectorWeightedProjection_sub_identity_le
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (s delta c : ℝ) (n0 : ℤ)
    (hs : 0 < s) (hc1 : c ≤ 1)
    (hdelta : delta ∈ Set.Ioc (0 : ℝ) c)
    (hgood : ScalarIdentityGoodTail a s delta n0)
    (hcoercive :
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c → ScalarIdentityGoodTail a s delta n →
        ∀ (q t : ℕ), n ≤ (q : ℤ) → ∀ e : Vec d,
          euclideanNorm e ≤ 2 * euclideanNorm
            (cubeAverageVec (originCube d (q : ℤ))
              (finiteAffineSolution a ((q + t + 2 : ℕ) : ℤ) e).toH1.grad))
    (q m : ℕ) (hnq : n0 ≤ (q : ℤ)) (hqm2 : q + 2 ≤ m)
    (K : ℝ) (hK : 0 ≤ K)
    (htail : ∀ e : Vec d,
      let T := finiteTrialHarmonicGradientLinearMap a (by omega : q ≤ m)
      let J := jointTargetHarmonicGradientLinearMap a hCauchy q
      Real.sqrt (localHarmonicEnergy a q (J e - T e)) ≤
        K * euclideanNorm e) :
    let hT := finiteTrialHarmonicGradientLinearMap_injective
      a s delta c n0 hdelta hgood hcoercive q m hnq hqm2
    let P := finiteCorrectorWeightedProjection a hCauchy
      (by omega : q ≤ m) hT
    ∀ e : Vec d,
      euclideanNorm (P e - e) ≤
        4 * Real.sqrt (4 * (d : ℝ)) * K * euclideanNorm e := by
  dsimp only
  intro e
  let hqm : q ≤ m := by omega
  let hT := finiteTrialHarmonicGradientLinearMap_injective
    a s delta c n0 hdelta hgood hcoercive q m hnq hqm2
  let T := finiteTrialHarmonicGradientLinearMap a hqm
  let J := jointTargetHarmonicGradientLinearMap a hCauchy q
  let P := finiteCorrectorWeightedProjection a hCauchy hqm hT
  let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
    (originCube d (q : ℤ)) a
  let R0 := J e - T e
  let RP := J e - T (P e)
  have hminEnergy : localHarmonicEnergy a q RP ≤
      localHarmonicEnergy a q R0 := by
    simpa only [hEll, RP, R0, J, T, P, hqm, hT] using
      finiteCorrectorWeightedProjection_energy_le a hCauchy hqm hT e
  have hminSqrt : Real.sqrt (localHarmonicEnergy a q RP) ≤
      Real.sqrt (localHarmonicEnergy a q R0) :=
    Real.sqrt_le_sqrt hminEnergy
  have hidentity : T (P e - e) = R0 + (-RP) := by
    dsimp only [R0, RP]
    rw [map_sub]
    abel
  have htrialEnergy : Real.sqrt
      (localHarmonicEnergy a q (T (P e - e))) ≤
      2 * Real.sqrt (localHarmonicEnergy a q R0) := by
    rw [hidentity]
    calc
      Real.sqrt (localHarmonicEnergy a q (R0 + -RP)) ≤
          Real.sqrt (localHarmonicEnergy a q R0) +
            Real.sqrt (localHarmonicEnergy a q (-RP)) := by
        unfold localHarmonicEnergy
        exact sqrt_normalizedLocalSymmetricEnergy_add_le hEll
          (by
            have hreal := volume_openCubeSet_originCube_toReal_pos
              (d := d) (q : ℤ)
            exact (ENNReal.toReal_pos_iff.mp hreal).1)
          (volume_openCubeSet_lt_top (originCube d (q : ℤ))).ne _ _
      _ = Real.sqrt (localHarmonicEnergy a q R0) +
          Real.sqrt (localHarmonicEnergy a q RP) := by
            have hnegEnergy : localHarmonicEnergy a q (-RP) =
                localHarmonicEnergy a q RP := by
              show normalizedLocalSymmetricEnergy hEll
                  (-(RP : LocalGradientL2 d q)) =
                normalizedLocalSymmetricEnergy hEll (RP : LocalGradientL2 d q)
              exact normalizedLocalSymmetricEnergy_neg hEll _
            rw [hnegEnergy]
      _ ≤ 2 * Real.sqrt (localHarmonicEnergy a q R0) := by
            linarith only [hminSqrt]
  have htailE : Real.sqrt (localHarmonicEnergy a q R0) ≤
      K * euclideanNorm e := by
    simpa only [hEll, R0, J, T, hqm] using htail e
  let z : Vec d := P e - e
  let t : ℕ := m - q - 2
  have hmt : q + t + 2 = m := by dsimp only [t]; omega
  have hzCoercive := hcoercive a delta n0 hdelta hgood q t hnq z
  rw [hmt] at hzCoercive
  let w := finiteCubeSolutionRestriction a
    (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm)
    (finiteAffineCubeSolution a (m : ℤ) z)
  have herror : scalarIdentityWeakError a s (q : ℤ) ≤ 1 :=
    (hgood.weakError_le hnq).trans (hdelta.2.trans hc1)
  have havg := euclideanNorm_cubeAverageVec_solutionGradient_le
    a s hs (q : ℤ) herror w
  have hclass : (T z : LocalGradientL2 d q) = w.toH1.gradToHilbertVectorL2 := by
    rfl
  have henergyEq : Book.Ch03.h1EnergyNormOnCube (originCube d (q : ℤ)) a w.toH1 =
      Real.sqrt (localHarmonicEnergy a q (T z)) := by
    unfold localHarmonicEnergy
    rw [hclass]
    exact (sqrt_normalizedEnergy_grad_eq_h1EnergyNormOnCube_restriction
      a (q : ℤ) w.toH1).symm
  have havg' : euclideanNorm
      (cubeAverageVec (originCube d (q : ℤ))
        (finiteAffineSolution a (m : ℤ) z).toH1.grad) ≤
        Real.sqrt (4 * (d : ℝ)) *
        Real.sqrt (localHarmonicEnergy a q (T z)) := by
    have hwgrad : w.toH1.grad =
        (finiteAffineSolution a (m : ℤ) z).toH1.grad := by
      rfl
    rw [← hwgrad, ← henergyEq]
    exact havg
  have hzEnergy : Real.sqrt (localHarmonicEnergy a q (T z)) ≤
      2 * K * euclideanNorm e := by
    have hKnorm : 0 ≤ K * euclideanNorm e :=
      mul_nonneg hK (euclideanNorm_nonneg e)
    calc
      _ ≤ 2 * Real.sqrt (localHarmonicEnergy a q R0) := by
        simpa only [z] using htrialEnergy
      _ ≤ 2 * (K * euclideanNorm e) :=
        by linarith only [htailE, hKnorm]
      _ = 2 * K * euclideanNorm e := by ring
  calc
    euclideanNorm (P e - e) = euclideanNorm z := rfl
    _ ≤ 2 * euclideanNorm
        (cubeAverageVec (originCube d (q : ℤ))
          (finiteAffineSolution a (m : ℤ) z).toH1.grad) := hzCoercive
    _ ≤ 2 * (Real.sqrt (4 * (d : ℝ)) *
        Real.sqrt (localHarmonicEnergy a q (T z))) :=
      mul_le_mul_of_nonneg_left havg' (by norm_num)
    _ ≤ 2 * (Real.sqrt (4 * (d : ℝ)) *
        (2 * K * euclideanNorm e)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hzEnergy (Real.sqrt_nonneg _)) (by norm_num)
    _ = 4 * Real.sqrt (4 * (d : ℝ)) * K * euclideanNorm e := by ring

/-- A strict near-identity coefficient makes the canonical weighted
projection bijective and hence supplies the finite-to-infinite slope
reparameterization. -/
theorem finiteCorrectorWeightedProjection_bijective
    {d : ℕ} (P : Vec d →ₗ[ℝ] Vec d) (theta : ℝ)
    (htheta : theta < 1)
    (hclose : ∀ e : Vec d,
      euclideanNorm (P e - e) ≤ theta * euclideanNorm e) :
    Function.Bijective P :=
  linearMap_bijective_of_euclideanNorm_sub_identity_lt_one
    P theta htheta hclose

end

end Root
end HighContrast
end HCPolySupport
