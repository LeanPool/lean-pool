/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineBestFit
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCubeSolutionRestriction
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCubeEnergyRestriction
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSuccessorLocalEnergy
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzFluctuation
public import LeanPool.HighContrastHomogenization.Provider.Regularity.HarmonicAffineDecay
public import LeanPool.HighContrastHomogenization.Provider.Regularity.HarmonicReplacementL2AtErrorOrder
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.ABK26.LocalCoarseGrainingPDE
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarseCaccioppoli
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarsePoincare
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.Energy
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.EndPoints
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeBesovPoincare

/-!
# High-contrast homogenization: Provider.Regularity.FiniteLipschitzCoreBase

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Shared analytic core for finite large-scale regularity

This module contains the common affine approximation, replacement, and
Poincare estimates used by the recurrence and best-fit branches.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Book.Ch03
open scoped BigOperators ENNReal

noncomputable section


namespace FiniteLipschitzCoreInternal

/-- Restrict a solution on the origin cube at scale `m` to scale `min k m`,
so the requested local scale never exceeds its domain. -/
@[expose]
noncomputable def finiteLipschitzRestriction
    {d : ℕ} (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a) (k : ℤ) :
    Book.Ch03.CubeSolution (originCube d (min k m)) a :=
  finiteCubeSolutionRestriction a (min_le_right k m) u

@[simp] theorem finiteLipschitzRestriction_toFun
    {d : ℕ} (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a) (k : ℤ) :
    (finiteLipschitzRestriction a m u k).toH1.toFun = u.toH1.toFun := by
  rfl

@[simp] theorem finiteLipschitzRestriction_grad
    {d : ℕ} (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a) (k : ℤ) :
    (finiteLipschitzRestriction a m u k).toH1.grad = u.toH1.grad := by
  rfl

/-- The coefficient-weighted H¹ energy norm of the solution on the origin
cube at scale `min k m`. -/
@[expose]
noncomputable def finiteLipschitzEnergyRow
    {d : ℕ} (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a) (k : ℤ) : ℝ :=
  Book.Ch03.h1EnergyNormOnCube (originCube d (min k m)) a
    (finiteLipschitzRestriction a m u k).toH1

/-- The intercept of the L² best affine fit to the restricted solution on the
origin cube at scale `min k m`. -/
@[expose]
noncomputable def finiteLipschitzBestIntercept
    {d : ℕ} (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a) (k : ℤ) : ℝ :=
  originCubeAffineBestFitIntercept d (min k m)
    (finiteLipschitzRestriction a m u k).toH1.toScalarL2

/-- The slope of the L² best affine fit to the restricted solution on the
origin cube at scale `min k m`. -/
@[expose]
noncomputable def finiteLipschitzBestSlope
    {d : ℕ} (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a) (k : ℤ) : Vec d :=
  originCubeAffineBestFitSlope d (min k m)
    (finiteLipschitzRestriction a m u k).toH1.toScalarL2

/-- The normalized affine approximation error of the restricted solution,
using its best-fit intercept and slope at scale `min k m`. -/
@[expose]
noncomputable def finiteLipschitzAffineErrorRow
    {d : ℕ} (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a) (k : ℤ) : ℝ :=
  normalizedAffineCandidateError (originCube d (min k m))
    (finiteLipschitzRestriction a m u k).toH1.toFun
    (finiteLipschitzBestIntercept a m u k)
    (finiteLipschitzBestSlope a m u k)

theorem finiteLipschitzEnergyRow_nonneg
    {d : ℕ} (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a) (k : ℤ) :
    0 ≤ finiteLipschitzEnergyRow a m u k := by
  unfold finiteLipschitzEnergyRow Book.Ch03.h1EnergyNormOnCube
  exact Real.sqrt_nonneg _

theorem finiteLipschitzEnergyRow_eq_h1EnergyNormOnCube_of_le
    {d : ℕ} (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a)
    (k : ℤ) (hkm : k ≤ m) :
    finiteLipschitzEnergyRow a m u k =
      Book.Ch03.h1EnergyNormOnCube (originCube d k) a
        (finiteCubeSolutionRestriction a hkm u).toH1 := by
  have hcoeff : (a.coeffOn (originCube d (min k m))).toCoeffField =
      (a.coeffOn (originCube d k)).toCoeffField :=
    congrArg (fun Q : TriadicCube d ↦ (a.coeffOn Q).toCoeffField)
      (congrArg (originCube d) (min_eq_left hkm))
  have hset : openCubeSet (originCube d (min k m)) =
      openCubeSet (originCube d k) :=
    congrArg openCubeSet (congrArg (originCube d) (min_eq_left hkm))
  unfold finiteLipschitzEnergyRow Book.Ch03.h1EnergyNormOnCube
    Book.Ch03.localizedCoeffEnergyValue
  simp only [finiteLipschitzRestriction_grad, finiteCubeSolutionRestriction_grad]
  rw [hcoeff, hset]

theorem finiteLipschitzEnergyRow_self
    {d : ℕ} (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a) :
    finiteLipschitzEnergyRow a m u m =
      Book.Ch03.h1EnergyNormOnCube (originCube d m) a u.toH1 := by
  calc
    finiteLipschitzEnergyRow a m u m =
        Book.Ch03.h1EnergyNormOnCube (originCube d m) a
          (finiteCubeSolutionRestriction a (le_refl m) u).toH1 :=
      finiteLipschitzEnergyRow_eq_h1EnergyNormOnCube_of_le a m u m (le_refl m)
    _ = Book.Ch03.h1EnergyNormOnCube (originCube d m) a u.toH1 := by
      unfold Book.Ch03.h1EnergyNormOnCube Book.Ch03.localizedCoeffEnergyValue
      simp only [finiteCubeSolutionRestriction_grad]

theorem finiteLipschitzAffineErrorRow_nonneg
    {d : ℕ} (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a) (k : ℤ) :
    0 ≤ finiteLipschitzAffineErrorRow a m u k := by
  exact normalizedAffineCandidateError_nonneg _ _ _ _

theorem solutionEnergyNorm_eq_h1EnergyNormOnCube
    {d : ℕ} (Q : TriadicCube d) (a : Book.Ch03.CoeffFamily d)
    (u : Book.Ch03.CubeSolution Q a) :
    Book.Ch03.solutionEnergyNorm Q a u =
      Book.Ch03.h1EnergyNormOnCube Q a u.toH1 := by
  rfl

theorem cubeBesovScaleWeight_one_originCube_sub_nat
    {d : ℕ} (k : ℤ) (N : ℕ) :
    cubeBesovScaleWeight 1 (originCube d (k - (N : ℤ))) =
      (3 : ℝ) ^ N * cubeBesovScaleWeight 1 (originCube d k) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.cast_succ]
      have hindex : k - (N : ℤ) - 1 = k - ((N : ℤ) + 1) := by
        ring
      rw [← hindex]
      have hone : cubeBesovScaleWeight 1
            (originCube d (k - (N : ℤ) - 1)) =
          3 * cubeBesovScaleWeight 1 (originCube d (k - (N : ℤ))) := by
        unfold cubeBesovScaleWeight
        rw [Real.rpow_neg_one, Real.rpow_neg_one]
        change ((3 : ℝ) ^ (k - (N : ℤ) - 1))⁻¹ =
          3 * ((3 : ℝ) ^ (k - (N : ℤ)))⁻¹
        rw [show k - (N : ℤ) = (k - (N : ℤ) - 1) + 1 by ring]
        rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
        field_simp
        ring_nf
      rw [hone, ih]
      ring

theorem cubeLpNorm_originCube_sub_nat_le
    {d : ℕ} (k : ℤ) (N : ℕ) (f : Vec d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d k))) :
    cubeLpNorm (originCube d (k - (N : ℤ))) (2 : ℝ≥0∞) f ≤
      (((3 ^ d) ^ N : ℕ) : ℝ) *
        cubeLpNorm (originCube d k) (2 : ℝ≥0∞) f := by
  have hraw :=
    CubeCalderonZygmund.eLpNorm_centralDescendant_le_descendantCount_mul
      (originCube d k) N FiniteLpExponent.two f
  rw [centralDescendant_originCube_eq_originCube_sub] at hraw
  have htop :
      ENNReal.ofReal (((3 ^ d) ^ N : ℕ) : ℝ) *
          eLpNorm f 2 (normalizedCubeMeasure (originCube d k)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono htop hraw
  simpa [cubeLpNorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal,
    Nat.cast_nonneg] using hreal

theorem normalizedCubeL2Distance_originCube_sub_nat_le
    {d : ℕ} (k : ℤ) (N : ℕ) (f g : Vec d → ℝ)
    (hfg : MemLp (fun x ↦ f x - g x) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d k))) :
    normalizedCubeL2Distance (originCube d (k - (N : ℤ))) f g ≤
      ((3 : ℝ) ^ N * (((3 ^ d) ^ N : ℕ) : ℝ)) *
        normalizedCubeL2Distance (originCube d k) f g := by
  have hnorm := cubeLpNorm_originCube_sub_nat_le k N
    (fun x ↦ f x - g x) hfg
  have hweight := cubeBesovScaleWeight_one_originCube_sub_nat (d := d) k N
  have hweight_nonneg : 0 ≤ cubeBesovScaleWeight 1
      (originCube d (k - (N : ℤ))) := cubeBesovScaleWeight_nonneg 1 _
  unfold normalizedCubeL2Distance
  rw [hweight]
  calc
    ((3 : ℝ) ^ N * cubeBesovScaleWeight 1 (originCube d k)) *
          cubeLpNorm (originCube d (k - (N : ℤ))) (2 : ℝ≥0∞)
            (fun x ↦ f x - g x) ≤
        ((3 : ℝ) ^ N * cubeBesovScaleWeight 1 (originCube d k)) *
          ((((3 ^ d) ^ N : ℕ) : ℝ) *
            cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
              (fun x ↦ f x - g x)) := by
      exact mul_le_mul_of_nonneg_left hnorm
        (mul_nonneg (by positivity) (cubeBesovScaleWeight_nonneg 1 _))
    _ = ((3 : ℝ) ^ N * (((3 ^ d) ^ N : ℕ) : ℝ)) *
          (cubeBesovScaleWeight 1 (originCube d k) *
            cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
              (fun x ↦ f x - g x)) := by ring

theorem cubeSolution_isWeakSolutionOn
    {d : ℕ} {Q : TriadicCube d} {a : Book.Ch03.CoeffFamily d}
    (u : Book.Ch03.CubeSolution Q a) :
    IsWeakSolutionOn (a.coeffOn Q).toCoeffField
      (Book.Ch02.cubeDomain Q : Set (Vec d)) u.toH1.grad := by
  intro phi hphi
  let psi : H10Function (Book.Ch02.cubeDomain Q : Set (Vec d)) :=
    H10Function.ofContDiff (Book.Ch02.cubeDomain Q).isOpen
      hphi.contDiff hphi.hasCompactSupport hphi.tsupport_subset
  have hpsiGrad : psi.toH1Function.grad = smoothGrad phi := rfl
  have hflux := Book.Ch02.Solution.flux_memVectorL2 u
  have htest : MemVectorL2 (Book.Ch02.cubeDomain Q : Set (Vec d))
      (smoothGrad phi) := by
    simpa only [← hpsiGrad] using psi.toH1Function.grad_memVectorL2
  refine ⟨?_, ?_⟩
  · exact integrableOn_vecDot_of_memVectorL2 htest hflux
  · have hzero := u.isHarmonic.2 psi
    simpa only [Book.Ch02.cubeDomain_coe, hpsiGrad, vecDot_comm] using hzero

theorem identityReplacement_weakPoisson
    {d : ℕ} (a : Book.Ch03.CoeffFamily d) (k : ℤ)
    (u : H1Function
      (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)))
    (hu : IsWeakSolutionOn (a.coeffOn (originCube d k)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)) u.grad) :
    WeakPoissonEquationOn (openCubeSet (originCube d k))
      (identityHarmonicReplacementDatum a k u hu).v (fun _ ↦ 0) := by
  have hv := (identityHarmonicReplacementDatum_characterization a k u hu).1
  intro phi hphi hcompact hsupport
  let psi : H10Function
      (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)) :=
    H10Function.ofContDiff (isOpen_openCubeSet (originCube d k))
      hphi hcompact hsupport
  have hpsiGrad : psi.toH1Function.grad = euclideanGradient phi := rfl
  have hweak := hv psi
  simpa [Book.Ch02.cubeDomain_coe, identityConstantCoeffMatrix_matrix,
    HCPolySupport.matVecMul_one, hpsiGrad, vecDot_zero_left, integral_zero] using hweak

theorem originCubeAffineH1LinearMap_weakPoisson
    (d : ℕ) (k : ℤ) (p : AffineCoefficients d) :
    WeakPoissonEquationOn (openCubeSet (originCube d k))
      (originCubeAffineH1LinearMap d k p) (fun _ ↦ 0) := by
  intro phi hphi hcompact hsupport
  let psi : H10Function (openCubeSet (originCube d k)) :=
    H10Function.ofContDiff (isOpen_openCubeSet (originCube d k))
      hphi hcompact hsupport
  have hpsiGrad : psi.toH1Function.grad = euclideanGradient phi := rfl
  have hzero := integral_vecDot_const_zeroTraceGrad_eq_zero psi p.2
  simpa only [originCubeAffineH1LinearMap_grad, hpsiGrad, zero_mul,
    integral_zero] using hzero

theorem normalizedAffineCandidateError_originCube_sub_nat_le
    {d : ℕ} (k : ℤ) (N : ℕ) (f : Vec d → ℝ) (c : ℝ) (e : Vec d)
    (hmem : MemLp (fun x ↦ f x - (c + vecDot e x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d k))) :
    normalizedAffineCandidateError (originCube d (k - (N : ℤ))) f c e ≤
      ((3 : ℝ) ^ N * (((3 ^ d) ^ N : ℕ) : ℝ)) *
        normalizedAffineCandidateError (originCube d k) f c e := by
  exact normalizedCubeL2Distance_originCube_sub_nat_le k N f
    (fun x ↦ c + vecDot e x) hmem

theorem normalizedAffineCandidateError_zero_sub_le_add
    {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ)
    (c₁ c₂ : ℝ) (e₁ e₂ : Vec d)
    (h₁ : MemLp (fun x ↦ f x - (c₁ + vecDot e₁ x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q))
    (h₂ : MemLp (fun x ↦ f x - (c₂ + vecDot e₂ x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q)) :
    normalizedAffineCandidateError Q (fun _ ↦ 0) (c₁ - c₂) (e₁ - e₂) ≤
      normalizedAffineCandidateError Q f c₁ e₁ +
        normalizedAffineCandidateError Q f c₂ e₂ := by
  let r₁ : Vec d → ℝ := fun x ↦ f x - (c₁ + vecDot e₁ x)
  let r₂ : Vec d → ℝ := fun x ↦ f x - (c₂ + vecDot e₂ x)
  have htri := cubeLpNorm_add_le Q (2 : ℝ≥0∞) r₁ (-r₂) h₁ h₂.neg
    (by norm_num)
  have hneg : cubeLpNorm Q (2 : ℝ≥0∞) (-r₂) =
      cubeLpNorm Q (2 : ℝ≥0∞) r₂ := by
    unfold cubeLpNorm
    rw [MeasureTheory.eLpNorm_neg]
  have hweight : 0 ≤ cubeBesovScaleWeight 1 Q :=
    cubeBesovScaleWeight_nonneg 1 Q
  unfold normalizedAffineCandidateError normalizedCubeL2Distance
  rw [hneg] at htri
  calc
    cubeBesovScaleWeight 1 Q *
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ 0 - ((c₁ - c₂) + vecDot (e₁ - e₂) x)) =
        cubeBesovScaleWeight 1 Q * cubeLpNorm Q (2 : ℝ≥0∞) (r₁ + -r₂) := by
      congr 2
      funext x
      dsimp [r₁, r₂]
      rw [vecDot_sub_left]
      ring
    _ ≤ cubeBesovScaleWeight 1 Q *
          (cubeLpNorm Q (2 : ℝ≥0∞) r₁ +
            cubeLpNorm Q (2 : ℝ≥0∞) r₂) :=
      mul_le_mul_of_nonneg_left htri hweight
    _ = cubeBesovScaleWeight 1 Q * cubeLpNorm Q (2 : ℝ≥0∞) r₁ +
          cubeBesovScaleWeight 1 Q * cubeLpNorm Q (2 : ℝ≥0∞) r₂ := by
      ring

theorem exists_originCubeAffineSlopeErrorConstant
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℤ) (c : ℝ) (e : Vec d),
      euclideanNorm e ≤ C *
        normalizedAffineCandidateError (originCube d k) (fun _ ↦ 0) c e := by
  obtain ⟨C, hC, hCbound⟩ :=
    CubeCalderonZygmund.exists_harmonic_centralChild_euclideanGradient_cubeLpNorm_le d
  refine ⟨C, hC, ?_⟩
  intro k c e
  let v : H1Function (openCubeSet (originCube d k)) :=
    originCubeAffineH1LinearMap d k (-c, -e)
  have hv : WeakPoissonEquationOn (openCubeSet (originCube d k)) v (fun _ ↦ 0) := by
    simpa only [v] using
      originCubeAffineH1LinearMap_weakPoisson d k (-c, -e)
  have hbound := hCbound (originCube d k) v hv
  have hleft : cubeLpNorm
        (CubeCalderonZygmund.centralChild (originCube d k)) (2 : ℝ≥0∞)
        (fun x ↦ euclideanNorm (v.grad x)) = euclideanNorm e := by
    rw [show v.grad = fun _ ↦ -e by
      simpa only [v] using originCubeAffineH1LinearMap_grad d k (-c, -e)]
    rw [cubeLpNorm_const _ _ (euclideanNorm (-e)) (by norm_num)]
    simp only [Real.norm_of_nonneg (euclideanNorm_nonneg _), euclideanNorm_neg]
  have hright :
      (cubeScaleFactor (originCube d k))⁻¹ *
          cubeLpNorm (originCube d k) (2 : ℝ≥0∞) v.toFun =
        normalizedAffineCandidateError (originCube d k) (fun _ ↦ 0) c e := by
    unfold normalizedAffineCandidateError normalizedCubeL2Distance
    rw [show v.toFun = fun x ↦ -(c + vecDot e x) by
      funext x
      dsimp only [v]
      change (originCubeAffineH1LinearMap d k (-c, -e)).toFun x =
        -(c + vecDot e x)
      rw [congrFun (originCubeAffineH1LinearMap_toFun d k (-c, -e)) x]
      rw [vecDot_neg_left]
      ring]
    congr 2
    · unfold cubeBesovScaleWeight
      rw [Real.rpow_neg_one]
    · funext x
      ring
  rw [← hleft, ← hright]
  simpa only [mul_assoc] using hbound

theorem finiteLipschitzBestResidual_memLp
    {d : ℕ} (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a)
    {k : ℤ} (hkm : k ≤ m) :
    MemLp
      (fun x ↦ u.toH1.toFun x -
        (finiteLipschitzBestIntercept a m u k +
          vecDot (finiteLipschitzBestSlope a m u k) x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d k)) := by
  let uk : Book.Ch03.CubeSolution (originCube d k) a :=
    finiteCubeSolutionRestriction a hkm u
  let p : AffineCoefficients d :=
    (finiteLipschitzBestIntercept a m u k,
      finiteLipschitzBestSlope a m u k)
  let v : H1Function (openCubeSet (originCube d k)) :=
    uk.toH1 - originCubeAffineH1LinearMap d k p
  have hv := v.memL2_normalizedCubeMeasure
  simpa only [v, p, H1Function.sub_toFun,
    finiteCubeSolutionRestriction_toFun,
    originCubeAffineH1LinearMap_toFun] using! hv

theorem finiteLipschitzAffineErrorRow_best_le
    {d : ℕ} (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a)
    {k : ℤ} (hkm : k ≤ m) (c : ℝ) (e : Vec d) :
    finiteLipschitzAffineErrorRow a m u k ≤
      normalizedAffineCandidateError (originCube d k) u.toH1.toFun c e := by
  have hmin : min k m = k := min_eq_left hkm
  simpa only [finiteLipschitzAffineErrorRow,
    finiteLipschitzBestIntercept, finiteLipschitzBestSlope,
    finiteLipschitzRestriction_toFun, hmin] using
      normalizedAffineCandidateError_bestFit_le d (min k m)
        (finiteLipschitzRestriction a m u k).toH1 c e

theorem exists_finiteLipschitzAdjacentSlopeConstant
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ)
        (u : Book.Ch03.CubeSolution (originCube d m) a)
        (k : ℤ), k + 1 ≤ m →
          euclideanNorm
              (finiteLipschitzBestSlope a m u k -
                finiteLipschitzBestSlope a m u (k + 1)) ≤
            C * (finiteLipschitzAffineErrorRow a m u k +
              finiteLipschitzAffineErrorRow a m u (k + 1)) := by
  obtain ⟨C₀, hC₀, hC₀bound⟩ := exists_originCubeAffineSlopeErrorConstant d
  let A : ℝ := 3 * ((3 ^ d : ℕ) : ℝ)
  let C : ℝ := C₀ * (1 + A)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos hC₀ (by linarith only [hA_nonneg])
  refine ⟨C, hC, ?_⟩
  intro a m u k hkm
  let c₀ := finiteLipschitzBestIntercept a m u k
  let e₀ := finiteLipschitzBestSlope a m u k
  let c₁ := finiteLipschitzBestIntercept a m u (k + 1)
  let e₁ := finiteLipschitzBestSlope a m u (k + 1)
  let E₀ := finiteLipschitzAffineErrorRow a m u k
  let E₁ := finiteLipschitzAffineErrorRow a m u (k + 1)
  have hk : k ≤ m := by omega
  have hres₀ : MemLp (fun x ↦ u.toH1.toFun x - (c₀ + vecDot e₀ x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d k)) := by
    simpa only [c₀, e₀] using finiteLipschitzBestResidual_memLp a m u hk
  have hres₁Outer :
      MemLp (fun x ↦ u.toH1.toFun x - (c₁ + vecDot e₁ x))
        (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d (k + 1))) := by
    simpa only [c₁, e₁] using
      finiteLipschitzBestResidual_memLp a m u hkm
  have hres₁ : MemLp (fun x ↦ u.toH1.toFun x - (c₁ + vecDot e₁ x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d k)) := by
    have h := CubeCalderonZygmund.memLp_centralDescendant_of_memLp
      (Q := originCube d (k + 1)) 1 hres₁Outer
    rw [centralDescendant_originCube_eq_originCube_sub] at h
    change MemLp (fun x ↦ u.toH1.toFun x - (c₁ + vecDot e₁ x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure
        (originCube d (k + 1 - (1 : ℤ)))) at h
    rw [show k + 1 - (1 : ℤ) = k by ring] at h
    exact h
  have houter :
      normalizedAffineCandidateError (originCube d k) u.toH1.toFun c₁ e₁ ≤
        A * E₁ := by
    have h := normalizedAffineCandidateError_originCube_sub_nat_le
      (d := d) (k + 1) 1 u.toH1.toFun c₁ e₁ hres₁Outer
    change normalizedAffineCandidateError
        (originCube d (k + 1 - (1 : ℤ))) u.toH1.toFun c₁ e₁ ≤
      ((3 : ℝ) ^ 1 * (((3 ^ d) ^ 1 : ℕ) : ℝ)) *
        normalizedAffineCandidateError (originCube d (k + 1))
          u.toH1.toFun c₁ e₁ at h
    rw [show k + 1 - (1 : ℤ) = k by ring] at h
    simpa only [A, E₁, c₁, e₁,
      finiteLipschitzAffineErrorRow, finiteLipschitzRestriction_toFun,
      show min (k + 1) m = k + 1 by exact min_eq_left hkm,
      pow_one] using h
  have hbest₀ :
      normalizedAffineCandidateError (originCube d k) u.toH1.toFun c₀ e₀ = E₀ := by
    simp only [E₀, c₀, e₀, finiteLipschitzAffineErrorRow,
      finiteLipschitzBestIntercept, finiteLipschitzBestSlope,
      finiteLipschitzRestriction_toFun, min_eq_left hk]
  have htriangle :
      normalizedAffineCandidateError (originCube d k) (fun _ ↦ 0)
          (c₀ - c₁) (e₀ - e₁) ≤ E₀ + A * E₁ := by
    calc
      normalizedAffineCandidateError (originCube d k) (fun _ ↦ 0)
          (c₀ - c₁) (e₀ - e₁) ≤
          normalizedAffineCandidateError (originCube d k) u.toH1.toFun c₀ e₀ +
            normalizedAffineCandidateError (originCube d k) u.toH1.toFun c₁ e₁ :=
        normalizedAffineCandidateError_zero_sub_le_add
          (originCube d k) u.toH1.toFun c₀ c₁ e₀ e₁ hres₀ hres₁
      _ ≤ E₀ + A * E₁ := by
        rw [hbest₀]
        exact add_le_add (le_refl E₀) houter
  have hslope := hC₀bound k (c₀ - c₁) (e₀ - e₁)
  have hE₀ : 0 ≤ E₀ := finiteLipschitzAffineErrorRow_nonneg a m u k
  have hE₁ : 0 ≤ E₁ := finiteLipschitzAffineErrorRow_nonneg a m u (k + 1)
  calc
    euclideanNorm (finiteLipschitzBestSlope a m u k -
          finiteLipschitzBestSlope a m u (k + 1)) = euclideanNorm (e₀ - e₁) := rfl
    _ ≤ C₀ * normalizedAffineCandidateError (originCube d k) (fun _ ↦ 0)
          (c₀ - c₁) (e₀ - e₁) := hslope
    _ ≤ C₀ * (E₀ + A * E₁) :=
      mul_le_mul_of_nonneg_left htriangle hC₀.le
    _ ≤ C₀ * (1 + A) * (E₀ + E₁) := by
      have hinside : E₀ + A * E₁ ≤ (1 + A) * (E₀ + E₁) := by
        nlinarith only [hA_nonneg, hE₀, hE₁]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hinside hC₀.le
    _ = C * (finiteLipschitzAffineErrorRow a m u k +
          finiteLipschitzAffineErrorRow a m u (k + 1)) := rfl

theorem poincareLowerEllipticityFactor_finite_two_eq_sqrt_inv
    {d : ℕ} (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) {s : ℝ} :
    Book.Ch03.poincareLowerEllipticityFactor Q a s (.finite 2) =
      Real.sqrt ((Book.Ch02.lambdaSq Q s (.finite 2) a)⁻¹) := by
  have hleft :
      Real.sqrt ((Book.Ch02.lambdaSq Q s (.finite 2) a)⁻¹) =
        Real.rpow (Book.Ch02.lambdaSq Q s (.finite 2) a) (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_eq_inv_rpow]
    rw [← Real.rpow_eq_pow]
    ring_nf
  have hexponent : (-1 / 2 : ℝ) = (-(1 / 2 : ℝ)) := by ring
  simpa [Book.Ch03.poincareLowerEllipticityFactor, hexponent] using hleft.symm

theorem scalarIdentityWeakError_le_one_lowerEllipticity
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d}
    {s : ℝ} (hs : 0 < s) {k : ℤ}
    (herror : scalarIdentityWeakError a s k ≤ 1) :
    (Book.Ch02.lambdaSq (originCube d k) s (.finite 2) a)⁻¹ ≤
      4 * (d : ℝ) := by
  let E := scalarIdentityWeakError a s k
  have hE_nonneg : 0 ≤ E := scalarIdentityWeakError_nonneg a s k
  have hE_sq : E ^ 2 + 1 ≤ 2 := by
    nlinarith only [hE_nonneg, herror]
  have hlower :=
    Book.Ch02.sigma_mul_lambdaSq_finite_two_inv_le_card_mul_homogenizationError_sq_add_one
      (originCube d k) a hs (by norm_num : (0 : ℝ) < 1)
  have hlower' :
      (Book.Ch02.lambdaSq (originCube d k) s (.finite 2) a)⁻¹ ≤
        2 * (d : ℝ) * (E ^ 2 + 1) := by
    simpa [E, scalarIdentityWeakError, scalarMatrix] using hlower
  calc
    (Book.Ch02.lambdaSq (originCube d k) s (.finite 2) a)⁻¹ ≤
        2 * (d : ℝ) * (E ^ 2 + 1) := hlower'
    _ ≤ 2 * (d : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left hE_sq (by positivity)
    _ = 4 * (d : ℝ) := by ring

theorem scalarIdentityWeakError_le_one_qoneEllipticity
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d}
    {s r : ℝ} (hs : 0 < s) (hsr : s < r) {k : ℤ}
    (herror : scalarIdentityWeakError a s k ≤ 1) :
    Book.Ch02.LambdaS (originCube d k) r a ≤
        exponentGapFactor s r * (4 * (d : ℝ)) ∧
      (Book.Ch02.lambdaS (originCube d k) r a)⁻¹ ≤
        exponentGapFactor s r * (4 * (d : ℝ)) := by
  let E := scalarIdentityWeakError a s k
  have hgap_nonneg : 0 ≤ exponentGapFactor s r :=
    (exponentGapFactor_pos hs hsr).le
  have hE_nonneg : 0 ≤ E := scalarIdentityWeakError_nonneg a s k
  have hE_sq : E ^ 2 + 1 ≤ 2 := by
    nlinarith only [hE_nonneg, herror]
  have hupperRaw :=
    Book.Ch02.inv_mul_LambdaSq_finite_two_le_card_mul_homogenizationError_sq_add_one
      (originCube d k) a hs (by norm_num : (0 : ℝ) < 1)
  have hlowerRaw :=
    Book.Ch02.sigma_mul_lambdaSq_finite_two_inv_le_card_mul_homogenizationError_sq_add_one
      (originCube d k) a hs (by norm_num : (0 : ℝ) < 1)
  have hupper : Book.Ch02.LambdaSq (originCube d k) s (.finite 2) a ≤
      2 * (d : ℝ) * (E ^ 2 + 1) := by
    simpa [E, scalarIdentityWeakError, scalarMatrix] using hupperRaw
  have hlower : (Book.Ch02.lambdaSq (originCube d k) s (.finite 2) a)⁻¹ ≤
      2 * (d : ℝ) * (E ^ 2 + 1) := by
    simpa [E, scalarIdentityWeakError, scalarMatrix] using hlowerRaw
  constructor
  · calc
      Book.Ch02.LambdaS (originCube d k) r a ≤
          exponentGapFactor s r *
            Book.Ch02.LambdaSq (originCube d k) s (.finite 2) a := by
        simpa only [exponentGapFactor] using
          LambdaS_le_exponentGap_mul_LambdaSq_finite_two
            (originCube d k) a hs hsr
      _ ≤ exponentGapFactor s r * (2 * (d : ℝ) * (E ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left hupper hgap_nonneg
      _ ≤ exponentGapFactor s r * (2 * (d : ℝ) * 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hE_sq (by positivity)) hgap_nonneg
      _ = exponentGapFactor s r * (4 * (d : ℝ)) := by ring
  · calc
      (Book.Ch02.lambdaS (originCube d k) r a)⁻¹ ≤
          exponentGapFactor s r *
            (Book.Ch02.lambdaSq (originCube d k) s (.finite 2) a)⁻¹ := by
        simpa only [exponentGapFactor] using
          lambdaS_inv_le_exponentGap_mul_lambdaSq_finite_two_inv
            (originCube d k) a hs hsr
      _ ≤ exponentGapFactor s r * (2 * (d : ℝ) * (E ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left hlower hgap_nonneg
      _ ≤ exponentGapFactor s r * (2 * (d : ℝ) * 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hE_sq (by positivity)) hgap_nonneg
      _ = exponentGapFactor s r * (4 * (d : ℝ)) := by ring

theorem caccioppoliPrefactor_weakError_le_one
    {d : ℕ} [NeZero d] {C₀ s r : ℝ}
    (hC₀ : 0 < C₀) (hs : 0 < s) (hsr : s < r) (hr_lt : r < 1 / 2)
    {a : Book.Ch02.TriadicCoeffFamily d} {k : ℤ}
    (herror : scalarIdentityWeakError a s k ≤ 1) :
    let D : ℝ := exponentGapFactor s r * (4 * (d : ℝ))
    let α : ℝ := r / (1 - 2 * r)
    let K : ℝ :=
      Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
        Real.rpow r (-(2 * r / (1 - 2 * r))) *
        Real.rpow (D * D) α * D
    Book.Ch03.caccioppoliPrefactor C₀ (originCube d k) a r r ≤
      K * cubeBesovScaleWeight 1 (originCube d k) ^ 2 := by
  dsimp
  let D : ℝ := exponentGapFactor s r * (4 * (d : ℝ))
  let α : ℝ := r / (1 - 2 * r)
  have hr : 0 < r := hs.trans hsr
  have hden : 0 < 1 - 2 * r := by linarith only [hr_lt]
  have hD : 0 < D := by
    dsimp [D]
    have hd : (0 : ℝ) < d := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    exact mul_pos (exponentGapFactor_pos hs hsr) (mul_pos (by norm_num) hd)
  have hα : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg hr.le hden.le
  obtain ⟨hLambda, hlambda⟩ :=
    scalarIdentityWeakError_le_one_qoneEllipticity hs hsr herror
  have hLambda_nonneg :
      0 ≤ Book.Ch02.LambdaS (originCube d k) r a := by
    unfold Book.Ch02.LambdaS
    exact Book.Ch02.LambdaSq_finite_nonneg _ _ hr (by norm_num)
  have hlambda_inv_nonneg :
      0 ≤ (Book.Ch02.lambdaS (originCube d k) r a)⁻¹ := by
    exact inv_nonneg.mpr (by
      unfold Book.Ch02.lambdaS
      exact Book.Ch02.lambdaSq_finite_nonneg _ _ hr (by norm_num))
  have htheta_nonneg :
      0 ≤ Book.Ch02.ThetaRatio (originCube d k) r r a := by
    unfold Book.Ch02.ThetaRatio
    exact div_nonneg hLambda_nonneg (by
      unfold Book.Ch02.lambdaS
      exact Book.Ch02.lambdaSq_finite_nonneg _ _ hr (by norm_num))
  have htheta :
      Book.Ch02.ThetaRatio (originCube d k) r r a ≤ D * D := by
    unfold Book.Ch02.ThetaRatio
    rw [div_eq_mul_inv]
    exact mul_le_mul hLambda hlambda hlambda_inv_nonneg hD.le
  have hthetaPow := Real.rpow_le_rpow htheta_nonneg htheta hα
  have hfront_nonneg :
      0 ≤ Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
        Real.rpow r (-(2 * r / (1 - 2 * r))) := by
    exact mul_nonneg (Real.rpow_nonneg (div_nonneg hC₀.le hden.le) _)
      (Real.rpow_nonneg hr.le _)
  have hscale : Real.rpow (3 : ℝ) (-2 * (k : ℝ)) =
      cubeBesovScaleWeight 1 (originCube d k) ^ 2 := by
    calc
      Real.rpow (3 : ℝ) (-2 * (k : ℝ)) =
          cubeBesovScaleWeight 2 (originCube d k) := by
        simpa using! Book.Ch03.publicDualBesovScaleWeight_eq_cubeBesovScaleWeight
          (originCube d k) (2 : ℝ)
      _ = cubeBesovScaleWeight 1 (originCube d k) *
          cubeBesovScaleWeight 1 (originCube d k) := by
        rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
        norm_num
      _ = cubeBesovScaleWeight 1 (originCube d k) ^ 2 := by ring
  unfold Book.Ch03.caccioppoliPrefactor
  rw [show 1 - r - r = 1 - 2 * r by ring]
  change
    Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
          Real.rpow r (-(2 * r / (1 - 2 * r))) *
          Real.rpow (Book.Ch02.ThetaRatio (originCube d k) r r a) α *
          Book.Ch02.LambdaS (originCube d k) r a *
          Real.rpow (3 : ℝ) (-2 * (k : ℝ)) ≤
      (Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
          Real.rpow r (-(2 * r / (1 - 2 * r))) *
          Real.rpow (D * D) α * D) *
        cubeBesovScaleWeight 1 (originCube d k) ^ 2
  rw [← hscale]
  have hscale_nonneg : 0 ≤ Real.rpow (3 : ℝ) (-2 * (k : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
            Real.rpow r (-(2 * r / (1 - 2 * r))) *
            Real.rpow (Book.Ch02.ThetaRatio (originCube d k) r r a) α *
            Book.Ch02.LambdaS (originCube d k) r a *
            Real.rpow (3 : ℝ) (-2 * (k : ℝ)) ≤
        Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
            Real.rpow r (-(2 * r / (1 - 2 * r))) *
            Real.rpow (D * D) α *
            Book.Ch02.LambdaS (originCube d k) r a *
            Real.rpow (3 : ℝ) (-2 * (k : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hthetaPow hfront_nonneg)
          hLambda_nonneg)
        hscale_nonneg
    _ ≤ Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
          Real.rpow r (-(2 * r / (1 - 2 * r))) *
          Real.rpow (D * D) α * D *
          Real.rpow (3 : ℝ) (-2 * (k : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLambda
          (mul_nonneg hfront_nonneg
            (Real.rpow_nonneg (mul_nonneg hD.le hD.le) _)))
        hscale_nonneg

theorem finiteCubeRestriction_sub_two_energy_eq_coreEnergy
    {d : ℕ} (a : Book.Ch02.TriadicCoeffFamily d)
    (k : ℤ) (u : Book.Ch03.CubeSolution (originCube d k) a) :
    Book.Ch03.h1EnergyNormOnCube (originCube d (k - 2)) a
        (finiteCubeSolutionRestriction a (by omega : k - 2 ≤ k) u).toH1 =
      Real.sqrt (Book.Ch03.interiorCaccioppoliCoreEnergy (originCube d k) a
        (cubeCenter (originCube d k)) u) := by
  let Q : TriadicCube d := originCube d k
  let R : TriadicCube d := originCube d (k - 2)
  have hsub : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_originCube_subset_of_le (by omega)
  have hcoeff : (a.coeffOn R).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet R)] (a.coeffOn Q).toCoeffField :=
    a.restrictsTo_of_subset hsub
  have henergy :
      Book.Ch03.localizedCoeffEnergyValue (openCubeSet R) (a.coeffOn R)
          (finiteCubeSolutionRestriction a (by omega : k - 2 ≤ k) u).toH1 =
        Book.Ch03.localizedCoeffEnergyValue (openCubeSet R) (a.coeffOn Q) u.toH1 := by
    rw [Book.Ch03.localizedCoeffEnergyValue_eq_volumeAverage_coefficientEnergyDensity,
      Book.Ch03.localizedCoeffEnergyValue_eq_volumeAverage_coefficientEnergyDensity]
    apply Book.Ch03.volumeAverage_eq_of_ae_eq
    filter_upwards [hcoeff] with x hx
    simp only [coefficientEnergyDensity, finiteCubeSolutionRestriction_grad, hx]
  unfold Book.Ch03.h1EnergyNormOnCube Book.Ch03.interiorCaccioppoliCoreEnergy
  rw [caccioppoliCoreSet_originCube_eq_openCubeSet_sub_two]
  exact congrArg Real.sqrt henergy

theorem exists_finiteLipschitzCaccioppoliAffineConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (k : ℤ)
        (u : Book.Ch03.CubeSolution (originCube d k) a) (c : ℝ) (e : Vec d),
        scalarIdentityWeakError a s k ≤ 1 →
          Book.Ch03.h1EnergyNormOnCube (originCube d (k - 2)) a
              (finiteCubeSolutionRestriction a (by omega : k - 2 ≤ k) u).toH1 ≤
            C * (normalizedAffineCandidateError (originCube d k) u.toH1.toFun c e +
              euclideanNorm e) := by
  rcases (Book.Ch03.coarseCaccioppoliTheory d).exists_constant with
    ⟨C₀, hC₀, _hboundary, hinterior⟩
  let r : ℝ := (s + 1 / 2) / 2
  have hsr : s < r := by
    dsimp only [r]
    linarith only [hs_lt]
  have hr : 0 < r := hs.trans hsr
  have hr_lt : r < 1 / 2 := by
    dsimp only [r]
    linarith only [hs_lt]
  let D : ℝ := exponentGapFactor s r * (4 * (d : ℝ))
  let α : ℝ := r / (1 - 2 * r)
  let K : ℝ :=
    Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
      Real.rpow r (-(2 * r / (1 - 2 * r))) *
      Real.rpow (D * D) α * D
  let A : ℝ := max 1 (cubeBesovW12LocalPoincareConstant d)
  let C : ℝ := 1 + 2 * Real.sqrt K * A
  have hden : 0 < 1 - 2 * r := by linarith only [hr_lt]
  have hD : 0 < D := by
    dsimp [D]
    have hd : (0 : ℝ) < d := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    exact mul_pos (exponentGapFactor_pos hs hsr) (mul_pos (by norm_num) hd)
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos
      (mul_pos
        (mul_pos (Real.rpow_pos_of_pos (div_pos hC₀ hden) _)
          (Real.rpow_pos_of_pos hr _))
        (Real.rpow_pos_of_pos (mul_pos hD hD) _)) hD
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro a k u c e herror
  let Q : TriadicCube d := originCube d k
  let W : ℝ := cubeBesovScaleWeight 1 Q
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toH1.toFun)
  let E : ℝ := normalizedAffineCandidateError Q u.toH1.toFun c e
  let N : ℝ := euclideanNorm e
  let B : ℝ := E + cubeBesovW12LocalPoincareConstant d * N
  have hW : 0 ≤ W := cubeBesovScaleWeight_nonneg 1 Q
  have hL : 0 ≤ L := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) _
  have hE : 0 ≤ E := normalizedAffineCandidateError_nonneg Q u.toH1.toFun c e
  have hN : 0 ≤ N := euclideanNorm_nonneg e
  have hP : 0 ≤ cubeBesovW12LocalPoincareConstant d :=
    cubeBesovW12LocalPoincareConstant_nonneg d
  have hB : 0 ≤ B := add_nonneg hE (mul_nonneg hP hN)
  have hpref : Book.Ch03.caccioppoliPrefactor C₀ Q a r r ≤
      K * W ^ 2 := by
    simpa only [Q, W, D, α, K] using
      caccioppoliPrefactor_weakError_le_one hC₀ hs hsr hr_lt herror
  have hoscEq : Book.Ch03.interiorCaccioppoliParentOscillationL2Sq Q a u = L ^ 2 := by
    have hfun : (fun x => u.toH1.toFun x - Book.Ch01.Legacy.normalizedAverage Q u.toH1.toFun) =
        cubeFluctuation Q u.toH1.toFun := by
      funext x
      simp [Book.Ch01.Legacy.normalizedAverage]
    unfold Book.Ch03.interiorCaccioppoliParentOscillationL2Sq
    rw [hfun]
    simpa [L] using
      Book.Ch03.normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq Q
        (cubeFluctuation Q u.toH1.toFun)
        (u.toH1.memL2_normalizedCubeMeasure.sub (memLp_const _))
  have hWL : W * L ≤ 2 * B := by
    simpa only [Q, W, L, E, N, B] using
      normalized_fluctuation_le_affine_error_add_slope Q u.toH1 c e
  have hcore := hinterior u hr hr (by linarith only [hr_lt] : r + r < 1)
  have hcoreBound :
      Book.Ch03.interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u ≤
        K * (2 * B) ^ 2 := by
    calc
      Book.Ch03.interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u ≤
          Book.Ch03.interiorCaccioppoliRHS C₀ Q a r r u := hcore
      _ = Book.Ch03.caccioppoliPrefactor C₀ Q a r r * L ^ 2 := by
        rw [Book.Ch03.interiorCaccioppoliRHS, hoscEq]
      _ ≤ (K * W ^ 2) * L ^ 2 :=
        mul_le_mul_of_nonneg_right hpref (sq_nonneg L)
      _ = K * (W * L) ^ 2 := by ring
      _ ≤ K * (2 * B) ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (mul_nonneg hW hL) (mul_nonneg (by norm_num) hB)).2 hWL)
          hK.le
  have hroot :
      Real.sqrt (Book.Ch03.interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u) ≤
        2 * Real.sqrt K * B := by
    apply (Real.sqrt_le_iff).2
    refine ⟨mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hB, ?_⟩
    calc
      Book.Ch03.interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u ≤
          K * (2 * B) ^ 2 := hcoreBound
      _ = (2 * Real.sqrt K * B) ^ 2 := by
        calc
          K * (2 * B) ^ 2 = (Real.sqrt K) ^ 2 * (2 * B) ^ 2 := by
            rw [Real.sq_sqrt hK.le]
          _ = (2 * Real.sqrt K * B) ^ 2 := by ring
  have hBA : B ≤ A * (E + N) := by
    have hP_le : cubeBesovW12LocalPoincareConstant d ≤ A := le_max_right _ _
    have hOne_le : 1 ≤ A := le_max_left _ _
    calc
      B = E + cubeBesovW12LocalPoincareConstant d * N := rfl
      _ ≤ A * E + A * N :=
        add_le_add
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hOne_le hE)
          (mul_le_mul_of_nonneg_right hP_le hN)
      _ = A * (E + N) := by ring
  have hfactor : 2 * Real.sqrt K * A ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_left zero_le_one
  calc
    Book.Ch03.h1EnergyNormOnCube (originCube d (k - 2)) a
          (finiteCubeSolutionRestriction a (by omega : k - 2 ≤ k) u).toH1 =
        Real.sqrt (Book.Ch03.interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u) := by
      simpa only [Q] using finiteCubeRestriction_sub_two_energy_eq_coreEnergy a k u
    _ ≤ 2 * Real.sqrt K * B := hroot
    _ ≤ 2 * Real.sqrt K * (A * (E + N)) :=
      mul_le_mul_of_nonneg_left hBA (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    _ = (2 * Real.sqrt K * A) * (E + N) := by ring
    _ ≤ C * (E + N) :=
      mul_le_mul_of_nonneg_right hfactor (add_nonneg hE hN)
    _ = C * (normalizedAffineCandidateError (originCube d k) u.toH1.toFun c e +
          euclideanNorm e) := rfl

theorem normalizedCubeL2Distance_comm
    {d : ℕ} (Q : TriadicCube d) (f g : Vec d → ℝ) :
    normalizedCubeL2Distance Q f g = normalizedCubeL2Distance Q g f := by
  unfold normalizedCubeL2Distance cubeLpNorm
  congr 1
  have hneg : (fun x ↦ f x - g x) = -(fun x ↦ g x - f x) := by
    funext x
    simp
  rw [hneg, MeasureTheory.eLpNorm_neg]

theorem exists_finiteLipschitzOneStepConstant_of_harmonic_decay
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2)
    (N : ℕ) (hN : 0 < N) (theta : ℝ) (htheta : 0 < theta)
    (hdecay : ∀ (k : ℤ) (v : H1Function (openCubeSet (originCube d k))),
      WeakPoissonEquationOn (openCubeSet (originCube d k)) v (fun _ => 0) →
        ∀ (c : ℝ) (e : Vec d), ∃ c' e',
          normalizedAffineCandidateError (originCube d (k - (N : ℤ)))
              v.toFun c' e' ≤
            theta * normalizedAffineCandidateError
              (originCube d k) v.toFun c e) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ)
        (u : Book.Ch03.CubeSolution (originCube d m) a)
        (k : ℤ), k ≤ m →
          finiteLipschitzAffineErrorRow a m u (k - (N : ℤ)) ≤
            theta * finiteLipschitzAffineErrorRow a m u k +
              C * scalarIdentityWeakError a s k * finiteLipschitzEnergyRow a m u k := by
  obtain ⟨C₀, hC₀, hreplacement⟩ :=
    exists_identityHarmonicReplacementL2EstimateConstant_at_error_order d s
      hs hs_lt
  let A : ℝ := (3 : ℝ) ^ N * (((3 ^ d) ^ N : ℕ) : ℝ)
  let C : ℝ := (A + theta) * C₀
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (add_pos_of_nonneg_of_pos hA htheta) hC₀
  refine ⟨C, hC, ?_⟩
  intro a m u k hkm
  let uk : Book.Ch03.CubeSolution (originCube d k) a :=
    finiteCubeSolutionRestriction a hkm u
  have huk : IsWeakSolutionOn (a.coeffOn (originCube d k)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)) uk.toH1.grad :=
    cubeSolution_isWeakSolutionOn uk
  let v := (identityHarmonicReplacementDatum a k uk.toH1 huk).v
  let c := finiteLipschitzBestIntercept a m u k
  let e := finiteLipschitzBestSlope a m u k
  let E := finiteLipschitzAffineErrorRow a m u k
  let D := finiteLipschitzEnergyRow a m u k
  let H := normalizedCubeL2Distance (originCube d k) uk.toH1.toFun v.toFun
  have hv : WeakPoissonEquationOn (openCubeSet (originCube d k)) v (fun _ ↦ 0) :=
    identityReplacement_weakPoisson a k uk.toH1 huk
  obtain ⟨c', e', hdec⟩ := hdecay k v hv c e
  have hdiff : MemLp (fun x ↦ uk.toH1.toFun x - v.toFun x) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d k)) :=
    uk.toH1.memL2_normalizedCubeMeasure.sub v.memL2_normalizedCubeMeasure
  have hdiffChild : MemLp (fun x ↦ uk.toH1.toFun x - v.toFun x) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d (k - (N : ℤ)))) := by
    have h := CubeCalderonZygmund.memLp_centralDescendant_of_memLp
      (Q := originCube d k) N hdiff
    rw [centralDescendant_originCube_eq_originCube_sub] at h
    exact h
  have hbestMem : MemLp (fun x ↦ uk.toH1.toFun x - (c + vecDot e x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d k)) := by
    simpa only [uk, c, e, finiteCubeSolutionRestriction_toFun] using
      finiteLipschitzBestResidual_memLp a m u hkm
  have hvCandidate :
      normalizedAffineCandidateError (originCube d k) v.toFun c e ≤ H + E := by
    have h := normalizedAffineCandidateError_le_distance_add
      (originCube d k) v.toFun uk.toH1.toFun c e
        (v.memL2_normalizedCubeMeasure.sub uk.toH1.memL2_normalizedCubeMeasure) hbestMem
    rw [normalizedCubeL2Distance_comm] at h
    simpa only [H, E, uk, finiteLipschitzAffineErrorRow,
      finiteLipschitzRestriction_toFun, min_eq_left hkm] using! h
  have hdec' :
      normalizedAffineCandidateError (originCube d (k - (N : ℤ))) v.toFun c' e' ≤
        theta * (H + E) := hdec.trans
      (mul_le_mul_of_nonneg_left hvCandidate htheta.le)
  have hsub : openCubeSet (originCube d (k - (N : ℤ))) ⊆
      openCubeSet (originCube d k) := openCubeSet_originCube_subset_of_le (by omega)
  let vR : H1Function (openCubeSet (originCube d (k - (N : ℤ)))) :=
    v.restrict (isOpen_openCubeSet _) hsub
  let ellR : H1Function (openCubeSet (originCube d (k - (N : ℤ)))) :=
    originCubeAffineH1LinearMap d (k - (N : ℤ)) (c', e')
  have hcandMem : MemLp (fun x ↦ v.toFun x - (c' + vecDot e' x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d (k - (N : ℤ)))) := by
    have hvR : MemLp v.toFun (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d (k - (N : ℤ)))) :=
      vR.memL2_normalizedCubeMeasure
    have hellR : MemLp (fun x => c' + vecDot e' x) (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d (k - (N : ℤ)))) := by
      simpa only [ellR, originCubeAffineH1LinearMap_toFun] using
        ellR.memL2_normalizedCubeMeasure
    exact hvR.sub hellR
  have htransfer := normalizedAffineCandidateError_le_distance_add
    (originCube d (k - (N : ℤ))) uk.toH1.toFun v.toFun c' e' hdiffChild hcandMem
  have hHchild : normalizedCubeL2Distance (originCube d (k - (N : ℤ)))
      uk.toH1.toFun v.toFun ≤ A * H := by
    simpa only [A, H] using normalizedCubeL2Distance_originCube_sub_nat_le
      k N uk.toH1.toFun v.toFun hdiff
  have hchildCandidate :
      normalizedAffineCandidateError (originCube d (k - (N : ℤ))) uk.toH1.toFun c' e' ≤
        A * H + theta * (H + E) :=
    htransfer.trans (add_le_add hHchild hdec')
  have hreplacement' : H ≤ C₀ * scalarIdentityWeakError a s k * D := by
    have h := hreplacement a k uk.toH1 huk
    have henergy :
        Book.Ch03.h1EnergyNormOnCube (originCube d k) a uk.toH1 = D := by
      simpa only [D, uk] using
        (finiteLipschitzEnergyRow_eq_h1EnergyNormOnCube_of_le a m u k hkm).symm
    rw [← henergy]
    simpa only [H, v, uk, normalizedCubeL2Distance] using h
  have hchildBest := finiteLipschitzAffineErrorRow_best_le a m u
    (by omega : k - (N : ℤ) ≤ m) c' e'
  calc
    finiteLipschitzAffineErrorRow a m u (k - (N : ℤ)) ≤
        normalizedAffineCandidateError (originCube d (k - (N : ℤ)))
          u.toH1.toFun c' e' := hchildBest
    _ = normalizedAffineCandidateError (originCube d (k - (N : ℤ)))
          uk.toH1.toFun c' e' := by rw [finiteCubeSolutionRestriction_toFun]
    _ ≤ A * H + theta * (H + E) := hchildCandidate
    _ = theta * E + (A + theta) * H := by ring
    _ ≤ theta * E +
          (A + theta) * (C₀ * scalarIdentityWeakError a s k * D) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hreplacement'
        (add_nonneg hA htheta.le)) _
    _ = theta * finiteLipschitzAffineErrorRow a m u k +
          C * scalarIdentityWeakError a s k * finiteLipschitzEnergyRow a m u k := by
      dsimp [C, E, D]
      ring

theorem exists_finiteLipschitzOneStepConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ)
        (u : Book.Ch03.CubeSolution (originCube d m) a)
        (k : ℤ), k ≤ m →
          finiteLipschitzAffineErrorRow a m u (k - (N : ℤ)) ≤
            (1 / 8 : ℝ) * finiteLipschitzAffineErrorRow a m u k +
              C * scalarIdentityWeakError a s k * finiteLipschitzEnergyRow a m u k := by
  obtain ⟨N, hN, hdecay⟩ :=
    CubeCalderonZygmund.exists_identity_harmonic_normalized_affine_candidate_error_decay d
  obtain ⟨C, hC, hstep⟩ :=
    exists_finiteLipschitzOneStepConstant_of_harmonic_decay d s hs hs_lt
      N hN (1 / 8) (by norm_num) hdecay
  exact ⟨N, hN, C, hC, hstep⟩



end FiniteLipschitzCoreInternal

open FiniteLipschitzCoreInternal

theorem exists_finiteLipschitzPoincareConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (k : ℤ)
        (u : Book.Ch03.CubeSolution (originCube d k) a),
        scalarIdentityWeakError a s k ≤ 1 →
          cubeBesovScaleWeight 1 (originCube d k) *
              cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
                (cubeFluctuation (originCube d k) u.toH1.toFun) ≤
            C * Book.Ch03.h1EnergyNormOnCube (originCube d k) a u.toH1 := by
  let G : ℝ := Real.sqrt
    ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 2)))⁻¹)
  let P : ℝ :=
    (((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
        (3 : ℝ) ^ ((d : ℝ) + 1)) * ((d : ℝ) * G))
  let L : ℝ := Real.sqrt (4 * (d : ℝ))
  let B : ℝ := Book.Ch03.poincareDiscountFactor s (.finite 2)
  let C : ℝ := 1 + P * B * L
  have hP_nonneg : 0 ≤ P := by
    dsimp [P, G]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity)
          (Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d))
        (Real.rpow_nonneg (by norm_num) _))
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  have hB_nonneg : 0 ≤ B := by
    dsimp [B, Book.Ch03.poincareDiscountFactor]
    exact Real.rpow_nonneg
      (HCPolySupport.geometricDiscount_pos (by positivity : 0 < s * (2 : ℝ))).le _
  have hL_nonneg : 0 ≤ L := Real.sqrt_nonneg _
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg hP_nonneg hB_nonneg) hL_nonneg)
  refine ⟨C, hC, ?_⟩
  intro a k u herror
  let Q : TriadicCube d := originCube d k
  let D : ℝ := Book.Ch03.h1EnergyNormOnCube Q a u.toH1
  let N : ℝ := cubeBesovNegativeVectorSeminormTwo Q s u.toH1.grad
  have ht : 0 < s / 2 := by linarith only [hs]
  have ht_lt : s / 2 < 1 / 2 := by linarith only [hs_lt]
  have hfluctRaw :=
    Book.Ch03.cubeBesovScaleWeight_one_mul_cubeLpNorm_fluctuation_le_grad_negativeBesovTwo
      Q u.toH1 ht ht_lt
  have hfluct :
      cubeBesovScaleWeight 1 Q *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toH1.toFun) ≤
        P * N := by
    simpa only [Q, P, G, Book.Ch02.cubeDomain_coe,
      Book.Ch01.Legacy.fullVectorPoincareConstant,
      fullVectorPoincareCubeConstant_eq_dimensionConstant,
      show 2 * (s / 2) = s by ring] using! hfluctRaw
  have hnegative : N ≤ Book.Ch03.coarsePoincareGradientRHS Q a s (.finite 2) u := by
    simpa only [N, solutionGradientField,
      scaleNegativeBesovVectorNorm_finiteTwo_eq_cubeNegativeSeminorm] using
      Book.Ch03.coarsePoincareGradient_negativeBesov_le Q a u hs (q := .finite 2) (by norm_num)
  have hlower :
      Book.Ch03.poincareLowerEllipticityFactor Q a s (.finite 2) ≤ L := by
    rw [poincareLowerEllipticityFactor_finite_two_eq_sqrt_inv]
    exact Real.sqrt_le_sqrt
      (by simpa only [Q, L] using
        scalarIdentityWeakError_le_one_lowerEllipticity hs herror)
  have henergy : Book.Ch03.solutionEnergyNorm Q a u = D := by
    exact solutionEnergyNorm_eq_h1EnergyNormOnCube Q a u
  have hN : N ≤ B * L * D := by
    calc
      N ≤ Book.Ch03.coarsePoincareGradientRHS Q a s (.finite 2) u := hnegative
      _ = B * Book.Ch03.poincareLowerEllipticityFactor Q a s (.finite 2) * D := by
        rw [Book.Ch03.coarsePoincareGradientRHS, henergy]
      _ ≤ B * L * D := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlower hB_nonneg)
          (by
            dsimp [D, Book.Ch03.h1EnergyNormOnCube]
            exact Real.sqrt_nonneg _)
  have hBLC : P * B * L ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_left (by norm_num)
  have hD_nonneg : 0 ≤ D := by
    dsimp [D, Book.Ch03.h1EnergyNormOnCube]
    exact Real.sqrt_nonneg _
  calc
    cubeBesovScaleWeight 1 (originCube d k) *
          cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
            (cubeFluctuation (originCube d k) u.toH1.toFun) ≤ P * N := hfluct
    _ ≤ P * (B * L * D) := mul_le_mul_of_nonneg_left hN hP_nonneg
    _ = (P * B * L) * D := by ring
    _ ≤ C * D := mul_le_mul_of_nonneg_right hBLC hD_nonneg
    _ = C * Book.Ch03.h1EnergyNormOnCube (originCube d k) a u.toH1 := rfl


end

end HighContrast
end HCPolySupport
