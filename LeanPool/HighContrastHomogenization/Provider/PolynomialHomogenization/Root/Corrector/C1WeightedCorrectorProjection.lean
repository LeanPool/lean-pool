/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1WeightedLeastSquaresCore
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1FiniteCorrectorLimitBridge
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1AdjacentExactMinimizer
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLocalEquation

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1WeightedCorrectorProjection

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Coefficient-weighted projection of a joint corrector onto a finite span

On a fixed inner cube, finite affine-solution gradients form an injected
finite-dimensional trial space once the scalar good tail is small.  The
coercive symmetric coefficient form therefore gives a canonical linear
least-squares slope selector for the joint corrector family.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory

noncomputable section

/-- The finite affine trial gradient at scale `m`, viewed in the harmonic
Hilbert space on the local cube at scale `q ≤ m`. -/
@[expose]
public noncomputable def finiteTrialHarmonicGradient
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {q m : ℕ} (hqm : q ≤ m) (e : Vec d) :=
  AHarmonicGradientHilbert.ofAHarmonicFunction
    (PotentialSolenoidalL2Data.ofSubmoduleClosures
      (localGradientCube d q))
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d (q : ℤ)) a)
    (finiteCubeSolutionRestriction a
      (by exact_mod_cast hqm)
      (finiteAffineCubeSolution a (m : ℤ) e)).toPointwiseAHarmonic

theorem finiteTrialHarmonicGradient_add
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {q m : ℕ} (hqm : q ≤ m) (e e' : Vec d) :
    finiteTrialHarmonicGradient a hqm (e + e') =
      finiteTrialHarmonicGradient a hqm e +
        finiteTrialHarmonicGradient a hqm e' := by
  apply Subtype.ext
  simp only [finiteTrialHarmonicGradient]
  have hqmZ : (q : ℤ) ≤ (m : ℤ) := by exact_mod_cast hqm
  change
    (finiteCubeSolutionRestriction a hqmZ
        (finiteAffineCubeSolution a (m : ℤ) (e + e'))).toH1.gradToHilbertVectorL2 =
      (finiteCubeSolutionRestriction a hqmZ
        (finiteAffineCubeSolution a (m : ℤ) e)).toH1.gradToHilbertVectorL2 +
      (finiteCubeSolutionRestriction a hqmZ
        (finiteAffineCubeSolution a (m : ℤ) e')).toH1.gradToHilbertVectorL2
  apply MeasureTheory.Lp.ext
  have hadd := finiteAffineSolution_grad_add a (m : ℤ) e e'
  have hsub : openCubeSet (originCube d (q : ℤ)) ⊆
      openCubeSet (originCube d (m : ℤ)) :=
    openCubeSet_originCube_subset_of_le hqmZ
  have hadd' := ae_mono
    (Measure.restrict_mono hsub (le_refl volume)) hadd
  filter_upwards
      [(finiteCubeSolutionRestriction a hqmZ
          (finiteAffineCubeSolution a (m : ℤ) (e + e'))).toH1.coeFn_gradToHilbertVectorL2,
        (finiteCubeSolutionRestriction a hqmZ
          (finiteAffineCubeSolution a (m : ℤ) e)).toH1.coeFn_gradToHilbertVectorL2,
        (finiteCubeSolutionRestriction a hqmZ
          (finiteAffineCubeSolution a (m : ℤ) e')).toH1.coeFn_gradToHilbertVectorL2,
        MeasureTheory.Lp.coeFn_add
          (finiteCubeSolutionRestriction a hqmZ
            (finiteAffineCubeSolution a (m : ℤ) e)).toH1.gradToHilbertVectorL2
          (finiteCubeSolutionRestriction a hqmZ
            (finiteAffineCubeSolution a (m : ℤ) e')).toH1.gradToHilbertVectorL2,
        hadd'] with x hx hxe hxe' hsum haddx
  simp only [finiteCubeSolutionRestriction_grad] at hx hxe hxe'
  rw [hx, hsum, Pi.add_apply, hxe, hxe']
  simp only [finiteAffineCubeSolution, hilbertifyVecField]
  rw [haddx]
  simp

theorem finiteTrialHarmonicGradient_smul
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {q m : ℕ} (hqm : q ≤ m) (c : ℝ) (e : Vec d) :
    finiteTrialHarmonicGradient a hqm (c • e) =
      c • finiteTrialHarmonicGradient a hqm e := by
  apply Subtype.ext
  simp only [finiteTrialHarmonicGradient]
  have hqmZ : (q : ℤ) ≤ (m : ℤ) := by exact_mod_cast hqm
  change
    (finiteCubeSolutionRestriction a hqmZ
        (finiteAffineCubeSolution a (m : ℤ) (c • e))).toH1.gradToHilbertVectorL2 =
      c • (finiteCubeSolutionRestriction a hqmZ
        (finiteAffineCubeSolution a (m : ℤ) e)).toH1.gradToHilbertVectorL2
  apply MeasureTheory.Lp.ext
  have hsmul := finiteAffineSolution_grad_smul a (m : ℤ) c e
  have hsub : openCubeSet (originCube d (q : ℤ)) ⊆
      openCubeSet (originCube d (m : ℤ)) :=
    openCubeSet_originCube_subset_of_le hqmZ
  have hsmul' := ae_mono
    (Measure.restrict_mono hsub (le_refl volume)) hsmul
  filter_upwards
      [(finiteCubeSolutionRestriction a hqmZ
          (finiteAffineCubeSolution a (m : ℤ) (c • e))).toH1.coeFn_gradToHilbertVectorL2,
        (finiteCubeSolutionRestriction a hqmZ
          (finiteAffineCubeSolution a (m : ℤ) e)).toH1.coeFn_gradToHilbertVectorL2,
        MeasureTheory.Lp.coeFn_smul c
          (finiteCubeSolutionRestriction a hqmZ
            (finiteAffineCubeSolution a (m : ℤ) e)).toH1.gradToHilbertVectorL2,
        hsmul'] with x hx hxe hcoe hsmulx
  simp only [finiteCubeSolutionRestriction_grad] at hx hxe
  rw [hx, hcoe, Pi.smul_apply, hxe]
  simp only [finiteAffineCubeSolution, hilbertifyVecField]
  rw [hsmulx]
  simp

private theorem finiteAffineBoundaryH1_gradClass_eq_constantGradient
    {d : ℕ} (q : ℕ) (e : Vec d) :
    (show LocalGradientL2 d q from by
      simp only [LocalGradientL2, localGradientCube]
      exact (finiteAffineBoundaryH1 (q : ℤ) e).gradToHilbertVectorL2) =
      (show LocalGradientL2 d q from
        constantGradientOnOriginCube e (q : ℤ)) := by
  let b : H1Function (localGradientCube d q) := finiteAffineBoundaryH1 (q : ℤ) e
  change b.gradToHilbertVectorL2 = constantGradientOnOriginCube e (q : ℤ)
  have hbgrad : b.grad = fun _ ↦ e := finiteAffineBoundaryH1_grad (q : ℤ) e
  have hmem : MemVectorL2 (openCubeSet (originCube d (q : ℤ))) (fun _ ↦ e) :=
    MeasureTheory.memLp_const
      (μ := volumeMeasureOn (openCubeSet (originCube d (q : ℤ))))
      (p := (2 : ENNReal)) (c := e)
  unfold constantGradientOnOriginCube
  apply MeasureTheory.Lp.ext
  refine b.coeFn_gradToHilbertVectorL2.trans ?_
  refine (Filter.EventuallyEq.of_eq (congrArg hilbertifyVecField hbgrad)).trans ?_
  exact (coeFn_toHilbertVectorL2OfVecField hmem).symm

/-- The finite affine full-gradient trial map in the harmonic-gradient
Hilbert space of the inner cube. -/
@[expose]
noncomputable def finiteTrialHarmonicGradientLinearMap
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {q m : ℕ} (hqm : q ≤ m) :
    Vec d →ₗ[ℝ]
      AHarmonicGradientHilbert.Space
        (PotentialSolenoidalL2Data.ofSubmoduleClosures
          (localGradientCube d q))
        (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
          (originCube d (q : ℤ)) a) where
  toFun := finiteTrialHarmonicGradient a hqm
  map_add' := finiteTrialHarmonicGradient_add a hqm
  map_smul' := finiteTrialHarmonicGradient_smul a hqm

/-- The harmonic-space target map has the canonical joint affine-gradient
representative on the inner cube. -/
theorem jointTargetHarmonicGradient_field_eq
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a) (q : ℕ) (e : Vec d) :
    ((AHarmonicGradientHilbert.ofAHarmonicFunction
      (PotentialSolenoidalL2Data.ofSubmoduleClosures
        (localGradientCube d q))
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
        (originCube d (q : ℤ)) a)
      (finiteAffineCorrectionJointLocalCubeSolution a hCauchy e q).toPointwiseAHarmonic :
        AHarmonicGradientHilbert.Space
          (PotentialSolenoidalL2Data.ofSubmoduleClosures
            (localGradientCube d q))
          (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
            (originCube d (q : ℤ)) a)) :
      LocalGradientL2 d q) =
      (jointAffineFullGradientLinearMap a hCauchy q) e := by
  change
    (finiteAffineCorrectionJointLocalCubeSolution a hCauchy e q).toH1.gradToHilbertVectorL2 =
      (jointAffineFullGradientLinearMap a hCauchy q) e
  rw [finiteAffineCorrectionJointLocalCubeSolution_toH1]
  refine (finiteAffineCorrectionJointLocalH1_gradToHilbertVectorL2 a hCauchy e q).trans ?_
  rw [finiteAffineBoundaryH1_gradClass_eq_constantGradient]
  rfl

/-- The joint affine-plus-corrector full gradient, as a linear map into the
same harmonic-gradient Hilbert space. -/
@[expose]
noncomputable def jointTargetHarmonicGradientLinearMap
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a) (q : ℕ) :
    Vec d →ₗ[ℝ]
      AHarmonicGradientHilbert.Space
        (PotentialSolenoidalL2Data.ofSubmoduleClosures
          (localGradientCube d q))
        (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
          (originCube d (q : ℤ)) a) where
  toFun e := AHarmonicGradientHilbert.ofAHarmonicFunction
    (PotentialSolenoidalL2Data.ofSubmoduleClosures
      (localGradientCube d q))
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d (q : ℤ)) a)
    (finiteAffineCorrectionJointLocalCubeSolution a hCauchy e q).toPointwiseAHarmonic
  map_add' e e' := by
    apply Subtype.ext
    rw [jointTargetHarmonicGradient_field_eq]
    change
      (jointAffineFullGradientLinearMap a hCauchy q) (e + e') =
        ((AHarmonicGradientHilbert.ofAHarmonicFunction
          (PotentialSolenoidalL2Data.ofSubmoduleClosures
            (localGradientCube d q))
          (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
            (originCube d (q : ℤ)) a)
          (finiteAffineCorrectionJointLocalCubeSolution a hCauchy e q).toPointwiseAHarmonic :
            AHarmonicGradientHilbert.Space
              (PotentialSolenoidalL2Data.ofSubmoduleClosures
                (localGradientCube d q))
              (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
                (originCube d (q : ℤ)) a)) : LocalGradientL2 d q) +
        ((AHarmonicGradientHilbert.ofAHarmonicFunction
          (PotentialSolenoidalL2Data.ofSubmoduleClosures
            (localGradientCube d q))
          (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
            (originCube d (q : ℤ)) a)
          (finiteAffineCorrectionJointLocalCubeSolution a hCauchy e' q).toPointwiseAHarmonic :
            AHarmonicGradientHilbert.Space
              (PotentialSolenoidalL2Data.ofSubmoduleClosures
                (localGradientCube d q))
              (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
                (originCube d (q : ℤ)) a)) : LocalGradientL2 d q)
    rw [jointTargetHarmonicGradient_field_eq,
      jointTargetHarmonicGradient_field_eq]
    exact map_add (jointAffineFullGradientLinearMap a hCauchy q) e e'
  map_smul' c e := by
    apply Subtype.ext
    rw [jointTargetHarmonicGradient_field_eq]
    change
      (jointAffineFullGradientLinearMap a hCauchy q) (c • e) =
        c • ((AHarmonicGradientHilbert.ofAHarmonicFunction
          (PotentialSolenoidalL2Data.ofSubmoduleClosures
            (localGradientCube d q))
          (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
            (originCube d (q : ℤ)) a)
          (finiteAffineCorrectionJointLocalCubeSolution a hCauchy e q).toPointwiseAHarmonic :
            AHarmonicGradientHilbert.Space
              (PotentialSolenoidalL2Data.ofSubmoduleClosures
                (localGradientCube d q))
              (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
                (originCube d (q : ℤ)) a)) : LocalGradientL2 d q)
    rw [jointTargetHarmonicGradient_field_eq]
    exact map_smul (jointAffineFullGradientLinearMap a hCauchy q) c e

private theorem localGradientClassAverage_grad_eq_cubeAverageVec_projection
    {d q : ℕ} (u : H1Function (localGradientCube d q)) :
    localGradientClassAverage u.gradToHilbertVectorL2 =
      cubeAverageVec (originCube d (q : ℤ)) u.grad := by
  apply localGradientClassAverage_eq_cubeAverageVec_of_ae
  exact u.coeFn_gradToHilbertVectorL2

/-- The finite trial map is injective under the small-good-tail
average-slope coercivity estimate. -/
theorem finiteTrialHarmonicGradientLinearMap_injective
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (s delta c : ℝ) (n0 : ℤ)
    (hdelta : delta ∈ Set.Ioc (0 : ℝ) c)
    (hgood : ScalarIdentityGoodTail a s delta n0)
    (hcoercive :
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c → ScalarIdentityGoodTail a s delta n →
        ∀ (q t : ℕ), n ≤ (q : ℤ) → ∀ e : Vec d,
          euclideanNorm e ≤ 2 * euclideanNorm
            (cubeAverageVec (originCube d (q : ℤ))
              (finiteAffineSolution a ((q + t + 2 : ℕ) : ℤ) e).toH1.grad))
    (q m : ℕ) (hnq : n0 ≤ (q : ℤ)) (hqm2 : q + 2 ≤ m) :
    Function.Injective (finiteTrialHarmonicGradientLinearMap a
      (by omega : q ≤ m)) := by
  intro e e' heq
  have hqm : q ≤ m := by omega
  have hqmZ : (q : ℤ) ≤ (m : ℤ) := by exact_mod_cast hqm
  let T := finiteTrialHarmonicGradientLinearMap a hqm
  let z : Vec d := e - e'
  have hTz : T z = 0 := by
    dsimp only [z]
    rw [map_sub, heq, sub_self]
  have hfield :
      (finiteCubeSolutionRestriction a
        hqmZ
        (finiteAffineCubeSolution a (m : ℤ) z)).toH1.gradToHilbertVectorL2 = 0 := by
    exact congrArg Subtype.val hTz
  have havg : cubeAverageVec (originCube d (q : ℤ))
      (finiteAffineSolution a (m : ℤ) z).toH1.grad = 0 := by
    let u : H1Function (localGradientCube d q) :=
      (finiteCubeSolutionRestriction a hqmZ (finiteAffineCubeSolution a (m : ℤ) z)).toH1
    have hu0 : u.gradToHilbertVectorL2 = 0 := hfield
    have hproj := localGradientClassAverage_grad_eq_cubeAverageVec_projection u
    rw [hu0, localGradientClassAverage_zero] at hproj
    change cubeAverageVec (originCube d (q : ℤ))
      (finiteAffineCubeSolution a (m : ℤ) z).toH1.grad = 0
    rw [← finiteCubeSolutionRestriction_grad a
      hqmZ
      (finiteAffineCubeSolution a (m : ℤ) z)]
    exact hproj.symm
  let t : ℕ := m - q - 2
  have hm : q + t + 2 = m := by dsimp only [t]; omega
  have hz := hcoercive a delta n0 hdelta hgood q t hnq z
  rw [hm, havg, euclideanNorm_zero, mul_zero] at hz
  have hz0 : z = 0 := euclideanNorm_eq_zero_iff.mp
    (le_antisymm hz (euclideanNorm_nonneg z))
  exact sub_eq_zero.mp (by simpa only [z] using hz0)

/-- The coefficient-weighted least-squares parameter map on the inner cube. -/
@[expose]
noncomputable def finiteCorrectorWeightedProjection
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    {q m : ℕ} (hqm : q ≤ m)
    (hT : Function.Injective (finiteTrialHarmonicGradientLinearMap a hqm)) :
    Vec d →ₗ[ℝ] Vec d := by
  let T := finiteTrialHarmonicGradientLinearMap a hqm
  let H := AHarmonicGradientHilbert.Space
    (PotentialSolenoidalL2Data.ofSubmoduleClosures
      (localGradientCube d q))
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d (q : ℤ)) a)
  let hclosed : IsClosed (LinearMap.range T : Set H) := by
    let _ : FiniteDimensional ℝ (LinearMap.range T) := T.finiteDimensional_range
    exact (LinearMap.range T).closed_of_finiteDimensional
  let B := AHarmonicGradientHilbert.symmCoeffBilin
    (PotentialSolenoidalL2Data.ofSubmoduleClosures
      (localGradientCube d q))
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d (q : ℤ)) a)
  let hB := AHarmonicGradientHilbert.isCoercive_symmCoeffBilin
    (M := PotentialSolenoidalL2Data.ofSubmoduleClosures
      (localGradientCube d q))
    (Book.Ch02.openCubeSet_nonempty (originCube d (q : ℤ)))
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d (q : ℤ)) a)
  exact weightedLeastSquaresSlopeMap T hT hclosed B hB
    (LinearMap.toContinuousLinearMap
      (jointTargetHarmonicGradientLinearMap a hCauchy q))

/-- The selected residual minimizes the coefficient quadratic energy against
every finite affine trial slope. -/
theorem finiteCorrectorWeightedProjection_minimizes
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    {q m : ℕ} (hqm : q ≤ m)
    (hT : Function.Injective (finiteTrialHarmonicGradientLinearMap a hqm))
    (e b : Vec d) :
    let T := finiteTrialHarmonicGradientLinearMap a hqm
    let J := jointTargetHarmonicGradientLinearMap a hCauchy q
    let B := AHarmonicGradientHilbert.symmCoeffBilin
      (PotentialSolenoidalL2Data.ofSubmoduleClosures
        (localGradientCube d q))
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
        (originCube d (q : ℤ)) a)
    quadraticEnergy B
        (J e - T (finiteCorrectorWeightedProjection a hCauchy hqm hT e)) ≤
      quadraticEnergy B (J e - T b) := by
  dsimp only
  let T := finiteTrialHarmonicGradientLinearMap a hqm
  let H := AHarmonicGradientHilbert.Space
    (PotentialSolenoidalL2Data.ofSubmoduleClosures
      (localGradientCube d q))
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d (q : ℤ)) a)
  let hclosed : IsClosed (LinearMap.range T : Set H) := by
    let _ : FiniteDimensional ℝ (LinearMap.range T) := T.finiteDimensional_range
    exact (LinearMap.range T).closed_of_finiteDimensional
  let B := AHarmonicGradientHilbert.symmCoeffBilin
    (PotentialSolenoidalL2Data.ofSubmoduleClosures
      (localGradientCube d q))
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d (q : ℤ)) a)
  let hB := AHarmonicGradientHilbert.isCoercive_symmCoeffBilin
    (M := PotentialSolenoidalL2Data.ofSubmoduleClosures
      (localGradientCube d q))
    (Book.Ch02.openCubeSet_nonempty (originCube d (q : ℤ)))
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d (q : ℤ)) a)
  apply quadraticEnergy_residual_weightedLeastSquaresSlopeMap_le
    T hT hclosed hB
  intro x y
  exact AHarmonicGradientHilbert.symmCoeffBilin_symm x y

end

end Root
end HighContrast
end HCPolySupport
