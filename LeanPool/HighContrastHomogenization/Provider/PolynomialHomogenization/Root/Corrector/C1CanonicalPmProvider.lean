/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1WeightedProjectionCloseness

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1CanonicalPmProvider

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Canonical finite-corrector slope reparameterization

The coefficient-weighted least-squares projection gives one linear slope
map at a fixed inner and outer cube.  Quantitative convergence of the finite
correctors makes this map uniformly close to the identity, and sufficiently
small good tails therefore make it bijective.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

noncomputable section

/-- The available joint local-limit family agrees with the harmonic target map
used by the coefficient-weighted projection. -/
theorem jointTargetHarmonicGradient_tail_of_jointLocalEquation
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (hPhi : IsFiniteAffineCorrectionJointLocalEquation a Phi)
    (q m : ℕ) (hqm2 : q + 2 ≤ m) (K : ℝ)
    (htail : ∀ e : Vec d,
      Real.sqrt (normalizedLocalSymmetricEnergy
        (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
          (originCube d (q : ℤ)) a)
        (((show LocalGradientL2 d q from
              constantGradientOnOriginCube e (q : ℤ)) +
            (Phi e).gradientComponent q) -
          finiteAffineInnerGradientClass a e q (m - q))) ≤
        K * euclideanNorm e) :
    ∀ e : Vec d,
      let T := finiteTrialHarmonicGradientLinearMap a
        (by omega : q ≤ m)
      let J := jointTargetHarmonicGradientLinearMap a hCauchy q
      Real.sqrt (localHarmonicEnergy a q (J e - T e)) ≤
        K * euclideanNorm e := by
  intro e
  dsimp only
  have hPhiLimit : IsFiniteAffineCorrectionJointLocalLimit a Phi := by
    simpa only [IsFiniteAffineCorrectionJointLocalLimit] using hPhi.1
  have hPhiEq : Phi = finiteAffineCorrectionJointLocalLimit a hCauchy :=
    (isFiniteAffineCorrectionJointLocalLimit_iff_eq a hCauchy Phi).mp hPhiLimit
  unfold localHarmonicEnergy
  change Real.sqrt (normalizedLocalSymmetricEnergy
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
        (originCube d (q : ℤ)) a)
      (((jointTargetHarmonicGradientLinearMap a hCauchy q) e :
          LocalGradientL2 d q) -
        ((finiteTrialHarmonicGradientLinearMap a
          (by omega : q ≤ m)) e : LocalGradientL2 d q))) ≤
      K * euclideanNorm e
  have hJ : ((jointTargetHarmonicGradientLinearMap a hCauchy q) e :
      LocalGradientL2 d q) =
      (jointAffineFullGradientLinearMap a hCauchy q) e := by
    exact jointTargetHarmonicGradient_field_eq a hCauchy q e
  have hT : ((finiteTrialHarmonicGradientLinearMap a
      (by omega : q ≤ m)) e : LocalGradientL2 d q) =
      finiteAffineInnerGradientClass a e q (m - q) := by
    unfold finiteTrialHarmonicGradientLinearMap finiteAffineInnerGradientClass
    change
      (finiteCubeSolutionRestriction a (by omega : (q : ℤ) ≤ (m : ℤ))
        (finiteAffineCubeSolution a (m : ℤ) e)).toH1.gradToHilbertVectorL2 =
      (finiteAffineSolutionInnerH1 a (q : ℤ) ((q + (m - q) : ℕ) : ℤ)
        (by omega) e).gradToHilbertVectorL2
    simp only [show q + (m - q) = m by omega]
    apply MeasureTheory.Lp.ext
    filter_upwards
      [(finiteCubeSolutionRestriction a (by omega : (q : ℤ) ≤ (m : ℤ))
        (finiteAffineCubeSolution a (m : ℤ) e)).toH1.coeFn_gradToHilbertVectorL2,
       (finiteAffineSolutionInnerH1 a (q : ℤ) (m : ℤ)
        (by omega) e).coeFn_gradToHilbertVectorL2]
      with x hleft hright
    rw [hleft, hright, finiteCubeSolutionRestriction_grad,
      finiteAffineSolutionInnerH1_grad]
    rfl
  rw [hJ, hT]
  change Real.sqrt (normalizedLocalSymmetricEnergy
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
        (originCube d (q : ℤ)) a)
      (((show LocalGradientL2 d q from
            constantGradientOnOriginCube e (q : ℤ)) +
          (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent q) -
        finiteAffineInnerGradientClass a e q (m - q))) ≤
      K * euclideanNorm e
  rw [← hPhiEq]
  exact htail e

end

end Root
end HighContrast
end HCPolySupport
