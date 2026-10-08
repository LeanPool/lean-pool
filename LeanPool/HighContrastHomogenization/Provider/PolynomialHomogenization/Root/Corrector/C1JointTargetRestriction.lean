/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1CanonicalProjectionExactness
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineVaryingSlopeLimit

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1JointTargetRestriction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Restriction of the joint affine-corrector target

The projective joint limit has one compatible full-gradient class on every
centered cube.  Consequently the harmonic target on an inner cube is the
restriction of the joint cube solution on any larger centered cube.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory

noncomputable section

/-- The joint harmonic target is the restriction of its outer cube-solution
representative. -/
theorem jointTargetHarmonicGradient_eq_restricted_outer
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (e : Vec d) {q m : ℕ} (hqm : q ≤ m) :
    ((jointTargetHarmonicGradientLinearMap a hCauchy q) e :
        LocalGradientL2 d q) =
      (finiteCubeSolutionRestriction a
        (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm)
        (finiteAffineCorrectionJointLocalCubeSolution a hCauchy e m)).toH1.gradToHilbertVectorL2
          := by
  have hq := jointTargetHarmonicGradient_field_eq a hCauchy q e
  have hm := jointTargetHarmonicGradient_field_eq a hCauchy m e
  have hJq : ((jointTargetHarmonicGradientLinearMap a hCauchy q) e :
      LocalGradientL2 d q) = (jointAffineFullGradientLinearMap a hCauchy q) e := by
    change ((AHarmonicGradientHilbert.ofAHarmonicFunction
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (localGradientCube d q))
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
        (originCube d (q : ℤ)) a)
      (finiteAffineCorrectionJointLocalCubeSolution a hCauchy e q).toPointwiseAHarmonic : _) :
        LocalGradientL2 d q) = _
    exact hq
  rw [hJq]
  have hrestrict :
      (finiteCubeSolutionRestriction a
        (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm)
        (finiteAffineCorrectionJointLocalCubeSolution a hCauchy e m)).toH1.gradToHilbertVectorL2 =
      localGradientRestrict hqm
        (finiteAffineCorrectionJointLocalCubeSolution a hCauchy e m).toH1.gradToHilbertVectorL2
          := by
    apply MeasureTheory.Lp.ext
    filter_upwards
        [(finiteCubeSolutionRestriction a
          (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm)
          (finiteAffineCorrectionJointLocalCubeSolution a hCauchy e
            m)).toH1.coeFn_gradToHilbertVectorL2,
        localGradientRestrict_coeFn_ae hqm
          (finiteAffineCorrectionJointLocalCubeSolution a hCauchy e m).toH1.gradToHilbertVectorL2,
        (finiteAffineCorrectionJointLocalCubeSolution a hCauchy e
          m).toH1.coeFn_gradToHilbertVectorL2.filter_mono
          (ae_mono (Measure.restrict_mono_set volume (localGradientCube_mono hqm)))]
      with x hleft hright houter
    rw [hleft, finiteCubeSolutionRestriction_grad]
    exact houter.symm.trans hright.symm
  rw [hrestrict]
  have hm' :
      (finiteAffineCorrectionJointLocalCubeSolution a hCauchy e m).toH1.gradToHilbertVectorL2 =
        (jointAffineFullGradientLinearMap a hCauchy m) e := by
    exact hm
  rw [hm']
  exact (localGradientRestrict_jointAffineFullGradientLinearMap
    a hCauchy hqm e).symm

end

end Root
end HighContrast
end HCPolySupport
