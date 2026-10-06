/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalRepresentative
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorIntrinsicSlope
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfaces.AECongruence

/-!
# High-contrast homogenization: Provider.Regularity.IntrinsicSlopeGlobalGradientUniqueness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Intrinsic-slope uniqueness from a global full-gradient identity

The intrinsic slope is the limit of centered-cube averages of the full
gradient.  This file identifies that sequence with the averages of the glued
global representative and records the resulting uniqueness principle.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Filter

noncomputable section

/-- The intrinsic local-class average is the centered-cube average of the
glued global full-gradient representative. -/
theorem localGradientClassAverage_eq_globalFullGradientAverage
    {d : ℕ} [NeZero d] (e : Vec d) (z : NormalizedLocalH1Carrier d)
    (n : ℕ) :
    localGradientClassAverage
        ((show LocalGradientL2 d n from
            Eq.mp (by simp only [LocalGradientL2, localGradientCube, Book.Ch02.cubeDomain_coe]; rfl)
              (finiteAffineBoundaryH1 (n : ℤ) e).gradToHilbertVectorL2) +
          z.gradientComponent n) =
      cubeAverageVec (originCube d (n : ℤ))
        (fun x => e + z.globalGradientRepresentative x) := by
  rw [← affinePlusLocalCarrierH1_gradToHilbertVectorL2 e z n]
  apply localGradientClassAverage_eq_cubeAverageVec_of_ae
  filter_upwards
    [(affinePlusLocalCarrierH1 e z n).coeFn_gradToHilbertVectorL2,
      z.globalGradientRepresentative_ae_eq_localH1Gradient n]
    with x hfull hz
  rw [hfull]
  change HilbertVec.ofVec ((affinePlusLocalCarrierH1 e z n).grad x) =
    HilbertVec.ofVec (e + z.globalGradientRepresentative x)
  congr 1
  rw [affinePlusLocalCarrierH1, H1Function.add_grad]
  change (finiteAffineBoundaryH1 (n : ℤ) e).grad x +
      (z.localH1Function n).grad x = e + z.globalGradientRepresentative x
  rw [finiteAffineBoundaryH1_grad, ← hz]

end

end HighContrast
end HCPolySupport
