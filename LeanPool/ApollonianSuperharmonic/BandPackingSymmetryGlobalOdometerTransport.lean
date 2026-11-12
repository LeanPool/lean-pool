/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5686T1UniformGlobalOdometerTransport

-- [TABLET NODE: BandPackingSymmetryGlobalOdometerTransport]

/-!
# BandPackingSymmetryGlobalOdometerTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandPackingSymmetryGlobalOdometerTransport
    (s : BandPackingSymmetry) (g : IntegerLatticeFunction)
    (h : PartialOdometer) (x : GaussianInt)
    (hext : GlobalOdometerExtends g h) :
    ∃ g' : IntegerLatticeFunction,
      GlobalOdometerExtends g'
        (BandPackingSymmetryPartialOdometerAction s h) ∧
      FourNeighborLaplacian g'
          (BandPackingSymmetryVectorAction s x) =
        FourNeighborLaplacian g x := by
-- BODY
  obtain ⟨g', he', hlap⟩ := P5686T1UniformGlobalOdometerTransport s g h hext
  exact ⟨g', he', hlap x⟩

end ApollonianSuperharmonic

end
