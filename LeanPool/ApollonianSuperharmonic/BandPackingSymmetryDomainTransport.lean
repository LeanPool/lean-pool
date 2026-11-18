/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryPartialOdometerActionFormulas
public import Mathlib.Init


/-!
# BandPackingSymmetryDomainTransport

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace BandPackingSymmetryDomainTransport

/-- A packing symmetry sends every domain point into the transformed domain. -/
theorem forward (a : BandPackingSymmetry) (k : PartialOdometer) (x : GaussianInt)
    (hx : x ∈ k.domain) :
    BandPackingSymmetryVectorAction a x ∈
      (BandPackingSymmetryPartialOdometerAction a k).domain := by
  change BandPackingSymmetryVectorAction a x ∈
    ((BandPackingSymmetryPartialOdometerAction a k).domain : Set GaussianInt)
  rw [(BandPackingSymmetryPartialOdometerActionFormulas a k k).1]
  exact ⟨x, hx, rfl⟩

end BandPackingSymmetryDomainTransport
end ApollonianSuperharmonic

end
