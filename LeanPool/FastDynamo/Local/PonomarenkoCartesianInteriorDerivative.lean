/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.PonomarenkoOriginProfiles

/-!
# Derivatives of the interior squared-radius profiles

The regular interior Ponomarenko branches are written through the squared-radius profiles
`Φ₋` (`B₋(r) = Φ₋(r²)`) and `Φ₊` (`B₊(r) = r² Φ₊(r²)`) of
`Local/PonomarenkoOriginProfiles.lean`.  This file records that both profiles are
differentiable at every real squared radius, with their own derivative; this is used by
`Local/HorizontalModeBulkIdentity.lean` for the one-sided derivatives of the two-component mode.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace PonomarenkoCartesianInteriorDerivative

open Complex Metric MeasureTheory Set
open CartesianRadialRegularity
open PonomarenkoOriginProfiles

/-! ## Derivatives of the squared-radius profiles -/

/-- The order-zero squared-radius profile `Φ₋`, defined by `B₋(r) = Φ₋(r²)`, is differentiable at
every real `s`, being entire in the squared-radius variable. -/
theorem minusOriginProfile_hasDerivAt (kappa : ℂ) (s : ℝ) :
    HasDerivAt (minusOriginProfile kappa) (deriv (minusOriginProfile kappa) s) s := by
  exact ((minusOriginProfile_contDiff kappa).differentiable (by simp) s).hasDerivAt

/-- The order-two squared-radius profile `Φ₊`, defined by `B₊(r) = r² Φ₊(r²)`, is differentiable at
every real `s`. -/
theorem plusOriginProfile_hasDerivAt (kappa : ℂ) (s : ℝ) :
    HasDerivAt (plusOriginProfile kappa) (deriv (plusOriginProfile kappa) s) s := by
  exact ((plusOriginProfile_contDiff kappa).differentiable (by simp) s).hasDerivAt

end PonomarenkoCartesianInteriorDerivative
end FastDynamo
