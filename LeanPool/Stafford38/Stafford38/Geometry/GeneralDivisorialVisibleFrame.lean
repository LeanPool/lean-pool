/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Geometry.ExactDivisorialVisibleFrameExistence


/-!
# Divisorial visible frames for arbitrary prime affine components

An invertible, transcendental coordinate on a prime affine component gives
a normalized visible divisor frame. This removes the canonical Weyl-support
hypotheses from the boundary producer. Identification of the resulting Laurent
direction with the smooth projective conormal closure is performed downstream
in the general asymptotic-conormal construction.
-/

@[expose] public section

namespace Stafford38.Geometry.GeneralDivisorialVisibleFrame

open IsLocalRing Polynomial
open Stafford38
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveOrder
open Stafford38.Geometry.ExactDivisorialVisibleFrameExistence
open Stafford38.Geometry.ExactVisibleDivisorFrameInterface
open Stafford38.Geometry.KaehlerDVRVisibility
open Stafford38.Geometry.ProjectiveDivisorOrderGap
open Stafford38.Geometry.ProjectiveValuationNormalization
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedDVR
open Stafford38.Geometry.DivisorTangentLattice

noncomputable section


universe u

/-- A polynomial inverse modulo the prime component forces the normalized
projective denominator to vanish at the retained boundary place. The visible
differential frame is then supplied by the generic divisorial construction. -/
theorem generalDivisorialVisibleFrameExistence
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (hunit : ∃ g : MvPolynomial (Fin m) k,
      MvPolynomial.X ⟨0, hm⟩ * g - 1 ∈ P.asIdeal)
    (htrans : Transcendental k
      (componentCoordinate P ⟨0, hm⟩)) :
    HasNormalizedCompatibleVisibleFrame P hm := by
  exact normalizedVisibleFrame_of_coordinate_inverse hm P hunit htrans


end

end Stafford38.Geometry.GeneralDivisorialVisibleFrame
