/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CoordinateDensityHermitian

/-!
# The exterior product of finitely many DIFFERENT real two-forms

`FirstPass.CoordinateDensityGeometry.coordinateWedgePower` is the `k`-fold exterior
power of ONE continuous real two-form.  The mixed Monge--Ampère density
(`fpmma:geometric-density`) is about `ddᶜu_1 ∧ ⋯ ∧ ddᶜu_n`, the exterior product of
`n` possibly DIFFERENT two-forms, and the project has no such object.

This file supplies it, by the same recursion, together with the two facts that make
it usable: the unfolding lemma for the successor step and the identification of its
diagonal with `coordinateWedgePower`.  With the diagonal identified, the blueprint's
polarization argument reduces the mixed density identity to
`actualTopPowerDensity_eq_normalizedTopPowerDensity`, which
`Pending.CoordinateDensityHermitian` now supplies for an ARBITRARY real `(1,1)`-form
— the sign-indefinite forms `∑ᵢ tᵢ ddᶜuᵢ` are exactly the ones the polarization needs.

The multilinearity of `coordinateWedgeFamily` in each slot and its symmetry under
permuting the slots — neither of which the recursion shows — are proved in
`Pending.CoordinateWedgeFamilyPairing`, and `fpmma:geometric-density` itself is
`Pending.MixedCoordinateDensity.actualMixedTopDensity_smoothDDC`.
-/

@[expose] public section

noncomputable section

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

/-- The exterior product `A 0 ∧ A 1 ∧ ⋯ ∧ A (k-1)` of `k` continuous real two-forms,
built by the same recursion as `coordinateWedgePower`. -/
def coordinateWedgeFamily : (k : ℕ) → (Fin k → CoordinateRealTwoForm n) →
    (ComplexModel n) [⋀^Fin (k * 2)]→L[ℝ] ℝ
  | 0, _ => coordinateWedgeUnit
  | 1, A => A 0
  | k + 2, A => by
      simpa [Nat.add_mul] using
        coordinateWedge (coordinateWedgeFamily (k + 1) fun i => A i.castSucc)
          (A (Fin.last (k + 1)))

@[simp] theorem coordinateWedgeFamily_zero (A : Fin 0 → CoordinateRealTwoForm n) :
    coordinateWedgeFamily 0 A = coordinateWedgeUnit := rfl

@[simp] theorem coordinateWedgeFamily_one (A : Fin 1 → CoordinateRealTwoForm n) :
    coordinateWedgeFamily 1 A = A 0 := rfl

/-- Unfolding the successor step of `coordinateWedgeFamily` at an evaluation. -/
theorem coordinateWedgeFamily_add_two_apply (k : ℕ)
    (A : Fin (k + 2) → CoordinateRealTwoForm n)
    (v : Fin ((k + 2) * 2) → ComplexModel n) :
    coordinateWedgeFamily (k + 2) A v =
      coordinateWedge (coordinateWedgeFamily (k + 1) fun i => A i.castSucc)
          (A (Fin.last (k + 1)))
        (v ∘ Fin.cast (show (k + 1) * 2 + 2 = (k + 2) * 2 by ring)) := by
  rw [coordinateWedgeFamily.eq_3, eq_mpr_eq_cast, eq_mp_eq_cast, cast_cast]
  exact cast_continuousAlternatingMap_apply _ _ _ _

/-- On the diagonal the mixed exterior product is the exterior power. -/
theorem coordinateWedgeFamily_const (A : CoordinateRealTwoForm n) (k : ℕ) :
    coordinateWedgeFamily k (fun _ => A) = coordinateWedgePower A k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | k + 2, ih =>
      ext v
      rw [coordinateWedgeFamily_add_two_apply, coordinateWedgePower_add_two_apply,
        ih (k + 1) (by omega)]

/-- The mixed analogue of `actualTopPowerDensity`: the genuine exterior product of `n`
real two-forms, evaluated on the standard interleaved real frame. -/
def actualMixedTopDensity (A : Fin n → CoordinateRealTwoForm n) : ℝ :=
  coordinateWedgeFamily n A coordinateRealFrame

/-- The diagonal of the mixed density is the top exterior-power density. -/
@[simp] theorem actualMixedTopDensity_const (A : CoordinateRealTwoForm n) :
    actualMixedTopDensity (fun _ => A) = actualTopPowerDensity A := by
  rw [actualMixedTopDensity, coordinateWedgeFamily_const, actualTopPowerDensity]

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
