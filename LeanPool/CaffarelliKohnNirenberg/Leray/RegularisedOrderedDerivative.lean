/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedMixedSecondPartial
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedConvolutionSmooth
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTransportDivergence

/-!
# Ordered spatial derivatives

An ordered list of coordinate directions defines a classical iterated
spatial derivative. This notation supports finite-order transport
commutator identities in the Sobolev energy argument.
-/

public section

open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Classical derivatives applied in the order of a list of coordinate
directions. -/
@[expose]
def regularisedOrderedSpatialDerivative :
    List (Fin 3) → (Vec3 → ℝ) → Vec3 → ℝ
  | [], f => f
  | i :: is, f => fun x => fderiv ℝ
      (regularisedOrderedSpatialDerivative is f) x (CKN.basisVec i)

/-- Every ordered spatial derivative of a smooth scalar field remains
smooth. -/
theorem regularisedOrderedSpatialDerivative_contDiff
    (f : Vec3 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (α : List (Fin 3)) :
    ContDiff ℝ (⊤ : ℕ∞) (regularisedOrderedSpatialDerivative α f) := by
  induction α with
  | nil => simpa [regularisedOrderedSpatialDerivative] using hf
  | cons i is ih =>
      change ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec3 => fderiv ℝ
          (regularisedOrderedSpatialDerivative is f) x (CKN.basisVec i))
      exact (ih.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuousLinearMap_comp
        (ContinuousLinearMap.apply ℝ ℝ (CKN.basisVec i))

/-- A coordinate derivative commutes with an ordered finite derivative of
an all-order smooth scalar field. -/
theorem regularisedOrderedSpatialDerivative_comm_spatialDerivative
    (f : Vec3 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (α : List (Fin 3)) (i : Fin 3) (x : Vec3) :
    regularisedOrderedSpatialDerivative α
      (fun y : Vec3 => fderiv ℝ f y (CKN.basisVec i)) x =
      fderiv ℝ (regularisedOrderedSpatialDerivative α f) x
        (CKN.basisVec i) := by
  induction α generalizing i x with
  | nil => rfl
  | cons j is ih =>
      change fderiv ℝ
        (regularisedOrderedSpatialDerivative is
          (fun y : Vec3 => fderiv ℝ f y (CKN.basisVec i))) x
          (CKN.basisVec j) =
        fderiv ℝ
          (fun y : Vec3 => fderiv ℝ
            (regularisedOrderedSpatialDerivative is f) y (CKN.basisVec j))
          x (CKN.basisVec i)
      have hfun : regularisedOrderedSpatialDerivative is
          (fun y : Vec3 => fderiv ℝ f y (CKN.basisVec i)) =
          fun y : Vec3 => fderiv ℝ
            (regularisedOrderedSpatialDerivative is f) y (CKN.basisVec i) := by
        funext y
        exact ih i y
      rw [hfun]
      exact regularised_mixedSecondPartial_comm
        (regularisedOrderedSpatialDerivative is f)
        ((regularisedOrderedSpatialDerivative_contDiff f hf is).of_le
          (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
            WithTop.coe_le_coe.mpr le_top)) x i j

end CKN.Leray

end
