/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedOrderedDerivativeFrechet
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData

/-!
# Ordered derivatives of the mollified initial state

The mollifier's Fréchet derivative estimate supplies every ordered
coordinate derivative required by the finite Hᵏ energy construction.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Every ordered spatial derivative of each component of a mollified
Leray datum is square integrable. -/
theorem regUniformMollifiedInitial_orderedDerivative_memLp
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a)
    (α : List (Fin 3)) (i : Fin 3) :
    MemLp (regularisedOrderedSpatialDerivative α
      (fun x : Vec3 => regUniformMollifiedInitial ρ ε hε a x i))
      (2 : ℝ≥0∞) volume := by
  let f : Vec3 → ℝ := fun x => regUniformMollifiedInitial ρ ε hε a x i
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (regUniformMollifiedInitial_contDiff ρ ε hε ha).continuousLinearMap_comp
      (ContinuousLinearMap.proj (R := ℝ) i)
  have hcoord := regUniformMollifiedInitial_coordinateDerivative_memLp
    ρ ε hε ha α.length (fun j => α.get j) i
  have heq : regularisedOrderedSpatialDerivative α f =
      fun x : Vec3 => (iteratedFDeriv ℝ α.length f x)
        (regularisedListBasisTuple α) := by
    funext x
    exact regularisedOrderedSpatialDerivative_eq_iteratedFDeriv f hf α x
  rw [heq]
  exact hcoord

end CKN.Leray

end
