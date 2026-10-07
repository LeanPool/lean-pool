/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.RellichBalls
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Compactness Gradient Fiber

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory
open CKN CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- The nine spatial derivative coordinates with their Euclidean Hilbert
norm. -/
abbrev CompactnessGradientFiber := PiLp 2 (fun _ : Fin 3 => L2Vec3)

/-- The matrix field in its Euclidean Hilbert carrier. -/
@[expose]
def toCompactnessGradientFiber (A : Fin 3 → Vec3) :
    CompactnessGradientFiber :=
  WithLp.toLp 2 (fun i : Fin 3 => WithLp.toLp 2 (A i))

/-- The norm in the gradient carrier has the exact spatial energy density. -/
theorem norm_toCompactnessGradientFiber_sq
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) :
    ‖toCompactnessGradientFiber (Du z)‖ ^ 2 =
      CKN.spatialGradientSq u Du z := by
  rw [toCompactnessGradientFiber, PiLp.norm_sq_eq_of_L2]
  unfold CKN.spatialGradientSq
  apply Finset.sum_congr rfl
  intro i hi
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Real.norm_eq_abs, sq_abs]

end CKN.Leray
