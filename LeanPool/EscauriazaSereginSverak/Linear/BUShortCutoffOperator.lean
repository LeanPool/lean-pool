/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCutoffWeak

/-!
# Heat operator of the short-time cutoff field

The specified weak heat vector separates into the scaled equation and the
first and second derivatives of the smooth cutoff in `lem:bu-small-time`.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The cutoff derivative terms in the weak heat equation. -/
@[expose] def buCutHeatError (κ : Vec3 × ℝ → ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) : Vec3 :=
  fun i =>
    (timePartial (buCutScalar κ) z +
      ∑ j : Fin 3, spatialSecondPartial (buCutScalar κ) j j z) * v z i +
    2 * ∑ j : Fin 3,
      spatialPartial (buCutScalar κ) j z * Dv z i j

/-- The weak heat vector of the cutoff field is the scalar cutoff times
the original weak heat vector plus the cutoff derivative error. -/
theorem buCutHeat_eq
    (κ : Vec3 × ℝ → ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3)
    (z : ParabolicPoint) :
    ucWeakHeatVector (buCutD2 κ v Dv D2v) (buCutDt κ v Dtv) z =
      buCutScalar κ z • ucWeakHeatVector D2v Dtv z +
        buCutHeatError κ v Dv z := by
  funext i
  simp only [ucWeakHeatVector, buCutD2, buCutDt, buCutHeatError,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end ESS
