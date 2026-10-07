/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Weak vorticity

The vorticity associated to the explicit weak gradient of a velocity field.
-/

public section


noncomputable section

open CKN.Foundation.Parabolic

namespace ESS

/-- The weak vorticity determined by the velocity gradient convention
`Du z i j = ∂ⱼ uᵢ` (manuscript `thm:vorticity-regularity`). -/
@[expose] def weakVorticity (Du : ParabolicPoint → Fin 3 → Vec3) : ParabolicPoint → Vec3 :=
  fun z => Fin.cases
    (Du z 2 1 - Du z 1 2)
    (fun j => Fin.cases
      (Du z 0 2 - Du z 2 0)
      (fun k => Fin.cases
        (Du z 1 0 - Du z 0 1)
        (fun l => Fin.elim0 l) k) j)

/-- The divergence-form flux in the weak vorticity equation
`thm:vorticity-regularity`. -/
@[expose] def vorticityFlux (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint)
    (j i : Fin 3) : ℝ :=
  u z j * weakVorticity Du z i - weakVorticity Du z j * u z i

@[simp]
theorem weakVorticity_zero (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) :
    weakVorticity Du z 0 = Du z 2 1 - Du z 1 2 := by
  rfl

@[simp]
theorem weakVorticity_one (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) :
    weakVorticity Du z 1 = Du z 0 2 - Du z 2 0 := by
  rfl

@[simp]
theorem weakVorticity_two (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) :
    weakVorticity Du z 2 = Du z 1 0 - Du z 0 1 := by
  rfl

end ESS
