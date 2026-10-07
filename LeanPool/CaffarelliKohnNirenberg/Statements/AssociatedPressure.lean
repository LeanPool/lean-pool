/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Main.AssociatedPressure

/-!
# Associated Pressure

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- Every finite-time Leray–Hopf solution has an associated CKN pressure, as in
`thm:assoc-pressure`. -/
theorem associatedPressure :
    ∀ T : ℝ, ∀ a : Vec3 → Vec3,
    ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
      IsLerayHopfSolution T a u Du →
      ∃ p : ParabolicPoint → ℝ,
        MemLp p (ENNReal.ofReal (5 / 3 : ℝ))
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
        (∀ φ : ParabolicPoint → Vec3,
          φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) →
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
            (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
              - ∑ i : Fin 3, ∑ j : Fin 3,
                  u z i * u z j * spatialPartial (fun y => φ y i) j z
              + ∑ i : Fin 3, ∑ j : Fin 3,
                  Du z i j * spatialPartial (fun y => φ y i) j z
              - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
              - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i = 0) ∧
        (essSup
          (fun t : ℝ => ∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
          (volume.restrict (Ioo 0 T)) < ⊤ →
          essSup
            (fun t : ℝ => ∫⁻ x : Vec3, ‖p (x, t)‖ₑ ^ (3 / 2 : ℝ))
            (volume.restrict (Ioo 0 T)) < ⊤) :=
by exact CKN.Main.associatedPressure

end CKN
