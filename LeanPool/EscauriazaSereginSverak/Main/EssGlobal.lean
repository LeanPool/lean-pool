/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.CaffarelliKohnNirenberg.Statements.SingularSet
public import LeanPool.EscauriazaSereginSverak.Main.EssLocal
public import LeanPool.CaffarelliKohnNirenberg.Main.AssociatedPressure
public import LeanPool.EscauriazaSereginSverak.Endpoint.EssGlobalProof

/-!
# Global endpoint regularity

The global Escauriaza–Seregin–Šverák theorem `thm:ess-global`: a Leray–Hopf
solution on `ℝ³ × (0, T)` that is bounded in `L³` in space uniformly in time
has no singular points. The local theorem `thm:ess-local` is applied to
rescalings of the solution around each point, with the associated pressure of
`thm:assoc-pressure` and its `L^∞ L^{3/2}` bound from `lem:assoc-pressure-L3`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.Main

/-- The global Escauriaza–Seregin–Šverák regularity theorem `thm:ess-global`. -/
theorem essGlobal :
    ∀ T : ℝ, ∀ a : Vec3 → Vec3,
    ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
      IsLerayHopfSolution T a u Du →
      essSup
        (fun t : ℝ => ∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
        (volume.restrict (Ioo 0 T)) < ⊤ →
      SingularSet (Set.univ : Set Vec3) (Ioo 0 T) u = ∅ :=
  essGlobal_of_localRegularity_and_associatedPressure ESS.Main.essLocal CKN.Main.associatedPressure

end ESS.Main

end
