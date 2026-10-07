/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.EscauriazaSereginSverak.Main.EssLocal
public import LeanPool.EscauriazaSereginSverak.PartV.EssL5UniqueInputs

/-!
# The L⁵ bound and uniqueness

The theorem `thm:ess-l5-unique`: a Leray–Hopf solution that is bounded in `L³`
in space uniformly in time lies in space-time `L⁵`, and every Leray–Hopf
solution with the same datum coincides with it. The local regularity theorem
`thm:ess-local` is its only regularity input; the short-time solution of
`prop:pv-local-solution` is constructed along the way.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.Main

/-- The `L⁵` bound and uniqueness theorem `thm:ess-l5-unique`. -/
theorem essL5Unique :
    ∀ T : ℝ, ∀ a : Vec3 → Vec3,
    ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
      IsLerayHopfSolution T a u Du →
      essSup
        (fun t : ℝ => ∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
        (volume.restrict (Ioo 0 T)) < ⊤ →
      MemLp u (ENNReal.ofReal (5 : ℝ))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      ∀ v : ParabolicPoint → Vec3,
        ∀ Dv : ParabolicPoint → Fin 3 → Vec3,
          IsLerayHopfSolution T a v Dv →
            v =ᵐ[volume.restrict
              (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))] u :=
  essL5Unique_of_inputs ESS.Main.essLocal

end ESS.Main

end
