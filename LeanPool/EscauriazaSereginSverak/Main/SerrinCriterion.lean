/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Main.EssSmooth
public import LeanPool.EscauriazaSereginSverak.Main.LadyzhenskayaProdiSerrin

/-!
# The regularity criterion for `3 ≤ s ≤ ∞`

The corollary `cor:serrin-criterion`: the endpoint `s = 3` is `cor:ess-smooth`, and the
range `3 < s ≤ ∞` is the Ladyzhenskaya–Prodi–Serrin theorem `thm:lps`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.Main

/-- The regularity criterion for `3 ≤ s ≤ ∞`, `cor:serrin-criterion`. -/
theorem serrinCriterion :
    ∀ T : ℝ, ∀ a : Vec3 → Vec3,
    ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
      IsLerayHopfSolution T a u Du →
      ((essSup
          (fun t : ℝ => ∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
          (volume.restrict (Ioo 0 T)) < ⊤) ∨
        (∃ s : ℝ, 3 < s ∧
          (∫⁻ t in Ioo (0 : ℝ) T,
            (∫⁻ x : Vec3,
              ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
                ((2 * s / (s - 3)) / s)) < ⊤) ∨
        (∫⁻ t in Ioo (0 : ℝ) T,
          (essSup
            (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
            (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤) →
      (∀ v : ParabolicPoint → Vec3,
        ∀ Dv : ParabolicPoint → Fin 3 → Vec3,
          IsLerayHopfSolution T a v Dv →
            v =ᵐ[volume.restrict
              (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))] u) ∧
      (∃ uSmooth : ParabolicPoint → Vec3,
        uSmooth =ᵐ[volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))] u ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => uSmooth z)
          ((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T)) := by
  intro T a u Du hLH hSerrin
  rcases hSerrin with h3 | hLps
  · obtain ⟨-, hUniq, hSmooth⟩ := essSmooth T a u Du hLH h3
    exact ⟨hUniq, hSmooth⟩
  · exact ladyzhenskayaProdiSerrin T a u Du hLH hLps

end ESS.Main

end
