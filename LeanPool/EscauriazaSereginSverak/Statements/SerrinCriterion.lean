/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Main.SerrinCriterion

/-!
# The Serrin regularity criterion

-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The regularity criterion `cor:serrin-criterion` over the whole range
`3 ≤ s ≤ ∞`: a Leray–Hopf solution on `[0,T]` in `L^ℓ(0,T;L^s(ℝ³))` with
`3/s + 2/ℓ = 1` is the only Leray–Hopf solution with its datum and agrees almost
everywhere with a function that is infinitely differentiable (C^∞; the exponent
`(⊤ : ℕ∞)`, not `ω`) on `ℝ³ × (0,T]`, with one-sided derivatives at `T`. The
hypothesis is a disjunction of the endpoint `s = 3` (`L^∞_t L³_x`, the
Escauriaza–Seregin–Šverák case, `cor:ess-smooth`), the finite range `3 < s < ∞`
with `ℓ = 2s/(s−3)` and the endpoint `s = ∞` (`L²_t L^∞_x`) — the last two being the
Ladyzhenskaya–Prodi–Serrin cases of `thm:lps`. -/
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
          ((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T)) :=
by exact ESS.Main.serrinCriterion

end ESS
