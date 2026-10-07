/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Main.EssSmooth

/-!
# Smoothness from endpoint velocity control

-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/--
The full regularity, integrability, and uniqueness conclusion corresponding to
manuscript label `cor:ess-smooth`; this is the consequence of Escauriaza–Seregin–
Šverák, Theorem 1.3, together with its smoothness-on-the-closed-top-time form
from Theorem 1.2. The smooth representative is viewed on the Euclidean
product `Vec3 × ℝ`, definitionally the CKN carrier `ParabolicPoint`, so
`ContDiffOn` uses the ordinary space-time differentiable structure. It is
infinitely differentiable (C^∞; the exponent `(⊤ : ℕ∞)`, not `ω`). The set
`univ × Ioc 0 T` has `UniqueDiffOn` by
`uniqueDiffOn_univ.prod (uniqueDiffOn_Ioc 0 T)`; thus at `t = T` within-set
derivatives are uniquely determined from times below `T`.
-/
theorem essSmooth :
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
by exact ESS.Main.essSmooth

end ESS
