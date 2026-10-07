/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Main.LadyzhenskayaProdiSerrin

/-!
# Ladyzhenskaya–Prodi–Serrin regularity

-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/--
The Ladyzhenskaya–Prodi–Serrin regularity and uniqueness theorem, corresponding
to manuscript label `thm:lps`; see Robinson–Rodrigo–Sadowski, Theorems 8.17
and 8.19, and Escauriaza–Seregin–Šverák, Theorem 1.2. For finite `s > 3`, the
hypothesis is the mixed norm `L^ℓ_t L^s_x` with `ℓ = 2s/(s-3)`; the second
alternative is `L²_t L^∞_x`. The smooth representative uses the Euclidean
product `Vec3 × ℝ`, definitionally the CKN carrier `ParabolicPoint`, so
`ContDiffOn` uses the ordinary space-time differentiable structure. It is
infinitely differentiable (C^∞; the exponent `(⊤ : ℕ∞)`, not `ω`). The set
`univ × Ioc 0 T` has `UniqueDiffOn` by the product of `uniqueDiffOn_univ` and
`uniqueDiffOn_Ioc`; thus at `t = T` within-set derivatives are uniquely
determined from times below `T`.
-/
theorem ladyzhenskayaProdiSerrin :
    ∀ T : ℝ, ∀ a : Vec3 → Vec3,
    ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
      IsLerayHopfSolution T a u Du →
      ((∃ s : ℝ, 3 < s ∧
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
by exact ESS.Main.ladyzhenskayaProdiSerrin

end ESS
