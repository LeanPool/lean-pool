/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Main.EssL5Unique
public import LeanPool.EscauriazaSereginSverak.LPS.L5Serrin

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The `L^5` and uniqueness conclusion under a uniform-in-time `L^3` bound
follows from `thm:lps` at `(s,ℓ) = (5,5)` and `thm:ess-l5-unique`.
The hypothesis is the full conclusion of `thm:lps`, supplied by its provider. -/
theorem ess_smooth_of_ladyzhenskaya_prodi_serrin
    (hLps : ∀ T : ℝ, ∀ a : Vec3 → Vec3,
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
                (spaceTimeSet Set.univ (Ioo 0 T))] u) ∧
        (∃ uSmooth : ParabolicPoint → Vec3,
          uSmooth =ᵐ[volume.restrict
            (spaceTimeSet Set.univ (Ioo 0 T))] u ∧
          ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => uSmooth z)
            ((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T))) :
    ∀ T : ℝ, ∀ a : Vec3 → Vec3,
    ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
      IsLerayHopfSolution T a u Du →
      essSup
        (fun t : ℝ => ∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
        (volume.restrict (Ioo 0 T)) < ⊤ →
      MemLp u (ENNReal.ofReal (5 : ℝ))
        (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) ∧
      (∀ v : ParabolicPoint → Vec3,
        ∀ Dv : ParabolicPoint → Fin 3 → Vec3,
          IsLerayHopfSolution T a v Dv →
            v =ᵐ[volume.restrict
              (spaceTimeSet Set.univ (Ioo 0 T))] u) ∧
      (∃ uSmooth : ParabolicPoint → Vec3,
        uSmooth =ᵐ[volume.restrict
          (spaceTimeSet Set.univ (Ioo 0 T))] u ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => uSmooth z)
          ((Set.univ : Set Vec3) ×ˢ Ioc (0 : ℝ) T)) := by
  intro T a u Du hLH hL3
  obtain ⟨hu5, hL5Unique⟩ := ESS.Main.essL5Unique T a u Du hLH hL3
  have hSerrin :
      (∃ s : ℝ, 3 < s ∧
        (∫⁻ t in Ioo (0 : ℝ) T,
          (∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
              ((2 * s / (s - 3)) / s)) < ⊤) ∨
      (∫⁻ t in Ioo (0 : ℝ) T,
        (essSup
          (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤ := by
    left
    exact ⟨5, by norm_num, lps_finite_branch_of_memLp_five hu5⟩
  obtain ⟨hUnique, hSmooth⟩ := hLps T a u Du hLH hSerrin
  exact ⟨hu5, hUnique, hSmooth⟩

end ESS

end
