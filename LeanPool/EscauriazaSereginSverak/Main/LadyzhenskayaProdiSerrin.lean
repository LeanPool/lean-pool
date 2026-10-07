/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.AssemblyGlobal
public import LeanPool.EscauriazaSereginSverak.LPS.Continuation
public import LeanPool.EscauriazaSereginSverak.LPS.Uniqueness
public import LeanPool.EscauriazaSereginSverak.LPS.Smoothing

/-!
# The Ladyzhenskaya–Prodi–Serrin theorem

The theorem `thm:lps`: a Leray–Hopf solution satisfying the Serrin condition is
unique among Leray–Hopf solutions with its datum and has a representative that is
smooth up to the final time. It is assembled from the continuation lemma
`lem:lps-continuation`, the comparison lemma `lem:lps-comparison` and the smoothing
proposition `prop:lps-smoothing`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.Main

/-- The Ladyzhenskaya–Prodi–Serrin theorem `thm:lps`. -/
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
  fun _T _a _u _Du hLH hSerrin =>
    lps_ladyzhenskaya_prodi_serrin_of_node_conclusions
      (fun hLH hSerrin _ _t₀ ht₀ hgood henergy =>
        lps_continuation hLH hSerrin ht₀ hgood henergy)
      (fun hLH hSerrin _v _Dv hV => lps_leray_hopf_uniqueness hLH hV hSerrin)
      (fun h => lps_smoothing h)
      hLH hSerrin

end ESS.Main

end
