/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationConcat
public import LeanPool.EscauriazaSereginSverak.LPS.Uniqueness
public import LeanPool.EscauriazaSereginSverak.LPS.UniquenessRestrict

/-!
# Comparing a strong continuation with a Leray–Hopf solution

A strong solution started, from a time of energy equality, at the slice of a
Leray–Hopf solution with finite Serrin norm coincides with it, by
uniqueness of Leray–Hopf solutions applied to the concatenation
(`lem:lps-continuation`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The Serrin hypotheses of `thm:lps` are inherited by shorter time intervals. -/
theorem lps_serrin_restrict {T σ : ℝ} {u : ParabolicPoint → Vec3} (hσT : σ ≤ T)
    (hSerrin :
      (∃ s : ℝ, 3 < s ∧
        (∫⁻ t in Ioo (0 : ℝ) T,
          (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
            ((2 * s / (s - 3)) / s)) < ⊤) ∨
      (∫⁻ t in Ioo (0 : ℝ) T,
        (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤) :
    (∃ s : ℝ, 3 < s ∧
        (∫⁻ t in Ioo (0 : ℝ) σ,
          (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
            ((2 * s / (s - 3)) / s)) < ⊤) ∨
      (∫⁻ t in Ioo (0 : ℝ) σ,
        (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤ := by
  have hsub : Ioo (0 : ℝ) σ ⊆ Ioo 0 T := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hσT⟩
  rcases hSerrin with ⟨s, hs, h⟩ | h
  · exact Or.inl ⟨s, hs, lt_of_le_of_lt (lintegral_mono_set hsub) h⟩
  · exact Or.inr (lt_of_le_of_lt (lintegral_mono_set hsub) h)

/-- A strong solution started from a slice of a Leray–Hopf solution with finite
Serrin norm, at a time of energy equality, agrees with it on the common time
interval (`lem:lps-continuation`). -/
theorem lps_continuation_compare {T s s' : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {W : ParabolicPoint → Vec3}
    {DW : ParabolicPoint → Fin 3 → Vec3} {pW : ParabolicPoint → ℝ}
    (hLH : IsLerayHopfSolution T a u Du)
    (hSerrin :
      (∃ s : ℝ, 3 < s ∧
        (∫⁻ t in Ioo (0 : ℝ) T,
          (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
            ((2 * s / (s - 3)) / s)) < ⊤) ∨
      (∫⁻ t in Ioo (0 : ℝ) T,
        (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤)
    (hs0 : 0 < s) (hsT : s ≤ T) (hW : IsLpsStrongSolution s s' W DW pW)
    (hweakEq : ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      (∫ x : Vec3, ∑ i : Fin 3, W (x, s) i * w x i) = ∫ x : Vec3, ∑ i : Fin 3, u (x, s) i * w x i)
    (hEnergy : ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (W (x, s))) ^ (2 : ℝ)) +
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s),
        ENNReal.ofReal (spatialGradientSq u Du z)) =
      ENNReal.ofReal (1 / 2 : ℝ) * ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ)) :
    W =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo s (min s' T)))] u := by
  have hV := lps_leray_hopf_concat hLH hs0 hsT hW hweakEq hEnergy
  have hσ : 0 < min s' T := lt_min (hs0.trans hW.1) (hs0.trans_le hsT)
  have hU' := CKN.IsLerayHopfSolution.restrict hLH hσ (min_le_right s' T)
  have hV' := CKN.IsLerayHopfSolution.restrict hV hσ (min_le_left s' T)
  have huniq := lps_leray_hopf_uniqueness hU' hV' (lps_serrin_restrict (min_le_right s' T) hSerrin)
  have hsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo s (min s' T)) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 (min s' T)) :=
    fun z hz => ⟨hz.1, hs0.trans hz.2.1, hz.2.2⟩
  have h1 := ae_restrict_of_ae_restrict_of_subset hsub huniq
  have hmeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo s (min s' T))) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  filter_upwards [h1, ae_restrict_mem hmeas] with z hz hzm
  rw [← hz, lpsCat_of_ge hzm.2.1.le]

end ESS

end
