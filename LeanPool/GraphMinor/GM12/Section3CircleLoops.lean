/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3CurveMultiplicity
import LeanPool.GraphMinor.GM12.Section2CirclePeriod
import Mathlib.Tactic.FinCases

/-!
# Short curves through two meeting circles

For XII (3.1)(iii) in the proof of (3.2), page 246, parameterize
each circle once from their common point. Their two loop paths join
to a closed curve covering their union. Each path is injective before
its final endpoint, so its piece index is a two-valued visit label.
The multiplicity bound gives length at most twice the number of
drawing vertices in the union.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM07

/-- Parameterize a circle once from a prescribed point, with no
repetition before the final endpoint. -/
theorem exists_circle_loop_based_at
    {S : Type*} [TopologicalSpace S] {F : Set S} (hF : IsOArc F) {p : S} (hp : p ∈ F) :
    ∃ γ : C(unitInterval, S), γ 0 = p ∧ γ 1 = p ∧ range γ = F ∧
      InjOn γ (Ico (0 : unitInterval) 1) := by
  obtain ⟨H⟩ := hF
  let a : Circle := H.symm ⟨p, hp⟩
  let J : Circle ≃ₜ F := (Homeomorph.mulLeft a).trans H
  have hJ1 : (J 1).val = p := by
    change (H (a * 1)).val = p
    simp only [mul_one, a, H.apply_symm_apply]
  let γ : C(unitInterval, S) :=
    ⟨fun t => (J (Circle.exp (2 * Real.pi * t.val))).val, by fun_prop⟩
  have hγ0 : γ 0 = p := by
    change (J (Circle.exp (2 * Real.pi * (0 : ℝ)))).val = p
    simpa only [mul_zero, Circle.exp_zero] using hJ1
  have hγ1 : γ 1 = p := by
    change (J (Circle.exp (2 * Real.pi * (1 : ℝ)))).val = p
    simpa only [mul_one, Circle.exp_two_pi] using hJ1
  have hrange : range γ = F := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (J _).property
    · intro hx
      obtain ⟨t, ht, htJ⟩ := (circle_parameter_bijOn 0).surjOn (mem_univ (J.symm ⟨x, hx⟩))
      let u : unitInterval := ⟨t, ht.1, by simpa only [zero_add] using ht.2.le⟩
      refine ⟨u, ?_⟩
      change (J (Circle.exp (2 * Real.pi * t))).val = x
      change Circle.exp (2 * Real.pi * t) = J.symm ⟨x, hx⟩ at htJ
      rw [htJ, J.apply_symm_apply]
  have hinj : InjOn γ (Ico (0 : unitInterval) 1) := by
    intro s hs t ht heq
    have hcircle := J.injective (Subtype.ext heq)
    have hs' : s.val < 1 := hs.2
    have ht' : t.val < 1 := ht.2
    have hreal := circle_parameter_injOn 0 ⟨s.property.1, by simpa only [zero_add] using hs'⟩
      ⟨t.property.1, by simpa only [zero_add] using ht'⟩ hcircle
    exact Subtype.ext hreal
  exact ⟨γ, hγ0, hγ1, hrange, hinj⟩

/-- Two normal circles with a common point lie in one normal closed
curve of length at most twice their union's drawing vertex count.
This is the short-curve construction for XII (3.1)(iii), page 246. -/
theorem exists_short_curve_covering_two_meeting_circles
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {A B : Set S}
    (hA : IsOArc A) (hB : IsOArc B) (hn : Γ.IsNormal (A ∪ B))
    {p : S} (hpA : p ∈ A) (hpB : p ∈ B) :
    ∃ φ : C(Circle, S), IsNormalCurve Γ φ ∧ range φ = A ∪ B ∧
      curveLength Γ φ ≤ 2 * (Γ.V ∩ (A ∪ B)).ncard := by
  obtain ⟨α, hα0, hα1, hαrange, hαi⟩ := exists_circle_loop_based_at hA hpA
  obtain ⟨β, hβ0, hβ1, hβrange, hβi⟩ := exists_circle_loop_based_at hB hpB
  let γ : Fin 2 → C(unitInterval, S) := fun i => if i = 0 then α else β
  have hmatch : ∀ i : Fin 2, γ i 1 = γ (finNext (by decide : 0 < 2) i) 0 := by
    intro i
    fin_cases i <;> simp [γ, finNext, hα0, hα1, hβ0, hβ1]
  have hγX : ∀ i, range (γ i) ⊆ A ∪ B := by
    intro i
    fin_cases i
    · change range α ⊆ A ∪ B
      rw [hαrange]
      exact subset_union_left
    · change range β ⊆ A ∪ B
      rw [hβrange]
      exact subset_union_right
  have hγi : ∀ i, InjOn (γ i) (Ico (0 : unitInterval) 1) := by
    intro i
    fin_cases i
    · exact hαi
    · exact hβi
  have hsep : ∀ (i j : Fin 2) (s t : unitInterval), s.val < 1 → t.val < 1 →
      γ i s = γ j t → (i : Fin 2) = j → i = j ∧ s = t := by
    intro i j s t hs ht heq hij
    subst j
    exact ⟨rfl, hγi i ⟨s.property.1, hs⟩ ⟨t.property.1, ht⟩ heq⟩
  obtain ⟨hφ, hlen⟩ := concatLoop_length_le_of_piece_labels hn (by decide : 0 < 2) γ hmatch hγX
    (fun i _ => i) hsep
  have hrange : range (concatLoop (by decide : 0 < 2) γ hmatch) = A ∪ B := by
    rw [range_concatLoop]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact hγX i hi
    · rintro (hx | hx)
      · exact mem_iUnion.mpr ⟨0, hαrange.symm ▸ hx⟩
      · exact mem_iUnion.mpr ⟨1, hβrange.symm ▸ hx⟩
  refine ⟨_, hφ, hrange, ?_⟩
  simpa only [inter_comm] using hlen

end GraphMinor.GM12
