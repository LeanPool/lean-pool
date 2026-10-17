/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Tactic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Independent generators for a finite conical combination

Every conical combination can be expressed using a linearly independent
subfamily of its original generators.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.AuxiliarySeparation

variable {I E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem exists_positive_relation (A : I → E) (s : Finset I)
    (h : ¬ LinearIndependent ℝ (fun i : s ↦ A i)) :
    ∃ g : I → ℝ, (∑ i ∈ s, g i • A i) = 0 ∧ ∃ i ∈ s, 0 < g i := by
  classical
  obtain ⟨g, hg, i, hi, hgi⟩ :=
    (not_linearIndepOn_finset_iff (R := ℝ) (v := A)).mp h
  rcases lt_or_gt_of_ne hgi with hneg | hpos
  · refine ⟨fun j ↦ -g j, ?_, i, hi, neg_pos.mpr hneg⟩
    simp_rw [neg_smul, Finset.sum_neg_distrib, hg, neg_zero]
  · exact ⟨g, hg, i, hi, hpos⟩

private theorem exists_nonneg_representation_erase [DecidableEq I] (A : I → E) (s : Finset I)
    (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (h : ¬ LinearIndependent ℝ (fun i : s ↦ A i)) :
    ∃ i ∈ s, ∃ v : I → ℝ, (∀ j ∈ s.erase i, 0 ≤ v j) ∧
      (∑ j ∈ s.erase i, v j • A j) = ∑ j ∈ s, w j • A j := by
  classical
  obtain ⟨g, hg, i, hi, hgi⟩ := exists_positive_relation A s h
  let p := s.filter fun i ↦ 0 < g i
  obtain ⟨i₀, hi₀, hmin⟩ :
      ∃ i₀ ∈ p, ∀ j ∈ p, w i₀ / g i₀ ≤ w j / g j := by
    apply p.exists_min_image
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  have hi₀s : i₀ ∈ s := (Finset.mem_filter.mp hi₀).1
  have hgi₀ : 0 < g i₀ := (Finset.mem_filter.mp hi₀).2
  let v : I → ℝ := fun j ↦ w j - w i₀ / g i₀ * g j
  have hvi₀ : v i₀ = 0 := by simp [v, ne_of_gt hgi₀]
  refine ⟨i₀, hi₀s, v, ?_, ?_⟩
  · intro j hj
    have hjs : j ∈ s := Finset.mem_of_mem_erase hj
    dsimp [v]
    apply sub_nonneg.mpr
    by_cases hjp : j ∈ p
    · have hgj : 0 < g j := (Finset.mem_filter.mp hjp).2
      exact (le_div_iff₀ hgj).mp (hmin j hjp)
    · have hgj : g j ≤ 0 := by
        simpa only [p, Finset.mem_filter, hjs, true_and, not_lt] using hjp
      exact (mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (hw i₀ hi₀s) hgi₀.le) hgj).trans (hw j hjs)
  · calc
      (∑ j ∈ s.erase i₀, v j • A j) = ∑ j ∈ s, v j • A j := by
        apply Finset.sum_erase
        rw [hvi₀, zero_smul]
      _ = ∑ j ∈ s, w j • A j := by
        simp only [v, sub_smul, mul_smul, Finset.sum_sub_distrib,
          ← Finset.smul_sum, hg, smul_zero, sub_zero]

/-- A nonnegative finite combination uses a linearly independent subfamily
after possibly changing its coefficients. -/
theorem exists_nonneg_representation_linearIndependent (A : I → E) (s : Finset I)
    (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∃ t : Finset I, t ⊆ s ∧ LinearIndependent ℝ (fun i : t ↦ A i) ∧
      ∃ v : I → ℝ, (∀ i ∈ t, 0 ≤ v i) ∧
        (∑ i ∈ t, v i • A i) = ∑ i ∈ s, w i • A i := by
  classical
  induction s using Finset.strongInductionOn generalizing w with
  | _ s ih =>
    by_cases hs : LinearIndependent ℝ (fun i : s ↦ A i)
    · exact ⟨s, Finset.Subset.refl _, hs, w, hw, rfl⟩
    · obtain ⟨i, hi, v, hv, heq⟩ := exists_nonneg_representation_erase A s w hw hs
      obtain ⟨t, hts, ht, z, hz, hzeq⟩ := ih (s.erase i) (Finset.erase_ssubset hi) v hv
      exact ⟨t, hts.trans (Finset.erase_subset _ _), ht, z, hz, hzeq.trans heq⟩

/-- Every element of a finitely generated cone belongs to the cone generated
by some linearly independent subfamily of the given generators. -/
theorem exists_linearIndependent_subcone [Fintype I] (A : I → E) {x : E}
    (hx : x ∈ PointedCone.hull ℝ (Set.range A)) :
    ∃ s : Finset I, LinearIndependent ℝ (fun i : s ↦ A i) ∧
      x ∈ PointedCone.hull ℝ (Set.range (fun i : s ↦ A i)) := by
  classical
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun (Nonneg ℝ)).mp hx
  obtain ⟨s, _, hs, v, hv, heq⟩ :=
    exists_nonneg_representation_linearIndependent A Finset.univ
      (fun i ↦ (w i : ℝ)) (fun i _ ↦ (w i).property)
  refine ⟨s, hs, ?_⟩
  have hsum : (∑ i ∈ s, v i • A i) = x := by
    exact heq.trans (by simpa only [← Nonneg.coe_smul] using hw)
  rw [← hsum]
  apply Submodule.sum_mem
  intro i hi
  exact PointedCone.smul_mem _ (hv i hi)
    (PointedCone.subset_hull ⟨⟨i, hi⟩, rfl⟩)

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
