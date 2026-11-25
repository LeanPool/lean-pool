/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.ConeAngles
public import LeanPool.DehnInvariant.EdgeData
public import LeanPool.DehnInvariant.TetrahedronData
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Tactic.Push

/-!
# The Dehn invariant of a tetrahedron

The barycentric coordinates in `IsTetraData` identify the points where exactly two constraints
are active as the open segment between the two opposite corners. The Dehn invariant sums
the lengths of these six segments tensored with the angle classes of their cones.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

/-- **A test for "not zero".** If the length `L₁` is not a rational multiple of the length `L₂`,
and the angle
class `θ₁` is not zero (the angle is not a rational multiple of π), then `L₁ ⊗ θ₁ + L₂ ⊗ θ₂ ≠ 0`,
whatever
`θ₂` is. -/
theorem tmul_add_tmul_ne_zero {L₁ L₂ : ℝ} {θ₁ θ₂ : Angle} (hL : L₁ ∉ Submodule.span ℚ {L₂})
    (hθ : θ₁ ≠ 0) : L₁ ⊗ₜ[ℚ] θ₁ + L₂ ⊗ₜ[ℚ] θ₂ ≠ (0 : DehnSpace) := by
  intro h
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hL inferInstance
  have hf2 : f L₂ = 0 := by
    have h1 : f L₂ ∈ (Submodule.span ℚ {L₂}).map f :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
    rw [hf0] at h1
    exact (Submodule.mem_bot ℚ).1 h1
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual ℚ Angle, g θ₁ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hθ ((Module.forall_dual_apply_eq_zero_iff ℚ _).1 hc)
  have h2 := congrArg (TensorProduct.lift ((LinearMap.mul ℚ ℚ).compl₁₂ f g)) h
  rw [map_add, TensorProduct.lift.tmul, TensorProduct.lift.tmul, map_zero, LinearMap.compl₁₂_apply,
    LinearMap.compl₁₂_apply, LinearMap.mul_apply', LinearMap.mul_apply', hf2, zero_mul,
        add_zero] at h2
  exact mul_ne_zero hf hg h2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma fin4_pair_compl : ∀ i j : Fin 4, i ≠ j →
    ∃ k l, k < l ∧ ∀ m, (m = i ∨ m = j) ↔ (m ≠ k ∧ m ≠ l) := by decide

lemma fin4_compl_pair : ∀ k l : Fin 4, k ≠ l →
    ∃ i j, i ≠ j ∧ ∀ m, (m ≠ k ∧ m ≠ l) ↔ (m = i ∨ m = j) := by decide

lemma fin4_pair_unique : ∀ k l k' l' : Fin 4, k < l → k' < l' →
    (∀ m, (m ≠ k ∧ m ≠ l) ↔ (m ≠ k' ∧ m ≠ l')) → k = k' ∧ l = l' := by decide

/-- The pairs of distinct tetrahedron corners, with the smaller index first. -/
def tetPairs : Finset (Fin 4 × Fin 4) := Finset.univ.filter fun p => p.1 < p.2

lemma tetPairs_card : tetPairs.card = 6 := by decide

/-- The six pairs of corners, written out. -/
lemma tetPairs_eq : tetPairs = {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by decide

lemma sum_tetPairs {M : Type*} [AddCommMonoid M] (f : Fin 4 × Fin 4 → M) :
    ∑ q ∈ tetPairs, f q = f (0, 1) + f (0, 2) + f (0, 3) + f (1, 2) + f (1, 3) + f (2, 3) := by
  rw [tetPairs_eq, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [add_assoc]

/-- The two faces through the edge between the corners `k`, `l` are the two other ones, `i`, `j`. -/
lemma compl_pair_eq {k l i j : Fin 4} (h : ∀ m : Fin 4, (m ≠ k ∧ m ≠ l) ↔ (m = i ∨ m = j)) :
    ({k, l}ᶜ : Set (Fin 4)) = {i, j} := by
  ext m
  rw [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or, mem_insert_iff, mem_singleton_iff]
  exact h m

/-- **The Dehn invariant of a tetrahedron**: the sum over its six edges of
(distance of the two corners of the edge) ⊗ (angle class of the cone of the two faces through the
edge;
the edge between the corners `k`, `l` lies on the two faces other than `k`, `l`). -/
theorem IsTetraData.dehnSet_eq [Fact (finrank ℝ E = 3)] {n p : Fin 4 → E} {b w : Fin 4 → ℝ}
    (h : IsTetraData n p b w) :
    dehnSet (sol n b) =
      ∑ q ∈ tetPairs, dist (p q.1) (p q.2) ⊗ₜ[ℚ] theta (cone n ({q.1, q.2}ᶜ : Set (Fin 4))) := by
  classical
  let F : Fin 4 × Fin 4 → Set (Fin 4) := fun q => {q.1, q.2}ᶜ
  have hzero : ∀ A : Set (Fin 4), A ∉ tetPairs.image F →
      (μH[1] (faceSet n b A)).toReal ⊗ₜ[ℚ] theta (cone n A) = 0 := by
    intro A hA
    by_cases hfin : finrank ℝ (linCone n A) = 1
    · exfalso
      obtain ⟨i, j, hij, rfl⟩ := pair_of_finrank_one n hfin
        (fun _ _ _ _ _ _ hij hik hjk _ hi hj hk => h.three hij hik hjk hi hj hk)
      obtain ⟨k, l, hkl, hm⟩ := fin4_pair_compl i j hij
      apply hA
      rw [Finset.mem_image]
      refine ⟨(k, l), Finset.mem_filter.2 ⟨Finset.mem_univ _, hkl⟩, ?_⟩
      ext m
      change m ∈ ({k, l}ᶜ : Set (Fin 4)) ↔ m ∈ ({i, j} : Set (Fin 4))
      rw [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or, mem_insert_iff,
          mem_singleton_iff]
      exact (hm m).symm
    · unfold theta; rw [linSpace_cone, ite_eq_right hfin, TensorProduct.tmul_zero]
  have hinj : Set.InjOn F (tetPairs : Set (Fin 4 × Fin 4)) := by
    rintro ⟨k, l⟩ hq ⟨k', l'⟩ hq' hF
    have hkl : k < l := (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).2
    have hkl' : k' < l' := (Finset.mem_filter.1 (Finset.mem_coe.1 hq')).2
    have hm : ∀ m, (m ≠ k ∧ m ≠ l) ↔ (m ≠ k' ∧ m ≠ l') := by
      intro m
      have h1 : m ∈ ({k, l}ᶜ : Set (Fin 4)) ↔ m ∈ ({k', l'}ᶜ : Set (Fin 4)) := by
        change m ∈ F (k, l) ↔ m ∈ F (k', l')
        rw [hF]
      rw [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or, mem_compl_iff, mem_insert_iff,
        mem_singleton_iff, not_or] at h1
      exact h1
    obtain ⟨e1, e2⟩ := fin4_pair_unique k l k' l' hkl hkl' hm
    rw [e1, e2]
  rw [dehnSet_eq_sum_faceSet n b h.bounded,
    ← Finset.sum_subset (Finset.subset_univ (tetPairs.image F)) (fun A _ hA => hzero A hA),
    Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  rintro ⟨k, l⟩ hq
  have hkl : k < l := (Finset.mem_filter.1 hq).2
  have hface : faceSet n b (F (k, l)) = openSegment ℝ (p k) (p l) := by
    ext x; exact (h.openSegment_iff hkl.ne x).symm
  rw [hface, hausdorff_openSegment (h.corner_ne hkl.ne)]

end DehnCanon.Library
