/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Separator
public import Mathlib.Algebra.BigOperators.Field

/-!
# Divisions of plane graphs into light pieces

Let `μ` be nonnegative weights on the vertices of a plane graph and `U` a set of vertices of
total weight `Φ`. Applying the separator theorem recursively to the pieces of weight more than
`1`, we find a set `S ⊆ U` of at most `6 √(#U) · max 0 (3Φ - 2)` vertices such that every piece of
`U \ S` (a union of connected components of the subgraph induced on `U \ S`) has weight at most
`1` (`PlanarSeparator.exists_division`). Each application of the separator theorem to a piece of
weight `Φ > 1` produces two pieces of weights `Φ₁, Φ₂ ≤ 2Φ/3` with `Φ₁ + Φ₂ ≤ Φ`, and
`1 + max 0 (3Φ₁ - 2) + max 0 (3Φ₂ - 2) ≤ 3Φ - 2`, which bounds the total number of separator
vertices.

The pieces are given by a labelling `κ`: adjacent vertices of `U \ S` have the same label, and
the label of a vertex is a set of vertices of `U` containing it.

## References

* G. N. Frederickson, *Fast algorithms for shortest paths in planar graphs, with applications*,
  SIAM J. Comput. 16 (1987), 1004–1022 (divisions of planar graphs).
-/

@[expose] public section

namespace PlanarSeparator

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {R : Kasteleyn.RotationSystem G}

lemma division_step_bound {Φ Φ₁ Φ₂ : ℝ} (hΦ : 1 < Φ) (h1 : Φ₁ ≤ 2 / 3 * Φ)
    (h2 : Φ₂ ≤ 2 / 3 * Φ) (h12 : Φ₁ + Φ₂ ≤ Φ) :
    1 + max 0 (3 * Φ₁ - 2) + max 0 (3 * Φ₂ - 2) ≤ 3 * Φ - 2 := by
  rcases le_total 0 (3 * Φ₁ - 2) with a | a <;> rcases le_total 0 (3 * Φ₂ - 2) with b | b <;>
    simp only [max_eq_left, max_eq_right, a, b] <;> linarith

omit [Fintype V] [DecidableRel G.Adj] in
/-- **Divisions into light pieces.** Let `G` have `c √m`-separators. For nonnegative weights `μ`
and a set `U` of vertices there is a set `S ⊆ U` of at most `c √(#U) · max 0 (3 μ(U) - 2)`
vertices and a labelling of `U \ S`, constant along edges, whose classes have weight at most
`1`. -/
theorem exists_division_of_separators {c : ℝ} (hG : HasSqrtSeparators G c) (hc : 0 ≤ c)
    (μ : V → ℝ) (hμ : ∀ v, 0 ≤ μ v) (U : Finset V) :
    ∃ S ⊆ U, ∃ κ : V → Finset V,
      (∀ v ∈ U \ S, v ∈ κ v ∧ κ v ⊆ U) ∧
      (∀ u ∈ U \ S, ∀ v ∈ U \ S, G.Adj u v → κ u = κ v) ∧
      (∀ i, ∑ v ∈ U \ S with κ v = i, μ v ≤ 1) ∧
      (#S : ℝ) ≤ c * √(#U : ℝ) * max 0 (3 * ∑ v ∈ U, μ v - 2) := by
  classical
  induction hn : #U using Nat.strong_induction_on generalizing U with
  | _ n ih =>
  set Φ := ∑ v ∈ U, μ v with hΦdef
  have hsub : ∀ (s s' : Finset V), s ⊆ s' → ∑ v ∈ s, μ v ≤ ∑ v ∈ s', μ v :=
    fun s s' h => sum_le_sum_of_subset_of_nonneg h fun v _ _ => hμ v
  by_cases hΦ : Φ ≤ 1
  · refine ⟨∅, empty_subset _, fun _ => U, fun v hv => ⟨(mem_sdiff.1 hv).1, subset_rfl⟩,
      fun _ _ _ _ _ => rfl, fun i => ?_, by simp only [card_empty, CharP.cast_eq_zero]; positivity⟩
    exact (hsub _ _ (fun v hv => (mem_sdiff.1 (mem_filter.1 hv).1).1)).trans hΦ
  push Not at hΦ
  have hΦ0 : 0 < Φ := by linarith
  set w : V → ℝ := fun v => μ v / Φ
  have hw : ∀ v, 0 ≤ w v := fun v => div_nonneg (hμ v) hΦ0.le
  have hwμ : ∀ s : Finset V, ∑ v ∈ s, w v = (∑ v ∈ s, μ v) / Φ := fun s => by
    simp only [w, sum_div]
  obtain ⟨S₁, A₁, A₂, hsep, hS₁, hA₁, hA₂⟩ :=
    hG U w hw (by rw [hwμ, div_self hΦ0.ne'])
  rw [hwμ, div_le_iff₀ hΦ0] at hA₁ hA₂
  have hA₁U : A₁ ⊆ U := fun x hx => hsep.union_eq ▸ mem_union_left _ (mem_union_right _ hx)
  have hA₂U : A₂ ⊆ U := fun x hx => hsep.union_eq ▸ mem_union_right _ hx
  have hS₁U : S₁ ⊆ U := fun x hx => hsep.union_eq ▸ mem_union_left _ (mem_union_left _ hx)
  have hlt : ∀ A ⊆ U, ∑ v ∈ A, μ v ≤ 2 / 3 * Φ → #A < n := by
    intro A hAU hAμ
    rw [← hn]
    refine card_lt_card ⟨hAU, fun hUA => ?_⟩
    have := hsub _ _ hUA
    linarith
  obtain ⟨S', hS'A, κ₁, hκ₁, hadj₁, hpiece₁, hsize₁⟩ :=
    ih _ (hlt A₁ hA₁U (by linarith)) A₁ rfl
  obtain ⟨S'', hS''A, κ₂, hκ₂, hadj₂, hpiece₂, hsize₂⟩ :=
    ih _ (hlt A₂ hA₂U (by linarith)) A₂ rfl
  have hdisj := hsep.disjoint
  set S := S₁ ∪ S' ∪ S''
  set κ : V → Finset V := fun v => if v ∈ A₁ then κ₁ v else κ₂ v
  -- vertices off `S`
  have hside : ∀ v ∈ U \ S, (v ∈ A₁ ∧ v ∈ A₁ \ S') ∨ (v ∉ A₁ ∧ v ∈ A₂ \ S'') := by
    intro v hv
    obtain ⟨hvU, hvS⟩ := mem_sdiff.1 hv
    simp only [S, mem_union, not_or] at hvS
    rw [← hsep.union_eq] at hvU
    simp only [mem_union] at hvU
    rcases hvU with (h | h) | h
    · exact absurd h hvS.1.1
    · exact Or.inl ⟨h, mem_sdiff.2 ⟨h, hvS.1.2⟩⟩
    · exact Or.inr ⟨fun h' => disjoint_left.1 hdisj h' h, mem_sdiff.2 ⟨h, hvS.2⟩⟩
  refine ⟨S, union_subset (union_subset hS₁U (hS'A.trans hA₁U)) (hS''A.trans hA₂U), κ, ?_, ?_,
    ?_, ?_⟩
  · intro v hv
    rcases hside v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [κ, ite_eq_left h1]
      exact ⟨(hκ₁ v h2).1, (hκ₁ v h2).2.trans hA₁U⟩
    · simp only [κ, ite_eq_right h1]
      exact ⟨(hκ₂ v h2).1, (hκ₂ v h2).2.trans hA₂U⟩
  · intro u hu v hv huv
    rcases hside u hu with ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩ <;>
      rcases hside v hv with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
    · simp only [κ, ite_eq_left hu1, ite_eq_left hv1]
      exact hadj₁ u hu2 v hv2 huv
    · exact absurd huv (hsep.not_adj u hu1 v (mem_sdiff.1 hv2).1)
    · exact absurd huv.symm (hsep.not_adj v hv1 u (mem_sdiff.1 hu2).1)
    · simp only [κ, ite_eq_right hu1, ite_eq_right hv1]
      exact hadj₂ u hu2 v hv2 huv
  · intro i
    by_cases hi : ∃ v ∈ A₁ \ S', κ₁ v = i
    · obtain ⟨v₀, hv₀, rfl⟩ := hi
      refine (hsub _ ((A₁ \ S').filter fun v => κ₁ v = κ₁ v₀) fun v hv => ?_).trans
        (hpiece₁ _)
      obtain ⟨hv1, hv2⟩ := mem_filter.1 hv
      rcases hside v hv1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [κ, ite_eq_left h1] at hv2
        exact mem_filter.2 ⟨h2, hv2⟩
      · simp only [κ, ite_eq_right h1] at hv2
        have : v ∈ κ₁ v₀ := hv2 ▸ (hκ₂ v h2).1
        exact absurd ((hκ₁ v₀ hv₀).2 this) h1
    · push Not at hi
      refine (hsub _ ((A₂ \ S'').filter fun v => κ₂ v = i) fun v hv => ?_).trans (hpiece₂ _)
      obtain ⟨hv1, hv2⟩ := mem_filter.1 hv
      rcases hside v hv1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [κ, ite_eq_left h1] at hv2
        exact absurd hv2 (hi v h2)
      · simp only [κ, ite_eq_right h1] at hv2
        exact mem_filter.2 ⟨h2, hv2⟩
  · have hcard : (#S : ℝ) ≤ #S₁ + #S' + #S'' := by
      have := (card_union_le _ _).trans (add_le_add_left (card_union_le S₁ S') #S'')
      have h' : #S ≤ #S₁ + #S' + #S'' := by
        calc #S ≤ #(S₁ ∪ S') + #S'' := card_union_le _ _
          _ ≤ #S₁ + #S' + #S'' := by
            have := card_union_le S₁ S'
            omega
      exact_mod_cast h'
    have hsq : ∀ A ⊆ U, √(#A : ℝ) ≤ √(#U : ℝ) := fun A hA =>
      Real.sqrt_le_sqrt (by exact_mod_cast card_le_card hA)
    have h1 : (#S' : ℝ) ≤ c * √(#U : ℝ) * max 0 (3 * ∑ v ∈ A₁, μ v - 2) :=
      hsize₁.trans (by gcongr)
    have h2 : (#S'' : ℝ) ≤ c * √(#U : ℝ) * max 0 (3 * ∑ v ∈ A₂, μ v - 2) :=
      hsize₂.trans (by gcongr)
    have h12 : ∑ v ∈ A₁, μ v + ∑ v ∈ A₂, μ v ≤ Φ := by
      rw [← sum_union hdisj]
      exact hsub _ _ (union_subset hA₁U hA₂U)
    have key := division_step_bound hΦ (by linarith) (by linarith) h12
    have hsqU := Real.sqrt_nonneg (#U : ℝ)
    have : c * √(#U : ℝ) * (1 + max 0 (3 * ∑ v ∈ A₁, μ v - 2) + max 0 (3 * ∑ v ∈ A₂, μ v - 2))
        ≤ c * √(#U : ℝ) * max 0 (3 * Φ - 2) := by
      gcongr
      exact key.trans (le_max_right _ _)
    rw [← hn]
    linarith

/-- **Divisions of plane graphs into light pieces.** For nonnegative weights `μ` and a set `U` of
vertices of a plane graph, there is a set `S ⊆ U` of at most `6 √(#U) · max 0 (3 μ(U) - 2)`
vertices and a labelling of `U \ S`, constant along edges, whose classes have weight at most
`1`. -/
theorem exists_division (hR : R.IsPlane) (μ : V → ℝ) (hμ : ∀ v, 0 ≤ μ v) (U : Finset V) :
    ∃ S ⊆ U, ∃ κ : V → Finset V,
      (∀ v ∈ U \ S, v ∈ κ v ∧ κ v ⊆ U) ∧
      (∀ u ∈ U \ S, ∀ v ∈ U \ S, G.Adj u v → κ u = κ v) ∧
      (∀ i, ∑ v ∈ U \ S with κ v = i, μ v ≤ 1) ∧
      (#S : ℝ) ≤ 6 * √(#U : ℝ) * max 0 (3 * ∑ v ∈ U, μ v - 2) :=
  exists_division_of_separators (hasSqrtSeparators_of_isPlane hR) (by norm_num) μ hμ U

end PlanarSeparator
