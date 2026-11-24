/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Rotation

/-!
# A drawing near a vertex consists of its short half-edges

For the entry-edge construction of XII page 243, it is useful to remove
all but prescribed positive initial pieces of the incident edges.
The remaining parts are compact and miss the vertex. Their complement
is the required neighbourhood. The proof also applies to isolated
vertices and loops.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 unitInterval

/-- Prescribed positive initial pieces of every half-edge cover the
drawing in a neighbourhood of the vertex, together with the vertex
itself. Compact edge remainders can all be excluded at once. -/
theorem exists_halfEdge_neighbourhood {S : Type*} [TopologicalSpace S] [T2Space S]
    (Γ : Drawing S) {γ : Set S → I → S} (hγ : EdgePar Γ γ) {v : S} (hv : v ∈ Γ.V)
    (τ : halfEdges Γ γ v → I) (hτ0 : ∀ i, 0 < τ i) :
    ∃ O : Set S, IsOpen O ∧ v ∈ O ∧
      O ∩ Γ.U ⊆ {v} ∪ ⋃ i : halfEdges Γ γ v, spoke γ i.val '' Icc 0 (τ i) := by
  classical
  let H := halfEdges Γ γ v
  let J : H → Set S := fun i => spoke γ i.val '' Icc 0 (τ i)
  let C : Set S → Set I := fun e => {t | ∀ x : H, x.1.1 = e →
    (if x.1.2 then t.1 ≤ 1 - (τ x).1 / 2 else (τ x).1 / 2 ≤ t.1)}
  have hCclosed : ∀ e, IsClosed (C e) := by
    intro e
    have : C e = ⋂ x : H, {t : I | x.1.1 = e →
        (if x.1.2 then t.1 ≤ 1 - (τ x).1 / 2 else (τ x).1 / 2 ≤ t.1)} := by
      ext t
      simp [C]
    rw [this]
    refine isClosed_iInter fun x => ?_
    by_cases hx : x.1.1 = e
    · cases hb : x.1.2
      · simpa [hx, hb] using isClosed_le continuous_const continuous_subtype_val
      · simpa [hx, hb] using isClosed_le continuous_subtype_val continuous_const
    · simp [hx]
  let K : Set S := (Γ.V \ {v}) ∪ ⋃ e ∈ Γ.E, γ e '' C e
  have hKclosed : IsClosed K := by
    refine ((Γ.finite_V.subset sdiff_subset).isClosed).union ?_
    exact Γ.finite_edges.isClosed_biUnion fun e he =>
      ((hCclosed e).isCompact.image (hγ.cont e he)).isClosed
  have hend : ∀ e ∈ Γ.E, ∀ t : I, t ∉ Ioo (0 : I) 1 → t = 0 ∨ t = 1 := by
    intro e _ t ht
    by_contra hcon
    push Not at hcon
    exact ht ⟨unitInterval.pos_iff_ne_zero.mpr hcon.1, lt_of_le_of_ne le_top hcon.2⟩
  have hvK : v ∉ K := by
    rintro (⟨-, h⟩ | h)
    · exact h rfl
    · obtain ⟨e, he, t, ht, hte⟩ := mem_iUnion₂.mp h
      by_cases hIoo : t ∈ Ioo (0 : I) 1
      · have : v ∈ e := by
          rw [← hγ.image e he]
          exact ⟨t, hIoo, hte⟩
        exact edge_notMem_V he this hv
      · rcases hend e he t hIoo with rfl | rfl
        · have hx : ((e, false) : Set S × Bool) ∈ halfEdges Γ γ v := ⟨he, hte⟩
          have := ht ⟨_, hx⟩ rfl
          simp only [Bool.false_eq_true, ite_false] at this
          have h0 : (0 : ℝ) < τ ⟨_, hx⟩ := hτ0 ⟨_, hx⟩
          simp at this
          linarith
        · have hx : ((e, true) : Set S × Bool) ∈ halfEdges Γ γ v := ⟨he, hte⟩
          have := ht ⟨_, hx⟩ rfl
          simp only [ite_true] at this
          have h0 : (0 : ℝ) < τ ⟨_, hx⟩ := hτ0 ⟨_, hx⟩
          simp at this
          linarith
  have hclosureE : ∀ e ∈ Γ.E, closure e ⊆ γ e '' univ := by
    intro e he
    refine closure_minimal ?_ ((isCompact_univ.image (hγ.cont e he)).isClosed)
    intro x hx
    have h' : x ∈ γ e '' Ioo 0 1 := by rw [hγ.image e he]; exact hx
    obtain ⟨t, -, rfl⟩ := h'
    exact ⟨t, mem_univ _, rfl⟩
  have hUsub : Γ.U ⊆ K ∪ ({v} ∪ ⋃ i, J i) := by
    rw [Γ.U_eq]
    rintro x (hx | hx)
    · by_cases hxv : x = v
      · exact Or.inr (Or.inl (mem_singleton_iff.mpr hxv))
      · exact Or.inl (Or.inl ⟨hx, hxv⟩)
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      obtain ⟨t, -, rfl⟩ := hclosureE e he hxe
      by_cases htC : t ∈ C e
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨e, he, t, htC, rfl⟩))
      · right
        right
        simp only [C, mem_ofPred_eq, not_forall] at htC
        obtain ⟨y, hye, hcon⟩ := htC
        refine mem_iUnion.mpr ⟨y, ?_⟩
        subst hye
        have hy0 := (τ y).2.2
        cases hb : y.1.2
        · rw [hb] at hcon
          simp only [Bool.false_eq_true, ite_false, not_le] at hcon
          have ht0 := t.2.1
          refine ⟨⟨2 * t.1, by linarith, by linarith⟩, ⟨bot_le, ?_⟩, ?_⟩
          · change 2 * t.1 ≤ (τ y).1
            linarith
          · change γ y.1.1 (halfPar y.1.2 _) = _
            rw [hb]
            congr 1
            exact Subtype.ext (by simp [halfPar, halfT])
        · rw [hb] at hcon
          simp only [ite_true, not_le] at hcon
          have ht1 := t.2.2
          refine ⟨⟨2 * (1 - t.1), by linarith, by linarith⟩, ⟨bot_le, ?_⟩, ?_⟩
          · change 2 * (1 - t.1) ≤ (τ y).1
            linarith
          · change γ y.1.1 (halfPar y.1.2 _) = _
            rw [hb]
            congr 1
            exact Subtype.ext (by simp [halfPar, halfT])
  refine ⟨Kᶜ, hKclosed.isOpen_compl, hvK, ?_⟩
  intro x hx
  exact (hUsub hx.2).resolve_left hx.1

end GraphMinor.GM12
