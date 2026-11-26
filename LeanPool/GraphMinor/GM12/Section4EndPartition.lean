/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM12.Section3Punctured
import LeanPool.GraphMinor.Surface.DiscGrow
import Mathlib.Data.Set.Card

/-!
# Partitioning the selected edge ends

In XII (4.3), page 250, direct the target graph's edges and
assign each selected end to the corresponding target vertex.
The resulting classes partition the selected ends. Distinct
selected ends are distinct points because their discs are disjoint
and each edge has distinct ends. The total boundary set has size
at most twice the number of discs.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Surface

/-- The class `Z_v` of XII (4.3), page 250: the selected ends
assigned to the target vertex `v` by the edge orientation. -/
def edgeEndClass {ι κ S : Type*} (ends : ι → S) (vertexOfEnd : ι → κ) (v : κ) : Set S :=
  ends '' {i | vertexOfEnd i = v}

/-- The oriented end classes cover exactly the selected ends. -/
theorem iUnion_edgeEndClass {ι κ S : Type*} (ends : ι → S) (vertexOfEnd : ι → κ) :
    ⋃ v, edgeEndClass ends vertexOfEnd v = range ends := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, i, _, rfl⟩ := mem_iUnion.mp hx
    exact mem_range_self i
  · rintro ⟨i, rfl⟩
    exact mem_iUnion.mpr ⟨vertexOfEnd i, i, rfl, rfl⟩

/-- Distinct oriented end classes are disjoint when all selected
ends are distinct points. -/
theorem disjoint_edgeEndClass {ι κ S : Type*} (ends : ι → S) (vertexOfEnd : ι → κ)
    (hinj : Function.Injective ends) {u v : κ} (huv : u ≠ v) :
    Disjoint (edgeEndClass ends vertexOfEnd u) (edgeEndClass ends vertexOfEnd v) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨i, hi, hix⟩ ⟨j, hj, hjx⟩
  have hij : i = j := hinj (hix.trans hjx.symm)
  subst j
  exact huv (hi.symm.trans hj)

/-- Endpoints on pairwise disjoint discs give an injective list
of selected ends, as used in XII (4.3), page 250. -/
theorem edge_ends_injective_of_disjoint_discs
    {S ι : Type*} (a b : ι → S) (Δ : ι → Set S)
    (hab : ∀ i, a i ≠ b i) (ha : ∀ i, a i ∈ Δ i) (hb : ∀ i, b i ∈ Δ i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)) :
    Function.Injective (fun q : ι × Bool => if q.2 then a q.1 else b q.1) := by
  intro ⟨i, c⟩ ⟨j, d⟩ heq
  have hij : i = j := by
    by_contra hne
    have hmem₁ : (if c then a i else b i) ∈ Δ i := by cases c <;> simp [ha, hb]
    have hmem₂ : (if d then a j else b j) ∈ Δ j := by cases d <;> simp [ha, hb]
    change (if c then a i else b i) = (if d then a j else b j) at heq
    exact Set.disjoint_left.mp (hdisj i j hne) hmem₁ (heq.symm ▸ hmem₂)
  subst j
  congr 1
  cases c <;> cases d
  · rfl
  · exact False.elim ((hab i).symm heq)
  · exact False.elim (hab i heq)
  · rfl

/-- The boundary set of `t` empty two-end discs has size at most
`2t`, the parameter `z` used in XII (4.3), page 249. -/
theorem discBoundaryVertices_ncard_le_twice
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {t : ℕ}
    (Δ : Fin t → Set S) (a b : Fin t → S)
    (hbd : ∀ i, Γ.V ∩ discBd (Δ i) = {a i, b i}) :
    (discBoundaryVertices Γ Δ).ncard ≤ 2 * t := by
  let ends : Fin t × Bool → S := fun q => if q.2 then a q.1 else b q.1
  have hsub : discBoundaryVertices Γ Δ ⊆ ends '' univ := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [hbd i] at hi
    rcases hi with rfl | hi
    · exact ⟨(i, true), mem_univ _, rfl⟩
    · exact ⟨(i, false), mem_univ _, Set.mem_singleton_iff.mp hi |>.symm⟩
  have hcard := (ncard_le_ncard hsub (toFinite _)).trans (ncard_image_le (toFinite univ))
  simpa only [ncard_univ, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, Nat.mul_comm t 2] using hcard

/-- For empty two-end discs, the boundary set is the range of
the selected end labels. -/
theorem discBoundaryVertices_eq_range_ends
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {t : ℕ}
    (Δ : Fin t → Set S) (a b : Fin t → S)
    (hbd : ∀ i, Γ.V ∩ discBd (Δ i) = {a i, b i}) :
    discBoundaryVertices Γ Δ =
      range (fun q : Fin t × Bool => if q.2 then a q.1 else b q.1) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [hbd i] at hi
    rcases hi with rfl | hi
    · exact ⟨(i, true), rfl⟩
    · exact ⟨(i, false), (Set.mem_singleton_iff.mp hi).symm⟩
  · rintro ⟨⟨i, c⟩, rfl⟩
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [hbd i]
    cases c <;> simp

/-- Reindexing the ends and target vertices preserves their contact
classes, as used to label the source discs of XII (4.3), claim (7). -/
theorem edgeEndClass_reindex
    {ι ι' κ κ' S : Type*} (ε : ι ≃ ι') (ν : κ ≃ κ')
    (ends : ι' → S) (owner : ι' → κ') (owner' : ι → κ)
    (howner : ∀ i, owner (ε i) = ν (owner' i)) (v : κ) :
    edgeEndClass ends owner (ν v) = edgeEndClass (ends ∘ ε) owner' v := by
  ext x
  constructor
  · rintro ⟨i, hi, hix⟩
    refine ⟨ε.symm i, ?_, ?_⟩
    · apply ν.injective
      have h := howner (ε.symm i)
      rw [ε.apply_symm_apply] at h
      exact h.symm.trans hi
    · simpa only [Function.comp_apply, ε.apply_symm_apply] using hix
  · rintro ⟨i, hi, hix⟩
    exact ⟨ε i, (howner i).trans (congrArg ν hi), hix⟩

end GraphMinor.GM12
