/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.Section9HPathCuts
import LeanPool.GraphMinor.GM16.Section9PairCount
import LeanPool.GraphMinor.GM09.Basic

/-!
# The global boundary separator in XVI (8.1)

Claim (5), page 72, combines one Menger separator for every pair of
boundary sets. Either one pair has the required disjoint paths, or
the union of the separators meets all such paths and has the stated
size. Only unordered pairs contribute to the union.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM14
universe u v

/-- The Menger and union argument of XVI (8.1), Claim (5), page 72,
before Claim (4) turns its linkage alternative into a handle span.
Menger gives cuts of size less than `φ²`; the unordered-pair count
still gives precisely the printed global bound. -/
theorem boundary_linkages_or_global_separator {α : Type u} {β : Type v}
    (G H : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) (hHG : H ≤ G)
    (δ φ : ℕ) (X : Fin δ → Set α) (hX : ∀ i, X i ⊆ V(H))
    (hDis : Pairwise (fun i j => Disjoint (X i) (X j))) :
    (∃ i j : Fin δ, i < j ∧ ∃ P : Fin (φ ^ 2) → Graph α β,
      (∀ k, ∃ a ∈ X i, ∃ b ∈ X j, IsHPathWithEnds G H (P k) a b) ∧
      Pairwise (fun k l => Disjoint V(P k) V(P l))) ∨
    (∃ Z ⊆ V(G), Z.ncard < δ ^ 2 * φ ^ 2 / 2 + 1 ∧
      Z ∩ V(H) ⊆ ⋃ i, X i ∧
      ∀ i j : Fin δ, i ≠ j → ∀ P a b,
        IsHPathWithEnds G H P a b → a ∈ X i → b ∈ X j → (V(P) ∩ Z).Nonempty) := by
  classical
  by_cases hPack : ∃ i j : Fin δ, i < j ∧ ∃ P : Fin (φ ^ 2) → Graph α β,
      (∀ k, ∃ a ∈ X i, ∃ b ∈ X j, IsHPathWithEnds G H (P k) a b) ∧
      Pairwise (fun k l => Disjoint V(P k) V(P l))
  · exact Or.inl hPack
  have hex : ∀ i j : Fin δ, ∃ Z : Finset α,
      (↑Z : Set α) ⊆ V(G) ∧ Z.card ≤ φ ^ 2 ∧ (↑Z : Set α) ∩ V(H) ⊆ X i ∪ X j ∧
      (i < j → ∀ P a b, IsHPathWithEnds G H P a b → a ∈ X i → b ∈ X j →
        (V(P) ∩ (↑Z : Set α)).Nonempty) := by
    intro i j
    by_cases hij : i < j
    · rcases disjoint_hPaths_or_boundary_separator G H hV hE hHG (X i) (X j) (hX i) (hX j)
        (hDis (ne_of_lt hij)) (φ ^ 2) with hPaths | ⟨Z, hZG, hZcard, hZH, hCut⟩
      · exact False.elim (hPack ⟨i, j, hij, hPaths⟩)
      · have hfin := hV.subset hZG
        refine ⟨hfin.toFinset, ?_, ?_, ?_, fun _ => ?_⟩
        · simpa only [hfin.coe_toFinset] using hZG
        · rw [← Set.ncard_eq_toFinset_card _ hfin]
          exact le_of_lt hZcard
        · simpa only [hfin.coe_toFinset] using hZH
        · simpa only [hfin.coe_toFinset] using hCut
    · refine ⟨∅, ?_, ?_, ?_, fun h => False.elim (hij h)⟩
      · simp
      · simp
      · simp
  choose cuts hcutsG hcutsCard hcutsH hcutsHit using hex
  let pairs : Finset (Fin δ × Fin δ) :=
    (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 < p.2)
  let Zf := pairs.biUnion (fun p => cuts p.1 p.2)
  have hmem : ∀ i j : Fin δ, i < j → (↑(cuts i j) : Set α) ⊆ ↑Zf := by
    intro i j hij x hx
    exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hij⟩, hx⟩
  have hZG : (↑Zf : Set α) ⊆ V(G) := by
    intro x hx
    obtain ⟨p, _, hxp⟩ := Finset.mem_biUnion.mp hx
    exact hcutsG p.1 p.2 hxp
  have hZcard : (↑Zf : Set α).ncard < δ ^ 2 * φ ^ 2 / 2 + 1 := by
    rw [Set.ncard_coe_finset]
    have hb := pair_separator_union_bound (Finset.univ : Finset (Fin δ)) φ cuts
      (fun i _ j _ _ => hcutsCard i j)
    simpa only [Finset.card_univ, Fintype.card_fin] using hb
  refine Or.inr ⟨↑Zf, hZG, hZcard, ?_, ?_⟩
  · rintro x ⟨hxZ, hxH⟩
    obtain ⟨p, _, hxp⟩ := Finset.mem_biUnion.mp hxZ
    rcases hcutsH p.1 p.2 ⟨hxp, hxH⟩ with hi | hj
    · exact mem_iUnion.mpr ⟨p.1, hi⟩
    · exact mem_iUnion.mpr ⟨p.2, hj⟩
  · intro i j hij P a b hP ha hb
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · obtain ⟨x, hxP, hxCut⟩ := hcutsHit i j hlt P a b hP ha hb
      exact ⟨x, hxP, hmem i j hlt hxCut⟩
    · have hP' : IsHPathWithEnds G H P b a :=
        ⟨hP.1, hP.2.1.symm, Ne.symm hP.2.2.1, hP.2.2.2.2.1, hP.2.2.2.1,
          hP.2.2.2.2.2.1.trans (by ext x; simp only [mem_insert_iff, mem_singleton_iff]; exact
            or_comm),
          hP.2.2.2.2.2.2⟩
      obtain ⟨x, hxP, hxCut⟩ := hcutsHit j i hgt P b a hP' hb ha
      exact ⟨x, hxP, hmem j i hgt hxCut⟩

end GraphMinor.GM16
