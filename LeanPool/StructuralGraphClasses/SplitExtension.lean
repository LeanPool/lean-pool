/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.SplitObstructions
public import LeanPool.StructuralGraphClasses.ChordalBridge

/-!
# Reincorporating a simplicial vertex into a split partition

In a graph without an induced pair of disjoint edges, a split partition of
the graph minus a simplicial vertex extends to a split partition of the graph.
The extension may exchange one clique vertex with one independent vertex.
No finiteness hypothesis is needed for this local step.
-/

@[expose] public section

namespace SimpleGraph

universe u

variable {V : Type*} {G : SimpleGraph V}

/-- A clique whose complement is independent certifies split membership. -/
theorem isSplit_of_isClique_of_isIndepSet_compl {C : Set V}
    (hc : G.IsClique C) (hi : G.IsIndepSet Cᶜ) : G.IsSplit := by
  exact ⟨⟨C, Cᶜ, hc, hi, disjoint_compl_right, Set.union_compl_self C⟩⟩

/-- A split partition away from a simplicial vertex can be extended when `2K₂` is excluded. -/
theorem isSplit_of_simplicial_extension {C : Set V} {v : V}
    (hc : G.IsClique C) (hv : v ∉ C) (hi : G.IsIndepSet (Cᶜ \ {v}))
    (hs : G.IsSimplicial v)
    (hf : ¬((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).IsIndContained G) :
    G.IsSplit := by
  classical
  have htwo {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d)
      (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
      (hnac : ¬G.Adj a c) (hnad : ¬G.Adj a d)
      (hnbc : ¬G.Adj b c) (hnbd : ¬G.Adj b d) : False :=
    hf (twoK2_isIndContained_of_adj hab hcd hac had hbc hbd hnac hnad hnbc hnbd)
  by_cases hneighbor : ∃ i, i ∉ C ∧ G.Adj v i
  · obtain ⟨i, hiC, hvi⟩ := hneighbor
    have hiv : i ≠ v := hvi.ne.symm
    have hunique {j : V} (hjC : j ∉ C) (hjv : j ≠ v) (hji : j ≠ i) :
        ¬G.Adj v j := by
      intro hvj
      exact hi ⟨hiC, hiv⟩ ⟨hjC, hjv⟩ hji.symm (hs hvi hvj hji.symm)
    by_cases hall : ∀ a ∈ C, G.Adj i a
    · apply isSplit_of_isClique_of_isIndepSet_compl (C := insert i C)
      · exact isClique_insert.mpr ⟨hc, fun a ha _ => hall a ha⟩
      · intro x hx y hy hxy
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, not_or] at hx hy
        by_cases hxv : x = v
        · subst x
          exact hunique hy.2 hxy.symm hy.1
        by_cases hyv : y = v
        · subst y
          exact fun h => hunique hx.2 hxy hx.1 h.symm
        exact hi ⟨hx.2, hxv⟩ ⟨hy.2, hyv⟩ hxy
    · push Not at hall
      obtain ⟨a, haC, hnia⟩ := hall
      have hia : i ≠ a := fun h => hiC (h ▸ haC)
      have hva : v ≠ a := fun h => hv (h ▸ haC)
      have hnva : ¬G.Adj v a := fun h => hnia (hs hvi h hia)
      have hiall {b : V} (hbC : b ∈ C) (hba : b ≠ a) : G.Adj i b := by
        by_contra hnib
        have hvb : v ≠ b := fun h => hv (h ▸ hbC)
        have hib : i ≠ b := fun h => hiC (h ▸ hbC)
        have hnvb : ¬G.Adj v b := fun h => hnib (hs hvi h hib)
        exact htwo hvi (hc haC hbC hba.symm) hva hvb hia hib
          hnva hnvb hnia hnib
      have hano {j : V} (hjC : j ∉ C) (hjv : j ≠ v) (hji : j ≠ i) :
          ¬G.Adj a j := by
        intro haj
        have hajNe : a ≠ j := fun h => hjC (h ▸ haC)
        have hnij : ¬G.Adj i j := hi ⟨hiC, hiv⟩ ⟨hjC, hjv⟩ hji.symm
        exact htwo hvi haj hva hjv.symm hia hji.symm
          hnva (hunique hjC hjv hji) hnia hnij
      apply isSplit_of_isClique_of_isIndepSet_compl (C := insert i (C \ {a}))
      · apply isClique_insert.mpr
        refine ⟨hc.subset Set.sdiff_subset, ?_⟩
        intro b hb _
        exact hiall hb.1 hb.2
      · intro x hx y hy hxy
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_sdiff,
          Set.mem_singleton_iff, not_or, not_and_or, not_not] at hx hy
        have hcx : x ∉ C ∨ x = a := hx.2
        have hcy : y ∉ C ∨ y = a := hy.2
        rcases hcx with hxC | rfl <;> rcases hcy with hyC | rfl
        · by_cases hxv : x = v
          · subst x
            exact hunique hyC hxy.symm hy.1
          by_cases hyv : y = v
          · subst y
            exact fun h => hunique hxC hxy hx.1 h.symm
          exact hi ⟨hxC, hxv⟩ ⟨hyC, hyv⟩ hxy
        · by_cases hxv : x = v
          · subst x
            exact hnva
          exact fun h => hano hxC hxv hx.1 h.symm
        · by_cases hyv : y = v
          · subst y
            exact fun h => hnva h.symm
          exact hano hyC hyv hy.1
        · exact False.elim (hxy rfl)
  · apply isSplit_of_isClique_of_isIndepSet_compl hc
    intro x hx y hy hxy
    by_cases hxv : x = v
    · subst x
      exact fun h => hneighbor ⟨y, hy, h⟩
    by_cases hyv : y = v
    · subst y
      exact fun h => hneighbor ⟨x, hx, h.symm⟩
    exact hi ⟨hx, hxv⟩ ⟨hy, hyv⟩ hxy

/-- The local extension step applied to a split certificate on the deleted graph. -/
theorem isSplit_of_simplicial_delete {v : V} (hs : G.IsSimplicial v)
    (hf : ¬((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).IsIndContained G)
    (hd : (G.induce {x | x ≠ v}).IsSplit) : G.IsSplit := by
  obtain ⟨P⟩ := hd
  let C : Set V := Subtype.val '' P.clique
  have hc : G.IsClique C := G.isClique_induce_iff.mp P.isClique
  have hv : v ∉ C := by
    rintro ⟨x, _, hx⟩
    exact x.property hx
  apply isSplit_of_simplicial_extension hc hv _ hs hf
  intro x hx y hy hxy
  let x' : {x | x ≠ v} := ⟨x, hx.2⟩
  let y' : {x | x ≠ v} := ⟨y, hy.2⟩
  have hxc : x' ∉ P.clique := fun h => hx.1 ⟨x', h, rfl⟩
  have hyc : y' ∉ P.clique := fun h => hy.1 ⟨y', h, rfl⟩
  exact P.isIndepSet ((P.mem_clique_or_mem_independent x').resolve_left hxc)
    ((P.mem_clique_or_mem_independent y').resolve_left hyc)
    (fun h => hxy (congrArg Subtype.val h))

private theorem isSplit_of_chordal_of_card_le (n : ℕ) :
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ n →
      G.IsChordal →
      (¬((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).IsIndContained G) →
      G.IsSplit := by
  classical
  induction n with
  | zero =>
    intro V _ G hcard _ _
    let _ : IsEmpty V := Fintype.card_eq_zero_iff.mp (by omega)
    apply isSplit_of_isClique_of_isIndepSet_compl (C := ∅) isClique_empty
    intro x
    exact isEmptyElim x
  | succ n ih =>
    intro V _ G hcard hc hf
    by_cases hn : Nonempty V
    · let _ := hn
      obtain ⟨v, hv⟩ := hc.exists_isSimplicial
      let s : Set V := {x | x ≠ v}
      have hs : Fintype.card s ≤ n := by
        have : Fintype.card s < Fintype.card V :=
          Fintype.card_lt_of_injective_of_notMem (f := fun x : s => x.val) (b := v)
            Subtype.val_injective (by rintro ⟨x, hx⟩; exact x.property hx)
        omega
      have hf' :
          ¬((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).IsIndContained
            (G.induce s) := by
        intro h
        exact hf (h.trans ⟨Embedding.induce s⟩)
      exact isSplit_of_simplicial_delete hv hf (ih s (G.induce s) hs (hc.induce s) hf')
    · let _ : IsEmpty V := not_nonempty_iff.mp hn
      apply isSplit_of_isClique_of_isIndepSet_compl (C := ∅) isClique_empty
      intro x
      exact isEmptyElim x

/-- A finite chordal graph with no induced pair of disjoint edges is split. -/
theorem IsChordal.isSplit_of_not_twoK2_isIndContained [Finite V] (hc : G.IsChordal)
    (hf : ¬((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).IsIndContained G) :
    G.IsSplit := by
  classical
  let _ := Fintype.ofFinite V
  exact isSplit_of_chordal_of_card_le (Fintype.card V) V G le_rfl hc hf

/-- Finite split graphs are exactly chordal graphs without an induced pair of disjoint edges. -/
theorem isSplit_iff_isChordal_and_not_twoK2_isIndContained [Finite V] :
    G.IsSplit ↔ G.IsChordal ∧
      ¬((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).IsIndContained G :=
  ⟨fun h => ⟨h.isChordal, h.not_twoK2_isIndContained⟩,
    fun h => h.1.isSplit_of_not_twoK2_isIndContained h.2⟩

/-- Chordality pulls back along a native induced-containment certificate. -/
theorem IsChordal.of_isIndContained {W : Type*} {H : SimpleGraph W}
    (h : G.IsChordal) (hf : H.IsIndContained G) : H.IsChordal := by
  obtain ⟨f⟩ := hf
  have h' := h.comap f.toEmbedding
  change (G.comap f).IsChordal at h'
  rwa [f.comap_eq] at h'

/-- The complement of a disjoint pair of edges is not chordal. -/
theorem not_isChordal_compl_twoK2 :
    ¬((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2)))ᶜ.IsChordal := by
  intro h
  obtain ⟨v, hv⟩ := h.exists_isSimplicial
  rcases v with i | i
  · have hbad := hv (x := Sum.inr 0) (y := Sum.inr 1)
      (by simp [mem_neighborSet, compl_adj]) (by simp [mem_neighborSet, compl_adj])
      (by decide)
    simp [compl_adj] at hbad
  · have hbad := hv (x := Sum.inl 0) (y := Sum.inl 1)
      (by simp [mem_neighborSet, compl_adj]) (by simp [mem_neighborSet, compl_adj])
      (by decide)
    simp [compl_adj] at hbad

/-- A finite graph is split precisely when it and its complement are chordal. -/
theorem isSplit_iff_isChordal_and_compl [Finite V] :
    G.IsSplit ↔ G.IsChordal ∧ Gᶜ.IsChordal := by
  refine ⟨IsSplit.isChordal_and_compl, ?_⟩
  rintro ⟨hc, hcc⟩
  apply hc.isSplit_of_not_twoK2_isIndContained
  intro hf
  exact not_isChordal_compl_twoK2 (hcc.of_isIndContained hf.compl)

end SimpleGraph
