/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.DoubleCount

/-!
# Cancellation configurations for Dross's K₄ transfers

A configuration records a triangle, one of its non-root edges, and a K₄
partner. Swapping the two transfer edges preserves these configurations.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Configurations contributing to the off-root K₄-transfer sum. -/
@[expose] public def cancellationConfigs (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) : Finset (Finset V × Sym2 V × Sym2 V) :=
  ((G.cliqueFinset 3) ×ˢ (Finset.univ : Finset (Sym2 V)) ×ˢ
    (Finset.univ : Finset (Sym2 V))).filter
    (fun p => e ∈ triEdges p.1 ∧ p.2.1 ∈ (triEdges p.1).erase e ∧
      K4pair G p.2.1 p.2.2 ∧
      ∃ v, v ∈ p.1 ∧ v ∈ p.2.2 ∧ v ∉ p.2.1)

/-- Interchanging the transfer edges gives another valid configuration. -/
public theorem cancellationConfigs_swap_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (p : Finset V × Sym2 V × Sym2 V)
    (hp : p ∈ cancellationConfigs G e) :
    ((e.toFinset ∪ p.2.2.toFinset, p.2.2, p.2.1) :
      Finset V × Sym2 V × Sym2 V) ∈ cancellationConfigs G e := by
  simp only [cancellationConfigs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    and_true] at hp ⊢
  obtain ⟨htc, hetri, herase, hk, u, huT, huY, huX⟩ := hp
  have hk' : K4pair G p.2.2 p.2.1 := (k4pair_symm G p.2.1 p.2.2).mp hk
  have hkey := tri_eq_edge_union G htc hetri herase
  let X := p.2.1.toFinset
  let Y := p.2.2.toFinset
  let E := e.toFinset
  let T := p.1
  let N := E ∪ Y
  have hT3 : T.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp htc).card_eq
  have heND : ¬ e.IsDiag := by
    rw [triEdges, Finset.mem_filter] at hetri
    exact hetri.2
  have hE2 : E.card = 2 := by
    induction e using Sym2.inductionOn with | _ a b =>
      rw [Sym2.mk_isDiag_iff] at heND
      simp [E, Sym2.toFinset_mk_eq, heND]
  obtain ⟨a, b, c, d, hx, hy, hcard4, hclq⟩ := hk
  have hpw := card4_pairwise hcard4
  have hX : X = {a, b} := by
    simp [X, hx, Sym2.toFinset_mk_eq]
  have hY : Y = {c, d} := by
    simp [Y, hy, Sym2.toFinset_mk_eq]
  have hX2 : X.card = 2 := by simp [hX, hpw.1]
  have hY2 : Y.card = 2 := by simp [hY, hpw.2.2.2.2.2]
  have hdisj : Disjoint X Y := by
    rw [Finset.disjoint_left]
    rw [hX, hY]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    grind
  have hXY : X ∪ Y = {a, b, c, d} := by
    ext z
    simp only [hX, hY, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hTX : X ⊆ T := by
    change p.2.1.toFinset ⊆ p.1
    rw [← hkey]
    exact Finset.subset_union_right
  have huE : u ∈ E := by
    have : u ∈ E ∪ X := by simpa [E, X, T, hkey] using huT
    exact (Finset.mem_union.mp this).resolve_right (by simpa [X] using huX)
  have hTE : E ⊆ T := by
    change e.toFinset ⊆ p.1
    rw [← hkey]
    exact Finset.subset_union_left
  have hTuX : T = insert u X := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      by_cases hzx : z ∈ X
      · simp [hzx]
      · have hcardXz : (insert z X).card = 3 := by simp [hzx, hX2]
        have hsub : insert z X ⊆ T := by
          intro q hq
          simp only [Finset.mem_insert] at hq
          rcases hq with rfl | hq
          · exact hz
          · exact hTX hq
        have heq : insert z X = T := Finset.eq_of_subset_of_card_le hsub (by omega)
        have huins : u ∈ insert z X := by rw [heq]; exact huT
        rcases Finset.mem_insert.mp huins with huz | huX'
        · simp [huz]
        · have huXnot : u ∉ X := by simpa [X] using huX
          exact False.elim (huXnot huX')
    · have huX' : u ∉ X := by simpa [X] using huX
      rw [Finset.card_insert_of_notMem huX', hX2, hT3]
  have hTXY : T ⊆ X ∪ Y := by
    rw [hTuX]
    intro z hz
    simp only [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact Finset.mem_union_right X (by simpa [Y] using huY)
    · exact Finset.mem_union_left Y hz
  have hEYinter : E ∩ Y = {u} := by
    ext z
    constructor
    · intro hz
      have hzE := (Finset.mem_inter.mp hz).1
      have hzY := (Finset.mem_inter.mp hz).2
      have hzT : z ∈ T := hTE hzE
      rw [hTuX] at hzT
      rcases Finset.mem_insert.mp hzT with rfl | hzX
      · simp
      · exact False.elim ((Finset.disjoint_left.mp hdisj) hzX hzY)
    · intro hz
      have : z = u := by simpa using hz
      subst z
      exact Finset.mem_inter.mpr ⟨huE, by simpa [Y] using huY⟩
  have hN3 : N.card = 3 := by
    have hun := Finset.card_union_add_card_inter E Y
    have hinter : (E ∩ Y).card = 1 := by simp [hEYinter]
    simp only [N]
    omega
  have hNsub : N ⊆ ({a, b, c, d} : Finset V) := by
    rw [← hXY]
    exact Finset.union_subset (hTE.trans hTXY) (Finset.subset_union_right)
  have hNc : N ∈ G.cliqueFinset 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff]
    refine ⟨hclq.1.subset ?_, hN3⟩
    intro z hz
    exact hNsub hz
  have heN : e ∈ triEdges N := by
    rw [triEdges, Finset.mem_filter]
    refine ⟨?_, heND⟩
    rw [Finset.mem_sym2_iff]
    intro z hz
    exact Finset.mem_union_left Y (by simpa [E] using (Sym2.mem_toFinset.mpr hz))
  have hyND : ¬ p.2.2.IsDiag := by
    rw [hy, Sym2.mk_isDiag_iff]
    exact hpw.2.2.2.2.2
  have hyN : p.2.2 ∈ triEdges N := by
    rw [triEdges, Finset.mem_filter]
    refine ⟨?_, hyND⟩
    rw [Finset.mem_sym2_iff]
    intro z hz
    exact Finset.mem_union_right E (by simpa [Y] using (Sym2.mem_toFinset.mpr hz))
  have hene : e ≠ p.2.2 := by
    intro heq
    have hEY : E = Y := by simp [E, Y, heq]
    have : N.card = 2 := by simp [N, hEY, hY2]
    omega
  have hyErase : p.2.2 ∈ (triEdges N).erase e := Finset.mem_erase.mpr ⟨hene.symm, hyN⟩
  have hex : ∃ z, z ∈ E ∧ z ∉ Y := by
    by_contra hn
    push Not at hn
    have hsub : E ⊆ Y := hn
    have hle := Finset.card_le_card hsub
    have heq : E = Y := Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [heq] at hEYinter
    have : Y.card = 1 := by
      calc
        Y.card = (Y ∩ Y).card := by simp
        _ = ({u} : Finset V).card := congrArg Finset.card hEYinter
        _ = 1 := by simp
    omega
  obtain ⟨v, hvE, hvY⟩ := hex
  have hvT : v ∈ T := hTE hvE
  have hvX : v ∈ X := by
    rw [hTuX] at hvT
    rcases Finset.mem_insert.mp hvT with rfl | hvX
    · exact False.elim (hvY (by simpa [Y] using huY))
    · exact hvX
  refine ⟨by simpa [N, E, Y] using hNc, by simpa [N] using heN,
    by simpa [N] using hyErase, hk', v, ?_, ?_, ?_⟩
  · exact Finset.mem_union_left Y hvE
  · simpa [X] using (Sym2.mem_toFinset.mp hvX)
  · simpa [Y, Sym2.mem_toFinset] using hvY

end LeanPool.DrossFractionalTriangleDecomposition
