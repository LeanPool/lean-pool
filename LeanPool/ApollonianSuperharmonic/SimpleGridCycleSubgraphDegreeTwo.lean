/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import LeanPool.ApollonianSuperharmonic.SimpleGridCycle

-- [TABLET NODE: SimpleGridCycleSubgraphDegreeTwo]

/-!
# SimpleGridCycleSubgraphDegreeTwo

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem SimpleGridCycleSubgraphDegreeTwo
    (X W : Set GaussianInt) (E F : Set (Finset GaussianInt))
    (hcycle : SimpleGridCycle W F)
    (hX : X ⊆ W) (hE : E ⊆ F)
     :
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
      ({a.1, b.1} : Finset GaussianInt) ∈ E
    ∀ v : X, Set.ncard (G.neighborSet v) ≤ 2 := by
-- BODY
  classical
  dsimp only
  let C : SimpleGraph GaussianInt := SimpleGraph.fromRel fun a b =>
    ({a, b} : Finset GaussianInt) ∈ F
  let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
    ({a.1, b.1} : Finset GaussianInt) ∈ E
  change ∀ v : X, Set.ncard (G.neighborSet v) ≤ 2
  have pair_eq_iff_sym2 (a b r s : GaussianInt) :
      ({a, b} : Finset GaussianInt) = {r, s} ↔ s(a, b) = s(r, s) := by
    constructor
    · intro h
      have hs : ({a, b} : Set GaussianInt) = {r, s} := by
        ext t
        have ht := congrArg (fun e : Finset GaussianInt => t ∈ e) h
        apply Iff.of_eq
        simpa only [Finset.mem_insert, Finset.mem_singleton,
          Set.mem_insert_iff, Set.mem_singleton_iff] using ht
      rw [Set.pair_eq_pair_iff] at hs
      simpa [Sym2.eq] using hs
    · intro h
      simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
        Prod.swap_prod_mk] at h
      rcases h with h | h
      · simp [h.1, h.2]
      · simp [h.1, h.2, Finset.pair_comm]
  obtain ⟨p, x, y, hpNodup, hpLength, hpHead, hpLast, hW, hclose,
    hpAdj, hpEdges⟩ := hcycle
  have hpne : p ≠ [] := by intro h; simp [h] at hpLength
  have hxy : y ≠ x := by
    intro h
    subst y
    simp [FourNeighborAdjacent, Zsqrtd.ext_iff] at hclose
    omega
  have C_adj_iff (a b : GaussianInt) :
      C.Adj a b ↔ a ≠ b ∧ ({a, b} : Finset GaussianInt) ∈ F := by
    simp only [C, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne, hab | hba⟩
      · exact ⟨hne, hab⟩
      · exact ⟨hne, Finset.pair_comm b a ▸ hba⟩
    · rintro ⟨hne, hab⟩
      exact ⟨hne, Or.inl hab⟩
  have hpChain : List.IsChain C.Adj p := by
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    intro a b l₁ l₂ heq
    apply (C_adj_iff a b).mpr
    refine ⟨?_, ?_⟩
    · have hadj := hpAdj a b l₁ l₂ heq
      intro hab
      subst b
      simp [FourNeighborAdjacent, Zsqrtd.ext_iff] at hadj
      omega
    · exact (hpEdges {a, b}).mpr (Or.inr ⟨a, b, l₁, l₂, heq, rfl⟩)
  have hx : p.head hpne = x := by
    exact (List.head_eq_iff_head?_eq_some hpne).mpr hpHead
  have hy : p.getLast hpne = y := by
    exact (List.getLast_eq_iff_getLast?_eq_some hpne).mpr hpLast
  let q : C.Walk x y := (SimpleGraph.Walk.ofSupport p hpne hpChain).copy hx hy
  have hqSupport : q.support = p := by simp [q]
  have hqPath : q.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hqSupport]
    exact hpNodup
  have hcloseAdj : C.Adj y x :=
    (C_adj_iff y x).mpr ⟨hxy, (hpEdges {y, x}).mpr (Or.inl rfl)⟩
  have hcloseNotMem : s(y, x) ∉ q.edges := by
    intro hmem
    have hlen := hqPath.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ hmem)
    have hqLength : q.length = p.length - 1 := by simp [q]
    omega
  let d : C.Walk y y := q.cons hcloseAdj
  have hdCycle : d.IsCycle := by
    change (q.cons hcloseAdj).IsCycle
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    exact ⟨hqPath, hcloseNotMem⟩
  have hdEdges {a b : GaussianInt} (hab : a ≠ b) :
      (({a, b} : Finset GaussianInt) ∈ F ↔ d.toSubgraph.Adj a b) := by
    rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    simp only [d, SimpleGraph.Walk.edges_cons, List.mem_cons]
    rw [hpEdges]
    constructor
    · intro he
      rcases he with he | ⟨r, s, l₁, l₂, heq, hrs⟩
      · left
        exact (pair_eq_iff_sym2 a b y x).mp he
      · right
        rw [SimpleGraph.Walk.edges_eq_zipWith_support, hqSupport]
        have adjacent_mem_zip (l₁ l₂ : List GaussianInt)
            (r s : GaussianInt) : s(r, s) ∈
              List.zipWith (fun x y => s(x, y))
                (l₁ ++ r :: s :: l₂) (l₁ ++ r :: s :: l₂).tail := by
          induction l₁ with
          | nil => simp
          | cons t l ih =>
              cases l with
              | nil => simp
              | cons r' l =>
                  simp only [List.cons_append, List.tail_cons,
                    List.zipWith_cons_cons, List.mem_cons]
                  exact Or.inr ih
        have hm : s(r, s) ∈ List.zipWith (fun x y => s(x, y)) p p.tail := by
          rw [heq]
          exact adjacent_mem_zip l₁ l₂ r s
        have hsym : s(a, b) = s(r, s) :=
          (pair_eq_iff_sym2 a b r s).mp hrs
        exact hsym ▸ hm
    · intro he
      rcases he with he | he
      · left
        exact (pair_eq_iff_sym2 a b y x).mpr he
      · right
        rw [SimpleGraph.Walk.edges_eq_zipWith_support, hqSupport] at he
        rw [List.mem_iff_getElem] at he
        obtain ⟨i, hi, hieq⟩ := he
        have hi' : i + 1 < p.length := by
          simp [List.length_zipWith] at hi
          omega
        let l₁ := p.take i
        let l₂ := p.drop (i + 2)
        have hpdecomp : p = l₁ ++ p[i] :: p[i + 1] :: l₂ := by
          simp only [l₁, l₂]
          calc
            p = p.take i ++ p.drop i := (List.take_append_drop i p).symm
            _ = p.take i ++ p[i] :: p.drop (i + 1) := by
              rw [List.drop_eq_getElem_cons (by omega)]
            _ = p.take i ++ p[i] :: p[i + 1] :: p.drop (i + 2) := by
              rw [List.drop_eq_getElem_cons hi']
        refine ⟨p[i], p[i + 1], l₁, l₂, hpdecomp, ?_⟩
        have hieq' : s(p[i], p[i + 1]) = s(a, b) := by simpa using hieq
        exact (pair_eq_iff_sym2 a b p[i] p[i + 1]).mpr hieq'.symm
  intro v
  have hvSupport : v.1 ∈ d.support := by
    have hvp : v.1 ∈ p := by
      have hvW : v.1 ∈ W := hX v.2
      rw [hW] at hvW
      simpa using hvW
    simp only [d, SimpleGraph.Walk.support_cons, List.mem_cons]
    exact Or.inr (hqSupport.symm ▸ hvp)
  calc
    Set.ncard (G.neighborSet v) ≤
        Set.ncard (d.toSubgraph.neighborSet v.1) := by
      apply Set.ncard_le_ncard_of_injOn Subtype.val
        (ht := SimpleGraph.Walk.finite_neighborSet_toSubgraph d)
      · intro w hw
        have hG : G.Adj v w := hw
        have hvw : v.1 ≠ w.1 := by
          intro h
          apply hG.ne
          exact Subtype.ext h
        apply (hdEdges hvw).mp
        have hrel : ({v.1, w.1} : Finset GaussianInt) ∈ E := by
          simp only [G, SimpleGraph.fromRel_adj] at hG
          rcases hG.2 with hG | hG
          · exact hG
          · simpa [Finset.pair_comm] using hG
        exact hE hrel
      · exact Subtype.val_injective.injOn
    _ = 2 := hdCycle.ncard_neighborSet_toSubgraph_eq_two hvSupport

end ApollonianSuperharmonic

end
