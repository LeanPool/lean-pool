/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.FixedPairMaximalTashkinovTree
public import LeanPool.GoldbergSeymour.NormalGlobalMaximumTriple
public import LeanPool.GoldbergSeymour.ScheideMaximalExtendsEveryTree
public import LeanPool.GoldbergSeymour.ScheideReversedPathCertificate

/-!
# Scheide Maximum Extension Normal Witness

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideMaximumExtensionNormalWitness {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T)
    (hmax : FixedPairMaximalTashkinovTree G e0 phi T)
    (alpha beta : Fin k)
    (halpha : alpha ∈ MissingColors G phi
      (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
    (hbeta : beta ∈ MissingColors G phi
      (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩))
    (p : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
      (Sum.inl (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩)))
    (hp : p.IsPath)
    (C : ScheideReversedPathCertificate G k e0 phi T alpha beta p) :
    ∃ (T' : TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T'),
    TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
      N.alpha = alpha ∧ N.beta = beta ∧ N.height = p.length / 2 + 1 := by
  classical
  obtain ⟨T', hTashkinov, hvertexSet, hinitial⟩ :=
    ScheideMaximalExtendsEveryTree G k e0 phi T C.tree
      hglobal.1 hmax C.tashkinov
  obtain ⟨hlen, hvertex, hedge⟩ := hinitial
  have hglobal' : GlobalMaximumTriple G k e0 phi T' := by
    refine ⟨hglobal.1, hTashkinov, ?_⟩
    rw [hvertexSet]
    exact hglobal.2.2
  have hheightUpper : C.tree.length + 1 ≤ T'.length + 1 :=
    Nat.succ_le_succ hlen
  have hfirst :
      T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩ =
        T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ := by
    calc
      T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩ =
          C.tree.vertex ⟨0, Nat.zero_lt_succ C.tree.length⟩ := by
            simpa using hvertex ⟨0, Nat.zero_lt_succ C.tree.length⟩
      _ = T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ := C.first_vertex
  have hsecond :
      T'.vertex ⟨1, Nat.succ_lt_succ T'.positive⟩ =
        T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩ := by
    calc
      T'.vertex ⟨1, Nat.succ_lt_succ T'.positive⟩ =
          C.tree.vertex ⟨1, Nat.succ_lt_succ C.tree.positive⟩ := by
            simpa using hvertex ⟨1, Nat.succ_lt_succ C.tree.positive⟩
      _ = T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩ := C.second_vertex
  have hshape : ∀ n ≤ p.length,
      (n % 2 = 0 → ∃ v, p.getVert n = Sum.inl v) ∧
      (n % 2 = 1 → ∃ f, p.getVert n = Sum.inr f) := by
    intro n
    induction n with
    | zero =>
        intro hn
        constructor
        · intro _
          exact ⟨T.vertex ⟨0, Nat.zero_lt_succ T.length⟩, p.getVert_zero⟩
        · omega
    | succ n ih =>
        intro hn
        have hnlt : n < p.length := by omega
        have hadj := p.adj_getVert_succ hnlt
        have hold := ih (by omega)
        constructor
        · intro heven
          obtain ⟨f, hf⟩ := hold.2 (by omega)
          cases hnext : p.getVert (n + 1) with
          | inl v => exact ⟨v, rfl⟩
          | inr g =>
              rw [hf, hnext] at hadj
              simp [TwoColorIncidenceGraph] at hadj
        · intro hodd
          obtain ⟨v, hv⟩ := hold.1 (by omega)
          cases hnext : p.getVert (n + 1) with
          | inl w =>
              rw [hv, hnext] at hadj
              simp [TwoColorIncidenceGraph] at hadj
          | inr f => exact ⟨f, rfl⟩
  have hlengthEven : p.length % 2 = 0 := by
    by_contra hnot
    have hodd : p.length % 2 = 1 := by omega
    obtain ⟨f, hf⟩ := (hshape p.length (by rfl)).2 hodd
    rw [p.getVert_length] at hf
    simp at hf
  have hlength : p.length = 2 * (p.length / 2) := by omega
  have hpathData : ∃ q : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl (T'.vertex ⟨1, Nat.succ_lt_succ T'.positive⟩))
      (Sum.inl (T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩)),
      q.IsPath ∧ q.length = p.length ∧ q.support = p.support.reverse := by
    rw [hsecond, hfirst]
    exact ⟨p.reverse, hp.reverse, p.length_reverse, p.support_reverse⟩
  obtain ⟨q, hqPath, hqLength, hqSupport⟩ := hpathData
  let lastIndex : Fin (T'.length + 1) :=
    Fin.castLE hheightUpper (Fin.last C.tree.length)
  have hclosingEnds : G.ends C.closingEdge =
      s(T'.vertex lastIndex,
        T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩) := by
    dsimp only [lastIndex]
    rw [hvertex (Fin.last C.tree.length)]
    have hzero := hvertex ⟨0, Nat.zero_lt_succ C.tree.length⟩
    simpa using C.closing_ends.trans (congrArg
      (fun v => s(C.tree.vertex (Fin.last C.tree.length), v)) hzero.symm)
  refine ⟨T', {
    global := hglobal'
    height := C.tree.length + 1
    height_lower := le_trans C.length_lower (Nat.le_succ _)
    height_upper := hheightUpper
    alpha := alpha
    beta := beta
    alpha_missing := by simpa only [hfirst] using halpha
    beta_missing := by simpa only [hsecond] using hbeta
    closingEdge := C.closingEdge
    lastIndex := lastIndex
    lastIndex_height := by simp [lastIndex]
    closing_ends := hclosingEnds
    closingPath := q
    closingPath_isPath := hqPath
    closingPath_length := by
      rw [hqLength]
      calc
        p.length = 2 * (p.length / 2) := hlength
        _ = 2 * ((C.tree.length + 1) - 1) := by rw [C.length_eq]; omega
    closingPath_vertices := by
      intro v
      rw [hqSupport]
      simp only [List.mem_reverse]
      rw [C.path_vertices v]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, hi.trans (hvertex i).symm⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, hi.trans (hvertex i)⟩
    closingPath_edges := by
      intro f
      rw [hqSupport]
      simp only [List.mem_reverse]
      rw [C.path_edges f]
      constructor
      · rintro (rfl | ⟨j, hjpos, rfl⟩)
        · exact Or.inl rfl
        · right
          refine ⟨Fin.castLE hlen j, hjpos, ?_, ?_⟩
          · change j.val + 2 ≤ C.tree.length + 1
            omega
          · exact (hedge j).symm
      · rintro (rfl | ⟨j, hjpos, hjbound, rfl⟩)
        · exact Or.inl rfl
        · right
          let j' : Fin C.tree.length := ⟨j.val, by omega⟩
          have hjcast : Fin.castLE hlen j' = j := Fin.ext rfl
          refine ⟨j', hjpos, ?_⟩
          rw [← hedge j', hjcast]
    trunk_edge_ends := by
      intro j hjpos hjbound
      let j' : Fin C.tree.length := ⟨j.val, by omega⟩
      let i' : Fin (C.tree.length + 1) := ⟨j.val, by omega⟩
      have hjcast : Fin.castLE hlen j' = j := Fin.ext rfl
      have hicast : Fin.castLE hheightUpper i' =
          (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (T'.length + 1)) :=
        Fin.ext rfl
      have hsucccast : Fin.castLE hheightUpper j'.succ = j.succ :=
        Fin.ext rfl
      have hedgeEq : T'.edge j = C.tree.edge j' := by
        rw [← hjcast]
        exact hedge j'
      have hvertexEq :
          T'.vertex ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ =
            C.tree.vertex i' := by
        rw [← hicast]
        exact hvertex i'
      have hsuccEq : T'.vertex j.succ = C.tree.vertex j'.succ := by
        rw [← hsucccast]
        exact hvertex j'.succ
      rw [hedgeEq, hvertexEq, hsuccEq]
      exact C.trunk_edge_ends j' hjpos
  }, hvertexSet, rfl, rfl, ?_⟩
  change C.tree.length + 1 = p.length / 2 + 1
  rw [C.length_eq]

end GoldbergSeymour

end
