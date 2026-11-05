/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.TashTreeBadPair
public import LeanPool.GoldbergSeymour.TashTreeMinimumBadPair
public import LeanPool.GoldbergSeymour.TashTreePathIndex
public import LeanPool.GoldbergSeymour.TashTreeRankLess
public import LeanPool.GoldbergSeymour.TashTreeSuffixPath
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet

/-!
# Tash Tree Path Index Two Replacement

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hedgeOne_67.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
      (T : TreeSequence G e0) (hlen : (2 : ℕ) ≤ T.length),
    TashTreePathIndex G T = (2 : ℕ) →
    let z : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ)));
    TashTreeSuffixPath G T (2 : ℕ) →
    G.ends (T.edge (⟨(1 : ℕ), by omega⟩ : Fin T.length)) =
      s(T.vertex (⟨(2 : ℕ), by omega⟩ : Fin (T.length + (1 : ℕ))), T.vertex z) := by
  classical
  intro V E G e0 T hlen hq z hsuffix2
  rcases T.attaches ⟨1, by omega⟩ with ⟨i, hi⟩
  by_cases hi0 : i.val = 0
  · rw [hi]
    apply (Sym2.eq_iff).2
    left
    constructor
    · congr 1
    · congr 1
      apply Fin.ext
      simpa [z] using hi0
  · have hilimit : i.val < 2 := by simp
    have hi1 : i.val = 1 := by omega
    have hbadEdge :
        G.ends (T.edge ⟨1, by omega⟩) =
          s(T.vertex ⟨1, by omega⟩, T.vertex ⟨2, by omega⟩) := by
      rw [hi]
      apply (Sym2.eq_iff).2
      right
      constructor <;> congr 1; apply Fin.ext; simp [hi1]
    have hsuffix1 : TashTreeSuffixPath G T 1 := by
      refine ⟨by omega, by omega, ?_⟩
      intro j hj
      by_cases hj1 : j.val = 1
      · have hjeq : j = ⟨1, by omega⟩ := Fin.ext hj1
        rw [hjeq]
        exact hbadEdge
      · exact hsuffix2.2.2 j (by omega)
    have hle : TashTreePathIndex G T ≤ 1 := by
      unfold TashTreePathIndex
      exact Nat.find_min' _ hsuffix1
    omega

theorem TashTreePathIndexTwoReplacement {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hlen : 2 ≤ T.length) (hq : TashTreePathIndex G T = 2) :
    ∃ S : TreeSequence G e0,
    (∃ hST : S.length = T.length,
        (∀ r : Fin S.length, S.edge r = T.edge (Fin.cast hST r)) ∧
          S.vertex ⟨0, Nat.zero_lt_succ S.length⟩ = T.vertex ⟨1, by omega⟩ ∧
            S.vertex ⟨1, by omega⟩ = T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ ∧
              (∀ r : Fin (S.length + 1),
                2 ≤ r.val →
                  S.vertex r = T.vertex (Fin.cast (congrArg (fun n => n + 1) hST) r))) ∧
      TashTreeBadPair G k e0 phi S ∧ TashTreeRankLess G S T := by
  classical
  let z : Fin (T.length + 1) := ⟨0, by omega⟩
  let o : Fin (T.length + 1) := ⟨1, by omega⟩
  have hswapZ : Equiv.swap z o z = o := Equiv.swap_apply_left z o
  have hswapO : Equiv.swap z o o = z := Equiv.swap_apply_right z o
  have hswapLater (r : Fin (T.length + 1)) (hr : 2 ≤ r.val) :
      Equiv.swap z o r = r := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      have hz : r.val = 0 := by simpa [z] using congrArg Fin.val h
      omega
    · intro h
      have ho : r.val = 1 := by simpa [o] using congrArg Fin.val h
      omega
  have hspecT : TashTreeSuffixPath G T (TashTreePathIndex G T) := by
    unfold TashTreePathIndex
    exact Nat.find_spec _
  have hsuffix2 : TashTreeSuffixPath G T 2 := by
    simpa [hq] using hspecT
  have hedgeOne := @helper_hedgeOne_67 (@V) (@E) (@G) (@e0) (@T) (@hlen) (@hq) (@hsuffix2)
  let S : TreeSequence G e0 :=
    { length := T.length
      positive := T.positive
      vertex := fun r => T.vertex (Equiv.swap z o r)
      edge := T.edge
      vertex_injective := by
        intro a b hab
        exact (Equiv.swap z o).injective (T.vertex_injective hab)
      edge_injective := T.edge_injective
      first_edge := T.first_edge
      attaches := by
        intro j
        by_cases hj0 : j.val = 0
        · have hj : j = ⟨0, T.positive⟩ := Fin.ext hj0
          rw [hj]
          rcases T.attaches ⟨0, T.positive⟩ with ⟨i, hi⟩
          have hi0 : i = 0 := Fin.eq_zero i
          subst i
          refine ⟨0, ?_⟩
          rw [hi]
          apply (Sym2.eq_iff).2
          right
          constructor
          · change T.vertex ⟨1, by omega⟩ = T.vertex (Equiv.swap z o z)
            rw [hswapZ]
          · change T.vertex z = T.vertex (Equiv.swap z o o)
            rw [hswapO]
        · by_cases hj1 : j.val = 1
          · have hj : j = ⟨1, by omega⟩ := Fin.ext hj1
            rw [hj]
            refine ⟨⟨1, by omega⟩, ?_⟩
            rw [hedgeOne]
            apply (Sym2.eq_iff).2
            left
            constructor
            · congr 1
            · change T.vertex z = T.vertex (Equiv.swap z o o)
              rw [hswapO]
          · refine ⟨⟨j.val, by omega⟩, ?_⟩
            rw [hsuffix2.2.2 j (by omega)]
            apply (Sym2.eq_iff).2
            right
            constructor
            · congr 1
              rw [hswapLater]
              · apply Fin.ext; rfl
              change 2 ≤ j.val
              omega
            · congr 1
              rw [hswapLater]
              change 2 ≤ j.val + 1
              omega }
  have hlength : S.length = T.length := rfl
  have hedge (r : Fin S.length) : S.edge r = T.edge (Fin.cast hlength r) := rfl
  have hvertexZero :
      S.vertex ⟨0, Nat.zero_lt_succ S.length⟩ = T.vertex ⟨1, by omega⟩ := by
    change T.vertex (Equiv.swap z o z) = T.vertex o
    rw [hswapZ]
  have hvertexOne :
      S.vertex ⟨1, by omega⟩ = T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ := by
    change T.vertex (Equiv.swap z o o) = T.vertex z
    rw [hswapO]
  have hvertexLater (r : Fin (S.length + 1)) (hr : 2 ≤ r.val) :
      S.vertex r = T.vertex
        (Fin.cast (congrArg (fun n => n + 1) hlength) r) := by
    change T.vertex (Equiv.swap z o r) = T.vertex r
    rw [hswapLater r hr]
  have hTash : TashkinovTree G e0 phi S := by
    intro j hj
    rcases hmin.1.2.1 j hj with ⟨i, c, hcolor, hmissing⟩
    let old : Fin (T.length + 1) :=
      Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))
    let new : Fin (T.length + 1) := Equiv.swap z o old
    have hnewBound : new.val < j.val + 1 := by
      simp only [new, Equiv.swap_apply_def]
      split_ifs with hz ho
      · simp [o]
        omega
      · simp [z]
      · simp [old]
    let i' : Fin (j.val + 1) := ⟨new.val, hnewBound⟩
    refine ⟨i', c, ?_, ?_⟩
    · exact hcolor
    · have hv : S.vertex
          (Fin.castLT i' (Nat.lt_trans i'.isLt (Nat.succ_lt_succ j.isLt))) =
          T.vertex (Fin.castLT i
            (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))) := by
        have hcast :
            Fin.castLT i' (Nat.lt_trans i'.isLt (Nat.succ_lt_succ j.isLt)) = new := by
          apply Fin.ext
          rfl
        change T.vertex (Equiv.swap z o
            (Fin.castLT i' (Nat.lt_trans i'.isLt
              (Nat.succ_lt_succ j.isLt)))) = T.vertex old
        rw [hcast]
        apply congrArg T.vertex
        exact Equiv.swap_apply_self z o old
      rw [hv]
      exact hmissing
  have hvertexSet : TreeSequenceVertexSet S = TreeSequenceVertexSet T := by
    apply Finset.ext
    intro v
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨Equiv.swap z o r, rfl⟩
    · rintro ⟨r, rfl⟩
      refine ⟨Equiv.swap z o r, ?_⟩
      change T.vertex (Equiv.swap z o (Equiv.swap z o r)) = T.vertex r
      rw [Equiv.swap_apply_self]
  have hbadS : TashTreeBadPair G k e0 phi S := by
    refine ⟨hmin.1.1, hTash, ?_⟩
    simpa [hvertexSet] using hmin.1.2.2
  have hsuffixS : TashTreeSuffixPath G S 1 := by
    refine ⟨by omega, by simpa [S] using T.positive, ?_⟩
    intro j hj
    by_cases hj1 : j.val = 1
    · change G.ends (T.edge j) =
        s(T.vertex (Equiv.swap z o j.castSucc),
          T.vertex (Equiv.swap z o j.succ))
      have hjeq : j = ⟨1, by omega⟩ := Fin.ext hj1
      rw [hjeq, hedgeOne]
      apply (Sym2.eq_iff).2
      right
      constructor
      · congr 1
      · congr 1
    · have hj2 : 2 ≤ j.val := by omega
      change G.ends (T.edge j) =
        s(T.vertex (Equiv.swap z o j.castSucc),
          T.vertex (Equiv.swap z o j.succ))
      rw [hsuffix2.2.2 j hj2]
      congr 1
      · congr 1
        rw [hswapLater]
        change 2 ≤ j.val
        omega
      · congr 1
        rw [hswapLater]
        change 2 ≤ j.val + 1
        omega
  have hindexSLe : TashTreePathIndex G S ≤ 1 := by
    unfold TashTreePathIndex
    exact Nat.find_min' _ hsuffixS
  have hspecS : TashTreeSuffixPath G S (TashTreePathIndex G S) := by
    unfold TashTreePathIndex
    exact Nat.find_spec _
  have hindexS : TashTreePathIndex G S = 1 :=
    Nat.le_antisymm hindexSLe hspecS.1
  refine ⟨S, ⟨hlength, hedge, hvertexZero, hvertexOne, hvertexLater⟩,
    hbadS, ?_⟩
  left
  rw [hindexS, hq]
  omega

end GoldbergSeymour

end
