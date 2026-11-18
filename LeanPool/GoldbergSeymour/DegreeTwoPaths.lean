/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Paths in graphs of maximum degree two

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Paths starting at degree at most one have no chords in a graph of degree at most two. -/
theorem degreeTwoPathAdjacentIndices {W : Type*} [Finite W]
    {H : SimpleGraph W} {a b : W} (p : H.Walk a b) (hpath : p.IsPath)
    (degreeBound : ∀ v, @SimpleGraph.degree W H v (Fintype.ofFinite _) ≤ 2)
    (startDegree : @SimpleGraph.degree W H a (Fintype.ofFinite _) ≤ 1)
    (n m : ℕ) (hn : n ≤ p.length) (hm : m ≤ p.length) (hnm : n < m)
    (hadj : H.Adj (p.getVert n) (p.getVert m)) : m = n + 1 := by
  classical
  let _ := Fintype.ofFinite W
  by_contra hne
  have hgap : n + 1 < m := by omega
  by_cases hn0 : n = 0
  · subst n
    have hfirstAdj := p.adj_getVert_succ (by omega : 0 < p.length)
    have hdeg := startDegree
    have hstart : p.getVert 0 = a := by simp
    have hneigh : p.getVert 1 ≠ p.getVert m := by
      intro heq
      have h1m : 1 ≤ m := by omega
      have := hpath.getVert_injOn (h1m.trans hm) hm heq
      omega
    have htwo : 2 ≤ (@SimpleGraph.neighborFinset W H (a)
        (Fintype.ofFinite _)).card := by
      have hs : ({p.getVert 1, p.getVert m} : Finset W) ⊆
          @SimpleGraph.neighborFinset W H (a)
            (Fintype.ofFinite _) := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · simpa [SimpleGraph.mem_neighborFinset, hstart] using hfirstAdj
        · simpa [SimpleGraph.mem_neighborFinset, hstart] using hadj
      have hc : ({p.getVert 1, p.getVert m} : Finset W).card = 2 := by
        simp [hneigh]
      rw [← hc]
      exact Finset.card_le_card hs
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
    have : 2 ≤ 1 := htwo.trans hdeg
    omega
  · have hnlt : n < p.length := by omega
    have hleft : H.Adj (p.getVert n) (p.getVert (n - 1)) := by
      have h := p.adj_getVert_succ (i := n - 1) (by omega)
      have heq : n - 1 + 1 = n := by omega
      simpa [ heq] using h.symm
    have hright : H.Adj (p.getVert n) (p.getVert (n + 1)) := by
      exact p.adj_getVert_succ hnlt
    have hnm1 : p.getVert (n - 1) ≠ p.getVert (n + 1) := by
      intro heq
      have := hpath.getVert_injOn (Nat.sub_le n 1 |>.trans hn)
        (Nat.succ_le_of_lt hnlt) heq
      omega
    have hnm2 : p.getVert (n - 1) ≠ p.getVert m := by
      intro heq
      have := hpath.getVert_injOn (Nat.sub_le n 1 |>.trans hn) hm heq
      omega
    have hnm3 : p.getVert (n + 1) ≠ p.getVert m := by
      intro heq
      have := hpath.getVert_injOn (Nat.succ_le_of_lt hnlt) hm heq
      omega
    have hthree : 3 ≤ (@SimpleGraph.neighborFinset W H (p.getVert n)
        (Fintype.ofFinite _)).card := by
      let S : Finset W :=
        {p.getVert (n - 1), p.getVert (n + 1), p.getVert m}
      have hs : S ⊆ @SimpleGraph.neighborFinset W H (p.getVert n)
          (Fintype.ofFinite _) := by
        intro q hq
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · simpa [SimpleGraph.mem_neighborFinset] using hleft
        · simpa [SimpleGraph.mem_neighborFinset] using hright
        · simpa [SimpleGraph.mem_neighborFinset] using hadj
      have hc : S.card = 3 := by
        simp [S, hnm1, hnm2, hnm3]
      rw [← hc]
      exact Finset.card_le_card hs
    have hdeg := degreeBound (p.getVert n)
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
    have : 3 ≤ 2 := hthree.trans hdeg
    omega

/-- An unchanged simple path with unique endpoint neighbors is closed in a degree-two graph. -/
theorem degreeTwoPathSupportClosed {W : Type*} [Finite W]
    {source target : SimpleGraph W} {a b : W} (p : source.Walk a b) (hpath : p.IsPath)
    (degreeBound : ∀ v, @SimpleGraph.degree W target v (Fintype.ofFinite _) ≤ 2)
    (adjacent : ∀ i < p.length, target.Adj (p.getVert i) (p.getVert (i + 1)))
    (startUnique : ∀ z, target.Adj a z → z = p.getVert 1)
    (endUnique : ∀ z, target.Adj b z → z = p.getVert (p.length - 1))
    (w : W) (hw : w ∈ p.support) (z : W) (hwz : target.Adj w z) : z ∈ p.support := by
  classical
  let _ := Fintype.ofFinite W
  obtain ⟨n, hn, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
  by_cases hn0 : n = 0
  · subst n
    have hwstart : w = a := by simpa using hn.symm
    have hz := startUnique z (by simpa [hwstart] using hwz)
    simp [hz]
  by_cases hnend : n = p.length
  · have hwend : w = b := by
      rw [← hn, hpath.getVert_eq_end_iff hnle]
      exact hnend
    have hz := endUnique z (by simpa [hwend] using hwz)
    simp [hz]
  have hleft : target.Adj (p.getVert n)
      (p.getVert (n - 1)) := by
    rw [← show n - 1 + 1 = n by omega]
    exact (adjacent (n - 1) (by omega)).symm
  have hright : target.Adj (p.getVert n)
      (p.getVert (n + 1)) :=
    adjacent n (by omega)
  by_contra hznot
  have hwz' := hwz
  rw [← hn] at hwz'
  have hneleft : p.getVert (n - 1) ≠ z := by
    intro he
    apply hznot
    rw [← he]
    exact p.getVert_mem_support _
  have hneright : p.getVert (n + 1) ≠ z := by
    intro he
    apply hznot
    rw [← he]
    exact p.getVert_mem_support _
  have hnelr : p.getVert (n - 1) ≠
      p.getVert (n + 1) := by
    intro he
    have hindex := hpath.getVert_injOn
      (show n - 1 ≤ p.length by omega)
      (show n + 1 ≤ p.length by omega) he
    omega
  let : Fintype (target.neighborSet (p.getVert n)) :=
    Fintype.ofFinite _
  have hthree : 3 ≤ target.degree (p.getVert n) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    let s : Finset W :=
      {z, p.getVert (n - 1), p.getVert (n + 1)}
    have hs : s ⊆ target.neighborFinset (p.getVert n) := by
      intro t ht
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · simpa [SimpleGraph.mem_neighborFinset] using hwz'
      · simpa [SimpleGraph.mem_neighborFinset] using hleft
      · simpa [SimpleGraph.mem_neighborFinset] using hright
    have hcard : 3 ≤ s.card := by
      simp [s, hnelr, hneleft.symm,
        hneright.symm]
    exact hcard.trans (Finset.card_le_card hs)
  have hupper := degreeBound (p.getVert n)
  omega

end GoldbergSeymour

end
