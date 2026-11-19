/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import LeanPool.GoldbergSeymour.BoundaryEdges
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Confinement of two-color incidence walks

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A two-color walk cannot leave a set before an index when every earlier departure is excluded. -/
theorem TwoColorWalk.confinedBefore {V E : Type*}
    {G : LooplessMultigraph V E} {k : ℕ} {phi : PartialEdgeColoring E k}
    {alpha beta : Fin k} {root terminal : V}
    (path : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl root) (Sum.inl terminal))
    (region : Finset V) (lastIndex : ℕ) (lastBound : lastIndex ≤ path.length)
    (rootMember : root ∈ region)
    (hnoDeparture : ∀ (n : ℕ) (y x : V) (e : E), n + 2 ≤ lastIndex →
      path.getVert n = Sum.inl y → y ∈ region → path.getVert (n + 1) = Sum.inr e →
      path.getVert (n + 2) = Sum.inl x → x ∉ region → False) :
    ∀ n ≤ lastIndex, ∀ x : V, path.getVert n = Sum.inl x → x ∈ region := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn x hx
      by_cases hn0 : n = 0
      · subst n
        rw [path.getVert_zero] at hx
        injection hx with hxe
        subst x
        exact rootMember
      by_cases hn1 : n = 1
      · have ha := path.adj_getVert_succ (i := 0) (by
          have h := lastBound
          omega)
        subst n
        rw [path.getVert_zero, hx] at ha
        simp [TwoColorIncidenceGraph] at ha
      · have hprev := path.adj_getVert_succ (i := n - 1) (by
          have h := lastBound
          omega)
        rw [show n - 1 + 1 = n by omega, hx] at hprev
        cases hmid : path.getVert (n - 1) with
        | inl z =>
            rw [hmid] at hprev
            simp [TwoColorIncidenceGraph] at hprev
        | inr e =>
            have hbefore := path.adj_getVert_succ (i := n - 2) (by
              have h := lastBound
              omega)
            rw [show n - 2 + 1 = n - 1 by omega, hmid] at hbefore
            cases hleft : path.getVert (n - 2) with
            | inl y =>
                rw [hleft] at hbefore
                simp only [TwoColorIncidenceGraph] at hbefore
                have hy := ih (n - 2) (by omega) (by omega) y hleft
                by_cases hxregion : x ∈ region
                · exact hxregion
                · exfalso
                  apply hnoDeparture (n - 2) y x e (by omega)
                    hleft hy (by simpa [show n - 2 + 1 = n - 1 by omega] using hmid)
                      (by simpa [show n - 2 + 2 = n by omega] using hx) hxregion
            | inr q =>
                rw [hleft] at hbefore
                simp [TwoColorIncidenceGraph] at hbefore

/-- A path confined before its last departure contains only that edge on the outer boundary. -/
theorem TwoColorWalk.lastBoundaryEdgeUnique {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {phi : PartialEdgeColoring E k}
    {alpha beta : Fin k} {root terminal : V}
    (path : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl root) (Sum.inl terminal))
    (pathSimple : path.IsPath) (X region : Finset V) (regionSubset : region ⊆ X)
    (lastIndex : Fin (path.length + 1)) (lastInside : V)
    (lastInsideAt : path.getVert lastIndex.val = Sum.inl lastInside)
    (crossing : E)
    (crossingAt : path.getVert (lastIndex.val + 1) = Sum.inr crossing)
    (afterLastOutside : ∀ j : Fin (path.length + 1), lastIndex.val < j.val →
      ∀ x : V, path.getVert j.val = Sum.inl x → x ∉ X)
    (hconf : ∀ n ≤ lastIndex.val, ∀ x : V, path.getVert n = Sum.inl x → x ∈ region)
    (f : E) (boundary : f ∈ BoundaryEdges G X) (support : Sum.inr f ∈ path.support) :
    f = crossing := by
  classical
  obtain ⟨u, hu, w, hw, hends⟩ : ∃ u ∈ X, ∃ w ∉ X, G.ends f = s(u, w) := by
    simpa [BoundaryEdges] using boundary
  have hneuw : u ≠ w := by
    intro h
    exact G.loopless f u (h ▸ hends)
  obtain ⟨n, hnget, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp support
  have hnpos : 0 < n := by
    by_cases hnzero : n = 0
    · subst n
      rw [path.getVert_zero] at hnget
      cases hnget
    · omega
  have hnlt : n < path.length := by
    by_contra hnl
    have heq : n = path.length := by omega
    subst n
    rw [path.getVert_length] at hnget
    cases hnget
  have hprev := path.adj_getVert_succ (i := n - 1) (by omega)
  have hnext := path.adj_getVert_succ (i := n) hnlt
  rw [show n - 1 + 1 = n by omega, hnget] at hprev
  have hprevExists : ∃ vprev : V, path.getVert (n - 1) = Sum.inl vprev := by
    cases hprevVert : path.getVert (n - 1) with
    | inl vprev => exact ⟨vprev, rfl⟩
    | inr q =>
        rw [hprevVert] at hprev
        simp [TwoColorIncidenceGraph] at hprev
  obtain ⟨vprev, hprevVert⟩ := hprevExists
  rw [hprevVert] at hprev
  simp only [TwoColorIncidenceGraph, Incident] at hprev
  rw [hnget] at hnext
  have hnextExists : ∃ vnext : V, path.getVert (n + 1) = Sum.inl vnext := by
    cases hnextVert : path.getVert (n + 1) with
    | inl vnext => exact ⟨vnext, rfl⟩
    | inr q =>
        rw [hnextVert] at hnext
        simp [TwoColorIncidenceGraph] at hnext
  obtain ⟨vnext, hnextVert⟩ := hnextExists
  rw [hnextVert] at hnext
  simp only [TwoColorIncidenceGraph, Incident] at hnext
  have hprevEnds : vprev = u ∨ vprev = w := by
    rw [hends] at hprev
    simpa [Sym2.mem_iff] using hprev.1
  have hnextEnds : vnext = u ∨ vnext = w := by
    rw [hends] at hnext
    simpa [Sym2.mem_iff] using hnext.1
  have hvne : vprev ≠ vnext := by
    intro heq
    have hidx := pathSimple.getVert_injOn
      (show n - 1 ≤ path.length by omega)
      (show n + 1 ≤ path.length by omega)
      (by rw [hprevVert, hnextVert, heq])
    omega
  have hprevXor : (vprev ∈ X ∧ vnext ∉ X) ∨
      (vprev ∉ X ∧ vnext ∈ X) := by
    rcases hprevEnds with hpu | hpw <;> rcases hnextEnds with hnu | hnw
    · exfalso
      apply hvne
      exact hpu.trans hnu.symm
    · left
      constructor
      · simpa [hpu] using hu
      · simpa [hnw] using hw
    · right
      constructor
      · simpa [hpw] using hw
      · simpa [hnu] using hu
    · exfalso
      apply hvne
      exact hpw.trans hnw.symm
  have hprevIn : n - 1 ≤ lastIndex.val := by
    rcases hprevXor with hcase | hcase
    · by_contra hnot
      have hout := afterLastOutside ⟨n - 1, by
        have h := hnlt
        omega⟩ (by
          change lastIndex.val < n - 1
          omega)
        vprev hprevVert
      exact hout hcase.1
    · have hnextIn : n + 1 ≤ lastIndex.val := by
        by_contra hbad
        have hout := afterLastOutside ⟨n + 1, by
          have h := hnlt
          omega⟩ (by
            change lastIndex.val < n + 1
            omega)
          vnext hnextVert
        exact hout hcase.2
      exact False.elim (hcase.1 (regionSubset (hconf (n - 1) (by omega)
        vprev hprevVert)))
  have hnextOut : ¬ n + 1 ≤ lastIndex.val := by
    by_contra hnext
    have hvnextX := regionSubset (hconf (n + 1) hnext vnext hnextVert)
    rcases hprevXor with hcase | hcase
    · exact hcase.2 hvnextX
    · exact hcase.1 (regionSubset (hconf (n - 1) hprevIn vprev hprevVert))
  have hidx : n = lastIndex.val + 1 := by
    have hsub : n - 1 + 1 ≤ lastIndex.val + 1 :=
      Nat.succ_le_succ hprevIn
    have hle : n ≤ lastIndex.val + 1 := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hsub
    have hneq : n ≠ lastIndex.val := by
      intro heq
      have hbad := hnget
      rw [heq, lastInsideAt] at hbad
      cases hbad
    have hgt : lastIndex.val < n := by
      by_contra hnot
      have hnle : n ≤ lastIndex.val := by omega
      have hsucc : n + 1 ≤ lastIndex.val := by omega
      exact hnextOut hsucc
    have hge : lastIndex.val + 1 ≤ n := by omega
    omega
  have heq : (Sum.inr f : Sum V E) = Sum.inr crossing := by
    rw [← hnget, hidx, crossingAt]
  injection heq

/-- A two-step crossing of a vertex set supplies a boundary edge with one of the path colors. -/
theorem TwoColorWalk.boundaryAtTwoStep {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {phi : PartialEdgeColoring E k}
    {alpha beta : Fin k} {root terminal : V}
    (path : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl root) (Sum.inl terminal))
    (pathSimple : path.IsPath) (region : Finset V) (n : ℕ) (y x : V) (e : E)
    (lengthBound : n + 2 ≤ path.length) (hny : path.getVert n = Sum.inl y) (hy : y ∈ region)
    (hne : path.getVert (n + 1) = Sum.inr e) (hexc : path.getVert (n + 2) = Sum.inl x)
    (hx : x ∉ region) : e ∈ BoundaryEdges G region ∧
      (phi e = some alpha ∨ phi e = some beta) := by
  classical
  have ha1 := path.adj_getVert_succ (i := n) (by
    have h := lengthBound
    omega)
  have ha2 := path.adj_getVert_succ (i := n + 1) (by
    have h := lengthBound
    omega)
  rw [show n + 1 + 1 = n + 2 by omega] at ha2
  rw [hny, hne] at ha1
  rw [hne, hexc] at ha2
  simp only [TwoColorIncidenceGraph, Incident] at ha1 ha2
  have hvne : y ≠ x := by
    intro heq
    have hinj := pathSimple.getVert_injOn
      (show n ≤ path.length by
        have h := lengthBound
        omega)
      (show n + 2 ≤ path.length by
        have h := lengthBound
        omega)
      (by rw [hny, hexc, heq])
    omega
  have hedge : e ∈ BoundaryEdges G region := by
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨y, hy, x, hx, ?_⟩
    exact (Sym2.mem_and_mem_iff hvne).mp ⟨ha1.1, ha2.1⟩
  exact ⟨hedge, ha1.2⟩

end GoldbergSeymour

end
