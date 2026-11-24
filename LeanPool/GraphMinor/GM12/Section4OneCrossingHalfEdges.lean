/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4SourceHalfEdges
public import LeanPool.GraphMinor.GM12.Section4CrossingPoints

/-!
# The half-edge system of the one-crossing subdivision

In XII (4.5), page 253, every subdivided edge contains exactly
one crossing. Select that crossing on each edge. A meeting of
two distinct edges away from the vertices is one of these
selected points, by the one-crossing equation. Split the edges
there to obtain the source half-edge system.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The actual one-crossing equations supply all the crossing
points and half-edges required by the source feasibility
construction in XII (4.5), claim (1), page 253. -/
theorem exists_one_crossing_halfedges {S V E : Type*} [TopologicalSpace S] [T2Space S]
    (v : V → S) (κ : E × Bool → V) (P : E → Set S)
    (hP : ∀ e, IsLineWithEnds (P e) (v (κ (e, false))) (v (κ (e, true))))
    (hPV : ∀ e w, v w ∈ P e → w = κ (e, false) ∨ w = κ (e, true))
    (hcross : ∀ e, ∃ x ∈ edgeMeetingPoints v P, P e ∩ edgeMeetingPoints v P = {x}) :
    ∃ (x : E → S) (L : E × Bool → Set S),
      (∀ e, x e ∈ edgeMeetingPoints v P ∧ P e ∩ edgeMeetingPoints v P = {x e}) ∧
      (∀ i, IsLineWithEnds (L i) (v (κ i)) (x i.1)) ∧
      (∀ i, L i ⊆ P i.1) ∧ (∀ i w, v w ∈ L i → w = κ i) ∧
      (∀ i j, i ≠ j → L i ∩ L j ⊆ range v ∪ range (fun q : E × Bool => x q.1)) ∧
      (∀ e, L (e, false) ∪ L (e, true) = P e) ∧
      ∀ e, L (e, false) ∩ L (e, true) = {x e} := by
  classical
  choose x hx hmeet using hcross
  have hxP : ∀ e, x e ∈ P e := fun e =>
    ((hmeet e).symm.subset (mem_singleton _)).1
  have hxV : ∀ e, x e ∉ range v := by
    intro e
    obtain ⟨_, _, _, _, hnot⟩ := hx e
    exact hnot
  have hPP : ∀ e f, e ≠ f → P e ∩ P f ⊆ range v ∪ range x := by
    intro e f hef z hz
    by_cases hzV : z ∈ range v
    · exact Or.inl hzV
    · have hzM : z ∈ edgeMeetingPoints v P := ⟨e, f, hef, hz, hzV⟩
      have hzx : z = x e := mem_singleton_iff.mp ((hmeet e).subset ⟨hz.1, hzM⟩)
      exact Or.inr ⟨e, hzx.symm⟩
  obtain ⟨L, hline, hsub, hvertex, hinter, hcover, hpair⟩ :=
    exists_source_halfedges v κ P x hP hxP hxV hPV hPP
  exact ⟨x, L, (fun e => ⟨hx e, hmeet e⟩), hline, hsub, hvertex, hinter, hcover, hpair⟩

end GraphMinor.GM12
