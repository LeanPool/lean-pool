/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Cited
import LeanPool.GraphMinor.GM16.Section9Annuli

import LeanPool.GraphMinor.GM09.Bridge

/-!
# Replacing a rural boundary linkage by a linked set

IX (10.5) offers either the desired linkage or a smaller set cutting
all paths from the outer boundary. An existing disjoint boundary
linkage rules out the cut by counting. One of the resulting paths
then avoids any set smaller than the linkage. This is the application
of IX (10.5) in XVI (8.1), Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.GM09
universe u v

/-- Breadth decreases when circuits are omitted from a nest. -/
theorem hasBreadthGe_mono {α : Type u} {β : Type v} {N : Neighborhood α β}
    {m n : ℕ} (h : N.HasBreadthGe n) (hmn : m ≤ n) : N.HasBreadthGe m := by
  obtain ⟨P, C, hC, hDis, D, hD, hIn, hNest⟩ := h
  let j : Fin m → Fin n := fun i => i.castLE hmn
  have hj : Function.Injective j := by
    intro i k heq
    exact Fin.ext (congrArg (fun x : Fin n => x.val) heq)
  refine ⟨P, fun i => C (j i), fun i => hC (j i), ?_,
    fun i => D (j i), fun i => hD (j i), fun i => hIn (j i), ?_⟩
  · intro i k hik
    exact hDis (fun heq => hik (hj heq))
  · intro i k hik
    exact hNest (j i) (j k) hik

/-- IX (10.5), applied when a boundary linkage already rules out its
separator outcome, replaces the boundary ends by the linked set. -/
theorem rural_linkage_of_boundary_linkage
    {α : Type u} {β : Type v} (S S₀ : Society α β) (N : Neighborhood α β)
    (p : ℕ) (X Y : Set α)
    (hRural : N.IsRural) (hBreadth : N.HasBreadthGe ((p + 1) / 2 + 1))
    (hLinked : N.IsLinked X) (hX : p ≤ X.ncard)
    (hComp : S.IsComposition S₀ N) (hY : Y ⊆ V(S₀.G))
    (Q : Fin p → Graph α β)
    (hQ : ∀ i, IsFromToPath S.G (Q i) S.Ω.bar Y)
    (hDis : Pairwise (fun i j => Disjoint V(Q i) V(Q j))) :
    ∃ P : Fin p → Graph α β,
      (∀ i, ∃ x ∈ X, ∃ y ∈ Y, IsFromToPathWithEnds S.G (P i) S.Ω.bar Y x y) ∧
      Pairwise (fun i j => Disjoint V(P i) V(P j)) := by
  rcases GraphMinor.GM09.gm16_theorem_10_5.{u, v} S S₀ N p X Y hRural hBreadth hLinked hX hComp hY
    with h | h
  · exact h
  · obtain ⟨W, hWS, hWp, _, hCut⟩ := h
    obtain ⟨i, hi⟩ := exists_disjoint_of_pairwise_disjoint
      (fun i => V(Q i)) hDis W (S.finite_V.subset hWS) hWp
    obtain ⟨x, hx, hxW⟩ := hCut (Q i) (hQ i)
    exact False.elim (hi.notMem_of_mem_left hx hxW)

/-- A disjoint rural linkage has a path avoiding any smaller finite
set. This is the last counting step of XVI (8.1), Claim (11), page 74. -/
theorem rural_linkage_avoids_small_set {α : Type u} {β : Type v}
    {G : Graph α β} {A X Y Z : Set α} {p : ℕ}
    (P : Fin p → Graph α β)
    (hP : ∀ i, ∃ x ∈ X, ∃ y ∈ Y, IsFromToPathWithEnds G (P i) A Y x y)
    (hDis : Pairwise (fun i j => Disjoint V(P i) V(P j)))
    (hZ : Z.Finite) (hCard : Z.ncard < p) :
    ∃ x ∈ X, ∃ y ∈ Y, ∃ Q : Graph α β,
      IsFromToPathWithEnds G Q A Y x y ∧ Disjoint V(Q) Z := by
  obtain ⟨i, hi⟩ := exists_disjoint_of_pairwise_disjoint (fun i => V(P i)) hDis Z hZ hCard
  obtain ⟨x, hx, y, hy, hxy⟩ := hP i
  exact ⟨x, hx, y, hy, P i, hxy, hi⟩

end GraphMinor.GM16
