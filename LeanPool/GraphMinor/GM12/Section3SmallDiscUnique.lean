/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3PuncturedBoundary
public import LeanPool.GraphMinor.Surface.TopologyStatements
import LeanPool.GraphMinor.GM12.Section3DiscUniqueness
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Uniqueness of a disc enclosing at most one deletion

Claim (2) in XII (3.2), page 246, compares two discs with the same
boundary in Sigma-star. On a surface other than a sphere, disc
uniqueness applies directly. With at least three deleted discs, the
two proposed discs cannot cover the surface: each deletion would be
on one side, but each side contains at most one deletion. This proves
the topological comparison needed for the tangle-selected disc.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- If two discs cover the surface and the first boundary lies in
Sigma-star, every deleted disc is wholly in one of them. Its connected
interior avoids that boundary, and closedness restores its boundary. -/
theorem deleted_disc_subset_one_of_cover
    {S ι : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    {D E : Set S} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hbd : discBd D ⊆ discComplement Δ) (hcover : D ∪ E = univ) (i : ι) :
    Δ i ⊆ D ∨ Δ i ⊆ E := by
  have hdis : Disjoint (discInt (Δ i)) (discBd D) := by
    apply Set.disjoint_left.mpr
    intro x hxI hxB
    exact hxI.2 (discComplement_inter_disc_subset_boundary hS Δ hΔ i
      ⟨hbd hxB, hxI.1⟩)
  rcases hD.side (fun x => (hS.2.2 x).isManifoldPoint)
    (hΔ i).isPreconnected_discInt hdis with hin | hout
  · apply Or.inl
    have hcl : closure (discInt (Δ i)) ⊆ D := by
      rw [← hD.isClosed.closure_eq]
      exact closure_mono (hin.trans (discInt_subset D))
    exact (hΔ i).subset_closure_discInt.trans hcl
  · apply Or.inr
    have hIE : discInt (Δ i) ⊆ E := by
      intro x hx
      have hDE : x ∈ D ∪ E := hcover.symm ▸ mem_univ x
      exact hDE.resolve_left (fun hxD => Set.disjoint_left.mp hout hx hxD)
    have hcl : closure (discInt (Δ i)) ⊆ E := by
      rw [← hE.isClosed.closure_eq]
      exact closure_mono hIE
    exact (hΔ i).subset_closure_discInt.trans hcl

/-- The topological uniqueness step of claim (2) in XII (3.2), page
246. Two discs bounded in Sigma-star and enclosing at most one
prescribed deletion each must agree in the allowed surface cases. -/
theorem eq_of_discBd_eq_of_at_most_one_deleted_disc
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι)
    {D E : Set S} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hb : discBd D = discBd E) (hbd : discBd D ⊆ discComplement Δ)
    (honeD : ∀ i j, Δ i ⊆ D → Δ j ⊆ D → i = j)
    (honeE : ∀ i j, Δ i ⊆ E → Δ j ⊆ E → i = j) : D = E := by
  rcases hcase with hns | hthree
  · exact Surface.eq_of_discBd_eq
      ⟨hS.1, hS.2.1, fun x => (hS.2.2 x).isManifoldPoint⟩ hns hD hE hb
  · apply eq_of_discBd_eq_of_union_ne_univ (fun x => (hS.2.2 x).isManifoldPoint) hD hE hb
    intro hcover
    let I : Set ι := {i | Δ i ⊆ D}
    let J : Set ι := {i | Δ i ⊆ E}
    have hI : I.ncard ≤ 1 := (Set.ncard_le_one (Set.toFinite _)).mpr fun i hi j hj
      => honeD i j hi hj
    have hJ : J.ncard ≤ 1 := (Set.ncard_le_one (Set.toFinite _)).mpr fun i hi j hj
      => honeE i j hi hj
    have hIJ : I ∪ J = univ := Set.eq_univ_iff_forall.mpr
      (fun i => deleted_disc_subset_one_of_cover hS Δ hΔ hD hE hbd hcover i)
    have hc := Set.ncard_union_le I J
    rw [hIJ, Set.ncard_univ] at hc
    omega

end GraphMinor.GM12
