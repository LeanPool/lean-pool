/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ThetaPlanarity
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.Surface.DiscsInSurface

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Three theta discs covering the surface force a sphere

The third schismatic shape in VII Section 8, used by XII (3.1), page
245, occurs only on a sphere with three cuffs. For the sphere assertion,
fill the cuffs and consider its three enclosing discs. Two pair circles
are planar, so VII (5.1) puts the whole proper theta in one disc. On a
surface other than a sphere, uniqueness of bounded discs then puts all
three enclosing discs in that disc. They cannot cover a closed surface.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

universe u

/-- A closed disc cannot fill a closed surface: its boundary is a
circle, whereas the frontier of the whole surface is empty. -/
theorem closed_disc_ne_univ
    {S : Type*} [TopologicalSpace S] (hS : IsClosedSurface S)
    {D : Set S} (hD : IsClosedDisc D) : D ≠ univ := by
  intro heq
  have hb : discBd D = ∅ := by
    rw [← IsClosedDisc.frontier_eq_discBd hS hD, heq, frontier_univ]
  obtain ⟨e⟩ := hD.isOArc_discBd
  exact hb.subset (e 1).property

/-- On a surface other than a sphere, a disc whose boundary lies in
another disc lies in that disc. Jordan inside the latter disc and
uniqueness in the original surface give the inclusion. -/
theorem disc_subset_of_boundary_subset_disc_of_not_sphere
    {S : Type*} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
    {D B : Set S} (hD : IsClosedDisc D) (hB : IsClosedDisc B)
    (hbd : discBd D ⊆ B) : D ⊆ B := by
  obtain ⟨E, hE, _⟩ := disc_oArc B (discBd D) hB hbd hD.isOArc_discBd
  have hsurf : IsSurface S := ⟨hS.1, hS.2.1, fun x => (hS.2.2 x).isManifoldPoint⟩
  have heq : D = E := Surface.eq_of_discBd_eq hsurf hns hD hE.2.1 hE.2.2.1.symm
  exact heq ▸ hE.1

/-- A proper theta whose three pair circles bound discs covering a
connected closed surface forces that surface to be a sphere. This is
the closed-surface step in VII Section 8's third-shape classification. -/
theorem isSphere_of_covering_theta_discs
    {S : Type u} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S)
    {P Q R D₀ D₁ D₂ : Set S} {a b : S} (hab : a ≠ b)
    (hP : IsLineWithEnds P a b) (hQ : IsLineWithEnds Q a b) (hR : IsLineWithEnds R a b)
    (hPQ : P ∩ Q = {a, b}) (hPR : P ∩ R = {a, b}) (hQR : Q ∩ R = {a, b})
    (hproper : P ∪ Q ∪ R ≠ univ)
    (hD₀ : IsClosedDisc D₀) (hD₁ : IsClosedDisc D₁) (hD₂ : IsClosedDisc D₂)
    (hb₀ : discBd D₀ = Q ∪ R) (hb₁ : discBd D₁ = R ∪ P) (hb₂ : discBd D₂ = P ∪ Q)
    (hcover : D₀ ∪ D₁ ∪ D₂ = univ) : IsSphere S := by
  classical
  by_contra hns
  have hsurf : IsSurface S := ⟨hS.1, hS.2.1, fun x => (hS.2.2 x).isManifoldPoint⟩
  have hpPQ : GM11.IsPlanar (P ∪ Q) := ⟨D₂, hD₂, hb₂ ▸ Surface.discBd_subset D₂⟩
  have hpPR : GM11.IsPlanar (P ∪ R) := by
    refine ⟨D₁, hD₁, ?_⟩
    rw [union_comm, ← hb₁]
    exact Surface.discBd_subset D₁
  obtain ⟨B, hB, hXB⟩ := planar_three_branches_of_two_planar_pairs hsurf inferInstance
    hab hP hQ hR hPQ hPR hQR hproper hpPQ hpPR
  have hsub : ∀ D : Set S, IsClosedDisc D → discBd D ⊆ P ∪ Q ∪ R → D ⊆ B := by
    intro D hD hb
    exact disc_subset_of_boundary_subset_disc_of_not_sphere hS hns hD hB (hb.trans hXB)
  have hs₀ : D₀ ⊆ B := hsub D₀ hD₀ (by
    rw [hb₀]
    exact union_subset (subset_union_right.trans subset_union_left) subset_union_right)
  have hs₁ : D₁ ⊆ B := hsub D₁ hD₁ (by
    rw [hb₁]
    exact union_subset subset_union_right (subset_union_left.trans subset_union_left))
  have hs₂ : D₂ ⊆ B := hsub D₂ hD₂ (by rw [hb₂]; exact subset_union_left)
  apply closed_disc_ne_univ hS hB
  apply Set.eq_univ_of_univ_subset
  rw [← hcover]
  exact union_subset (union_subset hs₀ hs₁) hs₂

end GraphMinor.GM12
