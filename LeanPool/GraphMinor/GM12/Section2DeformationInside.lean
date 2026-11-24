/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2InsideHomotopy
public import LeanPool.GraphMinor.GM12.Section2NormalNoncover
import LeanPool.GraphMinor.GM11.Regions

/-!
# Region deformations preserve the atoms met by selected insides

In Case 1 of XII (2.1), page 244, the curve is deformed to its
simple trace through its visited regions and boundary vertices.
An atom met by this deformation is either met by the final curve,
or is a visited region, which the final curve also meets. For an
atom missed by the final curve, the homotopy avoids that atom.
A drawing point outside both selected discs is avoided too. The
two-point inside comparison then transfers every inside incidence.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The inside-incidence conclusion of the deformation step in
XII (2.1), Case 1. The homotopy may use the visited regions and
the final curve's drawing vertices, and no other drawing points. -/
theorem atom_meets_disc_of_region_deformation
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsPretangle Γ.toHypergraph θ T)
    {φ ψ : C(Circle, S)} (hφ : IsEmbedding φ) (hψ : IsEmbedding ψ)
    {D E : Set S} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hbdD : subBd D = range φ) (hbdE : subBd E = range ψ)
    (hnD : Γ.IsNormal (range φ)) (hnE : Γ.IsNormal (range ψ))
    (hmD : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T)
    (hmE : ((PaintingOrDrawing.drawing Γ).inter E,
      (PaintingOrDrawing.drawing Γ).interOutside E) ∈ T)
    {Z : Set S} (hh : ClosedCurvesHomotopicIn Z φ ψ)
    (hZΓ : Z ∩ Γ.U ⊆ range ψ)
    (hZR : ∀ r ∈ Γ.R, (Z ∩ r).Nonempty → (range ψ ∩ r).Nonempty)
    {c : Set S} (hc : c ∈ Γ.A) (hcD : (c ∩ D).Nonempty) :
    (c ∩ E).Nonempty := by
  have hnDf : (PaintingOrDrawing.drawing Γ).IsNormal (frontier D) := by
    rw [← subBd_eq_frontier, hbdD]
    exact hnD
  have hnEf : (PaintingOrDrawing.drawing Γ).IsNormal (frontier E) := by
    rw [← subBd_eq_frontier, hbdE]
    exact hnE
  obtain ⟨q, hqΓ, hqD, hqE⟩ := exists_support_point_outside_two_small_sides (Γ := .drawing Γ) hT
    hD.isCompact.isClosed hE.isCompact.isClosed hnDf hnEf hmD hmE
  have hψE : range ψ ⊆ E := by
    intro x hx
    have hxb : x ∈ subBd E := hbdE.symm ▸ hx
    exact hE.isCompact.isClosed.closure_subset_iff.mpr subset_rfl hxb.1
  by_cases hmeet : (c ∩ range ψ).Nonempty
  · exact hmeet.mono (inter_subset_inter_right c hψE)
  · have hqZ : q ∉ Z := fun hq => hqE (hψE (hZΓ ⟨hq, hqΓ⟩))
    have hZc : Disjoint Z c := by
      apply disjoint_left.mpr
      intro x hxZ hxc
      rcases hc with (⟨v, hv, rfl⟩ | he) | hr
      · have hxΓ : x ∈ Γ.U := Γ.V_subset_U (hxc ▸ hv)
        exact hmeet ⟨x, hxc, hZΓ ⟨hxZ, hxΓ⟩⟩
      · have hxΓ : x ∈ Γ.U := (he.2.1 hxc).1
        exact hmeet ⟨x, hxc, hZΓ ⟨hxZ, hxΓ⟩⟩
      · obtain ⟨y, hyψ, hyr⟩ := hZR c hr ⟨x, hxZ, hxc⟩
        exact hmeet ⟨y, hyr, hyψ⟩
    obtain ⟨p, hpc, hpD⟩ := hcD
    have hZpair : Z ⊆ ({p, q} : Set S)ᶜ := by
      intro x hx hpair
      simp only [mem_insert_iff, mem_singleton_iff] at hpair
      rcases hpair with hxp | hxq
      · exact disjoint_left.mp hZc hx (hxp.symm ▸ hpc)
      · exact hqZ (hxq ▸ hx)
    exact ⟨p, hpc, (mem_disc_iff_of_boundary_homotopy hS hφ hψ hD hE hbdD hbdE
      hqD hqE (hh.mono hZpair)).mp hpD⟩

end GraphMinor.GM12
