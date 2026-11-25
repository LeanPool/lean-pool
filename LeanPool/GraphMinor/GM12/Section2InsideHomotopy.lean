/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section7b
import LeanPool.GraphMinor.GM12.Section3DiscUniqueness
import LeanPool.GraphMinor.GM07.Section11c

/-!
# Comparing disc insides through a homotopy avoiding two points

For the deformation step in XII (2.1), Case 1, page 244, keep a
point outside both chosen discs fixed. A second point lies outside
one disc precisely when its boundary contracts without meeting
either point. By Graph Minors XI (7.2), a contracting boundary bounds
a disc avoiding the points, and the common outside point makes that
disc the original one. A homotopy avoiding both points therefore
preserves membership of the second point in the two chosen insides.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM07

/-- With a fixed point outside a boundary disc, contraction avoiding
that point and a second point detects whether the second point is
outside the disc. -/
theorem curve_null_in_pair_compl_iff_not_mem_disc
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {φ : C(Circle, S)} (hφ : IsEmbedding φ)
    {D : Set S} (hD : IsClosedDisc D) (hbd : subBd D = range φ)
    {p q : S} (hq : q ∉ D) :
    ClosedCurveIsNullHomotopicIn ({p, q} : Set S)ᶜ φ ↔ p ∉ D := by
  constructor
  · intro hn
    have hF : IsOArc (range φ) := ⟨hφ.toHomeomorph⟩
    have hnF : IsNullHomotopicOArcIn ({p, q} : Set S)ᶜ (range φ) := ⟨hφ.toHomeomorph, hn⟩
    have hFZ : range φ ⊆ ({p, q} : Set S)ᶜ := by
      obtain ⟨c, hc, H, hH, hH0, _⟩ := hn
      rintro x ⟨z, rfl⟩
      rw [← hH0 z]
      exact hH (z, 0)
    obtain ⟨D', hD'Z, hD', hbd'⟩ := GM11.theorem_7_2_proof hS hF hFZ hnF
    have hfront : subBd D = discBd D :=
      (subBd_eq_frontier D).trans (IsClosedDisc.frontier_eq_discBd hS hD)
    have hfront' : subBd D' = discBd D' :=
      (subBd_eq_frontier D').trans (IsClosedDisc.frontier_eq_discBd hS hD')
    have hb : discBd D = discBd D' :=
      hfront.symm.trans (hbd.trans (hbd'.symm.trans hfront'))
    have hq' : q ∉ D' := fun hx => hD'Z hx (Or.inr rfl)
    have hnotcover : D ∪ D' ≠ univ := by
      intro heq
      rcases (heq.symm ▸ mem_univ q : q ∈ D ∪ D') with h | h
      · exact hq h
      · exact hq' h
    have heq := eq_of_discBd_eq_of_union_ne_univ (fun x => (hS.2.2 x).isManifoldPoint) hD hD' hb
      hnotcover
    intro hp
    exact hD'Z (heq ▸ hp) (Or.inl rfl)
  · intro hp
    have hDZ : D ⊆ ({p, q} : Set S)ᶜ := by
      intro x hx hpair
      simp only [mem_insert_iff, mem_singleton_iff] at hpair
      rcases hpair with hxp | hxq
      · exact hp (hxp ▸ hx)
      · exact hq (hxq ▸ hx)
    have hφD : range φ ⊆ D := by
      intro x hx
      have hxb : x ∈ subBd D := hbd.symm ▸ hx
      exact hD.isCompact.isClosed.closure_subset_iff.mpr subset_rfl hxb.1
    obtain ⟨c, hc, H⟩ := hD.isSimplyConnectedSet.2 φ hφD
    exact ⟨c, hDZ hc, H.mono hDZ⟩

/-- The inside comparison used in XII (2.1), Case 1: homotopic
boundary parameterizations avoiding two points give the same inside
membership, provided one of the points lies outside both discs. -/
theorem mem_disc_iff_of_boundary_homotopy
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {φ ψ : C(Circle, S)}
    (hφ : IsEmbedding φ) (hψ : IsEmbedding ψ)
    {D E : Set S} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hbdD : subBd D = range φ) (hbdE : subBd E = range ψ)
    {p q : S} (hqD : q ∉ D) (hqE : q ∉ E)
    (hh : ClosedCurvesHomotopicIn ({p, q} : Set S)ᶜ φ ψ) : p ∈ D ↔ p ∈ E := by
  have hnot : p ∉ D ↔ p ∉ E := by
    constructor
    · intro hp
      apply (curve_null_in_pair_compl_iff_not_mem_disc hS hψ hE hbdE hqE).mp
      exact GM11.null_of_homotopic subset_rfl (GM07.ClosedCurvesHomotopicIn.symm hh)
        ((curve_null_in_pair_compl_iff_not_mem_disc hS hφ hD hbdD hqD).mpr hp)
    · intro hp
      apply (curve_null_in_pair_compl_iff_not_mem_disc hS hφ hD hbdD hqD).mp
      exact GM11.null_of_homotopic subset_rfl hh
        ((curve_null_in_pair_compl_iff_not_mem_disc hS hψ hE hbdE hqE).mpr hp)
  exact not_iff_not.mp hnot

end GraphMinor.GM12
