/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3DisjointEnclosingDiscs
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# A third disc prevents coverage

In the sphere case of XII (3.1), page 245, at least three discs are
prescribed. The interior of a third disc is outside the partial fills
of the first two cuffs. It therefore supplies a point outside both
enclosing discs, so the noncoverage form of disc uniqueness applies.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Filling one cuff leaves the interiors of all other prescribed
discs outside the partially filled surface. -/
theorem discInt_disjoint_partial_fill
    {S ι : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i)) {i k : ι} (hki : k ≠ i) :
    Disjoint (discInt (Δ k)) (discComplement (fun j : {j // j ≠ i} => Δ j.val)) := by
  apply Set.disjoint_left.mpr
  intro x hxI hxC
  have hxB := discComplement_inter_disc_subset_boundary hS
    (fun j : {j // j ≠ i} => Δ j.val) (fun j => hΔ j.val) ⟨k, hki⟩ ⟨hxC, hxI.1⟩
  exact hxI.2 hxB

/-- A set in the partial fill includes precisely the filled disc,
provided it includes that disc at all. -/
theorem included_disc_iff_of_subset_partial_fill
    {S ι : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    {i : ι} {D : Set S} (hiD : Δ i ⊆ D)
    (hDT : D ⊆ discComplement (fun j : {j // j ≠ i} => Δ j.val)) :
    ∀ k, Δ k ⊆ D ↔ k = i := by
  intro k
  constructor
  · intro hkD
    by_contra hki
    obtain ⟨x, hx⟩ := (hΔ k).nonempty_discInt
    exact Set.disjoint_left.mp (discInt_disjoint_partial_fill hS Δ hΔ hki)
      hx (hDT (hkD hx.1))
  · rintro rfl
    exact hiD

/-- Two sets in distinct partial fills cannot cover the original
surface when a third deleted disc is present. -/
theorem union_ne_univ_of_subset_partial_fills
    {S ι : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    {i j k : ι} (hki : k ≠ i) (hkj : k ≠ j) {D E : Set S}
    (hDT : D ⊆ discComplement (fun l : {l // l ≠ i} => Δ l.val))
    (hET : E ⊆ discComplement (fun l : {l // l ≠ j} => Δ l.val)) : D ∪ E ≠ univ := by
  intro heq
  obtain ⟨x, hx⟩ := (hΔ k).nonempty_discInt
  have hxDE : x ∈ D ∪ E := heq.symm ▸ mem_univ x
  rcases hxDE with hxD | hxE
  · exact Set.disjoint_left.mp (discInt_disjoint_partial_fill hS Δ hΔ hki) hx (hDT hxD)
  · exact Set.disjoint_left.mp (discInt_disjoint_partial_fill hS Δ hΔ hkj) hx (hET hxE)

/-- A third deleted disc makes the enclosing discs of two distinct
cuffs disjoint, even when the original surface is a sphere. -/
theorem exists_disjoint_surrounding_discs_of_third_disc
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    {i j k : ι} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    {F₁ F₂ : Set (discComplement Δ)}
    (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂) (hFF : Disjoint F₁ F₂)
    (hs₁ : GM07.SurroundsCuff F₁ (Subtype.val ⁻¹' discBd (Δ i)))
    (hs₂ : GM07.SurroundsCuff F₂ (Subtype.val ⁻¹' discBd (Δ j))) :
    ∃ D E : Set S, IsClosedDisc D ∧ IsClosedDisc E ∧
      discBd D = (Subtype.val : discComplement Δ → S) '' F₁ ∧
      discBd E = (Subtype.val : discComplement Δ → S) '' F₂ ∧
      (∀ l, Δ l ⊆ D ↔ l = i) ∧ (∀ l, Δ l ⊆ E ↔ l = j) ∧ Disjoint D E := by
  obtain ⟨D, hD, hbD, hiD, hDT⟩ :=
    surrounding_bounds_disc_including_deleted_disc hS Δ hΔ hdisj i hF₁ hs₁
  obtain ⟨E, hE, hbE, hjE, hET⟩ :=
    surrounding_bounds_disc_including_deleted_disc hS Δ hΔ hdisj j hF₂ hs₂
  have hnoD : ¬ Δ j ⊆ D := by
    intro hjD
    obtain ⟨x, hx⟩ := (hΔ j).nonempty_discInt
    exact Set.disjoint_left.mp (discInt_disjoint_partial_fill hS Δ hΔ hij.symm)
      hx (hDT (hjD hx.1))
  have hnoE : ¬ Δ i ⊆ E := by
    intro hiE
    obtain ⟨x, hx⟩ := (hΔ i).nonempty_discInt
    exact Set.disjoint_left.mp (discInt_disjoint_partial_fill hS Δ hΔ hij)
      hx (hET (hiE hx.1))
  have hcover := union_ne_univ_of_subset_partial_fills hS Δ hΔ hki hkj hDT hET
  refine ⟨D, E, hD, hE, hbD, hbE,
    included_disc_iff_of_subset_partial_fill hS Δ hΔ hiD hDT,
    included_disc_iff_of_subset_partial_fill hS Δ hΔ hjE hET, ?_⟩
  apply disjoint_discs_of_disjoint_boundaries_of_not_nested_of_noncover hS hD hE
  · rw [hbD, hbE]
    apply Set.disjoint_left.mpr
    rintro x ⟨y, hy, rfl⟩ ⟨z, hz, he⟩
    exact Set.disjoint_left.mp hFF hy (Subtype.val_injective he ▸ hz)
  · intro hDE
    exact hnoE (hiD.trans hDE)
  · intro hED
    exact hnoD (hjE.trans hED)
  · exact hcover

/-- Under the topological assumption of XII (3.1), disjoint circles
surrounding distinct prescribed cuffs have disjoint enclosing discs.
This includes both the nonsphere case and the sphere with three or
more prescribed discs. -/
theorem exists_disjoint_surrounding_discs_of_surface_condition
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι)
    {i j : ι} (hij : i ≠ j) {F₁ F₂ : Set (discComplement Δ)}
    (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂) (hFF : Disjoint F₁ F₂)
    (hs₁ : GM07.SurroundsCuff F₁ (Subtype.val ⁻¹' discBd (Δ i)))
    (hs₂ : GM07.SurroundsCuff F₂ (Subtype.val ⁻¹' discBd (Δ j))) :
    ∃ D E : Set S, IsClosedDisc D ∧ IsClosedDisc E ∧
      discBd D = (Subtype.val : discComplement Δ → S) '' F₁ ∧
      discBd E = (Subtype.val : discComplement Δ → S) '' F₂ ∧
      (∀ l, Δ l ⊆ D ↔ l = i) ∧ (∀ l, Δ l ⊆ E ↔ l = j) ∧ Disjoint D E := by
  classical
  rcases hcase with hns | hthree
  · exact exists_disjoint_surrounding_discs hS hns Δ hΔ hdisj hij hF₁ hF₂ hFF hs₁ hs₂
  · let := Fintype.ofFinite ι
    have hthree' : 3 ≤ Fintype.card ι := by
      simpa only [Nat.card_eq_fintype_card] using hthree
    have hex : ∃ k : ι, k ≠ i ∧ k ≠ j := ENat.exists_ne_ne_of_three_le
      (by rw [ENat.card_eq_coe_fintype_card]; exact_mod_cast hthree') i j
    obtain ⟨k, hki, hkj⟩ := hex
    exact exists_disjoint_surrounding_discs_of_third_disc hS Δ hΔ hdisj hij hki hkj
      hF₁ hF₂ hFF hs₁ hs₂

end GraphMinor.GM12
