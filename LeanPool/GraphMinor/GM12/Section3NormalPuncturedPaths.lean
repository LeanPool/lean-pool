/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3NormalPathConnected
public import LeanPool.GraphMinor.GM12.Section3Punctured
import LeanPool.GraphMinor.GM12.Section3PushPathOutside
import LeanPool.GraphMinor.GM11.Section6

/-!
# Normal paths in the punctured surface

For candidate existence in XII (3.1), page 245, start with a normal
path in the closed surface. Push it outside each deleted disc in turn.
Disc boundaries are normal by the prescribed intersection condition.
Their pairwise disjointness ensures that adding a new boundary does
not enter any interior already excluded. The finite iteration gives
a normal path in the actual disc complement.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

private theorem isPathConnected_oArc
    {S : Type*} [TopologicalSpace S] {F : Set S} (hF : IsOArc F) : IsPathConnected F := by
  obtain ⟨e⟩ := hF
  have heq : range (fun t : Circle => (e t).val) = F := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (e t).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩
  rw [← heq]
  exact isPathConnected_range (continuous_subtype_val.comp e.continuous)

/-- Any two allowed points in the punctured surface have a normal
joining path there. The drawing may have arbitrary regions. -/
theorem exists_normal_path_in_discComplement
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Γ : Drawing S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i))
    {a b : S} (ha : a ∈ discComplement Δ) (hb : b ∈ discComplement Δ)
    (haN : a ∈ Γ.Uᶜ ∪ Γ.V) (hbN : b ∈ Γ.Uᶜ ∪ Γ.V) :
    ∃ q : Path a b, range q ⊆ discComplement Δ ∧ Γ.IsNormal (range q) := by
  classical
  let := Fintype.ofFinite ι
  have hCout : ∀ i, discComplement Δ ⊆ (interior (Δ i))ᶜ := by
    intro i
    apply closure_minimal
    · intro x hx hxi
      exact hx (mem_iUnion.mpr ⟨i, interior_subset hxi⟩)
    · exact isOpen_interior.isClosed_compl
  have hfrontN : ∀ i, frontier (Δ i) ⊆ Γ.Uᶜ ∪ Γ.V := by
    intro i x hx
    by_cases hxU : x ∈ Γ.U
    · have hxD : x ∈ Δ i := (hΔ i).isCompact.isClosed.frontier_subset hx
      exact Or.inr ((havoid i ▸ (show x ∈ Γ.U ∩ Δ i from ⟨hxU, hxD⟩)).1)
    · exact Or.inl hxU
  have hfrontpath : ∀ i, IsPathConnected (frontier (Δ i)) := by
    intro i
    rw [IsClosedDisc.frontier_eq_discBd hS (hΔ i)]
    exact isPathConnected_oArc (hΔ i).isOArc_discBd
  obtain ⟨p, hp⟩ := (isPathConnected_normal_points hS Γ).joinedIn a haN b hbN
  have hex : ∀ J : Finset ι, ∃ q : Path a b,
      range q ⊆ Γ.Uᶜ ∪ Γ.V ∧ ∀ i ∈ J, range q ⊆ (interior (Δ i))ᶜ := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      exact ⟨p, by rintro _ ⟨t, rfl⟩; exact hp t, by simp⟩
    | @insert i J hi ih =>
      obtain ⟨q, hqN, hqout⟩ := ih
      obtain ⟨r, hr, hrout⟩ := exists_path_outside_interior_of_pathConnected_frontier
        (hΔ i).isCompact.isClosed (hfrontpath i) q (hCout i ha) (hCout i hb)
      refine ⟨r, hr.trans (union_subset hqN (hfrontN i)), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hrout
      · intro x hx hxin
        rcases hr hx with hxq | hxfr
        · exact hqout j hj hxq hxin
        · have hji : i ≠ j := fun he => hi (he.symm ▸ hj)
          exact disjoint_left.mp (hdisj hji)
            ((hΔ i).isCompact.isClosed.frontier_subset hxfr) (interior_subset hxin)
  obtain ⟨q, hqN, hqout⟩ := hex Finset.univ
  refine ⟨q, ?_, ?_⟩
  · intro x hx
    by_cases hxD : x ∈ ⋃ i, Δ i
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxD
      apply mem_discComplement_of_mem_frontier Δ (fun i => (hΔ i).isCompact.isClosed) hdisj hxi
      rw [(hΔ i).isCompact.isClosed.frontier_eq]
      exact ⟨hxi, hqout i (Finset.mem_univ i) hx⟩
    · exact subset_closure hxD
  · rintro x ⟨hx, hxU⟩
    rcases hqN hx with hxnot | hxV
    · exact (hxnot hxU).elim
    · exact hxV

end GraphMinor.GM12
