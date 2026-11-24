/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section77
public import LeanPool.GraphMinor.GM12.Section7
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM11.Section91
import LeanPool.GraphMinor.GM12.Section4WalkMetric

/-!
# Restricting the radial inside function in XII (7.2)

On page 260 a radial drawing of the reduced drawing is chosen as a
subdrawing of the original radial drawing. Every one of its short
circuits is therefore an old circuit. Intersect the separation of its
selected disc with the reduced drawing. This proves that the old
inside function is a derived inside function for the restricted
tangle. Lifting a walk through the subdrawing does not change either
its drawing or its inside.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM14

/-- The old inside function remains derived for the restricted tangle
on a radial subdrawing, as used in XII (7.2), page 260. -/
theorem derivedSlope_restrict_subdrawing
    {S : Type*} [TopologicalSpace S] {Γ Γ' K K' : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S}
    (hΓ : Γ'.IsSubdrawing Γ) (hK : K'.IsSubdrawing K)
    (hd : IsDerivedSlope (.drawing Γ) K θ T ins) :
    IsDerivedSlope (.drawing Γ') K' θ (restrictTangle T Γ'.toHypergraph) ins := by
  intro C hC hCK' hlen
  obtain ⟨hD, hbd, hm⟩ := hd C hC (hCK'.trans hK) hlen
  refine ⟨hD, hbd, ?_⟩
  have hm' : (((PaintingOrDrawing.drawing Γ).inter (ins C)) ∩ Γ'.toHypergraph,
      ((PaintingOrDrawing.drawing Γ).interOutside (ins C)) ∩ Γ'.toHypergraph) ∈
      restrictTangle T Γ'.toHypergraph := ⟨_, _, hm, rfl⟩
  rwa [drawing_inter_inter_subdrawing hΓ, drawing_interOutside_inter_subdrawing hΓ] at hm'

/-- Lifting a closed walk through a subdrawing preserves its point
set, its length, and its inside. This is the walk comparison in
XII (7.2), page 260. -/
theorem exists_lifted_walk_same_inside
    {S : Type*} [TopologicalSpace S] [T1Space S] {K K' : Drawing S}
    (hK : K'.IsSubdrawing K) (ins : Drawing S → Set S) {v : S}
    (W : GraphWalk K'.toGraph v v) :
    ∃ X : GraphWalk K.toGraph v v, X.length = W.length ∧
      walkDrawing K X = walkDrawing K' W ∧ insWalk ins K X = insWalk ins K' W := by
  obtain ⟨X, hV, hE⟩ := hK.exists_walk_up W
  have hdraw : walkDrawing K X = walkDrawing K' W := by
    apply Drawing.ext_of_V_E
    · rw [walkDrawing_V, walkDrawing_V, hV]
    · rw [walkDrawing_E, walkDrawing_E, hE]
  exact ⟨X, congrArg List.length hE, hdraw, congrArg (insOf ins) hdraw⟩

/-- Passing to a radial subdrawing cannot decrease distance between
atoms shared by the old and reduced drawings. This proves the walk
comparison used for XII (7.2)(i), page 260. -/
theorem tangleMetric_le_of_radial_subdrawing
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ Γ' K K' : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S}
    (hΓ : Γ'.IsSubdrawing Γ) (hKK : K'.IsSubdrawing K)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hK' : (PaintingOrDrawing.drawing Γ').IsRadialDrawing K')
    (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    {a b : Set S} (ha : a ∈ Γ.A) (hb : b ∈ Γ.A) :
    tangleMetric Γ K ins θ a b ≤ tangleMetric Γ' K' ins θ a b := by
  classical
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  by_cases hab : a = b
  · subst b
    simp only [tangleMetric, ↓reduceIte, le_refl]
  rcases GM11.tangleMetric_cases hK'.2.1 hab with hfull | ⟨_, hw⟩
  · rw [hfull]
    exact tangleMetric_le_order hK ins θ a b
  · obtain ⟨v, W, a', b', hca', hcb', hshort, hlen, haW, hbW⟩ := hw
    have hd' := derivedSlope_restrict_subdrawing hΓ hKK hd
    have hameet := (corresponding_atom_subset_iff hS hK' hd' hca' W hshort).mp haW
    have hbmeet := (corresponding_atom_subset_iff hS hK' hd' hcb' W hshort).mp hbW
    obtain ⟨X, hXlen, _, hinside⟩ := exists_lifted_walk_same_inside hKK ins W
    have hXshort : X.length < 2 * θ := hXlen ▸ hshort
    obtain ⟨a₀, hca, _⟩ := existsUnique_correspondingAtom' hK ha
    obtain ⟨b₀, hcb, _⟩ := existsUnique_correspondingAtom' hK hb
    have haX : a₀ ⊆ insWalk ins K X :=
      (corresponding_atom_subset_iff hS hK hd hca X hXshort).mpr (hinside.symm ▸ hameet)
    have hbX : b₀ ⊆ insWalk ins K X :=
      (corresponding_atom_subset_iff hS hK hd hcb X hXshort).mpr (hinside.symm ▸ hbmeet)
    exact tangleMetric_le_of_walk hca hcb X hXshort (hXlen.trans hlen) haX hbX

/-- If the old region and the merged region retain the same radial
hub, their distances from an old atom satisfy the comparison in
XII (7.2)(ii), page 260. -/
theorem tangleMetric_region_le_of_radial_subdrawing
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ Γ' K K' : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S}
    (hΓ : Γ'.IsSubdrawing Γ) (hKK : K'.IsSubdrawing K)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hK' : (PaintingOrDrawing.drawing Γ').IsRadialDrawing K')
    (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    {a r r' : Set S} (ha : a ∈ Γ.A) (hr : r ∈ Γ.R) (hr' : r' ∈ Γ'.R)
    {u : S} (hur : u ∈ r) (hur' : u ∈ r') (huK' : u ∈ K'.V) :
    tangleMetric Γ K ins θ a r ≤ tangleMetric Γ' K' ins θ a r' := by
  classical
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  by_cases har' : a = r'
  · have har : a = r := atom_eq_of_inter_nonempty ha (Or.inr hr)
      ⟨u, har'.symm ▸ hur', hur⟩
    rw [har]
    simp only [tangleMetric, ↓reduceIte, Nat.zero_le]
  rcases GM11.tangleMetric_cases hK'.2.1 har' with hfull | ⟨_, hw⟩
  · rw [hfull]
    exact tangleMetric_le_order hK ins θ a r
  · obtain ⟨v, W, a', b', hca', hcb', hshort, hlen, haW, hbW⟩ := hw
    have hd' := derivedSlope_restrict_subdrawing hΓ hKK hd
    have hcr' : IsCorrespondingAtom Γ' K' r' {u} :=
      ⟨Or.inr hr', Or.inl (Or.inl ⟨u, huK', rfl⟩),
        Or.inr (Or.inr ⟨hr', u, ⟨huK', hur'⟩, rfl⟩)⟩
    have hrameet := (corresponding_atom_subset_iff hS hK' hd' hcb' W hshort).mp hbW
    have huW : u ∈ insWalk ins K' W :=
      ((corresponding_atom_subset_iff hS hK' hd' hcr' W hshort).mpr hrameet) rfl
    have hameet := (corresponding_atom_subset_iff hS hK' hd' hca' W hshort).mp haW
    obtain ⟨X, hXlen, _, hinside⟩ := exists_lifted_walk_same_inside hKK ins W
    have hXshort : X.length < 2 * θ := hXlen ▸ hshort
    obtain ⟨a₀, hca, _⟩ := existsUnique_correspondingAtom' hK ha
    have hcr : IsCorrespondingAtom Γ K r {u} :=
      ⟨Or.inr hr, Or.inl (Or.inl ⟨u, hKK.1 huK', rfl⟩),
        Or.inr (Or.inr ⟨hr, u, ⟨hKK.1 huK', hur⟩, rfl⟩)⟩
    have haX : a₀ ⊆ insWalk ins K X :=
      (corresponding_atom_subset_iff hS hK hd hca X hXshort).mpr (hinside.symm ▸ hameet)
    have huX : ({u} : Set S) ⊆ insWalk ins K X :=
      singleton_subset_iff.mpr (hinside.symm ▸ huW)
    exact tangleMetric_le_of_walk hca hcr X hXshort (hXlen.trans hlen) haX huX

end GraphMinor.GM12
