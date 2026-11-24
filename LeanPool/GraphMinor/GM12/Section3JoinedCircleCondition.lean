/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3SelectedSmallDisc
import LeanPool.GraphMinor.GM12.Section3JoinedCircleLoops
import LeanPool.GraphMinor.GM11.OArcCircuit

/-!
# The joined-circle condition in XII (3.2)

For condition (3.1)(ii), traverse the two circles and the line
joining them, using the line in both directions. If their union
has at most N drawing vertices, the curve has length at most 2N.
Claim (1) then forces the enclosed prescribed discs to agree,
contradicting disjointness of the two enclosing discs.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 GM14

/-- Condition (3.1)(ii) in the proof of XII (3.2), page 246. -/
theorem joined_circle_vertex_count_gt
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ η : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    (hη : η ≤ θ) (Δ r : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι) (hr : ∀ i, r i ∈ Γ.R)
    (hrΔ : ∀ i, (r i ∩ Δ i).Nonempty)
    (hsep : ∀ i j, i ≠ j → η ≤ tangleMetric Γ K ins θ (r i) (r j))
    {N : ℕ} (hN : 2 * N < η) {A B P D E : Set S} {u v : S}
    (hn : Γ.IsNormal (A ∪ B ∪ P)) (hA : IsOArc A) (hB : IsOArc B)
    (hP : IsLineWithEnds P u v) (hu : u ∈ A) (hv : v ∈ B)
    (hPA : P ∩ A = {u}) (hPB : P ∩ B = {v})
    (hstar : A ∪ B ∪ P ⊆ discComplement Δ) (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hbD : discBd D = A) (hbE : discBd E = B) (hdis : Disjoint D E)
    (hi : ∃ i, ∀ l, Δ l ⊆ D ↔ l = i) (hj : ∃ j, ∀ l, Δ l ⊆ E ↔ l = j) :
    N < (Γ.V ∩ (A ∪ B ∪ P)).ncard := by
  by_contra hlarge
  have hsmall := Nat.le_of_not_gt hlarge
  have hNη : N < η := (Nat.le_mul_of_pos_left N (by decide : 0 < 2)).trans_lt hN
  have hAfin : (Γ.V ∩ (A ∪ B ∪ P)).Finite := Γ.finite_V.inter_of_left _
  have hAlen : (Γ.V ∩ A).ncard < η :=
    (Set.ncard_le_ncard (inter_subset_inter_right Γ.V (subset_union_left.trans subset_union_left))
      hAfin).trans_lt
      (hsmall.trans_lt hNη)
  have hBlen : (Γ.V ∩ B).ncard < η :=
    (Set.ncard_le_ncard (inter_subset_inter_right Γ.V (subset_union_right.trans subset_union_left))
      hAfin).trans_lt
      (hsmall.trans_lt hNη)
  obtain ⟨i, hi⟩ := hi
  obtain ⟨j, hj⟩ := hj
  have honeD : ∀ k l, Δ k ⊆ D → Δ l ⊆ D → k = l := by
    intro k l hk hl
    exact (hi k).mp hk |>.trans ((hi l).mp hl).symm
  have honeE : ∀ k l, Δ k ⊆ E → Δ l ⊆ E → k = l := by
    intro k l hk hl
    exact (hj k).mp hk |>.trans ((hj l).mp hl).symm
  have hmD := small_disc_is_selected_of_at_most_one_prescribed_disc hS hT hrespect hK hd
    hη Δ r hΔ hcase hr hrΔ hsep hA (fun _ hx => hn ⟨Or.inl (Or.inl hx.1), hx.2⟩) hAlen
    (subset_union_left.trans (subset_union_left.trans hstar)) hD hbD honeD
  have hmE := small_disc_is_selected_of_at_most_one_prescribed_disc hS hT hrespect hK hd
    hη Δ r hΔ hcase hr hrΔ hsep hB (fun _ hx => hn ⟨Or.inl (Or.inr hx.1), hx.2⟩) hBlen
    (subset_union_right.trans (subset_union_left.trans hstar)) hE hbE honeE
  have hAB : Disjoint A B := hdis.mono (hbD ▸ Surface.discBd_subset D)
    (hbE ▸ Surface.discBd_subset E)
  obtain ⟨φ, hφ, hrange, hlen⟩ := exists_short_curve_covering_joined_circles hA hB hP
    hAB hu hv hPA hPB hn
  have hlenη : curveLength Γ φ < η :=
    hlen.trans_lt ((Nat.mul_le_mul_left 2 hsmall).trans_lt hN)
  have hsubD : subBd D = A := (subBd_eq_frontier D).trans
    ((IsClosedDisc.frontier_eq_discBd hS hD).trans hbD)
  have hsubE : subBd E = B := (subBd_eq_frontier E).trans
    ((IsClosedDisc.frontier_eq_discBd hS hE).trans hbE)
  have hij := short_curve_enclosing_discs_indices_eq hS hT hrespect hK hd hη Δ r hr hrΔ hsep
    hφ hlenη hA hB (subset_union_left.trans (subset_union_left.trans hrange.symm.subset))
    (subset_union_right.trans (subset_union_left.trans hrange.symm.subset)) hD hE hsubD hsubE hmD
      hmE
    ((hi i).mpr rfl) ((hj j).mpr rfl)
  obtain ⟨x, _, hx⟩ := hrΔ i
  exact Set.disjoint_left.mp hdis ((hi i).mpr rfl hx) ((hj i).mpr hij hx)

end GraphMinor.GM12
