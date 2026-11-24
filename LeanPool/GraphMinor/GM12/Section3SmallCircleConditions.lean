/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3SelectedSmallDisc
public import LeanPool.GraphMinor.GM12.Section3FreeBoundary

/-!
# The small-circle and free-boundary conditions of XII (3.1)

In the proof of XII (3.2), pages 246--247, respectfulness gives the
selected inside of a short normal circle. Claim (1) says that it
contains at most one prescribed disc, verifying (3.1)(i). For (v),
claim (2) selects a disc enclosing exactly one prescription, and
freeness bounds the boundary vertices by its separation order. If
the enclosing circle is not short, the total prescribed vertex bound
already proves the inequality. Choose the uniform threshold at least
that total bound when applying these lemmas.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 GM14 GM10

/-- Verification of XII (3.1)(i) in the proof of (3.2), page 246:
a normal circle with at most `N` drawing vertices bounds a disc
including at most one prescribed disc when `N < η`. -/
theorem small_circle_bounds_at_most_one_prescribed_disc
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ η N : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    (hη : η ≤ θ) (hN : N < η) (Δ r : ι → Set S) (hr : ∀ i, r i ∈ Γ.R)
    (hrΔ : ∀ i, (r i ∩ Δ i).Nonempty)
    (hsep : ∀ i j, i ≠ j → η ≤ tangleMetric Γ K ins θ (r i) (r j))
    {F : Set S} (hF : IsOArc F) (hn : Γ.IsNormal F) (hcount : (Γ.V ∩ F).ncard ≤ N) :
    ∃ D : Set S, IsClosedDisc D ∧ discBd D = F ∧
      ∀ i j, Δ i ⊆ D → Δ j ⊆ D → i = j := by
  have hshort : (Γ.V ∩ F).ncard < η := hcount.trans_lt hN
  have hlenθ : (F ∩ Γ.V).ncard < θ := by rw [Set.inter_comm]; exact hshort.trans_le hη
  obtain ⟨D, hD, hbd, hm⟩ := hrespect.2 F hF hn hlenθ
  refine ⟨D, hD, ?_, selected_disc_includes_at_most_one_prescribed_disc hS hT hrespect hK hd
    hη Δ r hr hrΔ hsep hF hn hshort hD hbd hm⟩
  exact (IsClosedDisc.frontier_eq_discBd hS hD).symm.trans ((subBd_eq_frontier D).symm.trans hbd)

/-- Verification of XII (3.1)(v) in the proof of (3.2), page 247.
Short enclosing circles are tangle-selected by claim (2), so freeness
bounds their vertex count. Long circles are covered by the total
prescribed boundary bound. -/
theorem free_boundary_count_le_of_enclosing_disc
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ η z : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    (hη : η ≤ θ) (hzη : z ≤ η) (Δ r : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι) (hr : ∀ i, r i ∈ Γ.R)
    (hrΔ : ∀ i, (r i ∩ Δ i).Nonempty)
    (hsep : ∀ i j, i ≠ j → η ≤ tangleMetric Γ K ins θ (r i) (r j))
    (hsmall : (discBoundaryVertices Γ Δ).ncard ≤ z)
    (hfree : ∀ i, IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ discBd (Δ i)))
    {F D : Set S} (hF : IsOArc F) (hn : Γ.IsNormal F) (hFstar : F ⊆ discComplement Δ)
    (hD : IsClosedDisc D) (hbd : discBd D = F) (i : ι)
    (hexact : ∀ j, Δ j ⊆ D ↔ j = i) :
    (Γ.V ∩ discBd (Δ i)).ncard ≤ (Γ.V ∩ F).ncard := by
  by_cases hshort : (Γ.V ∩ F).ncard < η
  · have hone : ∀ j k, Δ j ⊆ D → Δ k ⊆ D → j = k := by
      intro j k hj hk
      exact ((hexact j).mp hj).trans ((hexact k).mp hk).symm
    have hm := small_disc_is_selected_of_at_most_one_prescribed_disc hS hT hrespect hK hd
      hη Δ r hΔ hcase hr hrΔ hsep hF hn hshort hFstar hD hbd hone
    have hb := boundary_vertex_count_le_of_free_of_selected_disc hS hD
      ((hexact i).mpr rfl) (hfree i) hm
    simpa only [hbd] using hb
  · have hfinite : (discBoundaryVertices Γ Δ).Finite := Γ.finite_V.subset (by
      intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact hj.1)
    have hsub : Γ.V ∩ discBd (Δ i) ⊆ discBoundaryVertices Γ Δ :=
      fun _ hx => mem_iUnion.mpr ⟨i, hx⟩
    exact (Set.ncard_le_ncard hsub hfinite).trans
      (hsmall.trans (hzη.trans (le_of_not_gt hshort)))

end GraphMinor.GM12
