/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3SelectedSmallDisc
import LeanPool.GraphMinor.GM12.Section3ThetaFaceIntersection
import LeanPool.GraphMinor.GM12.Section2NormalNoncover
import LeanPool.GraphMinor.GM11.Theorem66
import Mathlib.Tactic.FinCases

/-!
# The theta-face condition in XII (3.2)

Condition (3.1)(iv) follows by selecting all three face discs.
Their pairwise intersections are boundary arcs in the punctured
surface, so no face contains another prescribed disc. Claim (2)
selects the faces, while the theta-cover lemma says that they cover
the surface. The second tangle axiom excludes this cover.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM14

/-- Condition (3.1)(iv) in the proof of XII (3.2), page 246. -/
theorem theta_vertex_count_gt
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ η : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    (hη : η ≤ θ) (Δ r : Fin 3 → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hr : ∀ i, r i ∈ Γ.R)
    (hrΔ : ∀ i, (r i ∩ Δ i).Nonempty)
    (hsep : ∀ i j, i ≠ j → η ≤ tangleMetric Γ K ins θ (r i) (r j))
    {N : ℕ} (hN : N < η) (P D : Fin 3 → Set S) {a b : S}
    (hn : Γ.IsNormal (⋃ i, P i)) (hP : ∀ i, IsLineWithEnds (P i) a b)
    (hij : ∀ i j, i ≠ j → P i ∩ P j = {a, b})
    (hstar : (⋃ i, P i) ⊆ discComplement Δ)
    (hD : ∀ i, IsClosedDisc (D i))
    (hbd : ∀ i, discBd (D i) = ⋃ j : {j // j ≠ i}, P j.val)
    (hin : ∀ i, Δ i ⊆ D i) (hout : ∀ i, ¬ P i ⊆ D i) :
    N < (Γ.V ∩ ⋃ i, P i).ncard := by
  by_contra hlarge
  have hsmall := Nat.le_of_not_gt hlarge
  have hb0 : discBd (D 0) = P 1 ∪ P 2 := by
    rw [hbd]
    ext x
    simp [Fin.exists_fin_succ]
  have hb1 : discBd (D 1) = P 2 ∪ P 0 := by
    rw [hbd]
    ext x
    simp [Fin.exists_fin_succ, or_comm]
  have hb2 : discBd (D 2) = P 0 ∪ P 1 := by
    rw [hbd]
    ext x
    simp [Fin.exists_fin_succ]
  have hf0 := (IsClosedDisc.frontier_eq_discBd hS (hD 0)).trans hb0
  have hf1 := (IsClosedDisc.frontier_eq_discBd hS (hD 1)).trans hb1
  have hf2 := (IsClosedDisc.frontier_eq_discBd hS (hD 2)).trans hb2
  have hi01 := hij 0 1 (by decide)
  have hi12 := hij 1 2 (by decide)
  have hi20 := hij 2 0 (by decide)
  have h01 := theta_face_disc_intersection hS (hP 0) (hP 1) hi01 hi12 hi20
    (hD 0) (hD 1) hf0 hf1 (hout 0) (hout 1)
  have h12 := theta_face_disc_intersection hS (hP 1) (hP 2) hi12 hi20 hi01
    (hD 1) (hD 2) hf1 hf2 (hout 1) (hout 2)
  have h20 := theta_face_disc_intersection hS (hP 2) (hP 0) hi20 hi01 hi12
    (hD 2) (hD 0) hf2 hf0 (hout 2) (hout 0)
  have hcap : ∀ i j, i ≠ j → D i ∩ D j ⊆ ⋃ k, P k := by
    intro i j hne
    fin_cases i <;> fin_cases j
    all_goals try exact False.elim (hne rfl)
    · change D 0 ∩ D 1 ⊆ _
      rw [h01]; exact subset_iUnion P 2
    · change D 0 ∩ D 2 ⊆ _
      rw [Set.inter_comm, h20]; exact subset_iUnion P 1
    · change D 1 ∩ D 0 ⊆ _
      rw [Set.inter_comm, h01]; exact subset_iUnion P 2
    · change D 1 ∩ D 2 ⊆ _
      rw [h12]; exact subset_iUnion P 0
    · change D 2 ∩ D 0 ⊆ _
      rw [h20]; exact subset_iUnion P 1
    · change D 2 ∩ D 1 ⊆ _
      rw [Set.inter_comm, h12]; exact subset_iUnion P 0
  have hone : ∀ i j, Δ j ⊆ D i → j = i := by
    intro i j hj
    by_contra hne
    obtain ⟨x, hx⟩ := (hΔ j).nonempty_discInt
    have hxC := hstar (hcap i j (Ne.symm hne) ⟨hj hx.1, hin j hx.1⟩)
    exact hx.2 (discComplement_inter_disc_subset_boundary hS Δ hΔ j ⟨hxC, hx.1⟩)
  have hbsub : ∀ i, discBd (D i) ⊆ ⋃ j, P j := by
    intro i
    rw [hbd]
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨j.val, hj⟩
  have hnorm : ∀ i, Γ.IsNormal (discBd (D i)) := fun i _ hx => hn ⟨hbsub i hx.1, hx.2⟩
  have hlen : ∀ i, (Γ.V ∩ discBd (D i)).ncard < η := by
    intro i
    exact (Set.ncard_le_ncard (inter_subset_inter_right Γ.V (hbsub i))
      (Γ.finite_V.inter_of_left _)).trans_lt (hsmall.trans_lt hN)
  have hm : ∀ i, ((PaintingOrDrawing.drawing Γ).inter (D i),
      (PaintingOrDrawing.drawing Γ).interOutside (D i)) ∈ T := by
    intro i
    exact small_disc_is_selected_of_at_most_one_prescribed_disc hS hT hrespect hK hd
      hη Δ r hΔ (Or.inr (by simp)) hr hrΔ hsep (hD i).isOArc_discBd (hnorm i) (hlen i)
      ((hbsub i).trans hstar) (hD i) rfl
      (fun j k hj hk => (hone i j hj).trans (hone i k hk).symm)
  have hcover := GM11.theta_cover hS (hP 0) (hP 1) (hP 2) hi01 hi12 hi20
    (hD 0) (hD 1) (hD 2) hf0 hf1 hf2 (hout 0) (hout 1) (hout 2)
  exact not_cover_of_normal_frontiers (Γ := PaintingOrDrawing.drawing Γ)
    (GM11.IsTangle.isPretangle hT)
    (hD 0).isCompact.isClosed (hD 1).isCompact.isClosed (hD 2).isCompact.isClosed
    (by rw [hf0, ← hb0]; exact hnorm 0)
    (by rw [hf1, ← hb1]; exact hnorm 1)
    (by rw [hf2, ← hb2]; exact hnorm 2) (hm 0) (hm 1) (hm 2) hcover

end GraphMinor.GM12
