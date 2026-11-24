/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4EndPartition
import LeanPool.GraphMinor.GM12.Section4DrawingControl
import LeanPool.GraphMinor.GM11.CitedResults

/-!
# Using the prescribed end classes as minor branches

XII (4.3), page 251, applies (3.2) with the classes defined
by the oriented target edges. Each selected edge then joins its
two assigned branches. Since every target vertex has two distinct
incident edges, each branch contains ends of two distant selected
edges. The connected-branch estimate verifies control.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM10 GM11 GM14 Hypergraph

/-- The assembly following the application of (3.2) in XII (4.3),
page 251, with finite vertex and edge labels. -/
theorem controlsMinor_of_end_partition
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ k p t : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d)
    (L : Graph (Fin p) (Fin t)) (f : Fin t → Set S) (a b : Fin t → S)
    (κ : Fin t × Bool → Fin p)
    (hl : ∀ i, Γ.toGraph.IsLink (f i) (a i) (b i))
    (hsep : ∀ i j, i ≠ j → k + 4 ≤ d (f i) (f j))
    (hloopless : ∀ e v, ¬ L.IsLink e v v)
    (hassign : ∀ e u v, L.IsLink e u v →
      (κ (e, true) = u ∧ κ (e, false) = v) ∨
        (κ (e, true) = v ∧ κ (e, false) = u))
    (htwo : ∀ v ∈ L.vertexSet, ∃ i j, i ≠ j ∧
      ∃ c d : Bool, κ (i, c) = v ∧ κ (j, d) = v)
    (hpθ : p ≤ θ) (hpk : 2 * p ≤ k)
    (H : Fin p → Drawing S)
    (hHs : ∀ v, (H v).IsSubdrawing Γ) (hconn : ∀ v, IsConnectedDrawing (H v))
    (hdisj : ∀ u v, u ≠ v → Disjoint (H u).V (H v).V)
    (hclass : ∀ v, (H v).V ∩ range (fun q : Fin t × Bool => if q.2 then a q.1 else b q.1) =
      edgeEndClass (fun q : Fin t × Bool => if q.2 then a q.1 else b q.1) κ v) :
    ControlsMinor Γ.toHypergraph θ T L := by
  let ends : Fin t × Bool → S := fun q => if q.2 then a q.1 else b q.1
  have hmem : ∀ q, ends q ∈ (H (κ q)).V := by
    intro q
    have hx : ends q ∈ edgeEndClass ends κ (κ q) := ⟨q, rfl, rfl⟩
    rw [← hclass (κ q)] at hx
    exact hx.1
  have hmem' : ∀ q v, κ q = v → ends q ∈ (H v).V := by
    intro q v h
    exact h ▸ hmem q
  have hcl : ∀ q, ends q ∈ closure (f q.1) := by
    intro ⟨i, c⟩
    have ha : a i ∈ closure (f i) ∩ Γ.V := by rw [(hl i).2.2.2]; simp
    have hb : b i ∈ closure (f i) ∩ Γ.V := by rw [(hl i).2.2.2]; simp
    cases c
    · exact hb.1
    · exact ha.1
  have h91 := GM11.gm15_theorem_9_1 Γ θ T d hS inferInstance hm
  have hfA : ∀ i, f i ∈ Γ.A := fun i => Or.inl (Or.inr (hl i).edge_mem)
  have hinj : ∀ e ∈ L.edgeSet, ∀ g ∈ L.edgeSet, e ≠ g → f e ≠ f g := by
    intro e _ g _ hne heq
    have hdist := hsep e g hne
    rw [heq, h91.2.1 (f g) (hfA g)] at hdist
    omega
  have hcard : L.vertexSet.ncard ≤ p := by
    exact (Set.ncard_le_card L.vertexSet).trans_eq (Nat.card_fin p)
  refine controlsMinor_of_connecting_drawings hS hm H f (fun v _ => hHs v)
    (fun v _ => hconn v) (fun u _ v _ hne => hdisj u v hne) ?_ hloopless hinj
    (hcard.trans hpθ) ((Nat.mul_le_mul_left 2 hcard).trans hpk) ?_
  · intro e u v he
    rcases hassign e u v he with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · exact ⟨a e, hmem' (e, true) u hu, b e, hmem' (e, false) v hv, hl e⟩
    · exact ⟨b e, hmem' (e, false) u hu, a e, hmem' (e, true) v hv, (hl e).symm⟩
  · intro v hv
    obtain ⟨i, j, hij, c, d, hic, hjd⟩ := htwo v hv
    exact ⟨f i, f j, ends (i, c), ends (j, d), (hl i).edge_mem, (hl j).edge_mem,
      hmem' (i, c) v hic, hmem' (j, d) v hjd, hcl (i, c), hcl (j, d), hsep i j hij⟩

end GraphMinor.GM12
