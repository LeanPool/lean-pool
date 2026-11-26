/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72Respectful
public import LeanPool.GraphMinor.GM12.Section72LostAtoms
import LeanPool.GraphMinor.GM12.Section72RadialExists
import LeanPool.GraphMinor.GM12.Section72Slope

/-!
# Graph Minors XII, (7.2)

Restrict a respectful drawing tangle to the closed outside of its
selected disc bounded by a normal circle through one vertex. The
merged region is an open disc, and every lost atom is at distance at
most one from that vertex. Diversion proves respectfulness of the
restricted tangle. A radial subdrawing with the old region's hub
then gives both metric comparisons by lifting closed walks.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM14 Hypergraph

/-- Graph Minors XII, (7.2), pages 259–260. Deleting the selected
inside of a normal circle through one vertex preserves the order of
the respectful tangle. Distances between shared atoms, and distances
from shared atoms to the enlarged region, do not decrease. -/
theorem theorem_7_2_proof
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hθ : 2 ≤ θ) (hd : HasTangleMetric Γ θ T d)
    {D F r : Set S} {v : S} (hD : IsClosedDisc D) (hbd : subBd D = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) (hFV : F ∩ Γ.V = {v})
    (hr : r ∈ Γ.R) (hFr : F \ {v} ⊆ r)
    (hm : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T) :
    (PaintingOrDrawing.drawing (Γ.interSet (closure (univ \ D)))).IsTwoCell ∧
      (∀ a ∈ Γ.A \ (Γ.interSet (closure (univ \ D))).A, d a {v} ≤ 1) ∧
      ∃ (d' : Set S → Set S → ℕ) (r' : Set S),
        HasTangleMetric (Γ.interSet (closure (univ \ D))) θ
          (restrictTangle T (Γ.interSet (closure (univ \ D))).toHypergraph) d' ∧
        r' ∈ (Γ.interSet (closure (univ \ D))).R ∧ r ⊆ r' ∧
        (∀ a ∈ Γ.A ∩ (Γ.interSet (closure (univ \ D))).A,
          ∀ b ∈ Γ.A ∩ (Γ.interSet (closure (univ \ D))).A, d a b ≤ d' a b) ∧
        (∀ a ∈ Γ.A ∩ (Γ.interSet (closure (univ \ D))).A, d a r ≤ d' a r') := by
  let Γ' := Γ.interSet (closure (univ \ D))
  let Y := r ∪ (D \ {v})
  have hΓ : Γ'.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hrespect := theorem_7_2_respectful hS hθ hd hD hbd hn hFV hr hFr hm
  have hY : Y ∈ Γ'.R := theorem_7_2_region hS hD hbd hn hFV hr hFr
  have hvFV : v ∈ F ∩ Γ.V := hFV.symm ▸ mem_singleton v
  have hF : IsOArc F := by
    have hbF : discBd D = F := (IsClosedDisc.frontier_eq_discBd hS hD).symm.trans
      ((subBd_eq_frontier D).symm.trans hbd)
    exact hbF ▸ hD.isOArc_discBd
  have hT : IsPretangle Γ.toHypergraph θ T :=
    ⟨hd.1.2.1.one_le, hd.1.2.1.isSeparation, hd.1.2.1.order_lt,
      hd.1.2.1.axiom1, hd.1.2.1.axiom2⟩
  obtain ⟨K, ins, hK, hderived, hmetric⟩ := hd.2
  have hE : Γ.E.Nonempty := edgeSet_nonempty_of_isTangle_of_two_le hd.1.2.1 hθ
  obtain ⟨K', hK', hKK, u, hur, huK'⟩ := exists_radial_subdrawing_after_disc_deletion
    hS hT hθ hK hE hderived hF hvFV.1 hvFV.2 hr hFr hn hD hbd hm
  have hderived' := derivedSlope_restrict_subdrawing hΓ hKK hderived
  let d' := tangleMetric Γ' K' ins θ
  have hmetric' : HasTangleMetric Γ' θ (restrictTangle T Γ'.toHypergraph) d' :=
    ⟨hrespect, K', ins, hK', hderived', fun _ _ _ _ => rfl⟩
  refine ⟨hrespect.1, ?_, d', Y, hmetric', hY, subset_union_left, ?_, ?_⟩
  · intro a ha
    exact theorem_7_2_lost_atoms hS hθ hd hD hbd hn hFV hr hFr hm ha.1 ha.2
  · intro a ha b hb
    rw [hmetric a ha.1 b hb.1]
    exact tangleMetric_le_of_radial_subdrawing hS hΓ hKK hK hK' hderived ha.1 hb.1
  · intro a ha
    rw [hmetric a ha.1 r (Or.inr hr)]
    exact tangleMetric_region_le_of_radial_subdrawing hS hΓ hKK hK hK' hderived ha.1 hr hY
      hur (Or.inl hur) huK'

end GraphMinor.GM12
