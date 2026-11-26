/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73MetricVisits
public import LeanPool.GraphMinor.GM12.Section73ComparisonConstruction
import LeanPool.GraphMinor.GM12.Section73SharedAtoms
import LeanPool.GraphMinor.GM12.Section1
import LeanPool.GraphMinor.GM12.Section4WalkMetric
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM11.Theorem66

/-!
# The metric bounds after radial contraction

For XII (7.3), page 262, apply the bounded-visit witnesses to the
new radial metric. The actual walk comparison from the star
contraction transfers the two atoms outside the merged region
to the old inside. Two hub visits add at most four to the walk
length, and one adds at most two. Dividing the old metric walk
bound by two gives the losses two and one. Distances near the
new order are handled by the old metric's order bound.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM14 GM10 Hypergraph

/-- The reduced radial construction gives the star contraction `(D, f, H, J)`,
the derived slope `ins'`, and both metric bounds of XII (7.3), pages 261--262. -/
theorem exists_starContraction_with_vertex_deletion_bounds_of_unique_spokes
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsRespectfulDrawingTangle Γ θ T)
    {ins : Drawing S → Set S}
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V)
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell)
    (hE' : (deleteVertices Γ {v}).E.Nonempty)
    (hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g)
    {r : Set S} (hr : r ∈ (deleteVertices Γ {v}).R) (hvr : v ∈ r) :
    ∃ (D : Set S) (f : C(S, S)) (H J : Drawing S) (ins' : Drawing S → Set S),
      IsStarContraction K v r D f H J ∧
      (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsRadialDrawing J ∧
      IsDerivedSlope (PaintingOrDrawing.drawing (deleteVertices Γ {v})) J (θ - 1)
        (deleteVerticesTangle Γ.toHypergraph {v} T θ) ins' ∧
      HasTangleMetric (deleteVertices Γ {v}) (θ - 1)
        (deleteVerticesTangle Γ.toHypergraph {v} T θ)
        (tangleMetric (deleteVertices Γ {v}) J ins' (θ - 1)) ∧ v ∈ J.V ∧
      (∀ a ∈ Γ.A ∩ (deleteVertices Γ {v}).A,
        ∀ b ∈ Γ.A ∩ (deleteVertices Γ {v}).A,
          tangleMetric Γ K ins θ a b ≤
            tangleMetric (deleteVertices Γ {v}) J ins' (θ - 1) a b + 2) ∧
      (∀ a ∈ Γ.A ∩ (deleteVertices Γ {v}).A,
          tangleMetric Γ K ins θ a {v} ≤
            tangleMetric (deleteVertices Γ {v}) J ins' (θ - 1) a r + 1) := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨D, f, H, J, ins', hc, hJ, hins', hm, hvJ, hcomp⟩ :=
    exists_starContraction_with_vertex_deletion_walk_comparison
      hS hθ hT hins hK hE hv htwo hE' hunique hr hvr
  let d' := tangleMetric (deleteVertices Γ {v}) J ins' (θ - 1)
  have hpret' := GM11.IsTangle.isPretangle hm.1.2.1
  have hs' := GM14.isSlope_of_derived (Γ := PaintingOrDrawing.drawing (deleteVertices Γ {v}))
    (Γ' := J) hS hpret' hJ.2.1.1 hins'
  have htransfer : ∀ (a : Set S), a ∈ Γ.A ∩ (deleteVertices Γ {v}).A →
      ∀ (p : S) (W : GraphWalk J.toGraph p p) (W' : GraphWalk K.toGraph p p),
      W.length < 2 * (θ - 1) → insWalk ins' J W ⊆ insWalk ins K W' ∪ r →
      W'.length < 2 * θ → ∀ a', IsCorrespondingAtom (deleteVertices Γ {v}) J a a' →
      a' ⊆ insWalk ins' J W → ∀ a₀, IsCorrespondingAtom Γ K a a₀ →
      a₀ ⊆ insWalk ins K W' := by
    intro a ha p W W' hW hinc hW' a' hca' haW a₀ hca
    have hmeet := (corresponding_atom_subset_iff hS hJ hins' hca' W hW).mp haW
    have hdis := shared_atom_disjoint_deleted_region hv htwo hr hvr ha
    apply (corresponding_atom_subset_iff hS hK hins hca W' hW').mpr
    obtain ⟨x, hxa, hxW⟩ := hmeet
    exact ⟨x, hxa, (hinc hxW).resolve_right (fun hxr => disjoint_left.mp hdis hxa hxr)⟩
  refine ⟨D, f, H, J, ins', hc, hJ, hins', hm, hvJ, ?_, ?_⟩
  · intro a ha b hb
    change _ ≤ d' a b + 2
    by_cases hab : a = b
    · subst b
      simp only [tangleMetric, ite_true, Nat.zero_le]
    have hold := tangleMetric_le_order hK ins θ a b
    by_cases hnear : θ ≤ d' a b + 2
    · exact hold.trans hnear
    have hlt : d' a b < θ - 1 := by omega
    obtain ⟨p, W, a', b', hca', hcb', hlen, hshort, haW, hbW, hcount⟩ :=
      exists_tangleMetric_walk_with_two_visit_bound hS hJ hs' hab hlt
    obtain ⟨W', hWlen, hinc, _⟩ := hcomp p W hshort
    have hc := hcount v
    have hWshort : W'.length < 2 * θ := by change W.length ≤ 2 * d' a b at hlen; omega
    obtain ⟨a₀, hca, _⟩ := existsUnique_correspondingAtom' hK ha.1
    obtain ⟨b₀, hcb, _⟩ := existsUnique_correspondingAtom' hK hb.1
    have haW' := htransfer a ha p W W' hshort hinc hWshort a' hca' haW a₀ hca
    have hbW' := htransfer b hb p W W' hshort hinc hWshort b' hcb' hbW b₀ hcb
    have hbound := two_mul_tangleMetric_le_walk_length hK hca hcb W' hWshort haW' hbW'
    change W.length ≤ 2 * d' a b at hlen
    omega
  · intro a ha
    change _ ≤ d' a r + 1
    have hold := tangleMetric_le_order hK ins θ a {v}
    by_cases hnear : θ ≤ d' a r + 1
    · exact hold.trans hnear
    have hlt : d' a r < θ - 1 := by omega
    have hdis := shared_atom_disjoint_deleted_region hv htwo hr hvr ha
    have har : a ≠ r := by
      intro heq
      exact disjoint_left.mp hdis (heq.symm ▸ hvr) hvr
    have hcor : IsCorrespondingAtom (deleteVertices Γ {v}) J r {v} :=
      ⟨Or.inr hr, Or.inl (Or.inl ⟨v, hvJ, rfl⟩),
        Or.inr (Or.inr ⟨hr, v, ⟨hvJ, hvr⟩, rfl⟩)⟩
    obtain ⟨p, W, a', hca', hlen, hshort, haW, hvW, hcount⟩ :=
      exists_tangleMetric_walk_with_one_point_visit_bound hS hJ hs' hcor har hlt
    obtain ⟨W', hWlen, hinc, hhub⟩ := hcomp p W hshort
    have hWshort : W'.length < 2 * θ := by change W.length ≤ 2 * d' a r at hlen; omega
    obtain ⟨a₀, hca, _⟩ := existsUnique_correspondingAtom' hK ha.1
    have haW' := htransfer a ha p W W' hshort hinc hWshort a' hca' haW a₀ hca
    have hcv : IsCorrespondingAtom Γ K {v} {v} :=
      ⟨Or.inl (Or.inl ⟨v, hv, rfl⟩),
        Or.inl (Or.inl ⟨v, hK.2.1.2.1 hv, rfl⟩), Or.inl ⟨v, hv, rfl, rfl⟩⟩
    have hbound := two_mul_tangleMetric_le_walk_length hK hca hcv W' hWshort haW'
      (singleton_subset_iff.mpr (hhub hvW))
    change W.length ≤ 2 * d' a r at hlen
    omega

/-- The reduced radial construction gives both metric bounds of
XII (7.3), pages 261--262. The old spoke uniqueness condition is
supplied by the selected-disc reduction before this construction. -/
theorem exists_metric_with_vertex_deletion_bounds_of_unique_spokes
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsRespectfulDrawingTangle Γ θ T)
    {ins : Drawing S → Set S}
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V)
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell)
    (hE' : (deleteVertices Γ {v}).E.Nonempty)
    (hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g)
    {r : Set S} (hr : r ∈ (deleteVertices Γ {v}).R) (hvr : v ∈ r) :
    ∃ d' : Set S → Set S → ℕ,
      HasTangleMetric (deleteVertices Γ {v}) (θ - 1)
        (deleteVerticesTangle Γ.toHypergraph {v} T θ) d' ∧
      (∀ a ∈ Γ.A ∩ (deleteVertices Γ {v}).A,
        ∀ b ∈ Γ.A ∩ (deleteVertices Γ {v}).A,
          tangleMetric Γ K ins θ a b ≤ d' a b + 2) ∧
      (∀ a ∈ Γ.A ∩ (deleteVertices Γ {v}).A,
          tangleMetric Γ K ins θ a {v} ≤ d' a r + 1) := by
  obtain ⟨_, _, _, J, ins', _, _, _, hm, _, hi, hii⟩ :=
    exists_starContraction_with_vertex_deletion_bounds_of_unique_spokes
      hS hθ hT hins hK hE hv htwo hE' hunique hr hvr
  exact ⟨tangleMetric (deleteVertices Γ {v}) J ins' (θ - 1), hm, hi, hii⟩

end GraphMinor.GM12
