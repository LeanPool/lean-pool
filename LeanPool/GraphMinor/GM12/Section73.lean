/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM12.Section76
import LeanPool.GraphMinor.GM12.Section73MetricComparison
import LeanPool.GraphMinor.GM12.Section73VertexReduction
import LeanPool.GraphMinor.GM12.Section73NoParallel
import LeanPool.GraphMinor.GM12.Section73OrderOne
import LeanPool.GraphMinor.GM12.Section77
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.GM07.Section3

/-!
# Graph Minors XII, (7.3)

Deleting a vertex while preserving a two-cell drawing loses at
most two in shared-atom distances, and at most one in distance
to the deleted vertex's region. We follow the radial contraction
and lifted-walk proof on pages 261--262, using the visit bounds
from the proved construction of XI (9.2). First remove selected
one-vertex discs containing edges. This finite reduction corrects
the paper's parallel-spoke assertion and preserves all needed
old lower bounds. The reduced radial construction then proves
both inequalities. Original order two uses the order-one case.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 GM14 Hypergraph

/-- Graph Minors XII, (7.3), pages 261--262. A two-cell vertex
deletion has a respectful tangle of order one less, with shared
atom distances decreasing by at most two and distance to the
merged region decreasing by at most one. The finite selected-disc
reduction corrects the paper's assertion that the old
radial drawing has no parallel spokes at the vertex, which fails
when there is a contractible loop at the vertex. See the correction
to the proof of (7.3) in `corrections/GM12.md`. -/
theorem theorem_7_3_proof
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hθ : 2 ≤ θ) (hd : HasTangleMetric Γ θ T d)
    {v : S} (hv : v ∈ Γ.V)
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell) :
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ) (r : Set S),
      HasTangleMetric (deleteVertices Γ {v}) (θ - 1) T' d' ∧
      r ∈ (deleteVertices Γ {v}).R ∧ v ∈ r ∧
      (∀ a ∈ Γ.A ∩ (deleteVertices Γ {v}).A,
        ∀ b ∈ Γ.A ∩ (deleteVertices Γ {v}).A, d a b - 2 ≤ d' a b) ∧
      (∀ a ∈ Γ.A ∩ (deleteVertices Γ {v}).A, d a {v} - 1 ≤ d' a r) := by
  by_cases hθtwo : θ = 2
  · subst θ
    obtain ⟨d', r, hm, hr, hvr, hi, hii⟩ := theorem_7_3_order_two hS hd hv htwo
    exact ⟨_, d', r, hm, hr, hvr, hi, hii⟩
  have hθthree : 3 ≤ θ := by omega
  obtain ⟨Γ₀, T₀, d₀, hΓ₀, hv₀, hdelete, hd₀, hcomp₀, hno⟩ :=
    exists_vertex_reduction hS hθ hd hv htwo
  have htwo₀ : (PaintingOrDrawing.drawing (deleteVertices Γ₀ {v})).IsTwoCell :=
    hdelete.symm ▸ htwo
  obtain ⟨K, ins, hK, hins, heq⟩ := hd₀.2
  have hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g := by
    intro e he g hg u hel hgl
    by_contra heg
    have huK : u ∈ K.V := hel.2.2.1
    have hun : u ∉ Γ₀.V := (bipartite_of_preRadial hK.2.1 e v u hel).mp hv₀
    obtain ⟨r, hr, hur⟩ := hK.2.1.2.2.2.1 u ⟨huK, hun⟩
    exact no_parallel_spokes_of_no_selected_edge_inside hS hθ hd₀.1 hK.2.1 hv₀ htwo₀ hno
      he hg heg hr hur huK hel.2.2.2 hgl.2.2.2
  have hE : Γ₀.E.Nonempty := edgeSet_nonempty_of_isTangle_of_two_le hd₀.1.2.1 hθ
  have ht' := theorem_7_3_tangle hθ hd₀.1.2.1 hv₀
  have hE' : (deleteVertices Γ₀ {v}).E.Nonempty :=
    edgeSet_nonempty_of_isTangle_of_two_le ht' (by omega)
  have hvnot : v ∉ (deleteVertices Γ₀ {v}).U := by
    intro hvU
    have hvV := (isSubdrawing_U_inter_V (deleteVertices_isSubdrawing Γ₀ {v})).subset ⟨hvU, hv₀⟩
    exact ((deleteVertices_V Γ₀ {v}).subset hvV).2 rfl
  obtain ⟨r, hr, hvr⟩ := exists_region_of_notMem hvnot
  obtain ⟨d', hm, hi, hii⟩ := exists_metric_with_vertex_deletion_bounds_of_unique_spokes
    hS hθ hd₀.1 hins hK hE hv₀ htwo₀ hE' hunique hr hvr
  have hshared : ∀ a ∈ Γ.A ∩ (deleteVertices Γ {v}).A,
      a ∈ Γ₀.A ∩ (deleteVertices Γ₀ {v}).A := by
    intro a ha
    have ha' : a ∈ (deleteVertices Γ₀ {v}).A := hdelete.symm ▸ ha.2
    exact ⟨shared_atom_mem_intermediate hΓ₀ (deleteVertices_isSubdrawing Γ₀ {v}) ha.1 ha', ha'⟩
  refine ⟨_, d', r, hdelete ▸ hm, hdelete ▸ hr, hvr, ?_, ?_⟩
  · intro a ha b hb
    have ha₀ := hshared a ha
    have hb₀ := hshared b hb
    have hold := hcomp₀ a ⟨ha.1, ha₀.1⟩ b ⟨hb.1, hb₀.1⟩
    have hnew := hi a ha₀ b hb₀
    rw [← heq a ha₀.1 b hb₀.1] at hnew
    omega
  · intro a ha
    have ha₀ := hshared a ha
    have hvA : ({v} : Set S) ∈ Γ.A ∩ Γ₀.A :=
      ⟨Or.inl (Or.inl ⟨v, hv, rfl⟩), Or.inl (Or.inl ⟨v, hv₀, rfl⟩)⟩
    have hold := hcomp₀ a ⟨ha.1, ha₀.1⟩ {v} hvA
    have hnew := hii a ha₀
    rw [← heq a ha₀.1 {v} hvA.2] at hnew
    omega

end GraphMinor.GM12
