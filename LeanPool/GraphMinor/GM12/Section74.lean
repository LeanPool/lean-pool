/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section76
import LeanPool.GraphMinor.GM12.Section74Base
import LeanPool.GraphMinor.GM12.Section74BaseCellularity
import LeanPool.GraphMinor.GM12.Section74Induction

/-!
# Graph Minors XII, (7.4)

A respectful tangle survives deletion of a vertex in a two-cell
component, with the four distance and point-set bounds on pages
262--263. We follow the paper's induction on the number of edges.
If a selected normal one-vertex disc contains an edge, apply
(7.2), use the induction hypothesis outside the disc, and transfer
all four conclusions back. Otherwise distinct corner regions,
finite edge gluing, and final leaf deletion show that deleting
the vertex is two-cell. Apply (7.3), with the local bounds for
the removed atoms, in that base case.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 GM14

/-- Graph Minors XII, (7.4), pages 262--263. Vertex deletion has
a two-cell component with a respectful tangle of order one less,
shared-atom distances decreasing by at most two, and distance
to its region of the deleted vertex decreasing by at most one.
All original atoms contained in that region have old distance
at most two from the deleted vertex. The component condition
uses the connected components of the drawing's point set. -/
theorem theorem_7_4_proof
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hθ : 2 ≤ θ) (hd : HasTangleMetric Γ θ T d)
    {v : S} (hv : v ∈ Γ.V) :
    ∃ (Γ' : Drawing S) (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ) (r : Set S),
      Γ'.IsSubdrawing (deleteVertices Γ {v}) ∧
      Γ'.U ∈ componentsIn (deleteVertices Γ {v}).U ∧
      HasTangleMetric Γ' (θ - 1) T' d' ∧ r ∈ Γ'.R ∧ v ∈ r ∧
      Γ.U ⊆ Γ'.U ∪ r ∧
      (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 2 ≤ d' a b) ∧
      (∀ a ∈ Γ.A ∩ Γ'.A, d a {v} - 1 ≤ d' a r) ∧
      (∀ a ∈ Γ.A, a ⊆ r → d a {v} ≤ 2) := by
  induction hn : Γ.E.ncard using Nat.strong_induction_on generalizing Γ T d with
  | ind n ih =>
    by_cases hex : ∃ (D F : Set S), IsClosedDisc D ∧ IsOArc F ∧ subBd D = F ∧
        (PaintingOrDrawing.drawing Γ).IsNormal F ∧ F ∩ Γ.V = {v} ∧
        ((PaintingOrDrawing.drawing Γ).inter D, (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T ∧
        ∃ e ∈ Γ.E, e ⊆ D
    · obtain ⟨D, F, hD, hF, hbd, hnF, hFV, hm, e, he, heD⟩ := hex
      apply theorem_7_4_disc_induction hS hθ hd hv ?_ hD hF hbd hnF hFV hm he heD
      intro Λ U δ hsmall hmetric hvΛ
      exact ih _ (by omega) hmetric hvΛ rfl
    · have hno : ∀ D F : Set S, IsClosedDisc D → IsOArc F → subBd D = F →
          (PaintingOrDrawing.drawing Γ).IsNormal F → F ∩ Γ.V = {v} →
          ((PaintingOrDrawing.drawing Γ).inter D, (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T
            →
          ∀ e ∈ Γ.E, ¬ e ⊆ D := by
        intro D F hD hF hbd hnF hFV hm e he heD
        exact hex ⟨D, F, hD, hF, hbd, hnF, hFV, hm, e, he, heD⟩
      exact theorem_7_4_of_twoCell_delete hS hθ hd hv
        (isTwoCell_delete_vertex_of_no_selected_edge hS hθ hd hv hno)

end GraphMinor.GM12
