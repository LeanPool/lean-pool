/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73DiscOrientation
public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.Epstein
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.Section7
import LeanPool.GraphMinor.GM16.SphereRespectful

/-!
# Respectfulness of the deleted tangle

For XII (7.3), page 261, representativity supplies a disc bounded
by every short normal circle. On a nonspherical surface the
orientation argument selects this disc in the deleted tangle.
On the sphere the tangle axiom selects one of the two discs.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 GM14 Hypergraph

/-- Complete the disc-selection argument of XII (7.3), page 261,
once representativity of the deleted drawing has been proved. -/
theorem isRespectful_after_vertex_deletion_of_representative
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsRespectfulDrawingTangle Γ θ T) {v : S} (hv : v ∈ Γ.V)
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell)
    (hrep : (deleteVertices Γ {v}).IsRepresentative (θ - 1)) :
    IsRespectfulDrawingTangle (deleteVertices Γ {v}) (θ - 1)
      (deleteVerticesTangle Γ.toHypergraph {v} T θ) := by
  have hnew := theorem_7_3_tangle hθ hT.2.1 hv
  refine ⟨htwo, hnew, ?_⟩
  by_cases hsphere : IsSphere S
  · exact GM16.drawing_tangle_isRespectful_of_isSphere hS hsphere _ hnew
  · refine ⟨inferInstance, ?_⟩
    intro F hF hn hcard
    have hnull := hrep.2 F hF hn hcard
    have hSurface : IsSurface S := ⟨hS.1, hS.2.1, fun x => (hS.2.2 x).isManifoldPoint⟩
    have hbd : Disjoint F (bd S) := disjoint_left.mpr fun x _ hx => hx (hS.2.2 x)
    obtain ⟨D, _, hD, hDF⟩ := epstein_first hSurface hF (subset_univ F) hbd hnull
    have hfront : frontier D = F := (IsClosedDisc.frontier_eq_discBd hS hD).trans hDF
    have hnormal : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsNormal
        (frontier D) := hfront.symm ▸ hn
    have hcount : (frontier D ∩ (deleteVertices Γ {v}).V).ncard < θ - 1 :=
      hfront.symm ▸ hcard
    exact ⟨D, hD, (subBd_eq_frontier D).trans hfront,
      disc_orientation_after_vertex_deletion hS hsphere hθ hT hv hD hnormal hcount⟩

end GraphMinor.GM12
