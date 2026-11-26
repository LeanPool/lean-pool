/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73FaceRefinement
public import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM11.RadialExists
import LeanPool.GraphMinor.GM11.RadialFacts
import LeanPool.GraphMinor.GM12.Section72MaximalCriterion
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# Maximality of the cleaned radial contraction

For XII (7.3), page 261, extend the cleaned pre-radial drawing to a
radial drawing using the finite spoke bound. If an edge was added,
it splits one old disc face into two regions of the extension. Each
new radial region contains an original drawing edge. Those edges
would lie in the same old face, contradicting the edge-uniqueness
condition retained during cleanup. Hence no edge was added.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A pre-radial drawing extends to a radial drawing. The finite
spoke bound gives a maximum edge count among its pre-radial
extensions. This is used for maximality in XII (7.3), page 261. -/
theorem exists_radial_extension
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ J : Drawing S}
    (htwo : (PaintingOrDrawing.drawing Γ).IsTwoCell)
    (hJ : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing J) :
    ∃ K : Drawing S, (PaintingOrDrawing.drawing Γ).IsRadialDrawing K ∧ J.IsSubdrawing K := by
  classical
  obtain ⟨N, hN⟩ := exists_spoke_bound_drawing htwo hS
  let A : Set ℕ := {n | ∃ K : Drawing S,
    (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K ∧ J.IsSubdrawing K ∧ K.E.ncard = n}
  have hAne : A.Nonempty := ⟨J.E.ncard, J, hJ, ⟨Subset.rfl, Subset.rfl⟩, rfl⟩
  have hAbdd : BddAbove A := ⟨N, by rintro _ ⟨K, hK, _, rfl⟩; exact hN K hK⟩
  obtain ⟨K, hK, hJK, hcount⟩ := Nat.sSup_mem hAne hAbdd
  refine ⟨K, ⟨htwo, hK, ?_⟩, hJK⟩
  intro L hL hKL
  have hVL := preRadial_vertices_eq_of_extension hK hL hKL
  refine ⟨hVL.subset, ?_⟩
  have hle : L.E.ncard ≤ K.E.ncard := by
    rw [hcount]
    exact le_csSup hAbdd ⟨L, hL, hJK.trans hKL, rfl⟩
  exact (eq_of_subset_of_ncard_le hKL.2 hle L.finite_edges).superset

/-- A two-cell pre-radial drawing is radial if each of its regions
contains at most one original drawing edge and that original drawing
has an edge. This closes the global maximality verification for the
cleanup in XII (7.3), page 261. -/
theorem isRadial_of_twoCell_unique_edges
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ J : Drawing S}
    (htwo : (PaintingOrDrawing.drawing Γ).IsTwoCell) (hE : Γ.E.Nonempty)
    (hJ : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing J)
    (hJtwo : (PaintingOrDrawing.drawing J).IsTwoCell)
    (hunique : ∀ r ∈ J.R, ∀ a ∈ Γ.E, ∀ b ∈ Γ.E, a ⊆ r → b ⊆ r → a = b) :
    (PaintingOrDrawing.drawing Γ).IsRadialDrawing J := by
  obtain ⟨K, hK, hJK⟩ := exists_radial_extension hS htwo hJ
  have hV : K.V = J.V := preRadial_vertices_eq_of_extension hJ hK.2.1 hJK
  have hfacts := regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hE
  have hback : K.E ⊆ J.E := by
    intro g hg
    by_contra hgn
    obtain ⟨a, ha, b, hb, hcap⟩ := hK.2.1.2.2.2.2.1 g hg
    have hab : a ≠ b := fun h => hb.2 (h ▸ ha)
    obtain ⟨A, hA, p, hp, q, hq, hpq, hpA, hqA⟩ := exists_two_regions_in_old_face
      hS hJK hV.symm hJtwo hg hgn (isLine_closure hg hab hcap) hcap
    obtain ⟨e, he, hep⟩ := hfacts.1 p hp
    obtain ⟨f, hf, hfq⟩ := hfacts.1 q hq
    have hef : e = f := hunique A hA e he f hf (hep.trans hpA) (hfq.trans hqA)
    obtain ⟨x, hxe⟩ := he.1
    exact hpq (region_eq_of_mem hp hq (hep hxe) (hfq (hef ▸ hxe)))
  have heq : J = K := Drawing.ext_of_V_E hV.symm (Subset.antisymm hJK.2 hback)
  exact heq.symm ▸ hK

end GraphMinor.GM12
