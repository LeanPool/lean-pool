/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73DiscComparison
public import LeanPool.GraphMinor.GM12.Section73CircuitLift
public import LeanPool.GraphMinor.GM12.Section73SplicedSeparation
import LeanPool.GraphMinor.GM11.Separate

/-!
# The inside comparison for a circuit through the merged hub

For XII (7.3), Claim (1), page 262, construct the old circuit
inside the lifted walk. Its length and deleted-vertex alternative
keep the enlarged separation below the old tangle order. Thus
its selected disc is also selected in the new tangle. The circuit
image and its point-or-arc fibre give equality of the selected
discs outside the merged region. This puts the new circuit's
inside in the lifted walk's inside together with that region.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 Hypergraph

/-- The circuit-through-the-hub case of XII (7.3), Claim (1),
page 262, with the old circuit, separation transfer, and selected
disc comparison all proved from the constructed collapse. -/
theorem circuit_inside_subset_lifted_walk_through_hub
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K J : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsTangle Γ.toHypergraph θ T)
    {v : S} {ins ins' : Drawing S → Set S}
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins)
    (hins' : IsDerivedSlope (PaintingOrDrawing.drawing (deleteVertices Γ {v})) J (θ - 1)
      (deleteVerticesTangle Γ.toHypergraph {v} T θ) ins')
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    (hv : v ∈ Γ.V) {r' : Set S}
    (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r')
    (f : C(S, S)) (hfix : ∀ x ∉ r', f x = x)
    (hcollapse : ∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨
      (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
      (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e))
    (hJV : J.V = f '' K.V)
    (hJE : J.E ⊆ (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g})
    (hJpre : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsPreRadialDrawing J)
    (hJtwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell)
    {B : Set S} (hB : IsClosedDisc B) (hBr : B ⊆ r')
    (hAB : ({v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ⊆ discInt B)
    (hfixB : ∀ x ∉ discInt B, f x = x)
    {a : S} (W : GraphWalk J.toGraph a a) (W' : GraphWalk K.toGraph a a)
    (hpoints : (walkDrawing K W').U \ r' = (walkDrawing J W).U \ r')
    (hedges : ∀ e ∈ W.edges, ∀ g ∈ spokeReplacementEdges K J v f e, g ∈ W'.edges)
    {C : Drawing S} (hC : C.IsCircuit) (hCW : C.IsSubdrawing (walkDrawing J W))
    (hvC : v ∈ C.V) (hshort : C.length + 2 < 2 * θ) :
    ins' C ⊆ insWalk ins K W' ∪ r' := by
  obtain ⟨D, ε, hD, hDW, hε, hDlen, hvD, himage, hshape⟩ :=
    exists_circuit_in_lifted_walk_through_hub hS hK hE hv hr' hvr' f hfix hcollapse hfibre
      hJV hJE hJpre hJtwo W W' hpoints hedges hC hCW hvC
  have hDK : D.IsSubdrawing K := hDW.trans (walkDrawing_isSubdrawing K W')
  have hCJ : C.IsSubdrawing J := hCW.trans (walkDrawing_isSubdrawing J W)
  obtain ⟨hOld, hOldbd, _⟩ := hins D hD hDK (by omega)
  obtain ⟨hNew, hNewbd, hmNew⟩ := hins' C hC hCJ (by omega)
  have hmOld := spliced_circuit_disc_mem_deleted_tangle hT hv hK.2.1 hins hD hDK
    hε hDlen.le hvD hshort
  have hdelete := deleteVertices_isSubdrawing Γ {v}
  have hnOld : (deleteVertices Γ {v}).IsNormal D.U := by
    rintro z ⟨hzD, hzΓ'⟩
    have hzΓ : z ∈ Γ.V := hK.2.1.1.subset ⟨hdelete.U_subset hzΓ', hDK.U_subset hzD⟩
    exact (isSubdrawing_U_inter_V hdelete).subset ⟨hzΓ', hzΓ⟩
  have hnNew : (deleteVertices Γ {v}).IsNormal C.U := by
    rintro z ⟨hzC, hzΓ'⟩
    exact hJpre.1.subset ⟨hzΓ', hCJ.U_subset hzC⟩
  have ht := theorem_7_3_tangle hθ hT hv
  have hpret : IsPretangle (PaintingOrDrawing.drawing (deleteVertices Γ {v})).toHypergraph
      (θ - 1) (deleteVerticesTangle Γ.toHypergraph {v} T θ) :=
    ⟨ht.one_le, ht.isSeparation, ht.order_lt, ht.axiom1, ht.axiom2⟩
  have heq := selected_discs_agree_outside_collapsed_region hS hpret hr'
    hOld hNew hB hBr hAB hOldbd hNewbd hnOld hnNew hmOld hmNew
    (IsCircuit.isOArc_U hD) hshape f hfixB hfibre himage
  intro z hz
  by_cases hzr : z ∈ r'
  · exact Or.inr hzr
  · have hzOld : z ∈ ins D := (heq.superset ⟨hz, hzr⟩).1
    exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨D, ⟨hD, hDW⟩, hzOld⟩))

end GraphMinor.GM12
