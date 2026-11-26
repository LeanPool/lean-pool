/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2Simple
import LeanPool.GraphMinor.GM12.Section2
import LeanPool.GraphMinor.GM12.Section2TraceEdgeRestriction
import LeanPool.GraphMinor.GM12.Section2CurveCounts
import LeanPool.GraphMinor.GM12.Section2NonemptyEdges
import LeanPool.GraphMinor.GM12.Section2WalkInside

/-!
# Graph Minors XII (2.1): the trace contains every relevant inside atom

A trace has twice the length of its original normal curve, so its
inside is defined below the tangle order. For an embedded circle
in the image, parameterize it injectively. Its length is at most
the original curve length, since its drawing vertices are a subset
of the original image's drawing vertices. The restriction theorem
puts its trace inside the original trace. Apply the simple-curve
induction and monotonicity of walk insides. If the original curve
has length zero, use the region argument directly. This follows
the reduction and the two-case induction on pages 243--244.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Graph Minors XII, (2.1), pages 243--244. The trace is short enough
for its inside to be defined. Every atom meeting the tangle-selected
disc bounded by a circle in the original image meets that trace inside.
The selected disc explicitly represents `ins(F)` from the paper. -/
theorem theorem_2_1_proof
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    {φ : C(Circle, S)} {u : S} (W : GraphWalk K.toGraph u u)
    (hW : IsTrace Γ K φ W) (hlen : curveLength Γ φ < θ)
    {F D c : Set S} (hF : IsOArc F) (hFφ : F ⊆ range φ)
    (hD : IsClosedDisc D) (hbdD : subBd D = F)
    (hmD : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T)
    (hc : c ∈ Γ.A) (hcD : (c ∩ D).Nonempty) :
    W.length < 2 * θ ∧ (c ∩ insWalk ins K W).Nonempty := by
  refine ⟨theorem_2_1_length hW hlen, ?_⟩
  by_cases hzero : curveLength Γ φ = 0
  · exact theorem_2_1_zero hS hT hK.1 hW hzero hF hFφ hD hbdD hmD hc hcD
  · have hpos : 0 < curveLength Γ φ := Nat.pos_of_ne_zero hzero
    have hθ : 2 ≤ θ := by omega
    have hE : Γ.E.Nonempty := edges_nonempty_of_tangle_order_two hT hθ
    obtain ⟨H⟩ := hF
    let ψ : C(Circle, S) := ⟨fun t => (H t).val, continuous_subtype_val.comp H.continuous⟩
    have hψrange : range ψ = F := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact (H t).property
      · intro hx
        exact ⟨H.symm ⟨x, hx⟩, congrArg Subtype.val (H.apply_symm_apply ⟨x, hx⟩)⟩
    have hψemb : IsEmbedding ψ := IsEmbedding.subtypeVal.comp H.isEmbedding
    have hsub : range ψ ⊆ range φ := hψrange ▸ hFφ
    have hψn : Γ.IsNormal (range ψ) := fun x hx => hW.1.2 ⟨hsub hx.1, hx.2⟩
    have hψ : IsNormalCurve Γ ψ := isNormalCurve_of_injective ψ hψemb.injective hψn
    have hψlen : curveLength Γ ψ ≤ curveLength Γ φ := by
      rw [curveLength_eq_vertex_count ψ hψemb.injective hψn]
      exact (Set.ncard_le_ncard (inter_subset_inter_left Γ.V hsub)
        (Γ.finite_V.subset inter_subset_right)).trans (vertex_count_le_curveLength hW.1)
    obtain ⟨v, P, hP, hPW⟩ := exists_trace_subdrawing_of_range_subset hS hK hE W hW hψ hsub
    have hmeet := theorem_2_1_simple hS hT hrespect hK hd hψemb P hP
      (hψlen.trans_lt hlen) hD (hbdD.trans hψrange.symm) hmD hc hcD
    exact meets_insWalk_of_subdrawing ins K W P hPW hmeet

end GraphMinor.GM12
