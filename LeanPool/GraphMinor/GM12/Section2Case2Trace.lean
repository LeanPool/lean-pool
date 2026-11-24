/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2Case2Inside
public import LeanPool.GraphMinor.GM12.Section2ChordTraceRestriction
import LeanPool.GraphMinor.GM12.Section2TraceExistence
import LeanPool.GraphMinor.GM12.Section2CurveCounts

/-!
# The smaller trace in Case 2 of XII (2.1)

A repeated region gives the two circles formed by a minimal region
chord. The theta-disc argument selects a smaller circle whose inside
still meets the chosen atom. Parameterize that circle injectively
and construct its trace. The chord avoids all drawing vertices, so
the chord trace restriction theorem makes this trace a subdrawing
of the original trace. Its positive, strictly smaller curve length
is precisely what the induction in XII (2.1), page 244, needs.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The full smaller-curve and smaller-trace construction in Case 2
of XII (2.1), page 244. The selected inside still meets the specified
set, and the trace lies in the original trace drawing. -/
theorem theorem_2_1_case2_smaller_trace
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsPretangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    {φ : C(Circle, S)} (hφi : Function.Injective φ) (hF : IsOArc (range φ))
    {u : S} (W : GraphWalk K.toGraph u u) (hW : IsTrace Γ K φ W)
    (hcount : curveLength Γ φ < θ)
    {r Δ C : Set S} (hr : r ∈ Γ.R) (hdisconn : ¬ IsPreconnected (range φ ∩ r))
    (hΔ : IsClosedDisc Δ) (hbd : subBd Δ = range φ)
    (hm : ((PaintingOrDrawing.drawing Γ).inter Δ,
      (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈ T)
    (hC : (C ∩ Δ).Nonempty) :
    ∃ (ψ : C(Circle, S)) (Δ' : Set S) (v : S) (P : GraphWalk K.toGraph v v),
      IsEmbedding ψ ∧ IsTrace Γ K ψ P ∧
      0 < curveLength Γ ψ ∧ curveLength Γ ψ < curveLength Γ φ ∧
      IsClosedDisc Δ' ∧ subBd Δ' = range ψ ∧
      ((PaintingOrDrawing.drawing Γ).inter Δ',
        (PaintingOrDrawing.drawing Γ).interOutside Δ') ∈ T ∧
      (C ∩ Δ').Nonempty ∧ (walkDrawing K P).IsSubdrawing (walkDrawing K W) := by
  have hφlength := curveLength_eq_vertex_count φ hφi hW.1.2
  have hcount' : (range φ ∩ Γ.V).ncard < θ := hφlength ▸ hcount
  obtain ⟨F', Δ', hF', hn', hsmall, hΔ', hbd', hm', hC', hFV', L, hL, hLV, hsub⟩ :=
    theorem_2_1_case2_smaller_inside hS hT hrespect hF hW.1.2 hcount' hr hdisconn hΔ hbd hm hC
  obtain ⟨H⟩ := hF'
  let ψ : C(Circle, S) := ⟨fun t => (H t).val, continuous_subtype_val.comp H.continuous⟩
  have hψrange : range ψ = F' := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (H t).property
    · intro hx
      refine ⟨H.symm ⟨x, hx⟩, ?_⟩
      exact congrArg Subtype.val (H.apply_symm_apply ⟨x, hx⟩)
  have hψemb : IsEmbedding ψ := IsEmbedding.subtypeVal.comp H.isEmbedding
  have hψn : Γ.IsNormal (range ψ) := hψrange.symm ▸ hn'
  have hψ : IsNormalCurve Γ ψ := isNormalCurve_of_injective ψ hψemb.injective hψn
  have hψlength : curveLength Γ ψ = (F' ∩ Γ.V).ncard := by
    rw [curveLength_eq_vertex_count ψ hψemb.injective hψn, hψrange]
  have hψpos : 0 < curveLength Γ ψ := by
    rw [hψlength]
    exact (Set.ncard_pos (Γ.finite_V.subset inter_subset_right)).mpr hFV'
  obtain ⟨v, P, hP⟩ := exists_trace hS hK hE hψ
  have hPpos : 0 < P.length := by
    rcases hP.2 with ⟨hzero, _⟩ | ⟨_, hlen, _⟩
    · exact (not_lt_of_ge hzero.le hψpos).elim
    · omega
  have hsub' : range ψ ⊆ range φ ∪ L := hψrange.symm ▸ hsub
  refine ⟨ψ, Δ', v, P, hψemb, hP, hψpos, ?_, hΔ', hbd'.trans hψrange.symm,
    hm', hC', trace_isSubdrawing_of_range_subset_union hS hK hE W P hW hP hPpos hL hLV hsub'⟩
  rw [hψlength, hφlength]
  exact hsmall

end GraphMinor.GM12
