/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section7
public import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM11.Theorem61

/-!
# Restricting the tangle in Graph Minors XII, (7.2)

A normal circle through one vertex bounds a disc chosen by respectfulness.
The disc separation has order one, so XII, (7.1) restricts the tangle to the
outside drawing without lowering its order. This proves the tangle assertion
in the first part of the proof of (7.2), pages 259–260. It does not prove
that the new drawing is two-cell, or that the new tangle is respectful.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- On a closed set, the hypergraph of the restricted drawing agrees with the
intersection hypergraph used for respectful tangles in XII, (7.2), page 260. -/
theorem interSet_toHypergraph (Γ : Drawing S) {X : Set S} (hX : IsClosed X) :
    (Γ.interSet X).toHypergraph = (PaintingOrDrawing.drawing Γ).inter X := by
  apply Hypergraph.ext
  · ext v
    exact mem_interSet_V_iff hX
  · ext e
    exact mem_interSet_E_iff
  · funext e v
    apply propext
    constructor
    · rintro ⟨he, hv, hc⟩
      obtain ⟨heΓ, heX⟩ := mem_interSet_E_iff.mp he
      obtain ⟨hvΓ, hvX⟩ := (mem_interSet_V_iff hX).mp hv
      exact ⟨⟨heΓ, hvΓ, hc⟩, heX, hvX⟩
    · rintro ⟨⟨he, hv, hc⟩, heX, hvX⟩
      exact ⟨mem_interSet_E_iff.mpr ⟨he, heX⟩,
        (mem_interSet_V_iff hX).mpr ⟨hv, hvX⟩, hc⟩

omit [T2Space S] in
/-- In the proof of XII, (7.2), the separation across the chosen disc has
order one because its common vertices are precisely the vertices on the circle. -/
theorem separationOrder_inter_eq_one {Γ : Drawing S} {Δ F : Set S} {v : S}
    (hΔ : IsClosed Δ) (hbd : subBd Δ = F) (hFV : F ∩ Γ.V = {v}) :
    separationOrder ((PaintingOrDrawing.drawing Γ).inter Δ)
      ((PaintingOrDrawing.drawing Γ).interOutside Δ) = 1 := by
  have hfr : frontier Δ = F := (subBd_eq_frontier Δ).symm.trans hbd
  have hvertices :
      (((PaintingOrDrawing.drawing Γ).inter Δ) ∩
        ((PaintingOrDrawing.drawing Γ).interOutside Δ)).vertexSet = F ∩ Γ.V := by
    ext x
    constructor
    · intro hx
      have h := inter_outside_subset hx
      exact ⟨hfr ▸ h.1, h.2⟩
    · rintro ⟨hxF, hxV⟩
      have hxfr : x ∈ frontier Δ := hfr.symm ▸ hxF
      have hxΔ : x ∈ Δ := hΔ.closure_eq ▸ hxfr.1
      have hxout : x ∈ closure (univ \ Δ) := by
        rw [← compl_eq_univ_sdiff, closure_compl]
        exact hxfr.2
      exact ⟨⟨hxV, hxΔ⟩, hxV, hxout⟩
  unfold separationOrder
  rw [hvertices, hFV, ncard_singleton]

/-- The tangle restriction in XII, (7.2), pages 259–260, obtained from (7.1).
Respectfulness supplies the disc and membership of its separation. The single
boundary vertex gives order one, with no extra separation hypothesis. -/
theorem theorem_7_2_tangle {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsTangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    {F : Set S} {v : S} (hF : IsOArc F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F)
    (hFV : F ∩ Γ.V = {v}) :
    ∃ Δ : Set S, IsClosedDisc Δ ∧ subBd Δ = F ∧
      ((PaintingOrDrawing.drawing Γ).inter Δ,
        (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈ T ∧
      IsTangle (Γ.interSet (closure (univ \ Δ))).toHypergraph θ
        (restrictTangle T (Γ.interSet (closure (univ \ Δ))).toHypergraph) := by
  have hcard : (F ∩ Γ.V).ncard < θ := by rw [hFV, ncard_singleton]; omega
  obtain ⟨Δ, hΔ, hbd, hm⟩ := hrespect.2 F hF hn hcard
  have hclosed : IsClosed Δ := (IsClosedDisc.isCompact hΔ).isClosed
  have ho := separationOrder_inter_eq_one hclosed hbd hFV
  have ht := theorem_7_1_proof hT hm ho
  refine ⟨Δ, hΔ, hbd, hm, ?_⟩
  rw [interSet_toHypergraph Γ isClosed_closure]
  exact ht

end GraphMinor.GM12
