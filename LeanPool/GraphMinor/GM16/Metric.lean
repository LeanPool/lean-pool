/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM11.RadialExists
import LeanPool.GraphMinor.GM11.Separate
import LeanPool.GraphMinor.GM12.Section4WalkMetric

/-!
# Metrics for the spans in Graph Minors XVI

A respectful tangle has a metric. Choose a radial drawing. Each short circuit of
that drawing is a normal circle meeting the original drawing in fewer than the
tangle order many vertices. Respectfulness chooses its inside disc. These choices
give the derived slope used in the definition of the tangle metric.
-/

public section

namespace GraphMinor.GM16

open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- The metric used in Graph Minors XVI, Section 4, page 52, exists for every
respectful tangle in a closed surface. It is obtained from a radial drawing and
the inside discs supplied by respectfulness, as in XI, Section 6, page 87. -/
theorem exists_tangleMetric (hS : IsClosedSurface S) {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsRespectfulDrawingTangle H θ T) :
    ∃ d, HasTangleMetric H θ T d := by
  classical
  obtain ⟨K, hK⟩ := exists_radialDrawing hS hT.1
  have hdisc : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing K → C.length < 2 * θ →
      ∃ Δ : Set S, IsClosedDisc Δ ∧ subBd Δ = C.U ∧
        ((PaintingOrDrawing.drawing H).inter Δ,
          (PaintingOrDrawing.drawing H).interOutside Δ) ∈ T := by
    intro C hC hCK hlen
    have hnormal : (PaintingOrDrawing.drawing H).IsNormal C.U := by
      intro x hx
      exact hK.2.1.1 ▸ ⟨hx.2, hCK.U_subset hx.1⟩
    have hinter : C.U ∩ H.V = C.V ∩ H.V := by
      ext x
      constructor
      · rintro ⟨hx, hxH⟩
        rw [C.U_eq] at hx
        rcases hx with hx | hx
        · exact ⟨hx, hxH⟩
        · obtain ⟨e, heC, hxe⟩ := mem_iUnion₂.mp hx
          have hxK := hK.2.1.2.1 hxH
          have hxC : x ∈ closure e ∩ C.V := by
            rw [hCK.closure_inter_V heC]
            exact ⟨hxe, hxK⟩
          exact ⟨hxC.2, hxH⟩
      · exact fun hx => ⟨C.V_subset_U hx.1, hx.2⟩
    have hcount := (GM12.circuit_length_eq_two_mul_ncard hK.2.1 hC hCK).1
    have hsmall : (C.U ∩ H.V).ncard < θ := by
      rw [hinter]
      omega
    exact hT.2.2.2 C.U (IsCircuit.isOArc_U hC) hnormal hsmall
  let ins : Drawing S → Set S := fun C =>
    if hc : C.IsCircuit ∧ C.IsSubdrawing K ∧ C.length < 2 * θ then
      (hdisc C hc.1 hc.2.1 hc.2.2).choose else ∅
  have hins : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins := by
    intro C hC hCK hlen
    dsimp only [ins]
    rw [dite_eq_left ⟨hC, hCK, hlen⟩]
    exact (hdisc C hC hCK hlen).choose_spec
  exact ⟨tangleMetric H K ins θ, hT, K, ins, hK, hins,
    fun _ _ _ _ => rfl⟩

end GraphMinor.GM16
