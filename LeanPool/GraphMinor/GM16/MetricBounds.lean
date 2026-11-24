/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Metric
import LeanPool.GraphMinor.GM12.Section4WalkMetric

/-!
# Changing the order in the tangle metric

Truncating a tangle cuts off its metric at the new order. A shortest radial walk
continues to witness its distance precisely when its half length is below that
order. This is the metric comparison used in XVI, proofs of (7.1) and (8.3).
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

private theorem metric_walk_of_lt {H K : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (ins : Drawing S → Set S) {θ : ℕ} {x y : Set S} (hne : x ≠ y)
    (hlt : tangleMetric H K ins θ x y < θ) :
    ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
      IsCorrespondingAtom H K x x' ∧ IsCorrespondingAtom H K y y' ∧
      W.length < 2 * θ ∧ W.length = 2 * tangleMetric H K ins θ x y ∧
      x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W := by
  classical
  unfold tangleMetric at hlt ⊢
  simp only [hne, ↓reduceIte] at hlt ⊢
  split_ifs at hlt ⊢ with hex
  · have hnonempty : {k : ℕ | ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
        IsCorrespondingAtom H K x x' ∧ IsCorrespondingAtom H K y y' ∧
        W.length < 2 * θ ∧ W.length = 2 * k ∧
        x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W}.Nonempty := by
      obtain ⟨u, W, x', y', hx, hy, hlen, hxW, hyW⟩ := hex
      refine ⟨W.support.tail.countP (· ∈ H.V), u, W, x', y', hx, hy, hlen, ?_, hxW, hyW⟩
      exact GM12.closed_walk_length_eq_two_mul hK.2.1 W
    exact Nat.sInf_mem hnonempty
  · exact (Nat.lt_irrefl _ hlt).elim

/-- Changing the order from `θ` to `θ' ≤ θ` truncates the radial metric at `θ'`.
This is the equality used in Graph Minors XVI, proof of (7.1), page 69, and
proof of (8.3), Claim (1), page 65. -/
theorem tangleMetric_truncation {H K : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (ins : Drawing S → Set S) {θ θ' : ℕ} (hle : θ' ≤ θ) (x y : Set S) :
    tangleMetric H K ins θ' x y = min (tangleMetric H K ins θ x y) θ' := by
  classical
  by_cases heq : x = y
  · subst y
    simp only [tangleMetric, ↓reduceIte, Nat.zero_min]
  have hsmall := GM12.tangleMetric_le_order hK ins θ' x y
  have hlarge := GM12.tangleMetric_le_order hK ins θ x y
  apply le_antisymm
  · apply le_min _ hsmall
    by_cases hlt : tangleMetric H K ins θ x y < θ'
    · obtain ⟨u, W, x', y', hx, hy, _, hlen, hxW, hyW⟩ :=
        metric_walk_of_lt hK ins heq (hlt.trans_le hle)
      exact GM12.tangleMetric_le_of_walk hx hy W (by omega) hlen hxW hyW
    · exact hsmall.trans (Nat.le_of_not_gt hlt)
  · by_cases hlt : tangleMetric H K ins θ' x y < θ'
    · obtain ⟨u, W, x', y', hx, hy, hshort, hlen, hxW, hyW⟩ :=
        metric_walk_of_lt hK ins heq hlt
      have hw : W.length < 2 * θ := lt_of_lt_of_le hshort (Nat.mul_le_mul_left 2 hle)
      exact (min_le_left _ _).trans (GM12.tangleMetric_le_of_walk hx hy W hw hlen hxW hyW)
    · exact (min_le_right _ _).trans (Nat.le_of_not_gt hlt)

end GraphMinor.GM16
