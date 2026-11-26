/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Metric
import LeanPool.GraphMinor.GM12.Section79

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

/-- Changing the order from `θ` to `θ' ≤ θ` truncates the radial metric at `θ'`.
This is the equality used in Graph Minors XVI, proof of (7.1), page 69, and
proof of (8.3), Claim (1), page 65. -/
theorem tangleMetric_truncation {H K : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (ins : Drawing S → Set S) {θ θ' : ℕ} (hle : θ' ≤ θ) (x y : Set S) :
    tangleMetric H K ins θ' x y = min (tangleMetric H K ins θ x y) θ' :=
  GM12.tangleMetric_truncation hK ins hle x y

end GraphMinor.GM16
