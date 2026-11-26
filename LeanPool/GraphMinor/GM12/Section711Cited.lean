/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section711

/-!
# Graph Minors XII, (7.11), in the form that Graph Minors XV cites

This file concludes `GM15.GM12Theorem711Statement` from `GM12.theorem_7_11_deleteAtomNeighborhood`.
-/

@[expose] public section

namespace GraphMinor.GM12

universe u

/-- Graph Minors XII, (7.11) (page 271), as cited in (4.3) of Graph Minors XV (page 125), with the
hypothesis "if `z ∈ E(H)` then `λ ≥ 2`" that the printed statement omits. -/
theorem gm12_theorem_7_11 : GM15.GM12Theorem711Statement.{u} := by
  intro S _ _ H θ lam T d z hS hConn hMetric hE hz hlam hz_lam
  have := hConn
  exact theorem_7_11_deleteAtomNeighborhood hS H θ lam T d z hMetric hE hz hlam hz_lam

end GraphMinor.GM12
