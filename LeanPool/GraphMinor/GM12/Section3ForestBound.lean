/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Cited

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# The forest bound used in XII (3.1)

The reduction of XII (3.1), page 245, uses VII (7.5) after removing the
prescribed discs. With at most z boundary vertices and c cuffs, choose
k = z + c + 1. This satisfies VII's boundary-count inequality. Its alpha
threshold then gives feasibility for any forest with the same boundary
vertices. The geometric work in XII must establish this alpha bound
from conditions (i)--(iv), and boundary linkage from condition (v).
-/

public section

namespace GraphMinor.GM12

open Set Surface

universe u

/-- Apply VII (7.5), page 240, with a parameter depending only on the
surface and the boundary vertex bound, as needed for XII (3.1), page 245.
The integer `k = z + c + 1` ensures the required boundary-count bound. -/
theorem feasible_forest_of_large_alpha {S : Type u} [TopologicalSpace S] [T1Space S]
  (hS : IsSurface S)
    {a b c z : ℕ} (hcomplex : 3 ≤ 3 * a + 3 * b + c)
    (hmodel : Nonempty (S ≃ₜ SurfaceModel a b c))
    (G H : Drawing S) (hlinked : GM07.IsBoundaryLinked G)
    (hcount : (G.V ∩ bd S).ncard ≤ z)
    (hα : 42 * (z + c + 1) * GM07.vModel a b (c + 1) (z + c + 1) ≤ GM07.alpha G)
    (hH : GM07.IsSurfaceForest H) (hboundary : G.V ∩ bd S = H.V ∩ bd S) :
    GM07.IsGFeasible G H := by
  apply GraphMinor.GM07.gm07_theorem_7_5 S hS a b c hcomplex hmodel (z + c + 1) G hlinked.1 hlinked
    hα
  · omega
  · exact hH
  · exact hboundary

end GraphMinor.GM12
