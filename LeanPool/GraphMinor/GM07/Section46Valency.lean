/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section2

/-!
# The seam valency bound in VII (4.6)

The first count on page 225 bounds the valency of a seam vertex by twice
the number of edges. The handshaking identity proves this for every drawing.
Applying (2.4) gives the bound used when choosing `l(z)`.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The inequality `d(z) ≤ 2|E(J)|` in VII (4.6), page 225. -/
theorem vertexValency_le_two_mul_ncard_edges
    (J : Drawing S) {z : S} (hz : z ∈ J.V) :
    vertexValency J z ≤ 2 * J.E.ncard := by
  classical
  calc
    vertexValency J z ≤ ∑ v ∈ J.finite_V.toFinset, vertexValency J v :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (J.finite_V.mem_toFinset.mpr hz)
    _ = 2 * J.E.ncard := sum_vertexValency_eq_two_mul_ncard_E J

/-- The valency estimate from (2.4) used in VII (4.6), page 225. -/
theorem seam_vertexValency_bound_4_6 (hS : IsSurface S)
    {a b c : ℕ} (habc : 1 < 2 * a + b + c)
    (hmodel : Nonempty (S ≃ₜ SurfaceModel a b c))
    {G J : Drawing S} {N : Net S} (hG : G.IsProper)
    (hmin : N.IsMinimalFor G) (hseam : N.IsSeamGraphFor J)
    {z : S} (hz : z ∈ J.V) :
    vertexValency J z ≤ 6 * (2 * a + b + c - 1) := by
  have he := (theorem_2_4_proof hS habc hmodel hG hmin hseam).2
  have hv := vertexValency_le_two_mul_ncard_edges J hz
  omega

end GraphMinor.GM07
