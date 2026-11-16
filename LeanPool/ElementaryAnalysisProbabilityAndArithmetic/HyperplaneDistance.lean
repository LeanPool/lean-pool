/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Geometry.Euclidean.Projection

import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Distance to a hyperplane through its normal vector

In a real Euclidean affine space, the distance from a point `p` to its orthogonal projection on
an affine subspace `s` whose orthogonal complement is spanned by `n` is `|⟪n, p -ᵥ q⟫| / ‖n‖`
for any point `q` of `s`. For the hyperplane through `q` with normal vector `n` this is the
classical formula `|a x₀ + b y₀ + c z₀ + d| / √(a² + b² + c²)`.

## Main statements

* `EuclideanGeometry.dist_orthogonalProjection_eq_abs_inner_div_norm`: the general statement.
* `EuclideanGeometry.dist_orthogonalProjection_mk'_eq_abs_inner_div_norm`: the hyperplane
  `AffineSubspace.mk' q (ℝ ∙ n)ᗮ` through `q` with normal vector `n`.
-/

public section

namespace EuclideanGeometry

open AffineSubspace
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The distance from a point `p` to its orthogonal projection on an affine subspace `s` whose
orthogonal complement is spanned by `n` (a hyperplane with normal vector `n`, when `n ≠ 0`) is
`|⟪n, p -ᵥ q⟫| / ‖n‖`, for any point `q` of `s`. -/
theorem dist_orthogonalProjection_eq_abs_inner_div_norm (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] {n : V} (hn : s.directionᗮ = ℝ ∙ n) {q : P}
    (hq : q ∈ s) (p : P) :
    dist p (orthogonalProjection s p) = |⟪n, p -ᵥ q⟫| / ‖n‖ := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1
    (hn ▸ vsub_orthogonalProjection_mem_direction_orthogonal s p)
  have hn' : n ∈ s.directionᗮ := hn ▸ Submodule.mem_span_singleton_self n
  have h0 : ⟪n, (orthogonalProjection s p : P) -ᵥ q⟫ = 0 :=
    s.direction.inner_left_of_mem_orthogonal
      (AffineSubspace.vsub_mem_direction (orthogonalProjection_mem p) hq) hn'
  rw [dist_eq_norm_vsub V, ← vsub_add_vsub_cancel p (orthogonalProjection s p : P) q,
    inner_add_right, h0, add_zero, ← ht, norm_smul, inner_smul_right,
    real_inner_self_eq_norm_sq, abs_mul, abs_of_nonneg (sq_nonneg ‖n‖), Real.norm_eq_abs]
  field

/-- The direction of `AffineSubspace.mk' q K` has an orthogonal projection when `K` has one. -/
instance hasOrthogonalProjection_direction_mk' (q : P) (K : Submodule ℝ V)
    [K.HasOrthogonalProjection] :
    (AffineSubspace.mk' q K).direction.HasOrthogonalProjection := by
  rw [AffineSubspace.direction_mk']
  infer_instance

/-- The distance from a point `p` to the affine hyperplane through `q` with normal vector `n`,
measured to its orthogonal projection, is `|⟪n, p -ᵥ q⟫| / ‖n‖`. -/
theorem dist_orthogonalProjection_mk'_eq_abs_inner_div_norm (q : P) (n : V) (p : P) :
    dist p (orthogonalProjection (AffineSubspace.mk' q (ℝ ∙ n)ᗮ) p) = |⟪n, p -ᵥ q⟫| / ‖n‖ :=
  dist_orthogonalProjection_eq_abs_inner_div_norm _
    (by rw [AffineSubspace.direction_mk', Submodule.orthogonal_orthogonal (ℝ ∙ n)])
    (AffineSubspace.self_mem_mk' q _) p

end EuclideanGeometry
