/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Kinderlehrer and Stampacchia: the projection on a closed convex set

D. Kinderlehrer and G. Stampacchia, *An introduction to variational inequalities and their
applications*, SIAM Classics in Applied Mathematics 31, 2000 (reprint of the 1980 edition),
Chapter I, Lemma 2.1 and Theorem 2.3, as the paper (arXiv:2609.28311, TeX lines 412–415) uses them:
the projection of a point of a real Hilbert space on a nonempty closed convex set exists, is unique
(`lemma2_1`), and is characterized by the variational inequality `⟪x − y, v − y⟫ ≤ 0` for all `v`
in the set (`theorem2_3`).

The source is not freely available and has not been read: the numbering is the paper's, and the
statements are the standard ones, as the paper uses them. Both are in Mathlib
(`exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero`).
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace External.KinderlehrerStampacchia

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Chapter I, Theorem 2.3** (as used by the paper): `y ∈ K` is the projection of `x` on the
convex `K` if and only if `⟪x − y, v − y⟫ ≤ 0` for every `v ∈ K`.

Proof: Mathlib's `norm_eq_iInf_iff_real_inner_le_zero`. -/
theorem theorem2_3 {K : Set H} (hcv : Convex ℝ K) {x y : H} (hy : y ∈ K) :
    ‖x - y‖ = ⨅ v : K, ‖x - v‖ ↔ ∀ v ∈ K, ⟪x - y, v - y⟫_ℝ ≤ 0 :=
  norm_eq_iInf_iff_real_inner_le_zero hcv hy

/-- **Chapter I, Lemma 2.1** (as used by the paper): the projection of `x` on a nonempty closed
convex `K` exists and is unique: there is exactly one `y ∈ K` with `‖x − y‖ = inf_{v ∈ K} ‖x − v‖`.

Proof: Mathlib's `exists_norm_eq_iInf_of_complete_convex` for the existence (`K` is complete, as a
closed subset of a complete space); for the uniqueness, if `y₁` and `y₂` are projections, adding the
variational inequalities `⟪x − y₁, y₂ − y₁⟫ ≤ 0` and `⟪x − y₂, y₁ − y₂⟫ ≤ 0` of `theorem2_3` gives
`‖y₂ − y₁‖² ≤ 0`. -/
theorem lemma2_1 [CompleteSpace H] {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K)
    (hcv : Convex ℝ K) (x : H) :
    ∃! y, y ∈ K ∧ ‖x - y‖ = ⨅ v : K, ‖x - v‖ := by
  obtain ⟨y, hy, hxy⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hcv x
  refine ⟨y, ⟨hy, hxy⟩, fun y' ⟨hy', hxy'⟩ => ?_⟩
  have h1 := (theorem2_3 hcv hy).1 hxy y' hy'
  have h2 := (theorem2_3 hcv hy').1 hxy' y hy
  have h3 : ⟪y' - y, y' - y⟫_ℝ ≤ 0 := by
    rw [show y - y' = -(y' - y) by abel, inner_neg_right] at h2
    calc ⟪y' - y, y' - y⟫_ℝ = ⟪x - y, y' - y⟫_ℝ - ⟪x - y', y' - y⟫_ℝ := by
          rw [← inner_sub_left, sub_sub_sub_cancel_left]
      _ ≤ 0 := by linarith
  have := real_inner_self_nonpos.1 h3
  exact (sub_eq_zero.1 this)

end External.KinderlehrerStampacchia
