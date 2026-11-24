/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Second differences of a `C²` function on an open set

The one-sided second difference `f(x+u) + f(x-u) - 2 f(x)` of a `C²` function
is at most `2M‖u‖²`, where `M` bounds the second derivative on a convex set
containing the three points.  Both the Taylor bound and the cancellation of
the first-order terms are stated for `ContDiffOn` on an **open** set rather
than for a globally `C²` function, because the functions that need them —
Mobius pullbacks, and generally anything with poles — are not globally `C²`.

`Pending.SemiconcaveTaylor.abs_sub_fderiv_le_of_norm_second_le` is the
`U = univ` case of the first statement and is derived from it there.

Source: Z. Blocki, *The complex Monge--Ampere operator in pluripotential
theory*, lecture notes, Proposition 2.3.3 and Theorem 2.3.2.
-/

@[expose] public section

noncomputable section

open Set

namespace SGPT.Foundations.Analysis.Pending.SemiconcaveHessian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Second-order Taylor bound on an open set.**  This is
`Pending.SemiconcaveTaylor.abs_sub_fderiv_le_of_norm_second_le` with the
global `ContDiff` hypothesis relaxed to `ContDiffOn` on an open set, which is
what a function with poles satisfies. -/
theorem abs_sub_fderiv_le_of_norm_fderiv_fderiv_le_on
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    {s : Set E} (hs : Convex ℝ s) (hsU : s ⊆ U) {M : ℝ}
    (hM : ∀ y ∈ s, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ M) {x y : E} (hx : x ∈ s)
    (hy : y ∈ s) : |f y - f x - fderiv ℝ f x (y - x)| ≤ M * ‖y - x‖ ^ 2 := by
  have hd1 : ∀ z ∈ U, HasFDerivAt f (fderiv ℝ f z) z := fun z hz =>
    ((hf.differentiableOn (by norm_num)).differentiableAt
      (hU.mem_nhds hz)).hasFDerivAt
  have hcd : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  have hd2 : ∀ z ∈ U, HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    fun z hz =>
      ((hcd.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hz)).hasFDerivAt
  have hM0 : 0 ≤ M := le_trans (ContinuousLinearMap.opNorm_nonneg _) (hM x hx)
  have hseg : segment ℝ x y ⊆ s := hs.segment_subset hx hy
  have hbound : ∀ w ∈ segment ℝ x y,
      ‖fderiv ℝ f w - fderiv ℝ f x‖ ≤ M * ‖y - x‖ := by
    intro w hw
    have hw' : ‖w - x‖ ≤ ‖y - x‖ := by
      rw [segment_eq_image'] at hw
      obtain ⟨t, ht, rfl⟩ := hw
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    have hMx : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ M :=
      fun z hz => hM z (hseg hz)
    have hmv := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (hd2 z (hsU (hseg hz))).hasFDerivWithinAt) hMx
      (left_mem_segment ℝ x y) hw
    calc ‖fderiv ℝ f w - fderiv ℝ f x‖ ≤ M * ‖w - x‖ := hmv
      _ ≤ M * ‖y - x‖ := mul_le_mul_of_nonneg_left hw' hM0
  set g : E → ℝ := fun w => f w - fderiv ℝ f x w with hg
  have hg' : ∀ w ∈ U, HasFDerivAt g (fderiv ℝ f w - fderiv ℝ f x) w :=
    fun w hw => (hd1 w hw).sub (fderiv ℝ f x).hasFDerivAt
  have hmv := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hg' z (hsU (hseg hz))).hasFDerivWithinAt) hbound
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have hgg : g y - g x = f y - f x - fderiv ℝ f x (y - x) := by
    simp only [hg, map_sub]
    ring
  rw [hgg, Real.norm_eq_abs] at hmv
  calc |f y - f x - fderiv ℝ f x (y - x)| ≤ M * ‖y - x‖ * ‖y - x‖ := hmv
    _ = M * ‖y - x‖ ^ 2 := by ring

/-- **The balanced second difference of a `C²` function.**  The first-order
terms cancel, so only the second-derivative bound survives. -/
theorem secondDifference_le_of_norm_fderiv_fderiv_le_on
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    {s : Set E} (hs : Convex ℝ s) (hsU : s ⊆ U) {M : ℝ}
    (hM : ∀ y ∈ s, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ M) {x u : E} (hx : x ∈ s)
    (hp : x + u ∈ s) (hm : x - u ∈ s) :
    f (x + u) + f (x - u) - 2 * f x ≤ 2 * M * ‖u‖ ^ 2 := by
  have h₁ := abs_sub_fderiv_le_of_norm_fderiv_fderiv_le_on hU hf hs hsU hM hx hp
  have h₂ := abs_sub_fderiv_le_of_norm_fderiv_fderiv_le_on hU hf hs hsU hM hx hm
  have e₁ : x + u - x = u := by abel
  have e₂ : x - u - x = -u := by abel
  rw [e₁] at h₁
  rw [e₂] at h₂
  have h₁' := (abs_le.mp h₁).2
  have h₂' := (abs_le.mp h₂).2
  have hneg : (fderiv ℝ f x) (-u) = -(fderiv ℝ f x) u := map_neg _ _
  rw [hneg, norm_neg] at h₂'
  linarith

/-- A `C²` function on an open set has a uniformly bounded second derivative
on every compact subset. -/
theorem exists_bound_fderiv_fderiv_of_isCompact
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ K, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ M := by
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  have h : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ f)) U :=
    h1.fderiv_of_isOpen hU (by norm_num)
  obtain ⟨M₀, hM₀⟩ :=
    IsCompact.exists_bound_of_continuousOn (E := E →L[ℝ] E →L[ℝ] ℝ) hK
      (h.continuousOn.mono hKU)
  exact ⟨max M₀ 0, le_max_right _ _,
    fun y hy => (hM₀ y hy).trans (le_max_left M₀ 0)⟩

end SGPT.Foundations.Analysis.Pending.SemiconcaveHessian

end
