/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Coercivity
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Regularity
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The gradient image of a strictly convex function

For a differentiable convex `u`, `p` is a value of `∇u` exactly when the tilt `u − ⟪p, ·⟫` attains
its minimum. For strictly
convex `u` on a proper space such tilts grow linearly, so the range of `∇u` is convex and open; in
finite dimension `∇u` is an
open map and a homeomorphism onto its range. The open map argument uses compactness and coercive
tilts only: neither
invariance of domain nor an invertible Hessian.
-/

@[expose] public section

section

namespace FunctionalInequalities.Analysis

section TiltMinima

open Set Metric Filter
open scoped Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
For a differentiable convex `u`, `p` is a value of `∇u` if and only if the tilt `x ↦ u x − ⟪p, x⟫`
attains its minimum
(supporting plane in one direction, Fermat's rule in the other). -/
theorem mem_range_gradient_iff_tilt_min {u : E → ℝ} (hu : ConvexOn ℝ univ u)
    (hd : Differentiable ℝ u) (p : E) :
    p ∈ range (gradient u) ↔ ∃ a, ∀ x, u a - ⟪p, a⟫ ≤ u x - ⟪p, x⟫ := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, fun x => ?_⟩
    have h := gradient_le_increment hu a (x - a) (hd a)
    have hx : a + (x - a) = x := by abel
    rw [hx, inner_sub_right] at h
    linarith
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hmin : IsMinOn (fun x => u x - ⟪p, x⟫) univ a := isMinOn_univ_iff.mpr ha
    have hD : HasFDerivAt (fun x => u x - ⟪p, x⟫) (fderiv ℝ u a - innerSL ℝ p) a :=
      (hd a).hasFDerivAt.sub (innerSL ℝ p).hasFDerivAt
    have hz := (hmin.isLocalMin (by simp)).hasFDerivAt_eq_zero hD
    apply (InnerProductSpace.toDual ℝ E).injective
    rw [toDual_gradient]
    exact sub_eq_zero.mp hz

/--
For a differentiable strictly convex `u` on a proper space and `p` in the range of `∇u`, the tilt `u
− ⟪p, ·⟫` grows at
least linearly. -/
theorem exists_linear_lower_bound_at_gradient [ProperSpace E] {u : E → ℝ}
    (hu : StrictConvexOn ℝ univ u) (hd : Differentiable ℝ u) {p : E}
    (hp : p ∈ range (gradient u)) : ∃ c : ℝ, 0 < c ∧ ∃ b : ℝ, ∀ x, c * ‖x‖ + b ≤ u x - ⟪p, x⟫ := by
  obtain ⟨a, ha⟩ := (mem_range_gradient_iff_tilt_min hu.convexOn hd p).mp hp
  let g := fun x => u x - ⟪p, x⟫
  have hs : StrictConvexOn ℝ univ g :=
    hu.sub_concaveOn ((innerSL ℝ p).toLinearMap.concaveOn convex_univ)
  have hc : Continuous g := hd.continuous.sub (innerSL ℝ p).continuous
  have hmin : IsMinOn g univ a := isMinOn_univ_iff.mpr ha
  apply exists_linear_lower_bound_of_strict_min hs.convexOn hc a
  intro x hx
  apply lt_of_le_of_ne (ha x)
  intro heq
  have hxMin : IsMinOn g univ x := by
    intro z _
    change u x - ⟪p, x⟫ ≤ u z - ⟪p, z⟫
    rw [← heq]
    exact ha z
  exact hx (hs.eq_of_isMinOn hmin hxMin (mem_univ a) (mem_univ x)).symm

/--
The range of the gradient of a differentiable strictly convex function on a proper space is convex.
-/
theorem convex_range_gradient [ProperSpace E] {u : E → ℝ} (hu : StrictConvexOn ℝ univ u)
    (hd : Differentiable ℝ u) : Convex ℝ (range (gradient u)) := by
  intro p hp q hq α β hα hβ hab
  obtain ⟨c₀, hc₀, b₀, hb₀⟩ := exists_linear_lower_bound_at_gradient hu hd hp
  obtain ⟨c₁, hc₁, b₁, hb₁⟩ := exists_linear_lower_bound_at_gradient hu hd hq
  let z := α • p + β • q
  have hcoef : 0 < α * c₀ + β * c₁ := by
    by_cases h : α = 0
    · have hβ1 : β = 1 := by linarith
      simpa only [h, hβ1, zero_mul, one_mul, zero_add] using hc₁
    · have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm h)
      exact add_pos_of_pos_of_nonneg (mul_pos hαp hc₀) (mul_nonneg hβ hc₁.le)
  have hbound (x : E) : (α * c₀ + β * c₁) * ‖x‖ + (α * b₀ + β * b₁) ≤ u x - ⟪z, x⟫ := by
    have h0 := mul_le_mul_of_nonneg_left (hb₀ x) hα
    have h1 := mul_le_mul_of_nonneg_left (hb₁ x) hβ
    have hz : ⟪z, x⟫ = α * ⟪p, x⟫ + β * ⟪q, x⟫ := by
      simp only [z, inner_add_left, real_inner_smul_left]
    rw [hz]
    have hux : (α + β) * u x = u x := by rw [hab, one_mul]
    nlinarith
  have hcont : Continuous (fun x => u x - ⟪z, x⟫) := hd.continuous.sub (innerSL ℝ z).continuous
  exact
    (mem_range_gradient_iff_tilt_min hu.convexOn hd z).mpr
      (exists_min_of_linear_lower_bound hcont hcoef hbound)

/--
The range of the gradient of a differentiable strictly convex function on a proper space is open:
tilts by nearby `q`
remain coercive and attain their minima. -/
theorem isOpen_range_gradient [ProperSpace E] {u : E → ℝ} (hu : StrictConvexOn ℝ univ u)
    (hd : Differentiable ℝ u) : IsOpen (range (gradient u)) := by
  apply Metric.isOpen_iff.mpr
  intro p hp
  obtain ⟨c, hc, b, hb⟩ := exists_linear_lower_bound_at_gradient hu hd hp
  refine ⟨c, hc, fun q hq => ?_⟩
  have hdist : ‖q - p‖ < c := by simpa only [mem_ball, dist_eq_norm] using hq
  have hbound (x : E) : (c - ‖q - p‖) * ‖x‖ + b ≤ u x - ⟪q, x⟫ := by
    have h0 := hb x
    have h1 := real_inner_le_norm (q - p) x
    rw [inner_sub_left] at h1
    nlinarith
  exact
    (mem_range_gradient_iff_tilt_min hu.convexOn hd q).mpr
      (exists_min_of_linear_lower_bound (hd.continuous.sub (innerSL ℝ q).continuous)
        (sub_pos.mpr hdist) hbound)

end TiltMinima

section OpenMap

open Set Metric Filter Topology FunctionalInequalities
open scoped Topology RealInnerProductSpace

/-- If `a` minimizes `u − ⟪p, ·⟫` for a differentiable `u`, then `∇u(a) = p`. -/
theorem gradient_eq_of_tilt_min {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {u : E → ℝ} (hd : Differentiable ℝ u) (p a : E)
    (ha : ∀ x, u a - ⟪p, a⟫ ≤ u x - ⟪p, x⟫) : gradient u a = p := by
  have hmin : IsMinOn (fun x => u x - ⟪p, x⟫) univ a := isMinOn_univ_iff.mpr ha
  have hD : HasFDerivAt (fun x => u x - ⟪p, x⟫) (fderiv ℝ u a - innerSL ℝ p) a :=
    (hd a).hasFDerivAt.sub (innerSL ℝ p).hasFDerivAt
  have hz := (hmin.isLocalMin (by simp)).hasFDerivAt_eq_zero hD
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient]
  exact sub_eq_zero.mp hz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/--
**Open gradient map.** The gradient of a differentiable strictly convex function on a
finite-dimensional space is an
open map. Near `p = ∇u(a)` every tilt minimizer lies in one fixed ball, and the closed image of the
compact part of that
ball outside an open `U ∋ a` misses `p`. Neither invariance of domain nor an invertible Hessian is
used. -/
theorem isOpenMap_gradient_of_strictConvexOn {u : E → ℝ} (hu : StrictConvexOn ℝ univ u)
    (hd : Differentiable ℝ u) : IsOpenMap (gradient u) := by
  have hg : Continuous (gradient u) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      ((Analysis.contDiff_one_of_convexOn_of_differentiable hu.convexOn hd).continuous_fderiv
        one_ne_zero)
  have hinj := Analysis.injective_gradient_of_strictConvexOn hd hu
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro p ⟨a, haU, rfl⟩
  let p := gradient u a
  obtain ⟨c, hc, b, hb⟩ := exists_linear_lower_bound_at_gradient hu hd (mem_range_self a)
  let R := 2 * (u 0 - b) / c
  let F := closedBall (0 : E) R \ U
  have hcomp : IsCompact F := (isCompact_closedBall (0 : E) R).diff hU
  have hclosed : IsClosed (gradient u '' F) := (hcomp.image hg).isClosed
  have hnot : p ∉ gradient u '' F := by
    rintro ⟨x, hx, hxp⟩
    have he : x = a := hinj hxp
    exact hx.2 (he ▸ haU)
  have hn : ball p (c / 2) ∩ (gradient u '' F)ᶜ ∈ 𝓝 p :=
    inter_mem (ball_mem_nhds p (by linarith)) (hclosed.isOpen_compl.mem_nhds hnot)
  apply mem_of_superset hn
  rintro q ⟨hq, hqF⟩
  have hdist : ‖q - p‖ < c / 2 := by simpa only [mem_ball, dist_eq_norm] using hq
  have hbound (x : E) : (c - ‖q - p‖) * ‖x‖ + b ≤ u x - ⟪q, x⟫ := by
    have h0 := hb x
    have h1 := real_inner_le_norm (q - p) x
    rw [inner_sub_left] at h1
    nlinarith
  obtain ⟨x, hx⟩ :=
    exists_min_of_linear_lower_bound (hd.continuous.sub (innerSL ℝ q).continuous)
      (by linarith : 0 < c - ‖q - p‖) hbound
  have hxg : gradient u x = q := gradient_eq_of_tilt_min hd q x hx
  have hxR : x ∈ closedBall (0 : E) R := by
    rw [mem_closedBall, dist_zero_right]
    apply (le_div_iff₀ hc).mpr
    have h0 := hx 0
    change u x - ⟪q, x⟫ ≤ u 0 - ⟪q, 0⟫ at h0
    simp only [inner_zero_right, sub_zero] at h0
    have hbnd := hbound x
    have hmul := mul_le_mul_of_nonneg_right hdist.le (norm_nonneg x)
    nlinarith
  refine ⟨x, ?_, hxg⟩
  by_contra hnU
  exact hqF ⟨x, ⟨hxR, hnU⟩, hxg⟩

/--
The gradient of a differentiable strictly convex function on a finite-dimensional space is a
homeomorphism onto its
range (continuous, injective and open). -/
theorem exists_gradient_homeomorph_range {u : E → ℝ} (hu : StrictConvexOn ℝ univ u)
    (hd : Differentiable ℝ u) : ∃ e : E ≃ₜ range (gradient u), ∀ x, (e x : E) = gradient u x := by
  have hg : Continuous (gradient u) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      ((Analysis.contDiff_one_of_convexOn_of_differentiable hu.convexOn hd).continuous_fderiv
        one_ne_zero)
  have he :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap hg
      (Analysis.injective_gradient_of_strictConvexOn hd hu)
      (isOpenMap_gradient_of_strictConvexOn hu hd)
  exact ⟨he.toIsEmbedding.toHomeomorph, fun _ => rfl⟩

end OpenMap

end FunctionalInequalities.Analysis
