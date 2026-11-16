/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Extrema
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.SupportingPlane

/-!
# Supporting inequalities and global/domain supporting images

Supporting convex infrastructure for Letwin arXiv:2607.24164v1
Theorem 1.2 and Lemma 2.2. Mathematical scopes and source attributions
are retained in the individual declarations.
-/

@[expose] public section

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis
/-- Convex first-order support from a derivative WITHIN its domain; no ambient
regularity, completeness or unique-differentiability premise is needed.
Supports CNS1984 Lemma5.1 (5.3), pp385-387. -/
theorem convex_support_of_hasFDerivWithinAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set F} {v : F → ℝ} {v' : F →L[ℝ] ℝ} {z y : F}
    (hconv : ConvexOn ℝ S v) (hd : HasFDerivWithinAt v v' S z)
    (hz : z ∈ S) (hy : y ∈ S) :
    v z + v' (y - z) ≤ v y := by
  -- the segment from `z` to `y` lies in `S`
  have hmaps : MapsTo (AffineMap.lineMap z y : ℝ →ᵃ[ℝ] F) (Icc 0 1) S := by
    intro t ht
    apply hconv.1.segment_subset hz hy
    rw [segment_eq_image_lineMap]
    exact mem_image_of_mem _ ht
  -- convexity along the segment
  have hg : ConvexOn ℝ (Icc (0 : ℝ) 1) (v ∘ (AffineMap.lineMap z y : ℝ →ᵃ[ℝ] F)) :=
    (hconv.comp_affineMap (AffineMap.lineMap z y)).subset (fun _ ht => hmaps ht) (convex_Icc 0 1)
  -- derivative along the segment, within `Icc 0 1`, at `0`
  have hder : HasDerivWithinAt (v ∘ (AffineMap.lineMap z y : ℝ →ᵃ[ℝ] F)) (v' (y - z)) (Icc 0 1) 0 :=
    hd.comp_hasDerivWithinAt_of_eq 0 AffineMap.hasDerivAt_lineMap.hasDerivWithinAt hmaps
      (AffineMap.lineMap_apply_zero z y).symm
  have hslope := hg.le_slope_of_hasDerivWithinAt (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one) zero_lt_one hder
  rw [slope_def_field, Function.comp_apply, Function.comp_apply, AffineMap.lineMap_apply_one,
    AffineMap.lineMap_apply_zero, sub_zero, div_one] at hslope
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A slope supporting on an open neighborhood of a differentiability point
is the actual gradient. Neither convexity nor global support is needed. -/
lemma subgradientOn_eq_gradient [CompleteSpace E]
    {u : E → ℝ} {S : Set E} (hS : IsOpen S) {x p : E} (hxS : x ∈ S)
    (hx : DifferentiableAt ℝ u x)
    (hp : ∀ y ∈ S, u x + ⟪p, y - x⟫ ≤ u y) :
    p = gradient u x := by
  have hm :
      IsLocalMin (fun y => u y - (InnerProductSpace.toDual ℝ E p) y) x := by
    filter_upwards [hS.mem_nhds hxS] with y hy
    change u x - (InnerProductSpace.toDual ℝ E p) x ≤
      u y - (InnerProductSpace.toDual ℝ E p) y
    simp only [InnerProductSpace.toDual_apply_apply]
    have h := hp y hy
    rw [inner_sub_right] at h
    linarith
  have hz := hm.hasFDerivAt_eq_zero
    (hx.hasGradientAt.hasFDerivAt.sub (InnerProductSpace.toDual ℝ E p).hasFDerivAt)
  exact ((InnerProductSpace.toDual ℝ E).injective (sub_eq_zero.mp hz)).symm

/-- At a differentiability point, an actual global supporting subgradient is
exactly the gradient. No convexity or uniqueness conclusion is an input. -/
lemma subgradient_eq_gradient [CompleteSpace E]
    {u : E → ℝ} {x p : E} (hx : DifferentiableAt ℝ u x)
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) :
    p = gradient u x := by
  exact subgradientOn_eq_gradient isOpen_univ (mem_univ x) hx (fun y _ => hp y)

/-- A differentiable convex function lies above its tangent plane, on any complete real
inner-product space. -/
lemma gradient_le_increment [CompleteSpace E]
    {u : E → ℝ} (hc : ConvexOn ℝ univ u)
    (z v : E) (hz : DifferentiableAt ℝ u z) :
    ⟪gradient u z, v⟫ ≤ u (z + v) - u z := by
  have h := convex_support_of_hasFDerivWithinAt hc
    hz.hasGradientAt.hasFDerivAt.hasFDerivWithinAt (mem_univ z) (mem_univ (z + v))
  simp only [add_sub_cancel_left, InnerProductSpace.toDual_apply_apply] at h
  linarith

/-- A strictly convex function lies strictly above the tangent plane at an
actual differentiability point. Only membership in the strict-convex set is
needed; the function need not be differentiable elsewhere. -/
lemma gradient_tangent_gap_pos_of_strictConvexOn [CompleteSpace E]
    {u : E → ℝ} {S : Set E} (hs : StrictConvexOn ℝ S u)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (hdx : DifferentiableAt ℝ u x) :
    0 < u y - u x - ⟪gradient u x, y - x⟫ := by
  let l : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hi : Function.Injective l := AffineMap.lineMap_injective ℝ hxy
  have hl : ∀ t ∈ Icc (0 : ℝ) 1, l t ∈ S := by
    intro t ht
    have hc : (1 - t : ℝ) • x + t • y ∈ S :=
      hs.1 hx hy (by linarith [ht.2]) ht.1 (by ring)
    convert hc using 1
    dsimp [l, AffineMap.lineMap_apply]
    module
  have hc : StrictConvexOn ℝ (Icc (0 : ℝ) 1) (u ∘ l) := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro a ha b hb hab s t hs' ht' hst
    change u (l (s • a + t • b)) < s • u (l a) + t • u (l b)
    rw [Convex.combo_affine_apply hst]
    exact hs.2 (hl a ha) (hl b hb) (fun h => hab (hi h)) hs' ht' hst
  have hd : HasDerivAt (u ∘ l) ⟪gradient u x, y - x⟫ 0 := by
    have hd0 : HasFDerivAt u ((InnerProductSpace.toDual ℝ E) (gradient u x)) (l 0) := by
      simpa only [l, AffineMap.lineMap_apply_zero] using hdx.hasGradientAt.hasFDerivAt
    have h := hd0.comp_hasDerivAt 0
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
    simpa only [AffineMap.lineMap_apply_zero, InnerProductSpace.toDual_apply_apply] using h
  have h := hc.lt_slope_of_hasDerivAt (by norm_num) (by norm_num) zero_lt_one hd
  simp only [slope_def_field, Function.comp_apply, l, AffineMap.lineMap_apply_one,
    AffineMap.lineMap_apply_zero, sub_zero, div_one] at h
  linarith


end FunctionalInequalities.Analysis
section SubgradientImageMonotone

open Set
open scoped RealInnerProductSpace
open scoped Topology

/-! Monotonicity of subgradient images (Gutiérrez Lemma 1.4.1). -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A real support on an open neighbourhood extends to the whole convex
support domain. No completeness, finite dimension or differentiability is needed. -/
theorem subgradient_le_on_of_isOpen {u : E → ℝ} {Ω D : Set E} (hu : ConvexOn ℝ D u)
    (hΩ : IsOpen Ω) (hΩD : Ω ⊆ D) {x p : E} (hx : x ∈ Ω)
    (hp : ∀ y ∈ Ω, u x + ⟪p, y - x⟫ ≤ u y) : ∀ y ∈ D, u x + ⟪p, y - x⟫ ≤ u y := by
  have hlocal : IsLocalMin (fun z => u z - ⟪p, z⟫) x := by
    filter_upwards [hΩ.mem_nhds hx] with z hz
    have hm := hp z hz
    rw [inner_sub_right] at hm
    change u x - ⟪p, x⟫ ≤ u z - ⟪p, z⟫
    linarith
  have hmin :=
    IsMinOn.of_isLocalMinOn_of_convexOn (hΩD hx) (hlocal.isLocalMinOn D)
      (hu.sub ((innerSL ℝ p).toLinearMap.concaveOn hu.1))
  intro y hy
  have hm := hmin hy
  change u x - ⟪p, x⟫ ≤ u y - ⟪p, y⟫ at hm
  rw [inner_sub_right]
  linarith

private lemma support_on_of_max {u : E → ℝ} {Ω D : Set E} (hu : ConvexOn ℝ D u) (hΩ : IsOpen Ω)
    (hΩD : Ω ⊆ D) (x₀ x₁ p : E) (c : ℝ) (hx₁ : x₁ ∈ Ω)
    (hmax : IsMaxOn (fun z => c + ⟪p, z - x₀⟫ - u z) (closure Ω) x₁) :
    ∀ y ∈ D, u x₁ + ⟪p, y - x₁⟫ ≤ u y := by
  apply subgradient_le_on_of_isOpen hu hΩ hΩD hx₁
  intro z hz
  have hm := hmax (subset_closure hz)
  change c + ⟪p, z - x₀⟫ - u z ≤ c + ⟪p, x₁ - x₀⟫ - u x₁ at hm
  simp only [inner_sub_right] at hm ⊢
  linarith

/-- The **subgradient image** `∂u(S) = {p | ∃ x ∈ S, p is a subgradient of u at x}`. -/
def subgradientImage {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : E → ℝ)
    (S : Set E) : Set E :=
  {p | ∃ x ∈ S, ∀ y, u x + ⟪p, y - x⟫ ≤ u y}

/-- The supporting-slope image relative to a domain. No convexity, topology of
sets, differentiability, finite dimension or measurability is part of this object. -/
def subgradientImageOn (u : E → ℝ) (D G : Set E) : Set E :=
  {p | ∃ x ∈ G, ∀ y ∈ D, u x + ⟪p, y - x⟫ ≤ u y}

/-- Enlarging the set of basepoints enlarges its domain-relative supporting image.
This is a pure set property, with no convexity or regularity hypothesis. -/
theorem subgradientImageOn_mono (u : E → ℝ) (D : Set E) : Monotone (subgradientImageOn u D) := by
  intro A B hAB
  rintro p ⟨x, hx, hp⟩
  exact ⟨x, hAB hx, hp⟩

/-- Pointwise order and equality at the actual contact points preserve the
SAME domain-supporting slopes. No topology, convexity, dimension or measure. -/
theorem subgradientImageOn_subset_of_le_of_eqOn {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E → ℝ) (D G : Set E) (hle : ∀ y ∈ D, u y ≤ v y)
    (heq : EqOn u v G) : subgradientImageOn u D G ⊆ subgradientImageOn v D G := by
  rintro p ⟨x, hx, hs⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  rw [← heq hx]
  exact (hs y hy).trans (hle y hy)

/-- At basepoints where the left function attains the maximum, each of its
actual domain-supporting slopes supports the maximum. This is a pure support
property, without topology/convexity/differentiability or measure premises. -/
theorem subgradientImageOn_subset_max_of_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E → ℝ) (Ω G : Set E) (hc : ∀ x ∈ G, v x ≤ u x) :
    subgradientImageOn u Ω G ⊆ subgradientImageOn (fun x => max (u x) (v x)) Ω G := by
  apply subgradientImageOn_subset_of_le_of_eqOn u (fun x => max (u x) (v x)) Ω G
  · intro y _hy
    exact le_max_left _ _
  · intro x hx
    exact (max_eq_left (hc x hx)).symm

/-- The ambient support domain recovers the original global image. -/
theorem subgradientImageOn_univ (u : E → ℝ) (G : Set E) :
    subgradientImageOn u univ G = subgradientImage u G := by
  ext p
  simp only [subgradientImageOn, subgradientImage, mem_ofPred_eq, mem_univ, true_implies]

/-- Every actual supporting slope of a constant on an open domain is zero.
No dimension, completeness, convexity or differentiability premise is needed. -/
theorem subgradientImageOn_const_subset_singleton (c : ℝ) {Ω G : Set E} (hΩ : IsOpen Ω)
    (hG : G ⊆ Ω) : subgradientImageOn (fun _ : E => c) Ω G ⊆ {0} := by
  rintro p ⟨x, hx, hp⟩
  have hall :=
    subgradient_le_on_of_isOpen (convexOn_const c convex_univ) hΩ (subset_univ _) (hG hx) hp
  have h := hall (x + p) (mem_univ _)
  have hinner : ⟪p, p⟫ ≤ 0 := by
    simpa only [add_sub_cancel_left] using (show ⟪p, x + p - x⟫ ≤ 0 by linarith)
  have hp0 : p = 0 := (inner_self_eq_zero.mp (le_antisymm hinner (real_inner_self_nonneg)))
  exact mem_singleton_iff.mpr hp0

private theorem support_on_closure {u : E → ℝ} {Ω : Set E} (hu : ContinuousOn u (closure Ω))
    {x p : E} (hp : ∀ y ∈ Ω, u x + ⟪p, y - x⟫ ≤ u y) :
    ∀ y ∈ closure Ω, u x + ⟪p, y - x⟫ ≤ u y := by
  let a : E → ℝ := fun y => u x + ⟪p, y - x⟫
  have ha : ContinuousOn a (closure Ω) := by dsimp [a]; fun_prop
  have hs : closure Ω ⊆ {y | y ∈ closure Ω ∧ a y ≤ u y} :=
    closure_minimal (fun y hy => ⟨subset_closure hy, hp y hy⟩)
      (isClosed_closure.isClosed_le ha hu)
  exact fun y hy => (hs hy).2

/-- Actual closure continuity extends supporting inequalities to the closure;
no global extension or image agreement is assumed. -/
theorem subgradientImageOn_closure {u : E → ℝ} {Ω : Set E} (hu : ContinuousOn u (closure Ω))
    (G : Set E) : subgradientImageOn u (closure Ω) G = subgradientImageOn u Ω G := by
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    exact ⟨x, hx, fun y hy => hp y (subset_closure hy)⟩
  · rintro ⟨x, hx, hp⟩
    refine ⟨x, hx, ?_⟩
    exact support_on_closure hu hp

/-- Actual domain supports at locally differentiable points are real gradients;
there is no convexity, injectivity, image-agreement or N-property input. -/
theorem subgradientImageOn_subset_gradient_image {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {v : E → ℝ} {Ω G : Set E} (hΩ : IsOpen Ω)
    (hd : DifferentiableOn ℝ v Ω) (hG : G ⊆ Ω) : subgradientImageOn v Ω G ⊆ gradient v '' G := by
  rintro p ⟨x, hx, hp⟩
  have heq :=
    subgradientOn_eq_gradient hΩ (hG hx) ((hd x (hG hx)).differentiableAt (hΩ.mem_nhds (hG hx)))
      hp
  exact ⟨x, hx, heq.symm⟩


/-- Restricting the support domain to an actual open neighbourhood of the
basepoints preserves its supporting image. Convexity is required only on the
larger domain; no smaller-domain convexity, regularity, dimension or measure. -/
theorem subgradientImageOn_eq_of_isOpen_subset {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u : E → ℝ} {D T G : Set E} (hu : ConvexOn ℝ D u) (hT : IsOpen T)
    (hTD : T ⊆ D) (hGT : G ⊆ T) : subgradientImageOn u T G = subgradientImageOn u D G := by
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    exact ⟨x, hx, subgradient_le_on_of_isOpen hu hT hTD (hGT hx) hp⟩
  · rintro ⟨x, hx, hp⟩
    exact ⟨x, hx, fun y hy => hp y (hTD hy)⟩

/-- A globally convex function has the same domain-relative and global
supporting images on every subset of an open domain. This uses the actual
nondifferentiable open-support lift, without completeness or regularity. -/
theorem subgradientImageOn_eq_subgradientImage_of_isOpen {u : E → ℝ} (hu : ConvexOn ℝ univ u)
    {Ω : Set E} (hΩ : IsOpen Ω) {G : Set E} (hG : G ⊆ Ω) :
    subgradientImageOn u Ω G = subgradientImage u G := by
  rw [← subgradientImageOn_univ u G]
  exact subgradientImageOn_eq_of_isOpen_subset hu hΩ (subset_univ _) hG

/-- For an actual globally convex function differentiable only on an open domain,
the real domain supporting image equals the global image on every subset. -/
theorem subgradientImageOn_eq_subgradientImage [CompleteSpace E] {u : E → ℝ}
    (hu : ConvexOn ℝ univ u) {Ω : Set E} (hΩ : IsOpen Ω) (hd : DifferentiableOn ℝ u Ω)
    {G : Set E} (hG : G ⊆ Ω) : subgradientImageOn u Ω G = subgradientImage u G := by
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    have hdAt : DifferentiableAt ℝ u x := (hd x (hG hx)).differentiableAt (hΩ.mem_nhds (hG hx))
    have heq : p = gradient u x := subgradientOn_eq_gradient hΩ (hG hx) hdAt hp
    have hgrad : ∀ z ∈ Ω, u x + ⟪gradient u x, z - x⟫ ≤ u z := by simpa only [heq] using hp
    rw [heq]
    exact (subgradientImageOn_eq_subgradientImage_of_isOpen hu hΩ hG).subset ⟨x, hx, hgrad⟩
  · rintro ⟨x, hx, hp⟩
    exact ⟨x, hx, fun y _ => hp y⟩

/-- Positive function scaling scales the genuine domain supporting image. -/
theorem subgradientImageOn_mul_pos (u : E → ℝ) {c : ℝ} (hc : 0 < c) (D G : Set E) :
    subgradientImageOn (fun x => c * u x) D G =
      (fun p : E => c • p) '' subgradientImageOn u D G := by
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    refine ⟨c⁻¹ • p, ⟨x, hx, ?_⟩, ?_⟩
    · intro y hy
      apply le_of_mul_le_mul_left (a := c) ?_ hc
      have h := hp y hy
      change c * u x + ⟪p, y - x⟫ ≤ c * u y at h
      simpa [real_inner_smul_left, mul_add, ← mul_assoc, ne_of_gt hc] using h
    · simp [smul_smul, ne_of_gt hc]
  · rintro ⟨q, ⟨x, hx, hq⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    intro y hy
    simpa only [real_inner_smul_left, mul_add] using mul_le_mul_of_nonneg_left (hq y hy) hc.le

/-- Gutiérrez's comparison of supporting images with an actual support domain.
The bounded open comparison set need not be convex. Actual closure containment,
continuity and boundary equality produce the new support by a compact maximum. -/
theorem subgradientImageOn_subset_of_le [FiniteDimensional ℝ E] {u v : E → ℝ} {D Ω : Set E}
    (hu : ConvexOn ℝ D u) (huc : ContinuousOn u (closure Ω)) (hvc : ContinuousOn v (closure Ω))
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hD : closure Ω ⊆ D) (hle : ∀ x ∈ Ω, u x ≤ v x)
    (heq : ∀ x ∈ frontier Ω, u x = v x) : subgradientImageOn v D Ω ⊆ subgradientImageOn u D Ω := by
  rintro p ⟨x₀, hx₀, hp⟩
  let w : E → ℝ := fun z => v x₀ + ⟪p, z - x₀⟫ - u z
  have hlin : Continuous (fun z : E => ⟪p, z - x₀⟫) := by fun_prop
  have hwc : ContinuousOn w (closure Ω) := (continuousOn_const.add hlin.continuousOn).sub huc
  obtain ⟨x₁, hx₁, hmax⟩ := hb.isCompact_closure.exists_isMaxOn ⟨x₀, subset_closure hx₀⟩ hwc
  have hΩD : Ω ⊆ D := subset_closure.trans hD
  by_cases hx₁Ω : x₁ ∈ Ω
  · exact ⟨x₁, hx₁Ω, support_on_of_max hu hΩ hΩD x₀ x₁ p (v x₀) hx₁Ω hmax⟩
  · have hwx₀ : 0 ≤ w x₀ := by simpa [w] using hle x₀ hx₀
    have hax : 0 ≤ w x₁ := hwx₀.trans (hmax (subset_closure hx₀))
    have hfront : x₁ ∈ frontier Ω := by rw [hΩ.frontier_eq]; exact ⟨hx₁, hx₁Ω⟩
    have hupper : w x₁ ≤ 0 := by
      have hpcl := support_on_closure hvc (x := x₀) (p := p) (fun y hy => hp y (hΩD hy))
      have hp₁ := hpcl x₁ hx₁
      rw [← heq x₁ hfront] at hp₁
      dsimp [w]
      linarith
    have hax0 : w x₁ = 0 := le_antisymm hupper hax
    have hwzero : w x₀ = 0 := le_antisymm (by simpa [hax0] using hmax (subset_closure hx₀)) hwx₀
    have hmax₀ : IsMaxOn w (closure Ω) x₀ := by
      intro z hz
      simpa [hax0, hwzero] using hmax hz
    exact ⟨x₀, hx₀, support_on_of_max hu hΩ hΩD x₀ x₀ p (v x₀) hx₀ hmax₀⟩

/-- **Monotonicity of subgradient images under comparison** (Gutiérrez, *The Monge–Ampère
equation*, Lemma 1.4.1; comparison principle): if `u ≤ v` on a
bounded open `Ω` and `u = v` on its frontier, then `∂v(Ω) ⊆ ∂u(Ω)`. -/
theorem subgradientImage_subset_of_le
    [FiniteDimensional ℝ E] {u v : E → ℝ} (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hle : ∀ x ∈ Ω, u x ≤ v x)
    (heq : ∀ x ∈ frontier Ω, u x = v x) : subgradientImage v Ω ⊆ subgradientImage u Ω := by
  have huc : Continuous u := continuousOn_univ.mp (hu.continuousOn isOpen_univ)
  have hvc : Continuous v := continuousOn_univ.mp (hv.continuousOn isOpen_univ)
  have hucont : ContinuousOn u (closure Ω) := huc.continuousOn
  simpa only [subgradientImageOn_univ] using
    subgradientImageOn_subset_of_le hu hucont hvc.continuousOn hΩ hb (subset_univ _) hle heq

end InnerProduct

end FunctionalInequalities.Analysis

end SubgradientImageMonotone
namespace FunctionalInequalities.Analysis
open Set Metric
open scoped Topology

/-- The actual supporting graph on a subset subtype is closed under reference
continuity there. No dimension, completeness, measure, convexity or open-domain
assumption is needed. -/
theorem isClosed_subgradient_graphOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v : E → ℝ} {D K : Set E} (hvc : ContinuousOn v K) :
    IsClosed {q : K × E | ∀ y ∈ D, v q.1.val + ⟪q.2, y - q.1.val⟫ ≤ v y} := by
  have hc : Continuous (fun x : K => v x.val) := continuousOn_iff_continuous_domRestrict.mp hvc
  have heq :
    {q : K × E | ∀ y ∈ D, v q.1.val + ⟪q.2, y - q.1.val⟫ ≤ v y} =
      ⋂ y ∈ D, {q : K × E | v q.1.val + ⟪q.2, y - q.1.val⟫ ≤ v y} := by
    ext q
    simp
  rw [heq]
  apply isClosed_biInter
  intro y _hy
  exact
    isClosed_le
      ((hc.comp continuous_fst).add
        (continuous_snd.inner
          (continuous_const.sub (continuous_subtype_val.comp continuous_fst))))
      continuous_const

end FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
open Set
/-- Domain supporting images preserve arbitrary indexed unions. This is a pure
set identity, without dimension, topology, measure or countability premises. -/
theorem subgradientImageOn_iUnion {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Sort*} (v : E → ℝ) (D : Set E) (G : ι → Set E) :
    subgradientImageOn v D (⋃ i, G i) = ⋃ i, subgradientImageOn v D (G i) := by
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    rcases mem_iUnion.mp hx with ⟨i, hi⟩
    exact mem_iUnion.mpr ⟨i, x, hi, hp⟩
  · intro hp
    rcases mem_iUnion.mp hp with ⟨i, x, hx, hp⟩
    exact ⟨x, mem_iUnion.mpr ⟨i, hx⟩, hp⟩
end FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The supporting image of a compact set is closed for a continuous real source.
No convexity or finite-dimensional hypothesis is required. -/
theorem isClosed_subgradientImage_of_isCompact {u : E → ℝ} (hu : Continuous u) {S : Set E}
    (hS : IsCompact S) : IsClosed (subgradientImage u S) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let C : Set (S × E) := {q | ∀ y : E, u q.1.val + ⟪q.2, y - q.1.val⟫ ≤ u y}
  have hC : IsClosed C := by
    simpa only [mem_univ, forall_true_left] using
      (isClosed_subgradient_graphOn (D := univ) (K := S) hu.continuousOn)
  have himage : Prod.snd '' C = subgradientImage u S := by
    ext p
    constructor
    · rintro ⟨⟨x, q⟩, hq, rfl⟩
      exact ⟨x.val, x.property, hq⟩
    · rintro ⟨x, hx, hp⟩
      exact ⟨(⟨x, hx⟩, p), hp, rfl⟩
  rw [← himage]
  exact isClosedMap_snd_of_compactSpace C hC


end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis
open Set Metric

/-- A value bound on a contained ball bounds every supporting slope. -/
lemma norm_subgradient_le_of_closedBall {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : E → ℝ} {Ω : Set E} {x p : E} {r M : ℝ} (hr : 0 < r)
    (hball : closedBall x r ⊆ Ω) (hvalue : ∀ y ∈ closedBall x r, |v y| ≤ M)
    (hp : ∀ y ∈ Ω, v x + ⟪p, y - x⟫ ≤ v y) : ‖p‖ ≤ 2 * M / r := by
  have hx : x ∈ closedBall x r := mem_closedBall_self hr.le
  have hM : 0 ≤ M := (abs_nonneg (v x)).trans (hvalue x hx)
  by_cases hp0 : p = 0
  · subst p
    simpa only [norm_zero] using (show 0 ≤ 2 * M / r by positivity)
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  let t : ℝ := r / ‖p‖
  have ht : 0 < t := div_pos hr hpn
  let y : E := x + t • p
  have hdist : dist y x = r := by
    rw [dist_eq_norm]
    dsimp [y]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    field_simp [ne_of_gt hpn]
  have hy : y ∈ closedBall x r := mem_closedBall.mpr hdist.le
  have hfx := (abs_le.mp (hvalue x hx)).1
  have hfy := (abs_le.mp (hvalue y hy)).2
  have hinner : ⟪p, y - x⟫ = r * ‖p‖ := by
    dsimp [y]
    rw [add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq]
    dsimp [t]
    field_simp [ne_of_gt hpn]
  have hs := hp y (hball hy)
  rw [hinner] at hs
  apply (le_div_iff₀ hr).mpr
  nlinarith


end FunctionalInequalities.Analysis
