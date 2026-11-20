/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Boundary
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.MetricSpace.HausdorffDistance


/-! # Alexandrov maximum principles and convex cone-volume geometry

Supporting convex geometry for Letwin arXiv:2607.24164v1 Lemma 2.2
via Berman--Berndtsson arXiv:1207.6128v1 Theorem 2.24(ii).
Each statement retains its actual hypotheses and dimensional scope.
-/

@[expose] public section

section

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal



section FarthestPointExposed

open Set
open scoped RealInnerProductSpace

/-! Farthest points are exposed. -/

namespace FunctionalInequalities.Analysis

/-- **A farthest point of a compact set is exposed** (Caffarelli's argument):
for a nonempty compact `C` in an inner product space and any `y`, there is `x_e ∈ C` with
`⟪x − x_e, x_e − y⟫ < 0` for every other `x ∈ C`; moreover `‖x_e − y‖ ≥ ‖x − y‖` for all `x ∈ C`. -/
theorem exists_farthest_point_exposed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} (hC : IsCompact C) (hne : C.Nonempty) (y : E) :
    ∃ xe ∈ C, (∀ x ∈ C, ‖x - y‖ ≤ ‖xe - y‖) ∧ ∀ x ∈ C, x ≠ xe → ⟪x - xe, xe - y⟫ < 0 := by
  have hcont : Continuous (fun x : E => ‖x - y‖) :=
    (continuous_id.sub (continuous_const : Continuous (fun _ : E => y))).norm
  obtain ⟨xe, hxe, hmax⟩ := hC.exists_isMaxOn hne hcont.continuousOn
  have hle : ∀ x ∈ C, ‖x - y‖ ≤ ‖xe - y‖ := by
    intro x hx
    have hm : C ⊆ {z : E | ‖z - y‖ ≤ ‖xe - y‖} :=
      Filter.mem_principal.mp
        (Filter.eventually_iff.mp
          (show ∀ᶠ z in Filter.principal C, ‖z - y‖ ≤ ‖xe - y‖ from hmax))
    exact hm hx
  refine ⟨xe, hxe, hle, ?_⟩
  intro x hx hne
  have hsq : ‖x - y‖ ^ 2 ≤ ‖xe - y‖ ^ 2 :=
    sq_le_sq'
      (le_trans
        (neg_nonpos.mpr (norm_nonneg (xe - y)))
        (norm_nonneg (x - y)))
      (hle x hx)
  have hidentity :
      ‖x - y‖ ^ 2 =
        ‖x - xe‖ ^ 2 + 2 * ⟪x - xe, xe - y⟫ + ‖xe - y‖ ^ 2 := by
    calc
      ‖x - y‖ ^ 2 = ‖(x - xe) + (xe - y)‖ ^ 2 := by
        rw [sub_add_sub_cancel]
      _ = ‖x - xe‖ ^ 2 + 2 * ⟪x - xe, xe - y⟫ + ‖xe - y‖ ^ 2 :=
        norm_add_sq_real (x - xe) (xe - y)
  have hinner : 2 * ⟪x - xe, xe - y⟫ ≤ -‖x - xe‖ ^ 2 := by
    nlinarith [hsq, hidentity]
  have hnormpos : 0 < ‖x - xe‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hspos : 0 < ‖x - xe‖ ^ 2 := sq_pos_of_pos hnormpos
  nlinarith [hinner, hspos]

end FunctionalInequalities.Analysis

end FarthestPointExposed



section AlexandrovSliding

open Set Metric
open scoped RealInnerProductSpace

/-! Sliding supporting hyperplanes (Caffarelli block). -/

namespace FunctionalInequalities.Analysis

/-- **Sliding lemma for the Alexandrov maximum principle** (Caffarelli's argument):
if `u` is convex, `u ≥ 0` on the frontier of a bounded open `Ω`, `u x₀ < 0` at some `x₀ ∈ Ω`, and
the
affine function `x ↦ u x₀ + ⟪p, x − x₀⟫` is `≤ 0` on `closure Ω`, then `p` is a subgradient of `u`
at
some point of `Ω`. In particular, `closedBall 0 (-u x₀ / diam Ω) ⊆ ∂u(Ω)`, and the cone over the
ball
with apex in the direction of a nearest boundary point is contained in `∂u(Ω)`. -/
private lemma exists_interior_support_of_affine_le_on_frontier {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    {Ω : Set E} (huc : ContinuousOn u (closure Ω)) (hb : Bornology.IsBounded Ω)
    (hfr : ∀ x ∈ frontier Ω, 0 ≤ u x) {x₀ : E} (hx₀ : x₀ ∈ Ω) {p : E}
    (hp : ∀ x ∈ closure Ω, u x₀ + ⟪p, x - x₀⟫ ≤ 0) : ∃ x ∈ Ω, ∀ y ∈ Ω, u x + ⟪p, y - x⟫ ≤ u y := by
  let ell : E → ℝ := fun x => u x₀ + ⟪p, x - x₀⟫
  let w : E → ℝ := fun x => u x - ell x
  have hellc : ContinuousOn ell (closure Ω) := by
    dsimp [ell]
    fun_prop
  have hwc : ContinuousOn w (closure Ω) := by
    dsimp [w]
    exact huc.sub hellc
  have hcompact : IsCompact (closure Ω) := hb.isCompact_closure
  have hne : (closure Ω).Nonempty := ⟨x₀, subset_closure hx₀⟩
  obtain ⟨x₁, hx₁, hmin₁⟩ := hcompact.exists_isMinOn hne hwc
  have hw₀ : w x₀ = 0 := by simp [w, ell]
  have hle₁ : w x₁ ≤ 0 := by
    calc
      w x₁ ≤ w x₀ := hmin₁ (subset_closure hx₀)
      _ = 0 := hw₀
  have hfront : ∀ x ∈ frontier Ω, 0 ≤ w x := by
    intro x hx
    change 0 ≤ u x - ell x
    apply sub_nonneg.mpr
    calc
      ell x ≤ 0 := by simpa [ell] using hp x (frontier_subset_closure hx)
      _ ≤ u x := hfr x hx
  have hex : ∃ x₂ ∈ Ω, IsMinOn w (closure Ω) x₂ := by
    by_cases h₁fr : x₁ ∈ frontier Ω
    · have hw₁ : w x₁ = 0 := le_antisymm hle₁ (hfront x₁ h₁fr)
      have hmin₀ : IsMinOn w (closure Ω) x₀ := by
        intro z hz
        calc
          w x₀ = w x₁ := hw₀.trans hw₁.symm
          _ ≤ w z := hmin₁ hz
      exact ⟨x₀, hx₀, hmin₀⟩
    · have hx₁union : x₁ ∈ Ω ∪ frontier Ω := by
        rw [← closure_eq_self_union_frontier]
        exact hx₁
      exact ⟨x₁, hx₁union.resolve_right h₁fr, hmin₁⟩
  obtain ⟨x₂, hx₂, hmin₂⟩ := hex
  refine ⟨x₂, hx₂, ?_⟩
  intro y hy
  have hminy := hmin₂ (subset_closure hy)
  change u x₂ - ell x₂ ≤ u y - ell y at hminy
  dsimp [ell] at hminy ⊢
  simp only [inner_sub_right] at hminy ⊢
  linarith

theorem mem_subgradientImage_of_affine_le_of_nonneg_frontier {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hfr : ∀ x ∈ frontier Ω, 0 ≤ u x)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) (hneg : u x₀ < 0) {p : E}
    (hp : ∀ x ∈ closure Ω, u x₀ + ⟪p, x - x₀⟫ ≤ 0) : p ∈ subgradientImage u Ω := by
  have _hneg : u x₀ < 0 := hneg
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  obtain ⟨x, hx, hp⟩ :=
    exists_interior_support_of_affine_le_on_frontier hu.continuousOn hb hfr hx₀ hp
  exact
    ⟨x, hx, fun y => subgradient_le_on_of_isOpen hconv hΩ (subset_univ _) hx hp y (mem_univ y)⟩

end FunctionalInequalities.Analysis

end AlexandrovSliding

section NearestBoundaryHalfspace

open Set Metric
open scoped RealInnerProductSpace

/-! Nearest boundary points and supporting half-spaces. -/

namespace FunctionalInequalities.Analysis

/-- **Supporting half-space at a nearest boundary point of an open convex set** (Caffarelli's
argument, the `dist(x₀, ∂Ω)` factor of the Alexandrov estimate): for a bounded open convex
`Ω` and `x₀ ∈ Ω`, with `d := infDist x₀ (frontier Ω)`, there is a unit vector `e` such that
`⟪x − x₀, e⟫ ≤ d` for every `x ∈ Ω`. -/
theorem exists_unit_inner_le_infDist_frontier {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] {Ω : Set E} (hΩ : IsOpen Ω)
    (hc : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ∃ e : E, ‖e‖ = 1 ∧ ∀ x ∈ Ω, ⟪x - x₀, e⟫ ≤ infDist x₀ (frontier Ω) := by
  classical
  obtain ⟨r, hr⟩ := hb.subset_closedBall x₀
  have hcompact_ball : IsCompact (closedBall x₀ r) := isCompact_closedBall x₀ r
  have hcompact_frontier : IsCompact (frontier Ω) :=
    hcompact_ball.of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans (closure_minimal hr isClosed_closedBall))
  have hfrontier_nonempty : (frontier Ω).Nonempty := by
    by_contra hne
    have hfrontier_empty : frontier Ω = ∅ := by
      ext y
      constructor
      · intro hy
        exact (hne ⟨y, hy⟩).elim
      · intro hy
        simp at hy
    rw [frontier_eq_empty_iff] at hfrontier_empty
    rcases hfrontier_empty with hΩempty | hΩuniv
    · rw [hΩempty] at hx₀
      exact hx₀
    · obtain ⟨s, hs⟩ := hb.subset_closedBall x₀
      have hs_nonneg : 0 ≤ s := by
        have hsx : dist x₀ x₀ ≤ s := hs hx₀
        simpa only [dist_self] using hsx
      obtain ⟨v, hv⟩ := exists_ne (0 : E)
      have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hunit : ‖‖v‖⁻¹ • v‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos)]
        simp [ne_of_gt hvpos]
      let y : E := x₀ + (s + 1) • (‖v‖⁻¹ • v)
      have hyΩ : y ∈ Ω := by
        rw [hΩuniv]
        exact mem_univ y
      have hyball : y ∈ closedBall x₀ s := hs hyΩ
      have hnorm : ‖y - x₀‖ = s + 1 := by
        have hs1 : 0 ≤ s + 1 := by linarith
        calc
          ‖y - x₀‖ = ‖(s + 1) • (‖v‖⁻¹ • v)‖ := by
            dsimp [y]
            rw [add_sub_cancel_left]
          _ = ‖s + 1‖ * ‖‖v‖⁻¹ • v‖ := norm_smul _ _
          _ = (s + 1) * 1 := by
            rw [Real.norm_eq_abs, abs_of_nonneg hs1, hunit]
          _ = s + 1 := by ring
      have hydist : dist y x₀ ≤ s := by
        exact hyball
      rw [dist_eq_norm, hnorm] at hydist
      linarith
  obtain ⟨xb, hxb, hxb_dist⟩ :=
    hcompact_frontier.exists_infDist_eq_dist hfrontier_nonempty x₀
  have hxbΩ : xb ∉ Ω := by
    intro h
    apply hxb.2
    rw [hΩ.interior_eq]
    exact h
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hc hΩ hxbΩ
  let e₀ : E := (InnerProductSpace.toDual ℝ E).symm f
  have hdual (z : E) : inner ℝ e₀ z = f z := by
    dsimp [e₀]
    exact InnerProductSpace.toDual_symm_apply
  have hrepr (z : E) : f z = inner ℝ z e₀ := by
    calc
      f z = inner ℝ e₀ z := (hdual z).symm
      _ = inner ℝ z e₀ := real_inner_comm _ _
  have he₀_ne : e₀ ≠ 0 := by
    intro he₀_zero
    have hzero (z : E) : f z = 0 := by
      rw [hrepr, he₀_zero]
      simp
    have hlt := hf x₀ hx₀
    rw [hzero x₀, hzero xb] at hlt
    exact (lt_irrefl 0) hlt
  let e : E := ‖e₀‖⁻¹ • e₀
  have he_norm : ‖e‖ = 1 := by
    have hnorm_pos : 0 < ‖e₀‖ := norm_pos_iff.mpr he₀_ne
    dsimp [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm_pos)]
    simp [ne_of_gt hnorm_pos]
  refine ⟨e, he_norm, ?_⟩
  intro x hx
  have hfx : f x ≤ f xb := (hf x hx).le
  have hgap : f xb - f x₀ ≤ ‖xb - x₀‖ * ‖e₀‖ := by
    calc
      f xb - f x₀ = f (xb - x₀) := (map_sub f xb x₀).symm
      _ = inner ℝ (xb - x₀) e₀ := hrepr (xb - x₀)
      _ ≤ |inner ℝ (xb - x₀) e₀| := le_abs_self _
      _ ≤ ‖xb - x₀‖ * ‖e₀‖ := abs_real_inner_le_norm _ _
  have hrepr_norm (z : E) : inner ℝ z e = f z / ‖e₀‖ := by
    change inner ℝ z (‖e₀‖⁻¹ • e₀) = f z / ‖e₀‖
    rw [real_inner_smul_right, hrepr]
    ring
  have hnorm_pos : 0 < ‖e₀‖ := norm_pos_iff.mpr he₀_ne
  calc
    ⟪x - x₀, e⟫ = (f x - f x₀) / ‖e₀‖ := by
      rw [hrepr_norm, map_sub]
    _ ≤ (f xb - f x₀) / ‖e₀‖ :=
      div_le_div_of_nonneg_right (sub_le_sub_right hfx _) (norm_nonneg _)
    _ ≤ (‖xb - x₀‖ * ‖e₀‖) / ‖e₀‖ :=
      div_le_div_of_nonneg_right hgap (norm_nonneg _)
    _ = ‖xb - x₀‖ := by
      field_simp [ne_of_gt hnorm_pos]
    _ = dist x₀ xb := by
      rw [dist_eq_norm]
      exact norm_sub_rev _ _
    _ = infDist x₀ (frontier Ω) := hxb_dist.symm

end FunctionalInequalities.Analysis

end NearestBoundaryHalfspace

section ConeVolume

open MeasureTheory Set Metric
open scoped ENNReal

/-! Volumes of cones over convex sets. -/

namespace FunctionalInequalities.Analysis

private theorem packedBalls_subset_cone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} {q e : E} {N : ℕ} (hr : 0 < r) (hqpos : 0 < ‖q‖)
    (hqe : q = ‖q‖ • e) (hN : (N : ℝ) ≤ ‖q‖ / (4 * r)) :
    ∀ k ∈ Finset.range (N + 1),
      closedBall (((k : ℝ) * (2 * r)) • e) (r / 2) ⊆
        convexHull ℝ (closedBall (0 : E) r ∪ {q}) := by
  let C : ℕ → E := fun k => ((k : ℝ) * (2 * r)) • e
  change ∀ k ∈ Finset.range (N + 1),
    closedBall (C k) (r / 2) ⊆ convexHull ℝ (closedBall (0 : E) r ∪ {q})
  intro k hk x hx
  have hkN : k ≤ N :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hkr : (k : ℝ) * (2 * r) ≤ ‖q‖ / 2 := by
    have hk' : (k : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hkN
    have h₁ : (k : ℝ) * (2 * r) ≤ (N : ℝ) * (2 * r) :=
      mul_le_mul_of_nonneg_right hk' (by positivity)
    have h₂ : (N : ℝ) * (2 * r) ≤ ‖q‖ / 2 := by
      calc
        (N : ℝ) * (2 * r) ≤ (‖q‖ / (4 * r)) * (2 * r) :=
          mul_le_mul_of_nonneg_right hN (by positivity)
        _ = ‖q‖ / 2 := by
          field_simp
          ring
    exact h₁.trans h₂
  have hx' : ‖x - C k‖ ≤ r / 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  let s : ℝ := ((k : ℝ) * (2 * r)) / ‖q‖
  let b : E := (1 - s)⁻¹ • (x - C k)
  have hs0 : 0 ≤ s := by
    dsimp [s]
    positivity
  have hs_half : s ≤ 1 / 2 := by
    dsimp [s]
    apply (div_le_iff₀ hqpos).2
    nlinarith [hkr]
  have hs1 : s ≤ 1 := by
    linarith
  have hden : 0 < 1 - s := by
    linarith
  have hi : (1 - s)⁻¹ ≤ 2 := by
    have hmul :
        (1 / 2 : ℝ) * (1 - s)⁻¹ ≤ (1 - s) * (1 - s)⁻¹ :=
      mul_le_mul_of_nonneg_right
        (by linarith [hs_half]) (inv_nonneg.mpr hden.le)
    rw [mul_inv_cancel₀ hden.ne'] at hmul
    nlinarith
  have hb : b ∈ closedBall (0 : E) r := by
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp [b]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hden.le)]
    calc
      (1 - s)⁻¹ * ‖x - C k‖ ≤ 2 * ‖x - C k‖ :=
        mul_le_mul_of_nonneg_right hi (norm_nonneg _)
      _ ≤ 2 * (r / 2) := by
        exact mul_le_mul_of_nonneg_left hx' (by norm_num)
      _ = r := by ring
  have hsQ : s * ‖q‖ = (k : ℝ) * (2 * r) := by
    dsimp [s]
    field_simp
  have hs_q : s • q = (s * ‖q‖) • e := by
    calc
      s • q = s • (‖q‖ • e) := congrArg (fun z : E => s • z) hqe
      _ = (s * ‖q‖) • e := by rw [smul_smul]
  have hrep : (1 - s) • b + s • q = x := by
    calc
      (1 - s) • b + s • q =
          (1 - s) • b + (s * ‖q‖) • e := by rw [hs_q]
      _ = (x - C k) + (s * ‖q‖) • e := by
        dsimp [b]
        rw [smul_smul, mul_inv_cancel₀ hden.ne', one_smul]
      _ = (x - C k) + ((k : ℝ) * (2 * r)) • e := by rw [hsQ]
      _ = x := by
        dsimp [C]
        abel
  have hxseg : x ∈ segment ℝ b q := by
    rw [segment_eq_image]
    refine ⟨s, ⟨hs0, hs1⟩, ?_⟩
    simpa using hrep
  exact
    segment_subset_convexHull
      (Set.mem_union_left {q} hb)
      (Set.mem_union_right (closedBall (0 : E) r) (by simp))
      hxseg

private theorem packedBalls_pairwiseDisjoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} {e : E} (N : ℕ) (hr : 0 < r) (he : ‖e‖ = 1) :
    (Finset.range (N + 1) : Set ℕ).PairwiseDisjoint
      (fun k => closedBall (((k : ℝ) * (2 * r)) • e) (r / 2)) := by
  let C : ℕ → E := fun k => ((k : ℝ) * (2 * r)) • e
  change (Finset.range (N + 1) : Set ℕ).PairwiseDisjoint
    (fun k => closedBall (C k) (r / 2))
  rw [Set.pairwiseDisjoint_iff]
  intro i hi j hj hne
  rcases hne with ⟨x, hxi, hxj⟩
  by_contra hneq
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · have hij : i + 1 ≤ j := Nat.succ_le_iff.mp hlt
    have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast hij
    have hscalar :
        (i : ℝ) * (2 * r) - (j : ℝ) * (2 * r) ≤ 0 := by
      nlinarith [hij', hr.le]
    have hdist : 2 * r ≤ dist (C i) (C j) := by
      rw [dist_eq_norm]
      dsimp [C]
      rw [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs,
        abs_of_nonpos hscalar]
      nlinarith [hij', hr]
    have hxi' : dist (C i) x ≤ r / 2 := by
      rw [dist_comm]
      exact Metric.mem_closedBall.mp hxi
    have hxj' : dist x (C j) ≤ r / 2 :=
      Metric.mem_closedBall.mp hxj
    have hlt' : dist (C i) (C j) ≤ r := by
      calc
        dist (C i) (C j) ≤ dist (C i) x + dist x (C j) :=
          dist_triangle _ _ _
        _ ≤ r := by linarith
    linarith
  · have hji : j + 1 ≤ i := Nat.succ_le_iff.mp hgt
    have hji' : (j : ℝ) + 1 ≤ (i : ℝ) := by
      exact_mod_cast hji
    have hscalar :
        (j : ℝ) * (2 * r) - (i : ℝ) * (2 * r) ≤ 0 := by
      nlinarith [hji', hr.le]
    have hdist : 2 * r ≤ dist (C j) (C i) := by
      rw [dist_eq_norm]
      dsimp [C]
      rw [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs,
        abs_of_nonpos hscalar]
      nlinarith [hji', hr]
    have hxj' : dist (C j) x ≤ r / 2 := by
      rw [dist_comm]
      exact Metric.mem_closedBall.mp hxj
    have hxi' : dist x (C i) ≤ r / 2 :=
      Metric.mem_closedBall.mp hxi
    have hlt' : dist (C j) (C i) ≤ r := by
      calc
        dist (C j) (C i) ≤ dist (C j) x + dist x (C i) :=
          dist_triangle _ _ _
        _ ≤ r := by linarith
    linarith

/-- **Volume of the cone over a ball** (Caffarelli's argument, Alexandrov maximum
principle): there is `c > 0`, depending only on `E`, such that the convex hull of the closed ball of
radius `r` and a point `q` with `‖q‖ ≥ r` has volume at least `c · r^(n−1) · ‖q‖`, `n = dim E`. -/
theorem exists_pos_volume_convexHull_closedBall_union_singleton_ge {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r → ∀ q : E, r ≤ ‖q‖ →
      ENNReal.ofReal (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) ≤
        (volume : Measure E) (convexHull ℝ (closedBall (0 : E) r ∪ {q})) := by
  classical
  by_cases hE : Nontrivial E
  · let v : ℝ := (volume (ball (0 : E) 1)).toReal
    let c : ℝ := v / (2 : ℝ) ^ (Module.finrank ℝ E + 2)
    have hn0 : Module.finrank ℝ E ≠ 0 := by
      intro hn
      have hs : Subsingleton E := Module.finrank_zero_iff.mp hn
      exact (not_nontrivial_iff_subsingleton.mpr hs) hE
    have hn : 1 ≤ Module.finrank ℝ E :=
      Nat.one_le_iff_ne_zero.mpr hn0
    have hv_top : volume (ball (0 : E) 1) ≠ ∞ :=
      ne_of_lt measure_ball_lt_top
    have hv_pos : 0 < v := by
      dsimp [v]
      exact ENNReal.toReal_pos
        (ne_of_gt (Metric.measure_ball_pos volume (0 : E) zero_lt_one)) hv_top
    have hc : 0 < c := by
      dsimp [c]
      positivity
    refine ⟨c, hc, ?_⟩
    intro r hr q hq
    have hqpos : 0 < ‖q‖ := lt_of_lt_of_le hr hq
    -- Normalize the direction of the added point.
    let e : E := ‖q‖⁻¹ • q
    have he : ‖e‖ = 1 := by
      dsimp [e]
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hqpos]
      exact inv_mul_cancel₀ hqpos.ne'
    have hqe : q = ‖q‖ • e := by
      calc
        q = (1 : ℝ) • q := (one_smul ℝ q).symm
        _ = (‖q‖ * ‖q‖⁻¹) • q := by
          rw [mul_inv_cancel₀ hqpos.ne', one_smul]
        _ = ‖q‖ • (‖q‖⁻¹ • q) := by rw [smul_smul]
        _ = ‖q‖ • e := by rfl
    let N : ℕ := ⌊‖q‖ / (4 * r)⌋₊
    let C : ℕ → E := fun k => ((k : ℝ) * (2 * r)) • e
    have hN : (N : ℝ) ≤ ‖q‖ / (4 * r) := by
      dsimp [N]
      exact Nat.floor_le (by positivity)
    have hball := packedBalls_subset_cone hr hqpos hqe hN
    have hdisj := packedBalls_pairwiseDisjoint N hr he
    have hmeas :
        ∀ k ∈ Finset.range (N + 1),
          MeasurableSet (closedBall (C k) (r / 2)) := by
      intro k hk
      exact isClosed_closedBall.measurableSet
    -- Estimate the volume of the packed balls and restore the dimensional constant.
    have hunion :
        volume (⋃ k ∈ Finset.range (N + 1), closedBall (C k) (r / 2)) =
          ∑ k ∈ Finset.range (N + 1), volume (closedBall (C k) (r / 2)) :=
      measure_biUnion_finset hdisj hmeas
    have hsum :
        (∑ k ∈ Finset.range (N + 1), volume (closedBall (C k) (r / 2))) =
          ((N + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
              volume (ball (0 : E) 1)) := by
      calc
        (∑ k ∈ Finset.range (N + 1), volume (closedBall (C k) (r / 2))) =
            ∑ k ∈ Finset.range (N + 1),
              (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
                volume (ball (0 : E) 1)) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [Measure.addHaar_closedBall volume (C k) (by positivity)]
        _ = ((N + 1 : ℕ) : ℝ≥0∞) *
              (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
                volume (ball (0 : E) 1)) := by
              simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsubset :
        (⋃ k ∈ Finset.range (N + 1), closedBall (C k) (r / 2)) ⊆
          convexHull ℝ (closedBall (0 : E) r ∪ {q}) := by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨k, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨hk, hx⟩
      exact hball k hk hx
    have hmeasure :
        ((N + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
              volume (ball (0 : E) 1)) ≤
          volume (convexHull ℝ (closedBall (0 : E) r ∪ {q})) := by
      calc
        ((N + 1 : ℕ) : ℝ≥0∞) *
              (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
                volume (ball (0 : E) 1)) =
            ∑ k ∈ Finset.range (N + 1), volume (closedBall (C k) (r / 2)) := hsum.symm
        _ = volume (⋃ k ∈ Finset.range (N + 1), closedBall (C k) (r / 2)) :=
          hunion.symm
        _ ≤ volume (convexHull ℝ (closedBall (0 : E) r ∪ {q})) :=
          measure_mono hsubset
    have hcount : ‖q‖ / (4 * r) < (N + 1 : ℝ) := by
      dsimp [N]
      exact Nat.lt_floor_add_one _
    have hreal :
        c * r ^ (Module.finrank ℝ E - 1) * ‖q‖ ≤
          (N + 1 : ℝ) * ((r / 2) ^ Module.finrank ℝ E) * v := by
      have hQ : ‖q‖ ≤ 4 * r * (N + 1 : ℝ) := by
        have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * r)).mp hcount
        exact le_of_lt (by linarith)
      have hcoef :
          0 ≤ c * r ^ (Module.finrank ℝ E - 1) :=
        mul_nonneg hc.le (pow_nonneg hr.le _)
      have hp :
          r ^ (Module.finrank ℝ E - 1) * r =
            r ^ Module.finrank ℝ E := by
        rw [← pow_succ]
        congr 1
        exact Nat.sub_add_cancel hn
      calc
        c * r ^ (Module.finrank ℝ E - 1) * ‖q‖ =
            (c * r ^ (Module.finrank ℝ E - 1)) * ‖q‖ := by ring
        _ ≤ (c * r ^ (Module.finrank ℝ E - 1)) *
              (4 * r * (N + 1 : ℝ)) :=
          mul_le_mul_of_nonneg_left hQ hcoef
        _ = ((N + 1 : ℝ) * v *
              (r ^ (Module.finrank ℝ E - 1) * r)) /
              (2 : ℝ) ^ Module.finrank ℝ E := by
          dsimp [c]
          field_simp [show (2 : ℝ) ≠ 0 by norm_num]
          ring
        _ = (N + 1 : ℝ) * ((r / 2) ^ Module.finrank ℝ E) * v := by
          rw [hp, div_pow]
          ring
    have hv : ENNReal.ofReal v = volume (ball (0 : E) 1) :=
      ENNReal.ofReal_toReal hv_top
    have hcast :
        ENNReal.ofReal ((N : ℝ) + 1) =
          (N : ℝ≥0∞) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (ENNReal.ofReal_natCast (N + 1))
    have hEq :
        ENNReal.ofReal
            ((N + 1 : ℝ) * ((r / 2) ^ Module.finrank ℝ E) * v) =
          ((N + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
              volume (ball (0 : E) 1)) := by
      calc
        ENNReal.ofReal
            ((N + 1 : ℝ) * ((r / 2) ^ Module.finrank ℝ E) * v) =
            ENNReal.ofReal
              (((N : ℝ) + 1) *
                (((r / 2) ^ Module.finrank ℝ E) * v)) := by
                  congr 1
                  ring
        _ = ENNReal.ofReal ((N : ℝ) + 1) *
              ENNReal.ofReal (((r / 2) ^ Module.finrank ℝ E) * v) := by
              rw [ENNReal.ofReal_mul (by positivity)]
        _ = ((N : ℝ≥0∞) + 1) *
              (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
                volume (ball (0 : E) 1)) := by
              rw [hcast, ENNReal.ofReal_mul (by positivity), hv]
        _ = ((N + 1 : ℕ) : ℝ≥0∞) *
              (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
                volume (ball (0 : E) 1)) := by
              norm_num
    calc
      ENNReal.ofReal (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) ≤
          ENNReal.ofReal
            ((N + 1 : ℝ) * ((r / 2) ^ Module.finrank ℝ E) * v) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ((N + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
              volume (ball (0 : E) 1)) := hEq
      _ ≤ volume (convexHull ℝ (closedBall (0 : E) r ∪ {q})) := hmeasure
  · have hsub : Subsingleton E :=
      not_nontrivial_iff_subsingleton.mp hE
    refine ⟨1, zero_lt_one, ?_⟩
    intro r hr q hq
    have hq0 : q = 0 := hsub.elim q 0
    rw [hq0, norm_zero] at hq
    linarith

end FunctionalInequalities.Analysis

end ConeVolume

section AlexandrovMaximumPrinciple

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal

/-! The Alexandrov maximum principle. -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma alexandrov_diam_pos [Nontrivial E]
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    0 < diam Ω := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let e : E := ‖v‖⁻¹ • v
  have he : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hvpos.le)]
    exact inv_mul_cancel₀ hvpos.ne'
  let y : E := x₀ + (r / 2) • e
  have hy : y ∈ Ω := by
    apply hball
    rw [mem_ball, dist_eq_norm]
    dsimp [y]
    rw [add_sub_cancel_left, norm_smul, he, mul_one,
      Real.norm_eq_abs, abs_of_pos (by linarith : 0 < r / 2)]
    linarith
  have hdist : dist x₀ y ≤ diam Ω :=
    Metric.dist_le_diam_of_mem hb hx₀ hy
  have hdist' : dist x₀ y = r / 2 := by
    rw [dist_eq_norm, norm_sub_rev]
    dsimp [y]
    rw [add_sub_cancel_left, norm_smul, he, mul_one,
      Real.norm_eq_abs, abs_of_pos (by linarith : 0 < r / 2)]
  rw [hdist'] at hdist
  linarith

section FiniteDimensional

variable [FiniteDimensional ℝ E] [Nontrivial E]

omit [FiniteDimensional ℝ E] in
private lemma alexandrov_infDist_frontier_pos
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    0 < infDist x₀ (frontier Ω) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  have hne : (frontier Ω).Nonempty :=
    frontier_nonempty_of_isBounded hb hx₀
  apply lt_of_lt_of_le hr
  apply (Metric.le_infDist hne).2
  intro y hy
  have hyn : y ∉ Ω := by
    intro hyΩ
    apply hy.2
    rw [hΩ.interior_eq]
    exact hyΩ
  have hnot : ¬ dist y x₀ < r := by
    intro hdist
    exact hyn (hball (mem_ball.mpr hdist))
  simpa [dist_comm] using (le_of_not_gt hnot)

end FiniteDimensional

private lemma alexandrov_affine_set_convex {u : E → ℝ} {x₀ : E}
    {Ω : Set E} :
    Convex ℝ {p : E | ∀ x ∈ closure Ω,
      u x₀ + ⟪p, x - x₀⟫ ≤ 0} := by
  intro p hp q hq a b ha hb hab x hx
  have hp' := hp x hx
  have hq' := hq x hx
  have hi :
      ⟪a • p + b • q, x - x₀⟫ =
        a * ⟪p, x - x₀⟫ + b * ⟪q, x - x₀⟫ := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  calc
    u x₀ + ⟪a • p + b • q, x - x₀⟫ =
        u x₀ + (a * ⟪p, x - x₀⟫ + b * ⟪q, x - x₀⟫) := by
          rw [hi]
    _ = (a + b) * u x₀ +
          (a * ⟪p, x - x₀⟫ + b * ⟪q, x - x₀⟫) := by
          rw [hab]
          ring
    _ = a * (u x₀ + ⟪p, x - x₀⟫) +
          b * (u x₀ + ⟪q, x - x₀⟫) := by
          ring
    _ ≤ 0 := by
      simpa using add_le_add
        (mul_nonpos_of_nonneg_of_nonpos ha hp')
        (mul_nonpos_of_nonneg_of_nonpos hb hq')

/-- The common geometric part of the Alexandrov maximum-principle proof. -/
private lemma alexandrov_maximum_principle_core
    [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {Ω I : Set E}
    (hΩ : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) (hneg : u x₀ < 0)
    (hmem : ∀ p : E,
      (∀ x ∈ closure Ω, u x₀ + ⟪p, x - x₀⟫ ≤ 0) → p ∈ I)
    {c : ℝ} (hc : 0 < c)
    (hcone : ∀ r : ℝ, 0 < r → ∀ q : E, r ≤ ‖q‖ →
      ENNReal.ofReal
          (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) ≤
        (volume : Measure E)
          (convexHull ℝ (closedBall (0 : E) r ∪ {q}))) :
    ENNReal.ofReal (c * (-u x₀) ^ Module.finrank ℝ E) ≤
      (volume : Measure E) I *
        ENNReal.ofReal
          (diam Ω ^ (Module.finrank ℝ E - 1) *
            infDist x₀ (frontier Ω)) := by
  let m : ℝ := -u x₀
  let D : ℝ := diam Ω
  let d : ℝ := infDist x₀ (frontier Ω)
  have hm : 0 < m := by
    dsimp [m]
    linarith
  have hD : 0 < D := alexandrov_diam_pos hΩ hb hx₀
  have hd : 0 < d := alexandrov_infDist_frontier_pos hΩ hb hx₀
  have hdd : d ≤ D :=
    infDist_frontier_le_diam_of_mem hb hx₀
  obtain ⟨e, he, heΩ⟩ :=
    exists_unit_inner_le_infDist_frontier hΩ hΩconv hb hx₀
  let r : ℝ := m / D
  let q : E := (m / d) • e
  have hr : 0 < r := div_pos hm hD
  have hqnorm : ‖q‖ = m / d := by
    dsimp [q]
    rw [norm_smul, he, mul_one, Real.norm_eq_abs,
      abs_of_pos (div_pos hm hd)]
  have hrq : r ≤ ‖q‖ := by
    rw [hqnorm]
    exact div_le_div_of_nonneg_left hm.le hd hdd
  let A : Set E := {p : E | ∀ x ∈ closure Ω,
      u x₀ + ⟪p, x - x₀⟫ ≤ 0}
  have hballA : closedBall (0 : E) r ⊆ A := by
    intro p hp x hx
    have hdist := Metric.dist_le_diam_of_mem hb.closure
      hx (subset_closure hx₀)
    have hxd : ‖x - x₀‖ ≤ D := by
      simpa only [dist_eq_norm, Metric.diam_closure] using hdist
    have hpnorm : ‖p‖ ≤ r := by
      simpa [mem_closedBall, dist_zero_right] using hp
    have hinner : ⟪p, x - x₀⟫ ≤ ‖p‖ * ‖x - x₀‖ :=
      le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
    have hmul : ‖p‖ * ‖x - x₀‖ ≤ r * D :=
      mul_le_mul hpnorm hxd (norm_nonneg _) (by positivity)
    have hzero : u x₀ + r * D = 0 := by
      dsimp [r, m]
      rw [div_mul_cancel₀ _ hD.ne']
      ring
    calc
      u x₀ + ⟪p, x - x₀⟫ ≤ u x₀ + ‖p‖ * ‖x - x₀‖ := by
        exact add_le_add (le_refl _) hinner
      _ ≤ u x₀ + r * D := by
        exact add_le_add (le_refl _) hmul
      _ = 0 := hzero
  have hqA : q ∈ A := by
    intro x hx
    have hΩbound : ∀ y ∈ Ω,
        u x₀ + ⟪q, y - x₀⟫ ≤ 0 := by
      intro y hy
      have hey := heΩ y hy
      have hey' : ⟪e, y - x₀⟫ ≤ d := by
        simpa only [real_inner_comm] using hey
      have hi :
          ⟪q, y - x₀⟫ =
            (m / d) * ⟪e, y - x₀⟫ := by
        rw [real_inner_smul_left]
      have hmul :
          (m / d) * ⟪e, y - x₀⟫ ≤ (m / d) * d :=
        mul_le_mul_of_nonneg_left hey' (div_pos hm hd).le
      calc
        u x₀ + ⟪q, y - x₀⟫ =
            u x₀ + (m / d) * ⟪e, y - x₀⟫ := by rw [hi]
        _ ≤ u x₀ + (m / d) * d := by
          exact add_le_add (le_refl _) hmul
        _ = 0 := by
          dsimp [m]
          rw [div_mul_cancel₀ _ hd.ne']
          ring
    have hcont : Continuous (fun y : E =>
        u x₀ + ⟪q, y - x₀⟫) := by
      fun_prop
    have hclosed :
        IsClosed {y : E | u x₀ + ⟪q, y - x₀⟫ ≤ 0} :=
      isClosed_Iic.preimage hcont
    exact closure_minimal (fun y hy ↦ hΩbound y hy) hclosed hx
  have hHullA : convexHull ℝ (closedBall (0 : E) r ∪ {q}) ⊆ A :=
    convexHull_min (union_subset hballA (singleton_subset_iff.mpr hqA))
      alexandrov_affine_set_convex
  have hsub :
      convexHull ℝ (closedBall (0 : E) r ∪ {q}) ⊆ I := by
    intro p hp
    exact hmem p (hHullA hp)
  have hvol :
      ENNReal.ofReal
          (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) ≤
        (volume : Measure E) I :=
    (hcone r hr q hrq).trans (measure_mono hsub)
  have hn : 1 ≤ Module.finrank ℝ E :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Module.finrank_pos (R := ℝ) (M := E)))
  have hcancel :
      (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          (D ^ (Module.finrank ℝ E - 1) * d) =
        c * m ^ (Module.finrank ℝ E - 1) * m := by
    rw [hqnorm]
    change
      (c * (m / D) ^ (Module.finrank ℝ E - 1) * (m / d)) *
          (D ^ (Module.finrank ℝ E - 1) * d) =
        c * m ^ (Module.finrank ℝ E - 1) * m
    simp only [div_eq_mul_inv, mul_pow]
    have hpowD :
        D ^ (Module.finrank ℝ E - 1) *
            D⁻¹ ^ (Module.finrank ℝ E - 1) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hD.ne', one_pow]
    calc
      (c * (m ^ (Module.finrank ℝ E - 1) *
          D⁻¹ ^ (Module.finrank ℝ E - 1)) *
          (m * d⁻¹)) *
          (D ^ (Module.finrank ℝ E - 1) * d) =
          c * m ^ (Module.finrank ℝ E - 1) * m *
            (D ^ (Module.finrank ℝ E - 1) *
              D⁻¹ ^ (Module.finrank ℝ E - 1)) *
            (d⁻¹ * d) := by ring
      _ = c * m ^ (Module.finrank ℝ E - 1) * m := by
        rw [hpowD, inv_mul_cancel₀ hd.ne']
        ring
  have hEq :
      (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          (D ^ (Module.finrank ℝ E - 1) * d) =
        c * m ^ Module.finrank ℝ E := by
    calc
      (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          (D ^ (Module.finrank ℝ E - 1) * d) =
          c * m ^ (Module.finrank ℝ E - 1) * m := hcancel
      _ = c * (m ^ (Module.finrank ℝ E - 1) * m) := by ring
      _ = c * m ^ ((Module.finrank ℝ E - 1) + 1) := by
        rw [pow_succ]
      _ = c * m ^ Module.finrank ℝ E := by
        rw [Nat.sub_add_cancel hn]
  have hreal :
      c * m ^ Module.finrank ℝ E ≤
        (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          (D ^ (Module.finrank ℝ E - 1) * d) := by
    rw [hEq]
  have hreal' :
      ENNReal.ofReal (c * m ^ Module.finrank ℝ E) ≤
        ENNReal.ofReal
            (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          ENNReal.ofReal
            (D ^ (Module.finrank ℝ E - 1) * d) := by
    rw [← ENNReal.ofReal_mul (by positivity :
      0 ≤ c * r ^ (Module.finrank ℝ E - 1) * ‖q‖)]
    exact ENNReal.ofReal_mono hreal
  calc
    ENNReal.ofReal (c * (-u x₀) ^ Module.finrank ℝ E) =
        ENNReal.ofReal (c * m ^ Module.finrank ℝ E) := by
          rfl
    _ ≤ ENNReal.ofReal
          (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) *
          ENNReal.ofReal
            (D ^ (Module.finrank ℝ E - 1) * d) := hreal'
    _ ≤ (volume : Measure E) I *
          ENNReal.ofReal
            (D ^ (Module.finrank ℝ E - 1) * d) :=
      mul_le_mul' hvol (le_refl _)
    _ = (volume : Measure E) I *
          ENNReal.ofReal
            (diam Ω ^ (Module.finrank ℝ E - 1) *
              infDist x₀ (frontier Ω)) := by
      rfl

/-- **Alexandrov maximum principle on a domain** with only closure convexity and
closure continuity. -/
theorem exists_pos_alexandrov_maximum_principle_domain [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E] :
    ∃ c : ℝ,
      0 < c ∧
        ∀ (u : E → ℝ) (Ω : Set E),
          ConvexOn ℝ (closure Ω) u →
            ContinuousOn u (closure Ω) →
              IsOpen Ω →
                Convex ℝ Ω →
                  Bornology.IsBounded Ω →
                    (∀ x ∈ frontier Ω, 0 ≤ u x) →
                      ∀ x₀ ∈ Ω,
                        u x₀ < 0 →
                          ENNReal.ofReal (c * (-u x₀) ^ Module.finrank ℝ E) ≤
                            (volume : Measure E) (subgradientImageOn u Ω Ω) *
                              ENNReal.ofReal
                                (diam Ω ^ (Module.finrank ℝ E - 1) * infDist x₀ (frontier Ω)) := by
  obtain ⟨c, hc, hcone⟩ := exists_pos_volume_convexHull_closedBall_union_singleton_ge (E := E)
  refine ⟨c, hc, ?_⟩
  intro u Ω hconv huc hΩ hΩconv hb hfr x₀ hx₀ hneg
  have hmem :
    ∀ p : E, (∀ x ∈ closure Ω, u x₀ + ⟪p, x - x₀⟫ ≤ 0) → p ∈ subgradientImageOn u Ω Ω := by
    intro p hp
    obtain ⟨x, hx, hp⟩ := exists_interior_support_of_affine_le_on_frontier huc hb hfr hx₀ hp
    have hclosure := subgradient_le_on_of_isOpen hconv hΩ subset_closure hx hp
    exact ⟨x, hx, fun y hy => hclosure y (subset_closure hy)⟩
  exact alexandrov_maximum_principle_core hΩ hΩconv hb hx₀ hneg hmem hc hcone

/-- **Alexandrov maximum principle** (Gutiérrez2001, Theorem1.4.2),
with the original globally convex source and exact public interface. -/
theorem exists_pos_alexandrov_maximum_principle [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E] :
    ∃ c : ℝ,
      0 < c ∧
        ∀ (u : E → ℝ),
          ConvexOn ℝ univ u →
            ∀ (Ω : Set E),
              IsOpen Ω →
                Convex ℝ Ω →
                  Bornology.IsBounded Ω →
                    (∀ x ∈ frontier Ω, 0 ≤ u x) →
                      ∀ x₀ ∈ Ω,
                        u x₀ < 0 →
                          ENNReal.ofReal (c * (-u x₀) ^ Module.finrank ℝ E) ≤
                            (volume : Measure E) (subgradientImage u Ω) *
                              ENNReal.ofReal
                                (diam Ω ^ (Module.finrank ℝ E - 1) * infDist x₀ (frontier Ω)) := by
  obtain ⟨c, hc, hcone⟩ := exists_pos_volume_convexHull_closedBall_union_singleton_ge (E := E)
  refine ⟨c, hc, ?_⟩
  intro u hconv Ω hΩ hΩconv hb hfr x₀ hx₀ hneg
  have hmem : ∀ p : E, (∀ x ∈ closure Ω, u x₀ + ⟪p, x - x₀⟫ ≤ 0) → p ∈ subgradientImage u Ω := by
    intro p hp
    exact mem_subgradientImage_of_affine_le_of_nonneg_frontier hconv hΩ hb hfr hx₀ hneg hp
  exact alexandrov_maximum_principle_core hΩ hΩconv hb hx₀ hneg hmem hc hcone

end InnerProduct

end FunctionalInequalities.Analysis

end AlexandrovMaximumPrinciple
