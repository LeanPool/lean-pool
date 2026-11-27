/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Lipschitz.GraphStraightening
public import LeanPool.FunctionSpaces.Domains.Lipschitz.SurfaceMeasure
public import LeanPool.FunctionSpaces.Rd.Sobolev.WeakDerivativeChangeOfVariables
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Gauss–Green on Lipschitz graph domains

Let `Ω = {x : φ(x) < ⟪x, e⟫}` be a Lipschitz graph domain in `V`, `dim V = n`, with the graph map
`γ(x') = x' + φ(x') e` over the hyperplane `H = e^⊥`, the gradient `∇φ` of `φ|_H`, the Gram density
`√(1 + ‖∇φ‖²)` and the outward unit normal `ν` of
`FunctionSpaces.Domains.Lipschitz.LipschitzGraphArea`.

* **Fubini in product coordinates**: the coordinates `(x', t) ↦ x' + t e` and
  `(x', t) ↦ γ(x') + t e` of `FunctionSpaces.Domains.Lipschitz.GraphStraightening` carry the
  Lebesgue measure of `H × ℝ` to that of `V`, so
  `∫_Ω F = ∫_H ∫_{φ(x')}^∞ F(x' + t e) dt dx' = ∫_H ∫_0^∞ F(γ(x') + t e) dt dx'`
  (`Rd.LipschitzGraph.setIntegral_domain_eq`, `Rd.LipschitzGraph.setIntegral_domain_eq_graphMap`).
* **Gauss–Green for `C^1` functions** (`Rd.LipschitzGraph.setIntegral_lineDeriv_eq`): for
  `g ∈ C^1` with compact support and every direction `v`, `∫_Ω ∂_v g = ∫_H g(γ x') n_v(x') dx'`
  with the normal weight `n_v = ⟪∇φ, v⟫ - ⟪v, e⟫ = ⟪v, ν⟫ √(1 + ‖∇φ‖²)`
  (`Rd.LipschitzGraph.normalWeight`, `Rd.LipschitzGraph.inner_normalAt_mul_gram`); with the area
  formula, `∫_Ω ∂_v g = ∫_Γ g ⟪v, ν⟫ dμHE[n-1]`
  (`Rd.LipschitzGraph.setIntegral_lineDeriv_eq_surface`). The proof uses the ray integral
  `Ψ(y) = ∫_0^∞ g(y + t e) dt` (`Rd.rayIntegral`), a differentiable function with
  `∂_e Ψ = -g` and bounded derivative, and the compactly supported Lipschitz function `Ψ ∘ γ` on
  `H` (`Rd.LipschitzGraph.graphRayIntegral`): the integral of its line derivative vanishes
  (`Rd.integral_lineDeriv_eq_zero_complex`, from Mathlib's integration by parts for Lipschitz
  functions), and the chain rule at the points where `φ|_H` is differentiable gives the
  horizontal directions (`Rd.LipschitzGraph.integral_fderiv_rayIntegral_graphMap`).
* **Green's formula for `W^1_2(V)`** (`Rd.LipschitzGraph.setIntegral_green`): for
  `f, g ∈ W^1_2(V)` with weak derivatives `∂_v f`, `∂_v g` in `L_2(V)`,
  `∫_Ω (∂_v f) g + f ∂_v g = ∫_H Tr f · Tr g · n_v`, with the product rule
  (`Rd.lineDeriv_mul`), the trace operator `H^1(V) → L_2(H)` (`Rd.LipschitzGraph.traceH1`), the
  density of compactly supported Schwartz functions in `H^1(V)`
  (`Rd.dense_ofSchwartz_hasCompactSupport`) and the continuity of both sides; in surface form
  the right side is `∫_Γ Tr f · Tr g ⟪v, ν⟫ dμHE[n-1]`
  (`Rd.LipschitzGraph.setIntegral_green_surface`).
-/

@[expose] public section

open MeasureTheory Module Metric Filter Topology Set
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace LineDeriv

namespace Rd

/-! ### Bounded functions with bounded support -/

/-- **Bounded functions vanishing outside a ball are integrable**: on a proper normed group with
a measure that is finite on compact sets, an a.e. strongly measurable `f` with `‖f x‖ ≤ C` for
every `x` and `f x = 0` for `‖x‖ > R` is integrable. -/
theorem integrable_of_norm_le_of_forall_norm_gt_eq_zero {F E : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [ProperSpace F] {μ : Measure F} [IsFiniteMeasureOnCompacts μ]
    [NormedAddCommGroup E]
    {f : F → E} (hf : AEStronglyMeasurable f μ) {C R : ℝ} (hC : ∀ x, ‖f x‖ ≤ C)
    (hR : ∀ x, R < ‖x‖ → f x = 0) : Integrable f μ := by
  have hi : IntegrableOn f (closedBall 0 R) μ :=
    Measure.integrableOn_of_bounded (isCompact_closedBall 0 R).measure_ne_top hf
      (ae_of_all _ hC)
  refine (integrableOn_iff_integrable_of_support_subset fun x hx => ?_).1 hi
  rw [mem_closedBall_zero_iff]
  by_contra h
  exact hx (hR x (lt_of_not_ge h))

/-! ### Ray integrals -/

section RayIntegral

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **ray integral** `Ψ(y) = ∫_0^∞ g(y + t w) dt` of `g` along the ray from `y` in the
direction `w`. -/
noncomputable def rayIntegral (g : V → E) (w y : V) : E := ∫ t in Ioi (0 : ℝ), g (y + t • w)

omit [NormedSpace ℝ E] in
/-- On a line in the direction of a unit vector `w`: if `‖y + t w‖ ≤ R`, then
`|t + ⟪y, w⟫| ≤ R`, since `t + ⟪y, w⟫ = ⟪y + t w, w⟫`. -/
theorem abs_add_inner_le_of_norm_add_smul_le {w : V} (hw : ‖w‖ = 1) {y : V} {t R : ℝ}
    (h : ‖y + t • w‖ ≤ R) : |t + inner ℝ y w| ≤ R := by
  have he : inner ℝ (y + t • w) w = t + inner ℝ y w := by
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hw]
    ring
  calc |t + inner ℝ y w| = |inner ℝ (y + t • w) w| := by rw [he]
    _ ≤ ‖y + t • w‖ * ‖w‖ := abs_real_inner_le_norm _ _
    _ ≤ R := by rw [hw, mul_one]; exact h

/-- **A function supported in a ball, along a line**: if `tsupport h ⊆ closedBall(0, R)` and `w`
is a unit
vector, then `h(y + t w) = 0` for every `t` outside `[-⟪y, w⟫ - R, -⟪y, w⟫ + R]`. -/
theorem apply_add_smul_eq_zero_of_notMem_Icc {F : Type*} [Zero F] {h : V → F} {R : ℝ}
    (hR : tsupport h ⊆ closedBall 0 R) {w : V} (hw : ‖w‖ = 1) (y : V) {t : ℝ}
    (ht : t ∉ Icc (-inner ℝ y w - R) (-inner ℝ y w + R)) : h (y + t • w) = 0 := by
  by_contra h0
  have hmem := hR (subset_tsupport _ h0)
  rw [mem_closedBall_zero_iff] at hmem
  have := abs_le.1 (abs_add_inner_le_of_norm_add_smul_le hw hmem)
  exact ht ⟨by linarith, by linarith⟩

/-- A compactly supported function restricted to a line in the direction of a unit vector is
compactly supported. -/
theorem hasCompactSupport_comp_add_smul {F : Type*} [NormedAddCommGroup F] {h : V → F}
    (hh : HasCompactSupport h) {w : V} (hw : ‖w‖ = 1) (y : V) :
    HasCompactSupport fun t : ℝ => h (y + t • w) := by
  obtain ⟨R, hR⟩ := hh.isCompact.isBounded.subset_closedBall 0
  exact HasCompactSupport.intro isCompact_Icc fun t ht =>
    apply_add_smul_eq_zero_of_notMem_Icc hR hw y ht

/-- A continuous compactly supported function restricted to a line in the direction of a unit
vector is integrable on `ℝ`. -/
theorem integrable_comp_add_smul {F : Type*} [NormedAddCommGroup F] {h : V → F}
    (hh : Continuous h) (hhc : HasCompactSupport h) {w : V} (hw : ‖w‖ = 1) (y : V) :
    Integrable fun t : ℝ => h (y + t • w) :=
  (hh.comp (continuous_const.add (continuous_id.smul continuous_const))
    ).integrable_of_hasCompactSupport (hasCompactSupport_comp_add_smul hhc hw y)

variable {g : V → E}

/-- **Differentiation under the ray integral**: for `g ∈ C^1` with compact support and a unit
vector `w`, the ray integral is differentiable with `DΨ(y) = ∫_0^∞ Dg(y + t w) dt` (Mathlib's
`hasFDerivAt_integral_of_dominated_of_fderiv_le`, with the bound `sup ‖Dg‖` on an interval of `t`
that contains the parameters of the line meeting the support of `g`). -/
theorem hasFDerivAt_rayIntegral (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) {w : V}
    (hw : ‖w‖ = 1) (y₀ : V) :
    HasFDerivAt (rayIntegral g w) (∫ t in Ioi (0 : ℝ), fderiv ℝ g (y₀ + t • w)) y₀ := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨C, hC⟩ := (hg.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hgc.fderiv (𝕜 := ℝ))
  have hd : ∀ z, HasFDerivAt g (fderiv ℝ g z) z := fun z =>
    ((hg.differentiable one_ne_zero) z).hasFDerivAt
  set T := ‖y₀‖ + 1 + R
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun y t => g (y + t • w))
    (F' := fun y t => fderiv ℝ g (y + t • w)) (bound := (Icc (-T) T).indicator
    fun _ => C) (ball_mem_nhds y₀ one_pos) (Eventually.of_forall fun y =>
      (hg.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
        ).aestronglyMeasurable)
    (integrable_comp_add_smul hg.continuous hgc hw y₀).restrict
    ((hg.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_id.smul continuous_const))).aestronglyMeasurable
    (ae_of_all _ fun t y hy => ?_)
    ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc).restrict
    (ae_of_all _ fun t y _ => (hasFDerivAt_comp_add_right (t • w)).2 (hd _))
  by_cases ht : t ∈ Icc (-T) T
  · rw [indicator_of_mem ht]
    exact hC _
  · rw [indicator_of_notMem ht,
      apply_add_smul_eq_zero_of_notMem_Icc ((tsupport_fderiv_subset ℝ).trans hR) hw y, norm_zero]
    intro hmem
    have h1 := abs_le.1 (abs_real_inner_le_norm y w)
    have h2 : ‖y‖ < ‖y₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' y y₀
      rw [mem_ball, dist_eq_norm] at hy
      linarith
    rw [hw, mul_one] at h1
    exact ht ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

/-- The derivative of the ray integral in a direction `v`:
`DΨ(y) v = ∫_0^∞ Dg(y + t w) v dt` (Mathlib's `ContinuousLinearMap.integral_apply`). -/
theorem fderiv_rayIntegral_apply (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) {w : V} (hw : ‖w‖ = 1) (y v : V) :
    fderiv ℝ (rayIntegral g w) y v = ∫ t in Ioi (0 : ℝ), fderiv ℝ g (y + t • w) v := by
  rw [(hasFDerivAt_rayIntegral hg hgc hw y).fderiv, ContinuousLinearMap.integral_apply
    (integrable_comp_add_smul (hg.continuous_fderiv one_ne_zero) (hgc.fderiv (𝕜 := ℝ)) hw
      y).restrict]

omit [InnerProductSpace ℝ V] in
/-- The chain rule along a line: `t ↦ g(y + t w)` has the derivative `Dg(y + t w) w`. -/
theorem hasDerivAt_comp_add_smul [NormedSpace ℝ V] (hg : ContDiff ℝ 1 g) (y w : V) (t : ℝ) :
    HasDerivAt (fun t : ℝ => g (y + t • w)) (fderiv ℝ g (y + t • w) w) t := by
  have h := ((hg.differentiable one_ne_zero) (y + t • w)).hasFDerivAt.comp_hasDerivAt t
    (((hasDerivAt_id t).smul_const w).const_add y)
  simp only [one_smul] at h
  exact h

/-- **The ray integral differentiated along its ray**: `DΨ(y) w = -g(y)`. This is the
fundamental theorem of calculus on `(0, ∞)`, since `g(y + t w) = 0` for large `t` (Mathlib's
`integral_Ioi_of_hasDerivAt_of_tendsto`). -/
theorem fderiv_rayIntegral_self [CompleteSpace E] (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) {w : V} (hw : ‖w‖ = 1) (y : V) :
    fderiv ℝ (rayIntegral g w) y w = -g y := by
  rw [fderiv_rayIntegral_apply hg hgc hw]
  have hlim : Tendsto (fun t : ℝ => g (y + t • w)) atTop (𝓝 0) := by
    obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (-inner ℝ y w + R)] with t ht
    exact (apply_add_smul_eq_zero_of_notMem_Icc hR hw y fun h => (not_le.2 ht) h.2).symm
  have hint := ((integrable_comp_add_smul (hg.continuous_fderiv one_ne_zero)
    (hgc.fderiv (𝕜 := ℝ)) hw y).apply_continuousLinearMap w).integrableOn (s := Ioi (0 : ℝ))
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0)
    (hasDerivAt_comp_add_smul hg y w 0).continuousAt.continuousWithinAt
    (fun t _ => hasDerivAt_comp_add_smul hg y w t) hint hlim
  rw [h, zero_smul, add_zero, zero_sub]

/-- **The derivative of the ray integral is bounded**: there is `K` with `‖DΨ(y)‖ ≤ K` for every
`y`; the proof takes `K = C max(2R, 0)` for `‖Dg‖ ≤ C` and `tsupport g ⊆ closedBall(0, R)`,
since each line
meets the support of `g` in an interval of length at most `2R`. -/
theorem exists_norm_fderiv_rayIntegral_le (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    {w : V} (hw : ‖w‖ = 1) : ∃ K : ℝ, ∀ y, ‖fderiv ℝ (rayIntegral g w) y‖ ≤ K := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨C, hC⟩ := (hg.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hgc.fderiv (𝕜 := ℝ))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C * max (2 * R) 0, fun y => ?_⟩
  set a := -inner ℝ y w
  rw [(hasFDerivAt_rayIntegral hg hgc hw y).fderiv]
  have hb : Integrable ((Icc (a - R) (a + R)).indicator fun _ => C) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  calc ‖∫ t in Ioi (0 : ℝ), fderiv ℝ g (y + t • w)‖
      ≤ ∫ t in Ioi (0 : ℝ), (Icc (a - R) (a + R)).indicator (fun _ => C) t := by
        refine norm_integral_le_of_norm_le hb.restrict (ae_of_all _ fun t => ?_)
        by_cases ht : t ∈ Icc (a - R) (a + R)
        · rw [indicator_of_mem ht]
          exact hC _
        · rw [indicator_of_notMem ht, apply_add_smul_eq_zero_of_notMem_Icc
            ((tsupport_fderiv_subset ℝ).trans hR) hw y ht, norm_zero]
    _ ≤ ∫ t, (Icc (a - R) (a + R)).indicator (fun _ => C) t :=
        setIntegral_le_integral hb (ae_of_all _ fun t => indicator_nonneg (fun _ _ => hC0) t)
    _ = C * max (2 * R) 0 := by
        rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc, smul_eq_mul,
          mul_comm]
        ring_nf

/-- **The ray integral is Lipschitz**, since its derivative is bounded
(`Rd.exists_norm_fderiv_rayIntegral_le`, Mathlib's `lipschitzWith_of_nnNorm_fderiv_le`). -/
theorem exists_lipschitzWith_rayIntegral (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    {w : V} (hw : ‖w‖ = 1) : ∃ K : ℝ≥0, LipschitzWith K (rayIntegral g w) := by
  obtain ⟨K, hK⟩ := exists_norm_fderiv_rayIntegral_le hg hgc hw
  refine ⟨K.toNNReal, lipschitzWith_of_nnNorm_fderiv_le
    (fun y => (hasFDerivAt_rayIntegral hg hgc hw y).differentiableAt) fun y => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnNorm]
  exact (hK y).trans (Real.le_coe_toNNReal K)

end RayIntegral

/-! ### The product rule -/

section ProductRule

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The product rule for line derivatives**: for `f, g : V → ℂ` differentiable at `x`,
`∂_v (f g)(x) = ∂_v f(x) g(x) + f(x) ∂_v g(x)` (Mathlib's `fderiv_fun_mul` and
`DifferentiableAt.lineDeriv_eq_fderiv`). -/
theorem lineDeriv_mul {f g : V → ℂ} {x : V} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : V) :
    lineDeriv ℝ (fun y => f y * g y) x v = lineDeriv ℝ f x v * g x + f x * lineDeriv ℝ g x v := by
  have hfg : DifferentiableAt ℝ (fun y => f y * g y) x := hf.mul hg
  rw [hfg.lineDeriv_eq_fderiv, fderiv_fun_mul hf hg, hf.lineDeriv_eq_fderiv,
    hg.lineDeriv_eq_fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The product rule for Schwartz functions: `∂_v (w₁ w₂) = (∂_v w₁) w₂ + w₁ ∂_v w₂`
(`Rd.lineDeriv_mul`, Mathlib's `SchwartzMap.lineDerivOp_apply`). -/
theorem lineDeriv_mul_schwartz (w₁ w₂ : 𝓢(V, ℂ)) (v x : V) :
    lineDeriv ℝ (fun y => w₁ y * w₂ y) x v = (∂_{v} w₁) x * w₂ x + w₁ x * (∂_{v} w₂) x := by
  rw [lineDeriv_mul w₁.differentiableAt w₂.differentiableAt, SchwartzMap.lineDerivOp_apply,
    SchwartzMap.lineDerivOp_apply]

end ProductRule

/-! ### Green's integrand -/

section GreenIntegrand

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **The integral of Green's integrand as a pairing**: for a measurable set `s` and
`U, W ∈ H^1(V)`, `∫_s (∂_v U) W + U ∂_v W = ⟨1_s ∂_v U, W⟩ + ⟨1_s U, ∂_v W⟩` with the bilinear
pairing of `L_2(V)` with itself (`Rd.setIntegral_mul_eq_lpPairing`). -/
theorem setIntegral_weakDeriv_mul_add_eq {s : Set V} (hs : MeasurableSet s) (v : V)
    (U W : H^{1}(V)) :
    ∫ x in s, weakDerivL2 v U x * toL2 W x + toL2 U x * weakDerivL2 v W x =
      (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume 2 2 (indicatorLp hs (weakDerivL2 v U))
          (toL2 W) +
        (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume 2 2 (indicatorLp hs (toL2 U))
          (weakDerivL2 v W) := by
  rw [← setIntegral_mul_eq_lpPairing, ← setIntegral_mul_eq_lpPairing, integral_add]
  · exact ((Lp.memLp _).integrable_mul (Lp.memLp _)).restrict
  · exact ((Lp.memLp _).integrable_mul (Lp.memLp _)).restrict

/-- The left side of Green's formula on a measurable set `s`,
`(U, W) ↦ ∫_s (∂_v U) W + U ∂_v W`, is continuous on `H^1(V) × H^1(V)`: a sum of bounded
bilinear pairings (`Rd.setIntegral_weakDeriv_mul_add_eq`). -/
theorem continuous_setIntegral_weakDeriv_mul_add {s : Set V} (hs : MeasurableSet s) (v : V) :
    Continuous fun p : H^{1}(V) × H^{1}(V) =>
      ∫ x in s, weakDerivL2 v p.1 x * toL2 p.2 x + toL2 p.1 x * weakDerivL2 v p.2 x := by
  set P := (ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume : Measure V) 2 2
  set I := indicatorLp (p := 2) (μ := (volume : Measure V)) hs
  simp only [setIntegral_weakDeriv_mul_add_eq hs]
  have h1 : Continuous fun p : H^{1}(V) × H^{1}(V) => I (weakDerivL2 v p.1) :=
    I.continuous.comp ((weakDerivL2 v).continuous.comp continuous_fst)
  have h2 : Continuous fun p : H^{1}(V) × H^{1}(V) => I (toL2 p.1) :=
    I.continuous.comp (toL2.continuous.comp continuous_fst)
  have h3 : Continuous fun p : H^{1}(V) × H^{1}(V) => toL2 p.2 :=
    toL2.continuous.comp continuous_snd
  have h4 : Continuous fun p : H^{1}(V) × H^{1}(V) => weakDerivL2 v p.2 :=
    (weakDerivL2 v).continuous.comp continuous_snd
  exact ((P.continuous.comp h1).clm_apply h3).add ((P.continuous.comp h2).clm_apply h4)

end GreenIntegrand

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (Ω : LipschitzGraph V)

/-! ### Fubini in product coordinates -/

/-- **Integrals over `Ω` in coordinates**: if `T : H × ℝ → V` preserves the Lebesgue measures and
`T(x', t) ∈ Ω` iff `a(x') < t`, then `∫_Ω F = ∫_H ∫_{a(x')}^∞ F(T(x', t)) dt dx'` for every `F`
integrable on `Ω` (Fubini's theorem, Mathlib's `integral_prod`). -/
theorem setIntegral_domain_eq_of_measurePreserving {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (T : Ω.hyperplane × ℝ ≃ᵐ V)
    (hT : MeasurePreserving T (volume.prod volume) volume) (a : Ω.hyperplane → ℝ)
    (ha : ∀ p, T p ∈ Ω.domain ↔ a p.1 < p.2) {F : V → E} (hF : IntegrableOn F Ω.domain) :
    ∫ x in Ω.domain, F x = ∫ x', ∫ t in Ioi (a x'), F (T (x', t)) := by
  rw [← integral_indicator Ω.measurableSet_domain, ← hT.integral_comp' (Ω.domain.indicator F)]
  have hint : Integrable (fun p => Ω.domain.indicator F (T p)) (volume.prod volume) :=
    (hT.integrable_comp_emb T.measurableEmbedding).2
      (hF.integrable_indicator Ω.measurableSet_domain)
  rw [integral_prod _ hint]
  refine integral_congr_ae (ae_of_all _ fun x' => ?_)
  dsimp only
  rw [← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  dsimp only
  by_cases h : a x' < t
  · rw [indicator_of_mem ((ha (x', t)).2 h), indicator_of_mem (show t ∈ Ioi (a x') from h)]
  · rw [indicator_of_notMem (fun hm => h ((ha (x', t)).1 hm)),
      indicator_of_notMem (show t ∉ Ioi (a x') from h)]

/-- `x' + t e ∈ Ω` iff `φ(x') < t`. -/
theorem prodEquiv_mem_domain_iff (p : Ω.hyperplane × ℝ) :
    Ω.prodEquiv p ∈ Ω.domain ↔ Ω.phi p.1 < p.2 := by
  rw [prodEquiv_apply]
  change Ω.phi ((p.1 : V) + p.2 • Ω.e) < inner ℝ ((p.1 : V) + p.2 • Ω.e) Ω.e ↔ _
  rw [Ω.const, inner_add_left, Ω.inner_coe_e, real_inner_smul_left, Ω.inner_e_self, mul_one,
    zero_add]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `γ(x') + t e ∈ Ω` iff `0 < t`: the domain lies above the graph. -/
theorem graphMap_add_smul_mem_domain_iff (x' : Ω.hyperplane) (t : ℝ) :
    Ω.graphMap x' + t • Ω.e ∈ Ω.domain ↔ 0 < t := by
  change Ω.phi (Ω.graphMap x' + t • Ω.e) < inner ℝ (Ω.graphMap x' + t • Ω.e) Ω.e ↔ _
  rw [Ω.const, Ω.phi_graphMap, inner_add_left, Ω.inner_graphMap, real_inner_smul_left,
    Ω.inner_e_self, mul_one, lt_add_iff_pos_right]

/-- **Fubini on a Lipschitz graph domain**: `∫_Ω F = ∫_H ∫_{φ(x')}^∞ F(x' + t e) dt dx'` for every
`F` integrable on `Ω`. -/
theorem setIntegral_domain_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : V → E}
    (hF : IntegrableOn F Ω.domain) :
    ∫ x in Ω.domain, F x = ∫ x' : Ω.hyperplane, ∫ t in Ioi (Ω.phi x'), F (x' + t • Ω.e) := by
  rw [Ω.setIntegral_domain_eq_of_measurePreserving Ω.prodEquiv Ω.measurePreserving_prodEquiv
    (fun x' => Ω.phi x') Ω.prodEquiv_mem_domain_iff hF]
  simp only [prodEquiv_apply]

/-- **Fubini in graph coordinates**: `∫_Ω F = ∫_H ∫_0^∞ F(γ(x') + t e) dt dx'` for every `F`
integrable on `Ω`. -/
theorem setIntegral_domain_eq_graphMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : V → E} (hF : IntegrableOn F Ω.domain) :
    ∫ x in Ω.domain, F x = ∫ x', ∫ t in Ioi (0 : ℝ), F (Ω.graphMap x' + t • Ω.e) := by
  rw [Ω.setIntegral_domain_eq_of_measurePreserving Ω.graphEquiv Ω.measurePreserving_graphEquiv
    (fun _ => 0) (fun p => by rw [graphEquiv_apply, graphMap_add_smul_mem_domain_iff]) hF]
  simp only [graphEquiv_apply]

/-! ### The normal weight -/

/-- The **normal weight** `n_v(x') = ⟪∇φ(x'), v⟫ - ⟪v, e⟫` of the direction `v` in the chart: the
boundary term of `∫_Ω ∂_v g` is `∫_H g(γ x') n_v(x') dx'`, and
`n_v = ⟪v, ν⟫ √(1 + ‖∇φ‖²)` (`Rd.LipschitzGraph.inner_normalAt_mul_gram`). -/
noncomputable def normalWeight (v : V) (x' : Ω.hyperplane) : ℝ :=
  inner ℝ (Ω.gradPhi x' : V) v - inner ℝ v Ω.e

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The normal weight by the unit normal**: `⟪v, ν(x')⟫ √(1 + ‖∇φ(x')‖²) = n_v(x')`, since
`ν = (∇φ - e)/√(1 + ‖∇φ‖²)`. -/
theorem inner_normalAt_mul_gram (v : V) (x' : Ω.hyperplane) :
    inner ℝ v (Ω.normalAt x') * Ω.gram x' = Ω.normalWeight v x' := by
  rw [normalAt, real_inner_smul_right, inner_sub_right, normalWeight, real_inner_comm v,
    mul_comm, ← mul_assoc, mul_inv_cancel₀ (Ω.gram_pos x').ne', one_mul]

omit [MeasurableSpace V] [BorelSpace V] in
/-- The normal weight is bounded: `|n_v| ≤ (M + 1) ‖v‖`, since `‖∇φ‖ ≤ M`. -/
theorem abs_normalWeight_le (v : V) (x' : Ω.hyperplane) :
    |Ω.normalWeight v x'| ≤ (Ω.M + 1) * ‖v‖ := by
  have h1 : |inner ℝ (Ω.gradPhi x' : V) v| ≤ Ω.M * ‖v‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      ((Submodule.norm_coe _).trans_le (Ω.norm_gradPhi_le x')) (norm_nonneg _))
  have h2 : |inner ℝ v Ω.e| ≤ ‖v‖ := by
    simpa [Ω.norm_e] using abs_real_inner_le_norm v Ω.e
  calc |Ω.normalWeight v x'| ≤ |inner ℝ (Ω.gradPhi x' : V) v| + |inner ℝ v Ω.e| :=
        abs_sub _ _
    _ ≤ (Ω.M + 1) * ‖v‖ := by linarith

/-- The normal weight is measurable. -/
theorem measurable_normalWeight (v : V) : Measurable (Ω.normalWeight v) :=
  ((continuous_subtype_val.measurable.comp Ω.measurable_gradPhi).inner measurable_const).sub
    measurable_const

/-! ### The ray integral from the graph -/

variable {g : V → ℂ}

/-- The **ray integral from the graph** `Ψ(γ x') = ∫_{φ(x')}^∞ g(x' + t e) dt`, the ray integral
of `g` from the boundary point `γ x'` upwards. -/
noncomputable def graphRayIntegral (g : V → ℂ) (x' : Ω.hyperplane) : ℂ :=
  rayIntegral g Ω.e (Ω.graphMap x')

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `‖x'‖ ≤ ‖γ(x') + t e‖`: `x'` is the projection of `γ(x') + t e` onto `H`. -/
theorem norm_le_norm_graphMap_add_smul (x' : Ω.hyperplane) (t : ℝ) :
    ‖x'‖ ≤ ‖Ω.graphMap x' + t • Ω.e‖ := by
  have h : Ω.graphMap x' + t • Ω.e = (x' : V) + (Ω.phi x' + t) • Ω.e := by
    rw [graphMap, add_smul, add_assoc]
  rw [h]
  exact Ω.norm_le_norm_coe_add_smul_e x' _

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- If `tsupport h ⊆ closedBall(0, R)` and `‖x'‖ > R`, then `h` vanishes on the vertical line
through
`γ(x')`. -/
theorem apply_graphMap_add_smul_eq_zero_of_norm_lt {F : Type*} [Zero F] {h : V → F} {R : ℝ}
    (hR : tsupport h ⊆ closedBall 0 R) {x' : Ω.hyperplane} (hx : R < ‖x'‖) (t : ℝ) :
    h (Ω.graphMap x' + t • Ω.e) = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun hm => ?_
  have := hR hm
  rw [mem_closedBall_zero_iff] at this
  linarith [Ω.norm_le_norm_graphMap_add_smul x' t]

omit [MeasurableSpace V] [BorelSpace V] in
/-- The ray integral from the graph of a compactly supported `g` has compact support in `H`. -/
theorem hasCompactSupport_graphRayIntegral (hgc : HasCompactSupport g) :
    HasCompactSupport (Ω.graphRayIntegral g) := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Ω.hyperplane) R) fun x' hx' => ?_
  rw [mem_closedBall_zero_iff, not_le] at hx'
  exact integral_eq_zero_of_ae (ae_of_all _ fun t =>
    Ω.apply_graphMap_add_smul_eq_zero_of_norm_lt hR hx' t)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The ray integral from the graph of `g ∈ C^1` with compact support is Lipschitz: the ray
integral is Lipschitz (`Rd.exists_lipschitzWith_rayIntegral`) and so is the graph map. -/
theorem exists_lipschitzWith_graphRayIntegral (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    ∃ K : ℝ≥0, LipschitzWith K (Ω.graphRayIntegral g) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_rayIntegral hg hgc Ω.norm_e
  exact ⟨_, hK.comp Ω.lipschitzWith_graphMap⟩

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
variable {Ω} in
/-- **The derivative of the graph map**: where `φ|_H` is differentiable,
`Dγ(x') v' = v' + Dφ(x') v' e`. -/
theorem hasFDerivAt_graphMap {x' : Ω.hyperplane} (hd : DifferentiableAt ℝ Ω.phiH x') :
    HasFDerivAt Ω.graphMap (Ω.hyperplane.subtypeL + (fderiv ℝ Ω.phiH x').smulRight Ω.e) x' :=
  Ω.hyperplane.subtypeL.hasFDerivAt.add (hd.hasFDerivAt.smul_const Ω.e)

omit [MeasurableSpace V] [BorelSpace V] in
variable {Ω} in
/-- **The line derivative of the ray integral from the graph**: where `φ|_H` is differentiable,
the chain rule and `DΨ e = -g` (`Rd.fderiv_rayIntegral_self`) give
`∂_{v'}(Ψ ∘ γ)(x') = DΨ(γ x') v' - ⟪∇φ(x'), v'⟫ g(γ x')` for `v' ∈ H`. -/
theorem lineDeriv_graphRayIntegral (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    {x' : Ω.hyperplane} (hd : DifferentiableAt ℝ Ω.phiH x') (v' : Ω.hyperplane) :
    lineDeriv ℝ (Ω.graphRayIntegral g) x' v' =
      fderiv ℝ (rayIntegral g Ω.e) (Ω.graphMap x') v' -
        (inner ℝ (Ω.gradPhi x') v' : ℂ) * g (Ω.graphMap x') := by
  have hL := hasFDerivAt_rayIntegral hg hgc Ω.norm_e (Ω.graphMap x')
  have h := hL.comp x' (hasFDerivAt_graphMap hd)
  have hfun : Ω.graphRayIntegral g = rayIntegral g Ω.e ∘ Ω.graphMap := rfl
  rw [hfun, h.differentiableAt.lineDeriv_eq_fderiv, h.fderiv, ← hL.fderiv]
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    Submodule.subtypeL_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul,
    fderiv_rayIntegral_self hg hgc Ω.norm_e, ← Ω.inner_gradPhi, Complex.real_smul]
  ring

/-- `x' ↦ h(γ x')` is integrable on `H` for continuous compactly supported `h`. -/
theorem integrable_comp_graphMap {h : V → ℂ} (hh : Continuous h) (hhc : HasCompactSupport h) :
    Integrable fun x' => h (Ω.graphMap x') := by
  obtain ⟨R, hR⟩ := hhc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨C, hC⟩ := hh.bounded_above_of_compact_support hhc
  refine integrable_of_norm_le_of_forall_norm_gt_eq_zero
    (hh.comp Ω.continuous_graphMap).aestronglyMeasurable (fun x' => hC _) (R := R) fun x' hx' => ?_
  simpa using Ω.apply_graphMap_add_smul_eq_zero_of_norm_lt hR hx' 0

/-- `x' ↦ DΨ(γ x') v` is integrable on `H`: it is bounded (`Rd.exists_norm_fderiv_rayIntegral_le`)
and vanishes for `‖x'‖ > R` when `tsupport g ⊆ closedBall(0, R)`. -/
theorem integrable_fderiv_rayIntegral (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (v : V) : Integrable fun x' => fderiv ℝ (rayIntegral g Ω.e) (Ω.graphMap x') v := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨K, hK⟩ := exists_norm_fderiv_rayIntegral_le hg hgc Ω.norm_e
  have hm : Measurable fun x' => fderiv ℝ (rayIntegral g Ω.e) (Ω.graphMap x') v :=
    (ContinuousLinearMap.apply ℝ ℂ v).continuous.measurable.comp
      ((measurable_fderiv ℝ (rayIntegral g Ω.e)).comp Ω.continuous_graphMap.measurable)
  refine integrable_of_norm_le_of_forall_norm_gt_eq_zero hm.aestronglyMeasurable
    (fun x' => ((fderiv ℝ (rayIntegral g Ω.e) (Ω.graphMap x')).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hK _) (norm_nonneg v))) (R := R) fun x' hx' => ?_
  rw [fderiv_rayIntegral_apply hg hgc Ω.norm_e]
  refine integral_eq_zero_of_ae (ae_of_all _ fun t => ?_)
  dsimp only
  rw [Pi.zero_apply,
    Ω.apply_graphMap_add_smul_eq_zero_of_norm_lt ((tsupport_fderiv_subset ℝ).trans hR) hx' t,
    zero_apply]

/-- `x' ↦ ⟪∇φ(x'), v'⟫ g(γ x')` is integrable on `H` for continuous compactly supported `g`. -/
theorem integrable_inner_gradPhi_mul (hg : Continuous g) (hgc : HasCompactSupport g)
    (v' : Ω.hyperplane) :
    Integrable fun x' => (inner ℝ (Ω.gradPhi x') v' : ℂ) * g (Ω.graphMap x') := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  have hm : Measurable fun x' => (inner ℝ (Ω.gradPhi x') v' : ℂ) :=
    Complex.measurable_ofReal.comp (Ω.measurable_gradPhi.inner measurable_const)
  refine integrable_of_norm_le_of_forall_norm_gt_eq_zero
    (hm.aestronglyMeasurable.mul (hg.comp Ω.continuous_graphMap).aestronglyMeasurable)
    (C := Ω.M * ‖v'‖ * C) (fun x' => ?_) (R := R) fun x' hx' => ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      (Ω.norm_gradPhi_le x') (norm_nonneg _))) (hC _) (norm_nonneg _)
      (mul_nonneg Ω.M_nonneg (norm_nonneg _))
  · have h0 := Ω.apply_graphMap_add_smul_eq_zero_of_norm_lt hR hx' 0
    rw [zero_smul, add_zero] at h0
    rw [h0, mul_zero]

/-- **The horizontal directions**: for `g ∈ C^1` with compact support and `v' ∈ H`,
`∫_H DΨ(γ x') v' dx' = ∫_H ⟪∇φ(x'), v'⟫ g(γ x') dx'`. The ray integral from the graph `Ψ ∘ γ` is
Lipschitz with compact support, so its line derivative integrates to zero
(`Rd.integral_lineDeriv_eq_zero_complex`), and almost everywhere it is the difference of the
two integrands (`Rd.LipschitzGraph.lineDeriv_graphRayIntegral`, Rademacher's theorem for `φ|_H`). -/
theorem integral_fderiv_rayIntegral_graphMap (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (v' : Ω.hyperplane) :
    ∫ x', fderiv ℝ (rayIntegral g Ω.e) (Ω.graphMap x') v' =
      ∫ x', (inner ℝ (Ω.gradPhi x') v' : ℂ) * g (Ω.graphMap x') := by
  have hA := Ω.integrable_fderiv_rayIntegral hg hgc v'
  have hB := Ω.integrable_inner_gradPhi_mul hg.continuous hgc v'
  have hae : (fun x' => lineDeriv ℝ (Ω.graphRayIntegral g) x' v') =ᵐ[volume] fun x' =>
      fderiv ℝ (rayIntegral g Ω.e) (Ω.graphMap x') v' -
        (inner ℝ (Ω.gradPhi x') v' : ℂ) * g (Ω.graphMap x') := by
    filter_upwards [Ω.ae_differentiableAt_phiH] with x' hx'
    exact lineDeriv_graphRayIntegral hg hgc hx' v'
  obtain ⟨K, hK⟩ := Ω.exists_lipschitzWith_graphRayIntegral hg hgc
  have h0 := integral_lineDeriv_eq_zero_complex (μ := volume) hK
    (Ω.hasCompactSupport_graphRayIntegral hgc) v'
  rw [integral_congr_ae hae, integral_sub hA hB, sub_eq_zero] at h0
  exact h0

/-! ### Gauss–Green for smooth functions -/

/-- **Gauss–Green on a Lipschitz graph domain, in chart form**: for `g ∈ C^1` with compact support
and every direction `v`, `∫_Ω ∂_v g = ∫_H g(γ x') n_v(x') dx'` with the normal weight
`n_v = ⟪∇φ, v⟫ - ⟪v, e⟫` (`Rd.LipschitzGraph.normalWeight`). By Fubini in graph coordinates the
left side is `∫_H DΨ(γ x') v dx'` for the ray integral `Ψ` of `g`
(`Rd.fderiv_rayIntegral_apply`); write `v = Pv + ⟪v, e⟫ e`, use `DΨ e = -g` and the horizontal
identity (`Rd.LipschitzGraph.integral_fderiv_rayIntegral_graphMap`). With the surface measure it
reads `∫_Ω ∂_v g = ∫_Γ g ⟪v, ν⟫ dσ` (`Rd.LipschitzGraph.setIntegral_lineDeriv_eq_surface`). -/
theorem setIntegral_lineDeriv_eq (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (v : V) :
    ∫ x in Ω.domain, lineDeriv ℝ g x v = ∫ x', g (Ω.graphMap x') * Ω.normalWeight v x' := by
  have hdv : ∀ x, lineDeriv ℝ g x v = fderiv ℝ g x v := fun x =>
    ((hg.differentiable one_ne_zero) x).lineDeriv_eq_fderiv
  have hint : IntegrableOn (fun x => fderiv ℝ g x v) Ω.domain :=
    (((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
      ).integrable_of_hasCompactSupport
      ((hgc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : V →L[ℝ] ℂ => L v) rfl)).integrableOn
  have hG := Ω.integrable_comp_graphMap hg.continuous hgc
  have hA := Ω.integrable_fderiv_rayIntegral hg hgc (Ω.proj v)
  have hB := Ω.integrable_inner_gradPhi_mul hg.continuous hgc (Ω.proj v)
  have hv : v = (Ω.proj v : V) + inner ℝ v Ω.e • Ω.e := by rw [coe_proj]; abel
  simp only [hdv]
  rw [Ω.setIntegral_domain_eq_graphMap hint]
  calc ∫ x', ∫ t in Ioi (0 : ℝ), fderiv ℝ g (Ω.graphMap x' + t • Ω.e) v
      = ∫ x', (fderiv ℝ (rayIntegral g Ω.e) (Ω.graphMap x') (Ω.proj v) -
          (inner ℝ v Ω.e : ℂ) * g (Ω.graphMap x')) := by
        refine integral_congr_ae (ae_of_all _ fun x' => ?_)
        simp only
        rw [← fderiv_rayIntegral_apply hg hgc Ω.norm_e]
        conv_lhs => rw [hv]
        rw [map_add, map_smul, fderiv_rayIntegral_self hg hgc Ω.norm_e, Complex.real_smul]
        ring
    _ = (∫ x', fderiv ℝ (rayIntegral g Ω.e) (Ω.graphMap x') (Ω.proj v)) -
          ∫ x', (inner ℝ v Ω.e : ℂ) * g (Ω.graphMap x') := integral_sub hA (hG.const_mul _)
    _ = (∫ x', (inner ℝ (Ω.gradPhi x') (Ω.proj v) : ℂ) * g (Ω.graphMap x')) -
          ∫ x', (inner ℝ v Ω.e : ℂ) * g (Ω.graphMap x') := by
        rw [Ω.integral_fderiv_rayIntegral_graphMap hg hgc]
    _ = ∫ x', ((inner ℝ (Ω.gradPhi x') (Ω.proj v) : ℂ) * g (Ω.graphMap x') -
          (inner ℝ v Ω.e : ℂ) * g (Ω.graphMap x')) := (integral_sub hB (hG.const_mul _)).symm
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun x' => ?_)
        simp only [normalWeight, Ω.inner_coe_eq_inner_proj, Complex.ofReal_sub]
        ring

/-- **Gauss–Green with the unit normal**: `∫_Ω ∂_v g = ∫_H g(γ x') ⟪v, ν(x')⟫ √(1 + ‖∇φ(x')‖²) dx'`
(`Rd.LipschitzGraph.inner_normalAt_mul_gram`). -/
theorem setIntegral_lineDeriv_eq_normal (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (v : V) :
    ∫ x in Ω.domain, lineDeriv ℝ g x v =
      ∫ x', g (Ω.graphMap x') * (inner ℝ v (Ω.normalAt x') : ℂ) * (Ω.gram x' : ℂ) := by
  rw [Ω.setIntegral_lineDeriv_eq hg hgc]
  refine integral_congr_ae (ae_of_all _ fun x' => ?_)
  simp only [← Ω.inner_normalAt_mul_gram, Complex.ofReal_mul]
  ring

/-- **The vertical direction**: `∫_Ω ∂_e g = -∫_H g(γ x') dx'`, the fundamental theorem of calculus
on each vertical line above the graph. -/
theorem setIntegral_lineDeriv_e (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    ∫ x in Ω.domain, lineDeriv ℝ g x Ω.e = -∫ x', g (Ω.graphMap x') := by
  rw [Ω.setIntegral_lineDeriv_eq hg hgc, ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun x' => ?_)
  simp [normalWeight, Ω.inner_coe_e, Ω.norm_e]

/-- **The horizontal directions**: `∫_Ω ∂_{v'} g = ∫_H g(γ x') ⟪∇φ(x'), v'⟫ dx'` for `v' ∈ H`,
a Leibniz rule for the integral above the graph in integrated form. -/
theorem setIntegral_lineDeriv_hyperplane (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (v' : Ω.hyperplane) :
    ∫ x in Ω.domain, lineDeriv ℝ g x v' =
      ∫ x', g (Ω.graphMap x') * (inner ℝ (Ω.gradPhi x') v' : ℂ) := by
  rw [Ω.setIntegral_lineDeriv_eq hg hgc]
  refine integral_congr_ae (ae_of_all _ fun x' => ?_)
  simp [normalWeight, Ω.inner_coe_e, Submodule.coe_inner]

/-- **Gauss–Green on a Lipschitz graph domain, surface form**: for `g ∈ C^1` with compact
support and every direction `v`, `∫_Ω ∂_v g = ∫_Γ g ⟪v, ν⟫ dμHE[n-1]` over the boundary
`Γ = γ(H)`, with the outward unit normal `ν(y) = ν(Py)` (the area formula
`Rd.LipschitzGraph.integral_graphMap`). -/
theorem setIntegral_lineDeriv_eq_surface (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (v : V) :
    ∫ x in Ω.domain, lineDeriv ℝ g x v = ∫ y in range Ω.graphMap,
      g y * (inner ℝ v (Ω.normalAt (Ω.proj y)) : ℂ) ∂(μHE[finrank ℝ V - 1] : Measure V) := by
  rw [Ω.integral_graphMap, Ω.setIntegral_lineDeriv_eq_normal hg hgc]
  simp only [proj_graphMap]

/-! ### Green's formula -/

/-- The normal weight is a bounded function, an element of `L_∞(H)`
(`Rd.LipschitzGraph.abs_normalWeight_le`). -/
theorem memLp_top_normalWeight (v : V) :
    MemLp (fun x' => (Ω.normalWeight v x' : ℂ)) ∞ volume :=
  memLp_top_of_bound
    (Complex.measurable_ofReal.comp (Ω.measurable_normalWeight v)).aestronglyMeasurable
    ((Ω.M + 1) * ‖v‖) (ae_of_all _ fun x' => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Ω.abs_normalWeight_le v x')

/-- `∫_H a b n_v = ⟨a, n_v b⟩` for `a, b ∈ L_2(H)`, with the pairing of `L_2` with `L_2` and the
product of `L_∞` with `L_2` (Mathlib's `ContinuousLinearMap.holderL`). -/
theorem integral_mul_mul_normalWeight_eq (v : V) (a b : Lp ℂ 2 (volume : Measure Ω.hyperplane)) :
    ∫ x', a x' * b x' * (Ω.normalWeight v x' : ℂ) =
      (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume 2 2 a
        ((ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2
          ((Ω.memLp_top_normalWeight v).toLp _) b) := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousLinearMap.coeFn_holder (ContinuousLinearMap.mul ℂ ℂ) (r := 2)
    ((Ω.memLp_top_normalWeight v).toLp _) b, (Ω.memLp_top_normalWeight v).coeFn_toLp] with x' h1 h2
  rw [ContinuousLinearMap.holderL_apply_apply, ContinuousLinearMap.mul_apply', h1,
    ContinuousLinearMap.mul_apply', h2]
  ring

/-- The left side of Green's formula, `(U, W) ↦ ∫_Ω (∂_v U) W + U ∂_v W`, is continuous on
`H^1(V) × H^1(V)` (`Rd.continuous_setIntegral_weakDeriv_mul_add`). -/
theorem continuous_setIntegral_weakDeriv_mul_add (v : V) : Continuous fun p : H^{1}(V) × H^{1}(V) =>
    ∫ x in Ω.domain, weakDerivL2 v p.1 x * toL2 p.2 x + toL2 p.1 x * weakDerivL2 v p.2 x :=
  Rd.continuous_setIntegral_weakDeriv_mul_add Ω.measurableSet_domain v

/-- The right side of Green's formula, `(U, W) ↦ ∫_H Tr U · Tr W · n_v`, is continuous on
`H^1(V) × H^1(V)`. -/
theorem continuous_integral_traceH1_mul_normalWeight (v : V) :
    Continuous fun p : H^{1}(V) × H^{1}(V) =>
      ∫ x', Ω.traceH1 p.1 x' * Ω.traceH1 p.2 x' * (Ω.normalWeight v x' : ℂ) := by
  set P := (ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume : Measure Ω.hyperplane) 2 2
  set N := (ContinuousLinearMap.mul ℂ ℂ).holderL (volume : Measure Ω.hyperplane) ∞ 2 2
    ((Ω.memLp_top_normalWeight v).toLp _)
  have he : ∀ p : H^{1}(V) × H^{1}(V),
      ∫ x', Ω.traceH1 p.1 x' * Ω.traceH1 p.2 x' * (Ω.normalWeight v x' : ℂ) =
        P (Ω.traceH1 p.1) (N (Ω.traceH1 p.2)) := fun p =>
    Ω.integral_mul_mul_normalWeight_eq v _ _
  simp only [he]
  have h1 : Continuous fun p : H^{1}(V) × H^{1}(V) => Ω.traceH1 p.1 :=
    Ω.traceH1.continuous.comp continuous_fst
  have h2 : Continuous fun p : H^{1}(V) × H^{1}(V) => N (Ω.traceH1 p.2) :=
    N.continuous.comp (Ω.traceH1.continuous.comp continuous_snd)
  exact (P.continuous.comp h1).clm_apply h2

/-- **Green's formula for Schwartz functions**: for Schwartz functions `w₁`, `w₂`, the first with
compact support, `∫_Ω (∂_v w₁) w₂ + w₁ ∂_v w₂ = ∫_H Tr w₁ · Tr w₂ · n_v`, Gauss–Green for the
product `w₁ w₂` (`Rd.LipschitzGraph.setIntegral_lineDeriv_eq`). -/
theorem setIntegral_green_ofSchwartz {w₁ : 𝓢(V, ℂ)} (hw₁ : HasCompactSupport w₁)
    (w₂ : 𝓢(V, ℂ)) (v : V) :
    ∫ x in Ω.domain, weakDerivL2 v (ofSchwartz 1 w₁) x * toL2 (ofSchwartz 1 w₂) x +
        toL2 (ofSchwartz 1 w₁) x * weakDerivL2 v (ofSchwartz 1 w₂) x =
      ∫ x', Ω.traceH1 (ofSchwartz 1 w₁) x' * Ω.traceH1 (ofSchwartz 1 w₂) x' *
        (Ω.normalWeight v x' : ℂ) := by
  have hL : ∫ x in Ω.domain, weakDerivL2 v (ofSchwartz 1 w₁) x * toL2 (ofSchwartz 1 w₂) x +
        toL2 (ofSchwartz 1 w₁) x * weakDerivL2 v (ofSchwartz 1 w₂) x =
      ∫ x in Ω.domain, lineDeriv ℝ (fun y => w₁ y * w₂ y) x v := by
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    rw [weakDerivL2_ofSchwartz, weakDerivL2_ofSchwartz, toL2_ofSchwartz, toL2_ofSchwartz]
    filter_upwards [(∂_{v} w₁).coeFn_toLp 2 volume, (∂_{v} w₂).coeFn_toLp 2 volume,
      w₁.coeFn_toLp 2 volume, w₂.coeFn_toLp 2 volume] with x h1 h2 h3 h4
    rw [h1, h2, h3, h4, lineDeriv_mul_schwartz]
  have hg : ContDiff ℝ 1 fun y => w₁ y * w₂ y :=
    ((w₁.smooth ⊤).mul (w₂.smooth ⊤)).of_le (by exact_mod_cast le_top)
  rw [hL, Ω.setIntegral_lineDeriv_eq hg hw₁.mul_right]
  refine integral_congr_ae ?_
  filter_upwards [Ω.traceH1_ofSchwartz_ae w₁, Ω.traceH1_ofSchwartz_ae w₂] with x' h1 h2
  rw [h1, h2]

/-- **Green's formula for `H^1(V)` on a Lipschitz graph domain**: for `U, W ∈ H^1(V)` and every
direction `v`, `∫_Ω (∂_v U) W + U ∂_v W = ∫_H Tr U · Tr W · n_v` with the normal weight
`n_v = ⟪∇φ, v⟫ - ⟪v, e⟫`. Both sides are continuous on `H^1(V) × H^1(V)` and agree on the dense set
of pairs of compactly supported Schwartz functions (`Rd.dense_ofSchwartz_hasCompactSupport`). -/
theorem setIntegral_green_besselPotentialSpace (U W : H^{1}(V)) (v : V) :
    ∫ x in Ω.domain, weakDerivL2 v U x * toL2 W x + toL2 U x * weakDerivL2 v W x =
      ∫ x', Ω.traceH1 U x' * Ω.traceH1 W x' * (Ω.normalWeight v x' : ℂ) := by
  have hd := (dense_ofSchwartz_hasCompactSupport (V := V) 1).prod
    (dense_ofSchwartz_hasCompactSupport (V := V) 1)
  refine hd.induction (P := fun p : H^{1}(V) × H^{1}(V) =>
    ∫ x in Ω.domain, weakDerivL2 v p.1 x * toL2 p.2 x + toL2 p.1 x * weakDerivL2 v p.2 x =
      ∫ x', Ω.traceH1 p.1 x' * Ω.traceH1 p.2 x' * (Ω.normalWeight v x' : ℂ)) ?_
    (isClosed_eq (Ω.continuous_setIntegral_weakDeriv_mul_add v)
      (Ω.continuous_integral_traceH1_mul_normalWeight v)) (U, W)
  rintro ⟨_, _⟩ ⟨⟨w₁, hw₁, rfl⟩, ⟨w₂, -, rfl⟩⟩
  exact Ω.setIntegral_green_ofSchwartz hw₁ w₂ v

/-- **Green's formula on a Lipschitz graph domain**: for `f, g ∈ W^1_2(V)` with weak derivatives
`f_v = ∂_v f`, `g_v = ∂_v g` in `L_2(V)`,
`∫_Ω f_v g + f g_v = ∫_H Tr f · Tr g · n_v` with the traces of the trace theorem at `s = 1/2` and
the normal weight `n_v = ⟪∇φ, v⟫ - ⟪v, e⟫`
(`Rd.LipschitzGraph.setIntegral_green_besselPotentialSpace`). -/
theorem setIntegral_green (f g : Lp ℂ 2 (volume : Measure V)) (hf : MemSobolev 1 f)
    (hg : MemSobolev 1 g) (v : V) {fv gv : Lp ℂ 2 (volume : Measure V)}
    (hfv : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) f fv)
    (hgv : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) g gv) :
    ∫ x in Ω.domain, fv x * g x + f x * gv x =
      ∫ x', Ω.trace two_ne_top 2 f x' * Ω.trace two_ne_top 2 g x' * (Ω.normalWeight v x' : ℂ) := by
  obtain ⟨U, rfl⟩ := exists_toL2_eq_of_memSobolev hf
  obtain ⟨W, rfl⟩ := exists_toL2_eq_of_memSobolev hg
  rw [← weakDerivL2_eq hfv, ← weakDerivL2_eq hgv]
  exact Ω.setIntegral_green_besselPotentialSpace U W v

/-- **Green's formula, surface form**: for `U, W ∈ H^1(V)` and every direction `v`,
`∫_Ω (∂_v U) W + U ∂_v W = ∫_Γ Tr U · Tr W ⟪v, ν⟫ dμHE[n-1]` over the boundary `Γ = γ(H)`, with
the traces and the normal read through the projection `P` (the area formula
`Rd.LipschitzGraph.integral_graphMap`). -/
theorem setIntegral_green_surface (U W : H^{1}(V)) (v : V) :
    ∫ x in Ω.domain, weakDerivL2 v U x * toL2 W x + toL2 U x * weakDerivL2 v W x =
      ∫ y in range Ω.graphMap, Ω.traceH1 U (Ω.proj y) * Ω.traceH1 W (Ω.proj y) *
        (inner ℝ v (Ω.normalAt (Ω.proj y)) : ℂ) ∂(μHE[finrank ℝ V - 1] : Measure V) := by
  rw [Ω.setIntegral_green_besselPotentialSpace, Ω.integral_graphMap]
  refine integral_congr_ae (ae_of_all _ fun x' => ?_)
  simp only [proj_graphMap, ← Ω.inner_normalAt_mul_gram, Complex.ofReal_mul]
  ring

end LipschitzGraph

end Rd
