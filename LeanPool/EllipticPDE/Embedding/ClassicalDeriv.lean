/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Embedding.Morrey


/-!
# Continuous weak gradient as a classical gradient

The Sobolev ladder puts a solution and its weak derivatives in a Hölder class, so both are
continuous. Continuity is what turns them back into classical derivatives: a function with a
continuous weak gradient on an open set is Fréchet differentiable there, with that gradient.

The argument is mollification. Each mollification is smooth, its classical partials are the
mollified weak gradient (`EllipticPdes.Embedding.partialD_convolution_eq_of_hasWeakGradOn`), and
a mollification of a continuous function converges to it uniformly on a ball whose enlargement by
the mollifier radius stays inside the region, since the function is uniformly continuous on the
enlargement. Mathlib's `hasFDerivAt_of_tendstoUniformlyOn` then passes the derivative to the
limit: derivatives converging uniformly and values converging pointwise identify the limit's
derivative.

Uniform convergence is where the hypotheses are spent. Pointwise convergence of the
mollifications alone would not do, since it says nothing about the derivatives, and the
convergence of the mollified gradient has to be uniform in the base point for the limit theorem
to see it.

## Main declarations

* `EllipticPdes.Embedding.gradCLM`: a gradient tuple read as a continuous linear functional.
* `EllipticPdes.Embedding.opNorm_le_sum_apply_single`: the operator norm of a functional on
  `EuclideanSpace ℝ (Fin d)`, bounded by its values on the coordinate directions.
* `EllipticPdes.Embedding.tendstoUniformlyOn_indicator_convolution`: mollifications of a
  continuous function converge uniformly on an interior ball.
* `EllipticPdes.Embedding.hasFDerivAt_of_continuousOn_hasWeakGradOn`: the classical derivative.
-/

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped NNReal ENNReal Convolution Topology

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-! ### Gradient tuple as a functional -/

/-- The continuous linear functional whose coordinate values are the entries of `g` at `y`. This
is the shape `HasFDerivAt` asks for, assembled from the shape a weak gradient comes in. -/
def gradCLM (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  ∑ k, g k y • (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)

@[simp]
theorem gradCLM_apply_single (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (y : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    gradCLM g y (EuclideanSpace.single j (1 : ℝ)) = g j y := by
  simp [gradCLM]

/-- **Control of a functional by its coordinate values.** On `EuclideanSpace ℝ (Fin d)` every
vector is the sum of its coordinates against the standard directions, so the operator norm is at
most the sum of the absolute values of the coordinate readings. -/
theorem opNorm_le_sum_apply_single (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ k, ‖L (EuclideanSpace.single k (1 : ℝ))‖ := by
  refine ContinuousLinearMap.opNorm_le_bound L (by positivity) fun x => ?_
  have hx : x = ∑ k, x k • EuclideanSpace.single k (1 : ℝ) := by
    conv_lhs => rw [← (PiLp.basisFun 2 ℝ (Fin d)).sum_repr x]
    simp only [PiLp.basisFun_repr, PiLp.basisFun_apply, EuclideanSpace.single]
  calc ‖L x‖ = ‖∑ k, x k • L (EuclideanSpace.single k (1 : ℝ))‖ := by
        conv_lhs => rw [hx]
        rw [map_sum]; simp_rw [map_smul]
    _ ≤ ∑ k, ‖x k • L (EuclideanSpace.single k (1 : ℝ))‖ := norm_sum_le _ _
    _ = ∑ k, ‖x k‖ * ‖L (EuclideanSpace.single k (1 : ℝ))‖ := by simp_rw [norm_smul]
    _ ≤ ∑ k, ‖x‖ * ‖L (EuclideanSpace.single k (1 : ℝ))‖ :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x k) (norm_nonneg _)
    _ = (∑ k, ‖L (EuclideanSpace.single k (1 : ℝ))‖) * ‖x‖ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-! ### Uniform convergence of the mollifications -/

/-- **Mollifications of a continuous function converge uniformly on an interior ball.** The
enlargement `Metric.closedBall x (ρ + σ)` is compact and sits inside the region, so the function
is uniformly continuous there. Once the mollifier radius drops below the modulus of continuity,
the mollification at every point of `Metric.ball x ρ` averages values within `ε/2` of the value
at that point, and the estimate is uniform because the modulus is.

The extension by zero is what the convolution reads, and it is invisible: every point the
mollifier sees at radius at most `σ` lies in the enlargement, hence in the region. -/
theorem tendstoUniformlyOn_indicator_convolution
    {B : Set (EuclideanSpace ℝ (Fin d))} (hBm : MeasurableSet B)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hint : IntegrableOn h B volume)
    (hcont : ContinuousOn h B) {x : EuclideanSpace ℝ (Fin d)} {ρ σ : ℝ}
    (hsub : Metric.closedBall x (ρ + σ) ⊆ B)
    (φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d))) (hφσ : ∀ n, (φ n).rOut ≤ σ)
    (hφ0 : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    TendstoUniformlyOn
      (fun n y => (B.indicator h ⋆[ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ), volume]
        ((φ n).normed volume)) y) h atTop (Metric.ball x ρ) := by
  classical
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ) with hL_def
  have hLflip : L.flip = L := by
    refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
    simp only [hL_def, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
      smul_eq_mul]
    exact mul_comm b a
  have hKc : IsCompact (Metric.closedBall x (ρ + σ)) := isCompact_closedBall _ _
  have huc : UniformContinuousOn h (Metric.closedBall x (ρ + σ)) :=
    hKc.uniformContinuousOn_of_continuous (hcont.mono hsub)
  have hmeas : AEStronglyMeasurable (B.indicator h) volume :=
    (hint.integrable_indicator hBm).aestronglyMeasurable
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (by positivity)
  filter_upwards [hφ0.eventually (gt_mem_nhds hδ0)] with n hn y hy
  have hyK : y ∈ Metric.closedBall x (ρ + σ) := by
    have hσ0 : 0 ≤ σ := le_trans (φ 0).rOut_pos.le (hφσ 0)
    exact Metric.closedBall_subset_closedBall (by linarith)
      (Metric.ball_subset_closedBall hy)
  have hyB : y ∈ B := hsub hyK
  -- Every point the mollifier reads lies in the enlargement, so the indicator is invisible.
  have hnear : ∀ z ∈ Metric.ball y (φ n).rOut,
      dist (B.indicator h z) (B.indicator h y) ≤ ε / 2 := by
    intro z hz
    have hzK : z ∈ Metric.closedBall x (ρ + σ) := by
      have h1 : dist z y < (φ n).rOut := Metric.mem_ball.mp hz
      have h2 : dist y x < ρ := Metric.mem_ball.mp hy
      have h3 : dist z x ≤ dist z y + dist y x := dist_triangle z y x
      have h4 := hφσ n
      exact Metric.mem_closedBall.mpr (by linarith)
    have hzB : z ∈ B := hsub hzK
    rw [Set.indicator_of_mem hzB, Set.indicator_of_mem hyB]
    have hzy : dist z y < δ := lt_trans (Metric.mem_ball.mp hz) hn
    exact (hδ z hzK y hyK hzy).le
  have hkey := (φ n).dist_normed_convolution_le (μ := volume) hmeas hnear
  rw [Set.indicator_of_mem hyB] at hkey
  have hcomm : (B.indicator h ⋆[L, volume] ((φ n).normed volume)) y
      = (((φ n).normed volume) ⋆[L, volume] B.indicator h) y := by
    conv_lhs => rw [← hLflip, convolution_flip]
  rw [dist_comm]
  calc dist ((B.indicator h ⋆[L, volume] ((φ n).normed volume)) y) (h y)
      = dist ((((φ n).normed volume) ⋆[L, volume] B.indicator h) y) (h y) := by rw [hcomm]
    _ ≤ ε / 2 := hkey
    _ < ε := by linarith

/-! ### Classical derivative -/

/-- **Continuous weak gradient as a classical derivative.** On an open region, a function that
is continuous and integrable, with a weak gradient that is continuous and integrable, is Fréchet
differentiable at every point, with derivative the functional the gradient names.

The proof mollifies on a ball whose double closure sits inside the region. Each mollification is
smooth, its partials are the mollified gradient components, and both converge uniformly on the
ball. `hasFDerivAt_of_tendstoUniformlyOn` collects that into the derivative of the limit, and the
limit is the function itself, since a mollification of a continuous function converges to it. -/
theorem hasFDerivAt_of_continuousOn_hasWeakGradOn
    {B : Set (EuclideanSpace ℝ (Fin d))} (hBm : MeasurableSet B) (hBo : IsOpen B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hui : IntegrableOn u B volume) (hgi : ∀ k, IntegrableOn (g k) B volume)
    (huc : ContinuousOn u B) (hgc : ∀ k, ContinuousOn (g k) B)
    (hw : HasWeakGradOn B u g) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ B) :
    HasFDerivAt u (gradCLM g x) x := by
  classical
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ) with hL_def
  obtain ⟨R, hR, hRB⟩ := Metric.isOpen_iff.1 hBo x hx
  set ρ : ℝ := R / 4 with hρ_def
  have hρ0 : 0 < ρ := by rw [hρ_def]; linarith
  have hencl : Metric.closedBall x (ρ + ρ) ⊆ B := by
    refine subset_trans (Metric.closedBall_subset_ball ?_) hRB
    rw [hρ_def]; linarith
  -- The shrinking mollifier family.
  have hn2 : ∀ n : ℕ, (0 : ℝ) < (n + 2 : ℝ) := fun n => by positivity
  set φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := fun n =>
    { rIn := ρ / (n + 2 : ℝ) / 2
      rOut := ρ / (n + 2 : ℝ)
      rIn_pos := div_pos (div_pos hρ0 (hn2 n)) two_pos
      rIn_lt_rOut := half_lt_self (div_pos hρ0 (hn2 n)) } with hφ_def
  have hrOut : ∀ n, (φ n).rOut = ρ / (n + 2 : ℝ) := fun _ => rfl
  have hφρ : ∀ n, (φ n).rOut ≤ ρ := by
    intro n
    rw [hrOut n, div_le_iff₀ (hn2 n)]
    nlinarith [hρ0, Nat.cast_nonneg (α := ℝ) n]
  have hφ0 : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    simp only [hrOut]
    exact tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  -- The mollifications, and their smoothness.
  have huB_li : LocallyIntegrable (B.indicator u) volume :=
    (hui.integrable_indicator hBm).locallyIntegrable
  set U : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n => B.indicator u ⋆[L, volume] ((φ n).normed volume) with hU_def
  have hUsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (U n) := fun n =>
    (φ n).hasCompactSupport_normed.contDiff_convolution_right (L := L) huB_li
      (φ n).contDiff_normed
  -- The partials of a mollification are the mollified gradient components.
  have hpartial : ∀ (n : ℕ) (k : Fin d), ∀ y ∈ Metric.ball x ρ,
      partialD k (U n) y
        = (B.indicator (g k) ⋆[L, volume] ((φ n).normed volume)) y := by
    intro n k y hy
    refine partialD_convolution_eq_of_hasWeakGradOn hBm hui hw (φ n) k ?_
    refine subset_trans (Metric.closedBall_subset_closedBall' ?_) hencl
    have h1 : dist y x < ρ := Metric.mem_ball.mp hy
    have h2 := hφρ n
    linarith
  -- Uniform convergence of the values and of the partials.
  have hvals : TendstoUniformlyOn (fun n y => U n y) u atTop (Metric.ball x ρ) :=
    tendstoUniformlyOn_indicator_convolution hBm hui huc hencl φ hφρ hφ0
  have hgrads : ∀ k, TendstoUniformlyOn
      (fun n y => (B.indicator (g k) ⋆[L, volume] ((φ n).normed volume)) y)
      (g k) atTop (Metric.ball x ρ) := fun k =>
    tendstoUniformlyOn_indicator_convolution hBm (hgi k) (hgc k) hencl φ hφρ hφ0
  -- The derivatives converge uniformly, coordinate by coordinate.
  have hfd : TendstoUniformlyOn (fun n y => fderiv ℝ (U n) y) (gradCLM g) atTop
      (Metric.ball x ρ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hεd : (0 : ℝ) < ε / (d + 1) := by positivity
    have hstep : ∀ k : Fin d, ∀ᶠ n in atTop, ∀ y ∈ Metric.ball x ρ,
        dist (g k y) ((B.indicator (g k) ⋆[L, volume] ((φ n).normed volume)) y)
          < ε / (d + 1) :=
      fun k => (Metric.tendstoUniformlyOn_iff.mp (hgrads k)) _ hεd
    filter_upwards [Filter.eventually_all.2 hstep] with n hn y hy
    have hcoord : ∀ k : Fin d,
        ‖(gradCLM g y - fderiv ℝ (U n) y) (EuclideanSpace.single k (1 : ℝ))‖
          ≤ ε / (d + 1) := by
      intro k
      rw [_root_.sub_apply, gradCLM_apply_single]
      have hrw : (fderiv ℝ (U n) y) (EuclideanSpace.single k (1 : ℝ)) = partialD k (U n) y := rfl
      rw [hrw, hpartial n k y hy, ← dist_eq_norm]
      exact (hn k y hy).le
    have hsum : ∑ _k : Fin d, ε / (d + 1) < ε := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_div_assoc'] at *
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [hε]
    rw [dist_eq_norm]
    exact lt_of_le_of_lt
      ((opNorm_le_sum_apply_single _).trans (Finset.sum_le_sum fun k _ => hcoord k)) hsum
  refine hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hfd (fun n y hy => ?_)
    (fun y hy => hvals.tendsto_at hy) (Metric.mem_ball_self hρ0)
  exact ((hUsmooth n).differentiable (by simp) y).hasFDerivAt

end EllipticPdes.Embedding
