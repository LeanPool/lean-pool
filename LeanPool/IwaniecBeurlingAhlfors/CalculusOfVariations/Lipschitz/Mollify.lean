/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Mollification of Lipschitz functions

For a normalised bump `ρ` and `φ : E → ℝ` (`E` finite-dimensional, `μ` an additive Haar measure),
`plancherelMollify μ ρ φ = ρ ⋆ φ`:

* it is smooth for continuous `φ`, compactly supported for compactly supported `φ`;
* for Lipschitz `φ`, `D (ρ ⋆ φ) v = ρ ⋆ ∂_v φ` (`plancherelMollify_fderiv`), bounded by the bound
  of `∂_v φ`, and vanishing away from the support;
* `∫ ∂_v φ = 0` for compactly supported Lipschitz `φ`;
* on `ℝ^m`, for the bumps `plancherelBump m n` of radii `→ 0`, `D (ρ_n ⋆ φ) v → ∂_v φ` almost
  everywhere (`plancherel_ae_tendsto`).

Moreover the mollification of a `K`-Lipschitz function is `K`-Lipschitz
(`plancherelMollify_lipschitzWith`), the mollification of a `ℤ^m`-periodic function is periodic
(`plancherelMollify_periodic`), and the componentwise mollification `mollifyPi n φ` of a
Lipschitz `ℤ^m`-periodic map `φ : ℝ^m → ℝ^d` is smooth, periodic, Lipschitz with the constant of
`φ`, vanishes outside the `2 / (n + 2)`-neighbourhood of a set outside which `φ` vanishes
(`mollifyPi_eq_zero`), and `∇ (mollifyPi n φ) → ∇φ` almost everywhere
(`ae_tendsto_grad_mollifyPi`).
-/

@[expose] public section

open MeasureTheory SchwartzMap Filter Topology ContinuousLinearMap
open scoped FourierTransform ComplexConjugate ComplexInnerProductSpace LineDeriv ContDiff Pointwise

namespace CalculusOfVariations

section Mollify

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

open scoped Convolution

/-- The mollification `ρ ⋆ φ` of `φ` by the normalised bump `ρ`. -/
noncomputable abbrev plancherelMollify (μ : Measure E) (ρ : ContDiffBump (0 : E)) (φ : E → ℝ) :
    E → ℝ :=
  ρ.normed μ ⋆[lsmul ℝ ℝ, μ] φ

theorem plancherelMollify_contDiff (ρ : ContDiffBump (0 : E)) {φ : E → ℝ} (hφ : Continuous φ) :
    ContDiff ℝ ∞ (plancherelMollify μ ρ φ) :=
  ρ.hasCompactSupport_normed.contDiff_convolution_left (n := ⊤) _ ρ.contDiff_normed
    (hφ.locallyIntegrable)

theorem plancherelMollify_hasCompactSupport (ρ : ContDiffBump (0 : E)) {φ : E → ℝ}
    (hφc : HasCompactSupport φ) : HasCompactSupport (plancherelMollify μ ρ φ) :=
  ρ.hasCompactSupport_normed.convolution _ hφc

/-- The derivative of the mollification of a Lipschitz function is the mollification of its
(almost everywhere defined) line derivative. -/
theorem plancherelMollify_fderiv (ρ : ContDiffBump (0 : E)) {φ : E → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) (x v : E) :
    fderiv ℝ (plancherelMollify μ ρ φ) x v =
      plancherelMollify μ ρ (fun y => lineDeriv ℝ φ y v) x := by
  set ρn := ρ.normed μ
  have hdiff : DifferentiableAt ℝ (plancherelMollify μ ρ φ) x :=
    ((plancherelMollify_contDiff ρ hφ.continuous).differentiable (by simp)) x
  have lim1 := (hdiff.hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero_right
  have hgi : Integrable (fun z => ρn (x - z)) μ :=
    (ρ.continuous_normed.integrable_of_hasCompactSupport ρ.hasCompactSupport_normed).comp_sub_left x
  have lim2 := hφ.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul hgi v
  have heq : ∀ t : ℝ, t⁻¹ • (plancherelMollify μ ρ φ (x + t • v) - plancherelMollify μ ρ φ x) =
      ∫ z, (t⁻¹ • (φ (z + t • v) - φ z)) * ρn (x - z) ∂μ := by
    intro t
    have hcs : HasCompactSupport (fun z => ρn (x - z)) :=
      ρ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)
    have hcont : Continuous (fun z => ρn (x - z)) :=
      ρ.continuous_normed.comp (continuous_const.sub continuous_id)
    have i1 : Integrable (fun z => ρn (x - z) * φ (z + t • v)) μ :=
      (hcont.mul (hφ.continuous.comp
          (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
        hcs.mul_right
    have i2 : Integrable (fun z => ρn (x - z) * φ z) μ :=
      (hcont.mul hφ.continuous).integrable_of_hasCompactSupport hcs.mul_right
    have e1 : plancherelMollify μ ρ φ (x + t • v) = ∫ z, ρn (x - z) * φ (z + t • v) ∂μ := by
      rw [plancherelMollify, convolution_lsmul_swap,
        ← integral_add_right_eq_self _ (t • v)]
      congr 1
      ext z
      simp only [smul_eq_mul]
      congr 2
      abel
    have e2 : plancherelMollify μ ρ φ x = ∫ z, ρn (x - z) * φ z ∂μ := by
      rw [plancherelMollify, convolution_lsmul_swap]
      rfl
    rw [e1, e2, ← integral_sub i1 i2, ← integral_smul]
    congr 1
    ext z
    simp only [smul_eq_mul]
    ring
  simp only [heq] at lim1
  have := tendsto_nhds_unique lim1 lim2
  rw [this, plancherelMollify, convolution_lsmul_swap]
  congr 1
  ext z
  simp only [smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem plancherel_lineDeriv_eq_zero_of_notMem {φ : E → ℝ} {y : E} (h : y ∉ tsupport φ)
    (v : E) : lineDeriv ℝ φ y v = 0 := by
  have := ((HasFDerivAt.of_notMem_tsupport ℝ h).hasLineDerivAt v).lineDeriv
  simpa using this

theorem plancherelMollify_abs_le (ρ : ContDiffBump (0 : E)) {g : E → ℝ} {C : ℝ}
    (hg : ∀ y, |g y| ≤ C) (x : E) : |plancherelMollify μ ρ g x| ≤ C := by
  rw [plancherelMollify, convolution_lsmul]
  have hi : Integrable (fun t => ρ.normed μ t * C) μ :=
    (ρ.continuous_normed.integrable_of_hasCompactSupport ρ.hasCompactSupport_normed).mul_const C
  have := norm_integral_le_of_norm_le hi (μ := μ) (f := fun t => ρ.normed μ t • g (x - t))
    (Filter.Eventually.of_forall fun t => by
      rw [norm_smul, Real.norm_of_nonneg (ρ.nonneg_normed t), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hg _) (ρ.nonneg_normed t))
  rw [integral_mul_const, ρ.integral_normed, one_mul] at this
  simpa [Real.norm_eq_abs] using this

theorem plancherelMollify_eq_zero (ρ : ContDiffBump (0 : E)) (hρ : ρ.rOut ≤ 1) {g : E → ℝ}
    {S : Set E} (hg : ∀ y ∉ S, g y = 0) {x : E} (hx : x ∉ Metric.closedBall (0 : E) 1 + S) :
    plancherelMollify μ ρ g x = 0 := by
  rw [plancherelMollify, convolution_lsmul]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)).trans (integral_zero _ _)
  by_cases ht : t ∈ Metric.ball (0 : E) ρ.rOut
  · have : x - t ∉ S := by
      intro h
      apply hx
      refine ⟨t, ?_, x - t, h, add_sub_cancel t x⟩
      exact Metric.closedBall_subset_closedBall hρ (Metric.ball_subset_closedBall ht)
    simp [hg _ this]
  · have : ρ.normed μ t = 0 := by
      rw [← Function.notMem_support, ρ.support_normed_eq]
      exact ht
    simp [this]

/-- The mollification vanishes outside the `rOut`-neighbourhood of a set outside which the
function vanishes. -/
theorem plancherelMollify_eq_zero_of_notMem (ρ : ContDiffBump (0 : E)) {g : E → ℝ}
    {S : Set E} (hg : ∀ y ∉ S, g y = 0) {x : E}
    (hx : x ∉ Metric.closedBall (0 : E) ρ.rOut + S) : plancherelMollify μ ρ g x = 0 := by
  rw [plancherelMollify, convolution_lsmul]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)).trans (integral_zero _ _)
  by_cases ht : t ∈ Metric.ball (0 : E) ρ.rOut
  · have : x - t ∉ S := fun h => hx ⟨t, Metric.ball_subset_closedBall ht, x - t, h,
      add_sub_cancel t x⟩
    simp [hg _ this]
  · have : ρ.normed μ t = 0 := by
      rw [← Function.notMem_support, ρ.support_normed_eq]
      exact ht
    simp [this]

/-- The integral of a partial derivative of a compactly supported Lipschitz function vanishes:
the difference quotients `t⁻¹ (φ (x + t v) - φ x)` have integral `0` by translation invariance and
converge to `∂_v φ` by dominated convergence. -/
theorem plancherel_integral_fderiv_eq_zero {φ : E → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (hφc : HasCompactSupport φ) (v : E) : ∫ x, fderiv ℝ φ x v ∂μ = 0 := by
  have h := hφ.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul' (μ := μ) hφc
    (g := fun _ => (1 : ℝ)) continuous_const v
  have hz : ∀ t : ℝ, ∫ x, (t⁻¹ • (φ (x + t • v) - φ x)) * (fun _ => (1 : ℝ)) x ∂μ = 0 := by
    intro t
    have i1 : Integrable (fun x => φ (x + t • v)) μ :=
      (hφ.continuous.comp (continuous_id.add continuous_const)).integrable_of_hasCompactSupport
        (hφc.comp_homeomorph (Homeomorph.addRight (t • v)))
    have i2 : Integrable φ μ := hφ.continuous.integrable_of_hasCompactSupport hφc
    simp only [mul_one, smul_eq_mul]
    rw [integral_const_mul, integral_sub i1 i2, integral_add_right_eq_self φ (t • v), sub_self,
      mul_zero]
  have h' := Tendsto.congr hz h
  have h0 : ∫ x, lineDeriv ℝ φ x v ∂μ = 0 := by
    simpa using (tendsto_nhds_unique tendsto_const_nhds h').symm
  rw [← h0]
  refine integral_congr_ae ?_
  filter_upwards [hφ.ae_differentiableAt (μ := μ)] with x hx
  exact hx.lineDeriv_eq_fderiv.symm

end Mollify

/-- The bumps `ρ_n` with radii `1/(n+2) < 2/(n+2)`. -/
noncomputable def plancherelBump (m : ℕ) (n : ℕ) : ContDiffBump (0 : Fin m → ℝ) where
  rIn := 1 / (n + 2)
  rOut := 2 / (n + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := by gcongr; norm_num

theorem plancherelBump_rOut_le (m n : ℕ) : (plancherelBump m n).rOut ≤ 1 := by
  change 2 / ((n : ℝ) + 2) ≤ 1
  rw [div_le_one (by positivity)]
  linarith [n.cast_nonneg (α := ℝ)]

theorem plancherelBump_tendsto (m : ℕ) :
    Tendsto (fun n => (plancherelBump m n).rOut) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0)
  have : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  simpa using this.const_div_atTop 2

/-- Mollified line derivatives converge almost everywhere to the derivative. -/
theorem plancherel_ae_tendsto {m : ℕ} {φ : (Fin m → ℝ) → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) (v : Fin m → ℝ) :
    ∀ᵐ x, Tendsto (fun n => fderiv ℝ (plancherelMollify volume (plancherelBump m n) φ) x v)
      atTop (𝓝 (fderiv ℝ φ x v)) := by
  have h1 := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
    (φ := plancherelBump m) (K := 2) (plancherelBump_tendsto m)
    (Filter.Eventually.of_forall fun n => by
      change 2 / ((n : ℝ) + 2) ≤ 2 * (1 / ((n : ℝ) + 2))
      rw [mul_one_div])
    (hφ.locallyIntegrable_lineDeriv v)
  filter_upwards [h1, hφ.ae_differentiableAt] with x hx hd
  simp only [plancherelMollify_fderiv _ hφ]
  rw [← hd.lineDeriv_eq_fderiv]
  exact hx

/-! ### Lipschitz and periodic maps -/

/-- The mollification of a `K`-Lipschitz function is `K`-Lipschitz:
`|ρ ⋆ φ (x) - ρ ⋆ φ (y)| ≤ ∫ ρ (t) |φ (x - t) - φ (y - t)| dt ≤ K ‖x - y‖`. -/
theorem plancherelMollify_lipschitzWith {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] (ρ : ContDiffBump (0 : E)) {φ : E → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) : LipschitzWith K (plancherelMollify μ ρ φ) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hi : ∀ z : E, Integrable (fun t => ρ.normed μ t * φ (z - t)) μ := fun z =>
    (ρ.continuous_normed.mul (hφ.continuous.comp (continuous_const.sub continuous_id))
      ).integrable_of_hasCompactSupport ρ.hasCompactSupport_normed.mul_right
  have e : ∀ z, plancherelMollify μ ρ φ z = ∫ t, ρ.normed μ t * φ (z - t) ∂μ := fun z => by
    rw [plancherelMollify, convolution_lsmul]; rfl
  have hb : Integrable (fun t => ρ.normed μ t * (K * dist x y)) μ :=
    (ρ.continuous_normed.integrable_of_hasCompactSupport ρ.hasCompactSupport_normed).mul_const _
  rw [e, e, Real.dist_eq, ← integral_sub (hi x) (hi y), ← Real.norm_eq_abs]
  calc ‖∫ t, (ρ.normed μ t * φ (x - t) - ρ.normed μ t * φ (y - t)) ∂μ‖
      ≤ ∫ t, ρ.normed μ t * (K * dist x y) ∂μ := by
        refine norm_integral_le_of_norm_le hb (Filter.Eventually.of_forall fun t => ?_)
        rw [← mul_sub, norm_mul, Real.norm_of_nonneg (ρ.nonneg_normed t), ← dist_eq_norm]
        refine mul_le_mul_of_nonneg_left ?_ (ρ.nonneg_normed t)
        calc dist (φ (x - t)) (φ (y - t)) ≤ K * dist (x - t) (y - t) := hφ.dist_le_mul _ _
          _ = K * dist x y := by rw [dist_sub_right]
    _ = K * dist x y := by rw [integral_mul_const, ρ.integral_normed, one_mul]

/-- The mollification of a `ℤ^m`-periodic function is `ℤ^m`-periodic:
`ρ ⋆ φ (x + z) = ∫ ρ (t) φ (x - t + z) dt = ρ ⋆ φ (x)`. -/
theorem plancherelMollify_periodic {m : ℕ} (ρ : ContDiffBump (0 : Fin m → ℝ))
    {φ : (Fin m → ℝ) → ℝ}
    (hper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), φ (x + fun i => (z i : ℝ)) = φ x)
    (x : Fin m → ℝ) (z : Fin m → ℤ) :
    plancherelMollify volume ρ φ (x + fun i => (z i : ℝ)) = plancherelMollify volume ρ φ x := by
  rw [plancherelMollify, convolution_lsmul, convolution_lsmul]
  congr 1
  ext t
  rw [show x + (fun i => (z i : ℝ)) - t = (x - t) + fun i => (z i : ℝ) by abel, hper]

/-- The componentwise mollification of `φ : ℝ^m → ℝ^d` by the bump `plancherelBump m n`. -/
noncomputable def mollifyPi {d m : ℕ} (n : ℕ) (φ : (Fin m → ℝ) → Fin d → ℝ) :
    (Fin m → ℝ) → Fin d → ℝ :=
  fun x i => plancherelMollify volume (plancherelBump m n) (fun y => φ y i) x

/-- The mollifications of a map vanishing off `S` vanish outside the `2 / (n + 2)`-neighbourhood
of `S`. -/
theorem mollifyPi_eq_zero {d m : ℕ} {φ : (Fin m → ℝ) → Fin d → ℝ} {S : Set (Fin m → ℝ)}
    (hφ : ∀ y ∉ S, φ y = 0) (n : ℕ) {x : Fin m → ℝ}
    (hx : x ∉ Metric.closedBall (0 : Fin m → ℝ) (2 / ((n : ℝ) + 2)) + S) :
    mollifyPi n φ x = 0 := by
  ext i
  change plancherelMollify volume (plancherelBump m n) (fun y => φ y i) x = 0
  exact plancherelMollify_eq_zero_of_notMem (plancherelBump m n)
    (fun y hy => by rw [hφ y hy]; rfl) hx

/-- A component of a `K`-Lipschitz map (sup norm) is `K`-Lipschitz. -/
private theorem mollifyPi_component_lipschitz {d m : ℕ} {φ : (Fin m → ℝ) → Fin d → ℝ}
    {K : NNReal} (hφ : LipschitzWith K φ) (i : Fin d) : LipschitzWith K fun y => φ y i :=
  LipschitzWith.of_dist_le_mul fun x y => (dist_le_pi_dist _ _ i).trans (hφ.dist_le_mul x y)

/-- The mollifications of a continuous map are smooth. -/
theorem mollifyPi_contDiff {d m : ℕ} {φ : (Fin m → ℝ) → Fin d → ℝ} (hφ : Continuous φ) (n : ℕ) :
    ContDiff ℝ ∞ (mollifyPi n φ) :=
  contDiff_pi.2 fun i => plancherelMollify_contDiff _ ((continuous_apply i).comp hφ)

/-- The mollifications of a `ℤ^m`-periodic map are `ℤ^m`-periodic. -/
theorem mollifyPi_periodic {d m : ℕ} {φ : (Fin m → ℝ) → Fin d → ℝ}
    (hper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), φ (x + fun i => (z i : ℝ)) = φ x) (n : ℕ)
    (x : Fin m → ℝ) (z : Fin m → ℤ) :
    mollifyPi n φ (x + fun i => (z i : ℝ)) = mollifyPi n φ x := by
  funext i
  exact plancherelMollify_periodic (φ := fun y => φ y i) _ (fun y w => congrFun (hper y w) i) x z

/-- The mollifications of a `K`-Lipschitz map are `K`-Lipschitz (sup norms), so their gradients
are bounded by `K` uniformly in `n`. -/
theorem mollifyPi_lipschitzWith {d m : ℕ} {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) (n : ℕ) : LipschitzWith K (mollifyPi n φ) :=
  LipschitzWith.of_dist_le_mul fun x y => (dist_pi_le_iff (by positivity)).2 fun i =>
    (plancherelMollify_lipschitzWith _ (mollifyPi_component_lipschitz hφ i)).dist_le_mul x y

/-- For a Lipschitz map, `∇ (ρ_n ⋆ φ) = ρ_n ⋆ ∇φ → ∇φ` almost everywhere: entry by entry, by
`plancherel_ae_tendsto`. -/
theorem ae_tendsto_grad_mollifyPi {d m : ℕ} {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) :
    ∀ᵐ x, Tendsto (fun n => grad (mollifyPi n φ) x) atTop (𝓝 (grad φ x)) := by
  have h := ae_all_iff.2 fun i => ae_all_iff.2 fun k =>
    plancherel_ae_tendsto (mollifyPi_component_lipschitz hφ i) (Pi.single k (1 : ℝ))
  filter_upwards [h] with x hx
  exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun k => hx i k

end CalculusOfVariations
