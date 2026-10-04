/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormPow
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.L1Space.Integrable


/-!
# Derivative of the `L^q` functional along a line

For `u` and `v` in `L^q(μ)` with `q > 1`, the map `t ↦ ∫ |u + tv|^q` is differentiable at `0`,
with derivative `q ∫ |u|^{q-2} u v`. This is the constraint derivative of the direct method: the
subcritical minimiser of `EllipticPdes.Embedding.exists_minimiser_of_lt` lives on the unit sphere
of `L^q`, and its Euler-Lagrange equation is this derivative set against the derivative of the
`H₀¹` norm.

The proof is differentiation under the integral sign.
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` asks for a dominating function on a
neighbourhood of `0`, and Hölder's inequality supplies one: the integrand's `t`-derivative is
bounded on `|t| < 1` by `q(|u| + |v|)^{q-1}|v|`, whose first factor lies in `L^{q/(q-1)}` and whose
second lies in `L^q`. Mathlib's `hasDerivAt_abs_rpow` supplies the pointwise derivative, including
at the origin, where `q > 1` makes `|·|^q` differentiable with derivative zero.

## Main declarations

* `EllipticPdes.Analysis.integrable_abs_rpow_sub_one_mul`: the dominating function is integrable.
* `EllipticPdes.Analysis.hasDerivAt_integral_abs_rpow`: the derivative at `0`.

## References

Y. Guo, *Partial Differential Equations*, Section IX.1; L. C. Evans, *Partial Differential
Equations* (2nd ed.), §8.1.2.
-/

@[expose] public section

open MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace EllipticPdes.Analysis

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The step that turns the pointwise derivative bound into the dominating function:
`|y|^{q-2}|y| ≤ a^{q-1}` whenever `|y| ≤ a`. At `y = 0` the left side vanishes for every
exponent, so no positivity of `y` is needed. -/
private lemma rpow_sub_two_mul_abs_le {r : ℝ} (hr : 1 < r) {y a : ℝ} (hy : ‖y‖ ≤ a) (ha : 0 ≤ a) :
    ‖y‖ ^ (r - 2) * ‖y‖ ≤ a ^ (r - 1) := by
  rcases eq_or_lt_of_le (norm_nonneg y) with h | h
  · rw [← h, mul_zero]
    exact Real.rpow_nonneg ha _
  · have hsplit : ‖y‖ ^ (r - 2) * ‖y‖ ^ (1 : ℝ) = ‖y‖ ^ (r - 2 + 1) := (Real.rpow_add h _ _).symm
    rw [Real.rpow_one] at hsplit
    rw [hsplit, show r - 2 + 1 = r - 1 by ring]
    exact Real.rpow_le_rpow (norm_nonneg y) hy (by linarith)

/-- **Integrability of the dominating function.** With `u` and `v` in `L^q`, the product
`(|u| + |v|)^{q-1}|v|` is integrable: the first factor lies in `L^{q/(q-1)}` and the second in
`L^q`, whose reciprocals sum to one. -/
theorem integrable_abs_rpow_sub_one_mul {p : ℝ≥0∞} (hptop : p ≠ ∞) (hp1 : 1 < p.toReal)
    {u v : α → ℝ} (hu : MemLp u p μ) (hv : MemLp v p μ) :
    Integrable (fun x => (‖u x‖ + ‖v x‖) ^ (p.toReal - 1) * ‖v x‖) μ := by
  set r := p.toReal with hrdef
  have hr0 : (0 : ℝ) < r := by linarith
  have hw : MemLp (fun x => ‖u x‖ + ‖v x‖) p μ := hu.norm.add hv.norm
  have hwnn : ∀ x, ‖(‖u x‖ + ‖v x‖)‖ = ‖u x‖ + ‖v x‖ := fun x =>
    Real.norm_of_nonneg (by positivity)
  have hpeq : p = ENNReal.ofReal r := (ENNReal.ofReal_toReal hptop).symm
  -- The conjugate exponent the first factor sits at.
  set p' : ℝ≥0∞ := ENNReal.ofReal (r / (r - 1)) with hp'def
  have hprod : p' * ENNReal.ofReal (r - 1) = p := by
    rw [hp'def, ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ (by linarith), hpeq]
  have hmem : MemLp (fun x => (‖u x‖ + ‖v x‖) ^ (r - 1)) p' μ := by
    have hcongr : eLpNorm (fun x => (‖u x‖ + ‖v x‖) ^ (r - 1)) p' μ
        = eLpNorm (fun x => ‖(‖u x‖ + ‖v x‖)‖ ^ (r - 1)) p' μ :=
      eLpNorm_congr_ae (Eventually.of_forall (fun x => by simp only [hwnn]))
    rw [memLp_iff, hcongr, eLpNorm_norm_rpow _ hw.aestronglyMeasurable (by linarith), hprod]
    exact ENNReal.rpow_lt_top_of_nonneg (by linarith) hw.eLpNorm_ne_top
  have : ENNReal.HolderTriple p' p 1 := by
    refine ⟨?_⟩
    rw [hp'def, ← ENNReal.ofReal_inv_of_pos (by positivity), inv_div, hpeq,
      ← ENNReal.ofReal_inv_of_pos hr0, ← ENNReal.ofReal_add (by positivity) (by positivity),
      inv_one, show (r - 1) / r + r⁻¹ = 1 by
        rw [inv_eq_one_div, ← add_div, sub_add_cancel, div_self hr0.ne']]
    simp
  exact (MemLp.integrable_mul hmem hv.norm).congr (Eventually.of_forall (fun _ => rfl))

/-- **Derivative of the `L^q` functional along a line.** For `u` and `v` in `L^q(μ)` with
`q > 1`, the map `t ↦ ∫ |u + tv|^q` is differentiable at `0` with derivative
`q ∫ |u|^{q-2} u v`. -/
theorem hasDerivAt_integral_abs_rpow {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (hp1 : 1 < p.toReal) {u v : α → ℝ} (hu : MemLp u p μ) (hv : MemLp v p μ) :
    HasDerivAt (fun t : ℝ => ∫ x, |u x + t * v x| ^ p.toReal ∂μ)
      (∫ x, p.toReal * |u x| ^ (p.toReal - 2) * u x * v x ∂μ) 0 := by
  simp only [← Real.norm_eq_abs]
  set r := p.toReal with hrdef
  have hr0 : (0 : ℝ) < r := by linarith
  set F : ℝ → α → ℝ := fun t x => ‖u x + t * v x‖ ^ r with hFdef
  set F' : ℝ → α → ℝ := fun t x => r * ‖u x + t * v x‖ ^ (r - 2) * (u x + t * v x) * v x
    with hF'def
  set bound : α → ℝ := fun x => r * ((‖u x‖ + ‖v x‖) ^ (r - 1) * ‖v x‖) with hbdef
  -- The line through `u` in the direction `v` is measurable at each time.
  have hline : ∀ t : ℝ, AEStronglyMeasurable (fun x => u x + t * v x) μ := fun t =>
    hu.aestronglyMeasurable.add (aestronglyMeasurable_const.mul hv.aestronglyMeasurable)
  have hFmeas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) μ :=
    Eventually.of_forall (fun t =>
      ((hline t).norm.aemeasurable.pow_const r).aestronglyMeasurable)
  have hFint : Integrable (F 0) μ := by
    have := memLp_one_iff_integrable.mp (hu.norm_rpow hp0 hptop)
    simpa [hFdef] using this
  have hF'meas : AEStronglyMeasurable (F' 0) μ :=
    ((((hline 0).norm.aemeasurable.pow_const (r - 2)).aestronglyMeasurable.const_mul r).mul
      (hline 0)).mul hv.aestronglyMeasurable
  have hbound_int : Integrable bound μ :=
    (integrable_abs_rpow_sub_one_mul hptop hp1 hu hv).const_mul r
  -- The derivative is dominated on `|t| < 1`.
  have hbound : ∀ᵐ x ∂μ, ∀ t ∈ ball (0 : ℝ) 1, ‖F' t x‖ ≤ bound x := by
    refine Eventually.of_forall (fun x t ht => ?_)
    rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    have hy : ‖u x + t * v x‖ ≤ ‖u x‖ + ‖v x‖ := by
      refine (norm_add_le _ _).trans ?_
      have : ‖t * v x‖ ≤ ‖v x‖ := by
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) ht.le
      linarith
    have hstep := rpow_sub_two_mul_abs_le hp1 hy (by positivity)
    have hnormF' : ‖F' t x‖
        = r * (‖u x + t * v x‖ ^ (r - 2) * ‖u x + t * v x‖) * ‖v x‖ := by
      have hnn : (0 : ℝ) ≤ r * ‖u x + t * v x‖ ^ (r - 2) :=
        mul_nonneg hr0.le (Real.rpow_nonneg (norm_nonneg _) _)
      rw [hF'def]
      simp only [norm_mul, Real.norm_of_nonneg hnn]
      ring
    rw [hnormF', hbdef]
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hstep hr0.le) (norm_nonneg (v x))
    linarith [this]
  -- The pointwise derivative, by the chain rule.
  have hdiff : ∀ᵐ x ∂μ, ∀ t ∈ ball (0 : ℝ) 1, HasDerivAt (F · x) (F' t x) t := by
    refine Eventually.of_forall (fun x t _ => ?_)
    have h1 : HasDerivAt (fun t : ℝ => u x + t * v x) (v x) t := by
      simpa using ((hasDerivAt_id t).mul_const (v x)).const_add (u x)
    exact (hasDerivAt_norm_rpow (u x + t * v x) hp1).comp t h1
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (bound := bound) (ball_mem_nhds (0 : ℝ) one_pos) hFmeas hFint hF'meas hbound hbound_int hdiff
  simpa [hFdef, hF'def] using hmain.2

end EllipticPdes.Analysis
