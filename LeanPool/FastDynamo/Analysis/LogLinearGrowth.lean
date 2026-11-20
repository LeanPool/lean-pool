/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Logarithms of linear functions grow slower than the time

Two real-analysis facts behind the vanishing ideal growth rate `γ_id(u) = 0` of `thm:main`
and of `cor:ideal-growth` (`eq:zero-ideal-growth` and the last sentence of its statement; the
squeeze is the last step of its proof):

* `tendsto_inv_mul_log_linear_atTop` — `t⁻¹ log (C (1 + t)) → 0` as `t → ∞` for every `C > 0`.
  It is `Real.log =o[atTop] id` read at `C (1 + t)`.
* `tendsto_inv_mul_log_of_two_sided` — the squeeze: a positive quantity trapped between
  `1 / (C (1 + t))` and `C (1 + t)` for large `t` has vanishing exponential growth rate.

Neither mentions the torus, a flow or an operator.  They are consumed by
`FastDynamo/Dynamics/ParticleFlow.lean` (`tendsto_inv_mul_log_opNorm_of_two_sided_bounds`), by
`FastDynamo/Dynamics/Flow/LipschitzRate.lean` (`tendsto_abs_inv_mul_log_of_two_sided`, the
cocompact form) and by `FastDynamo/Dynamics/Ideal/IdealGroup.lean`
(`tendsto_inv_mul_log_norm_idealGroup`).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-- The elementary limit behind `γ_id(u) = 0`: a logarithm of a linear function grows slower
than the time, `t⁻¹ log (C(1 + t)) → 0`.  It is `Real.log =o[atTop] id` read at `C(1 + t)`.
Consumed by `tendsto_inv_mul_log_of_two_sided` below, by
`tendsto_inv_mul_log_opNorm_of_two_sided_bounds`
(`FastDynamo/Dynamics/ParticleFlow.lean`) and by `tendsto_abs_inv_mul_log_of_two_sided`
(`FastDynamo/Dynamics/Flow/LipschitzRate.lean`). -/
theorem tendsto_inv_mul_log_linear_atTop {C : ℝ} (hC : 0 < C) :
    Filter.Tendsto (fun t : ℝ ↦ t⁻¹ * Real.log (C * (1 + t))) Filter.atTop (nhds (0 : ℝ)) := by
  have hlin : Filter.Tendsto (fun t : ℝ ↦ C * (1 + t)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hC
      (Filter.tendsto_atTop_add_const_left Filter.atTop 1 Filter.tendsto_id)
  have h1 : Filter.Tendsto (fun t : ℝ ↦ Real.log (C * (1 + t)) / (C * (1 + t)))
      Filter.atTop (nhds (0 : ℝ)) := by
    have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlin
    simpa [Function.comp_def] using h
  have h2 : Filter.Tendsto (fun t : ℝ ↦ C * (1 + t) / t) Filter.atTop (nhds C) := by
    have hcong : (fun t : ℝ ↦ C * (t⁻¹ + 1)) =ᶠ[Filter.atTop] fun t : ℝ ↦ C * (1 + t) / t := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
      field_simp
    refine Filter.Tendsto.congr' hcong ?_
    have hsum : Filter.Tendsto (fun t : ℝ ↦ t⁻¹ + 1) Filter.atTop (nhds (0 + 1)) :=
      tendsto_inv_atTop_zero.add tendsto_const_nhds
    simpa using hsum.const_mul C
  have h3 := h1.mul h2
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  have hne : C * (1 + t) ≠ 0 := by positivity
  field_simp

/-- **The squeeze at the end of the proof of `cor:ideal-growth`**, isolated from the dynamics:
a positive quantity trapped between `1 / (C(1 + t))` and `C(1 + t)` for large `t` has vanishing
exponential growth rate.

Only the values at positive times are constrained, which is all that
the two-sided per-datum bounds of `cor:ideal-growth` give once the absolute
value `|t|` is resolved. -/
theorem tendsto_inv_mul_log_of_two_sided {f : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hlow : ∀ t : ℝ, 0 < t → 1 / (C * (1 + t)) ≤ f t)
    (hup : ∀ t : ℝ, 0 < t → f t ≤ C * (1 + t)) :
    Filter.Tendsto (fun t : ℝ ↦ t⁻¹ * Real.log (f t)) Filter.atTop (nhds (0 : ℝ)) := by
  refine squeeze_zero_norm' ?_ (tendsto_inv_mul_log_linear_atTop hC)
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  have hden : (0 : ℝ) < C * (1 + t) := by positivity
  have hl := hlow t ht
  have hu := hup t ht
  have hpos : (0 : ℝ) < f t := lt_of_lt_of_le (by positivity) hl
  have hlog1 : Real.log (f t) ≤ Real.log (C * (1 + t)) := Real.log_le_log hpos hu
  have hlog2 : -Real.log (C * (1 + t)) ≤ Real.log (f t) := by
    have h := Real.log_le_log (by positivity) hl
    rwa [Real.log_div one_ne_zero hden.ne', Real.log_one, zero_sub] at h
  calc ‖t⁻¹ * Real.log (f t)‖ = t⁻¹ * |Real.log (f t)| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 ht.le)]
    _ ≤ t⁻¹ * Real.log (C * (1 + t)) :=
        mul_le_mul_of_nonneg_left (abs_le.2 ⟨hlog2, hlog1⟩) (inv_nonneg.2 ht.le)

end

end FastDynamo
