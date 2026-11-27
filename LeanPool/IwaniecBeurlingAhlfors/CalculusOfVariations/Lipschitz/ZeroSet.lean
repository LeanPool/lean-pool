/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.Gradient

/-!
# The gradient of a Lipschitz map vanishes almost everywhere on its zero set

`rd_ae_fderiv_eq_zero`: at a Lebesgue density point `x` of `{φ = 0}` where `φ` is differentiable,
a derivative `L` with `L v ≠ 0` would make `φ` nonzero on a ball of a fixed proportion of
`B (x, r)` for all small `r`. Hence `grad φ = 0` almost everywhere on `{φ = 0}`
(`rd_ae_grad_eq_zero`).
-/

@[expose] public section

open Metric Set MeasureTheory Filter Topology
open scoped Pointwise

namespace CalculusOfVariations

variable {d m : ℕ}

/-- A Lipschitz map has vanishing derivative at almost every point of its zero set: at a Lebesgue
density point `x` of the zero set where `φ` is differentiable, a derivative `L` with `L v ≠ 0`
would make `φ` nonzero on the ball `B (x + (r/2) v, ρ r/2)`, a fixed proportion of `B (x, r)`. -/
lemma rd_ae_fderiv_eq_zero {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) :
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), φ x = 0 → fderiv ℝ φ x = 0 := by
  set E := {x | φ x = 0}
  have hE : MeasurableSet E := (isClosed_eq hφ.continuous continuous_const).measurableSet
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hE,
    hφ.ae_differentiableAt] with x hden hdiff hx
  rw [Set.indicator_of_mem (show x ∈ E from hx), Pi.one_apply] at hden
  by_contra hL
  set L := fderiv ℝ φ x
  -- a direction `v`, `‖v‖ ≤ 1`, with `L v ≠ 0`
  obtain ⟨v, hv1, hc⟩ : ∃ v : Fin m → ℝ, ‖v‖ ≤ 1 ∧ 0 < ‖L v‖ := by
    by_contra h
    push Not at h
    apply hL
    ext w : 1
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · have h1 := h (‖w‖⁻¹ • w) (by rw [norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)])
      rw [map_smul, norm_smul, norm_inv, norm_norm] at h1
      have h2 : ‖L w‖ ≤ 0 := by
        have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
        have := mul_le_mul_of_nonneg_left h1 hw'.le
        rwa [← mul_assoc, mul_inv_cancel₀ hw'.ne', one_mul, mul_zero] at this
      simpa using norm_le_zero_iff.1 h2
  set c := ‖L v‖
  set ρ : ℝ := min 1 (c / (2 * (‖L‖ + 1)))
  have hρ0 : 0 < ρ := lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρL : ‖L‖ * ρ ≤ c / 2 := by
    calc ‖L‖ * ρ ≤ (‖L‖ + 1) * (c / (2 * (‖L‖ + 1))) := by
          gcongr
          · linarith [norm_nonneg L]
          · exact min_le_right _ _
      _ = c / 2 := by field_simp
  -- differentiability with `ε = c/8`
  have hlo := hdiff.hasFDerivAt.isLittleO.def (show (0 : ℝ) < c / 8 by positivity)
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.1 hlo
  -- for `0 < r < δ`, the zero set misses `B (x + (r/2) v, ρ r/2)`
  have hmiss : ∀ r, 0 < r → r < δ →
      E ∩ Metric.closedBall x r ⊆ Metric.closedBall x r \ Metric.closedBall (x + (r / 2) • v)
          (ρ * (r / 2)) := by
    intro r hr0 hrδ y ⟨hyE, hyr⟩
    refine ⟨hyr, fun hy => ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm] at hy hyr
    set z := y - (x + (r / 2) • v)
    have hyx : y - x = (r / 2) • v + z := by simp only [z]; abel
    have hnorm : ‖y - x‖ ≤ r := hyr
    have h1 := hδ (show dist y x < δ by rw [dist_eq_norm]; linarith)
    have hyE' : φ y = 0 := hyE
    rw [hyE', hx, sub_zero, zero_sub, norm_neg] at h1
    have h2 : ‖L (y - x)‖ ≥ (r / 2) * c - ‖L‖ * (ρ * (r / 2)) := by
      rw [hyx, map_add, map_smul]
      calc ‖(r / 2) • L v + L z‖ ≥ ‖(r / 2) • L v‖ - ‖L z‖ := norm_sub_le_norm_add _ _
        _ ≥ (r / 2) * c - ‖L‖ * (ρ * (r / 2)) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
          have := L.le_opNorm z
          have hz : ‖z‖ ≤ ρ * (r / 2) := hy
          nlinarith [norm_nonneg L]
    have h3 : ‖L‖ * (ρ * (r / 2)) ≤ (c / 2) * (r / 2) := by nlinarith
    have h4 : c / 8 * ‖y - x‖ ≤ c / 8 * r := by gcongr
    nlinarith
  -- the density ratio stays below `1 − (ρ/2)^m`
  set V := volume (Metric.closedBall (0 : Fin m → ℝ) 1)
  have hV0 : V ≠ 0 := (Metric.measure_closedBall_pos volume 0 one_pos).ne'
  have hVt : V ≠ ⊤ := measure_closedBall_lt_top.ne
  have hfin : Module.finrank ℝ (Fin m → ℝ) = m := by simp
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      volume (E ∩ Metric.closedBall x r) / volume (Metric.closedBall x r) ≤
        ENNReal.ofReal (1 - (ρ / 2) ^ m) := by
    filter_upwards [Ioo_mem_nhdsGT hδ0] with r hr
    have hsub : Metric.closedBall (x + (r / 2) • v) (ρ * (r / 2)) ⊆ Metric.closedBall x r := by
      intro y hy
      rw [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
      calc ‖y - x‖ = ‖(y - (x + (r / 2) • v)) + (r / 2) • v‖ := by congr 1; abel
        _ ≤ ‖y - (x + (r / 2) • v)‖ + ‖(r / 2) • v‖ := norm_add_le _ _
        _ ≤ ρ * (r / 2) + r / 2 := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hr.1])]
          nlinarith [hr.1]
        _ ≤ r := by nlinarith [hr.1]
    have hB : volume (Metric.closedBall x r) = ENNReal.ofReal (r ^ m) * V := by
      rw [Measure.addHaar_closedBall' volume x hr.1.le, hfin]
    have hb : volume (Metric.closedBall (x + (r / 2) • v) (ρ * (r / 2))) =
        ENNReal.ofReal ((ρ * (r / 2)) ^ m) * V := by
      rw [Measure.addHaar_closedBall' volume _ (by nlinarith [hr.1]), hfin]
    have hle := measure_mono (μ := volume) (hmiss r hr.1 hr.2)
    rw [measure_sdiff hsub measurableSet_closedBall.nullMeasurableSet
      (measure_closedBall_lt_top.ne), hB, hb] at hle
    have hr0 : 0 < r := hr.1
    have hpos : 0 < ENNReal.ofReal (r ^ m) * V :=
      ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by positivity)).ne' hV0
    rw [hB, ENNReal.div_le_iff hpos.ne' (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt)]
    refine hle.trans (le_of_eq ?_)
    rw [← ENNReal.sub_mul (fun _ _ => hVt), ← mul_assoc, ← ENNReal.ofReal_mul (by
      have : (ρ / 2) ^ m ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
      linarith), ← ENNReal.ofReal_sub _ (by positivity)]
    congr 2
    simp only [mul_pow, div_pow]
    ring
  have hlim := le_of_tendsto hden hbound
  rw [ENNReal.one_le_ofReal] at hlim
  have : 0 < (ρ / 2) ^ m := by positivity
  linarith


/-- The gradient of a Lipschitz map vanishes almost everywhere on its zero set. -/
lemma rd_ae_grad_eq_zero {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) :
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), φ x = 0 → grad φ x = 0 := by
  filter_upwards [rd_ae_fderiv_eq_zero hφ, hφ.ae_differentiableAt] with x hx hdiff h0
  ext i k
  have hi := (hasFDerivAt_pi'.1 hdiff.hasFDerivAt i).fderiv
  simp only [grad, Matrix.of_apply, Matrix.zero_apply]
  rw [hi, hx h0]
  simp

end CalculusOfVariations
