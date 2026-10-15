/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.MeasureTheory.Integral.Average

/-!
# Finite-measure average estimates

Shared analytic support for bounded measurable limits and local representatives.
Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
-/

@[expose] public section

namespace Algsuperdiff.Probability

open MeasureTheory

noncomputable section

/-- An almost-everywhere bound about a constant also bounds the finite-measure average. -/
theorem abs_average_sub_const_le_of_ae {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] (hmu : mu ≠ 0) {f : Omega → ℝ} (hf : Integrable f mu)
    {c C : ℝ} (hC : ∀ᵐ y ∂mu, |f y - c| ≤ C) :
    |(⨍ y, f y ∂mu) - c| ≤ C := by
  have : NeZero mu := ⟨hmu⟩
  have huniv : mu Set.univ ≠ 0 := by
    simpa [Measure.measure_univ_eq_zero] using hmu
  have hpos : 0 < mu.real Set.univ := by
    rw [Measure.real]
    exact ENNReal.toReal_pos huniv (measure_ne_top mu Set.univ)
  have hconst : (⨍ _y : Omega, c ∂mu) = c := average_const mu c
  have hsub : (⨍ y, f y ∂mu) - c = ⨍ y, (f y - c) ∂mu := by
    conv_lhs => rw [← hconst]
    rw [average_eq, average_eq, average_eq, ← smul_sub,
      ← integral_sub hf (integrable_const c)]
  have hbd : ‖∫ y, (f y - c) ∂mu‖ ≤ C * mu.real Set.univ := by
    refine norm_integral_le_of_norm_le_const ?_
    filter_upwards [hC] with y hy
    simpa using hy
  rw [hsub, average_eq, smul_eq_mul, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr hpos.le)]
  calc
    (mu.real Set.univ)⁻¹ * |∫ y, (f y - c) ∂mu|
        ≤ (mu.real Set.univ)⁻¹ * (C * mu.real Set.univ) :=
          mul_le_mul_of_nonneg_left hbd (inv_nonneg.mpr hpos.le)
    _ = C := by rw [mul_left_comm, inv_mul_cancel₀ hpos.ne', mul_one]

end

end Algsuperdiff.Probability
