/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Interpolation between `L_p` and `L_∞`

For a function bounded by `M` and `0 < p ≤ r < ∞`,

`‖f‖_r ≤ M^(1 - p/r) ‖f‖_p^(p/r)`

(`eLpNorm_le_rpow_mul_eLpNorm_rpow`), because `|f|^r ≤ M^(r-p) |f|^p` pointwise.  This is the
elementary case of log-convexity of `p ↦ ‖f‖_p`; Mathlib has Hölder's inequality but not this
form.  It reduces every Nikolskii inequality `‖a‖_r ≲ n^(D(1/p-1/r)) ‖a‖_p` to the case
`r = ∞`.  The real-valued form `toReal_eLpNorm_le_rpow_mul` is the one used in estimates.
A consequence is `MemLp.mono_exponent_of_enorm_le`: a bounded function in `L_p` lies in `L_r` for
every `r ≥ p`.  The exponent `1 - p/r` is nonnegative for `p ≤ r ≤ ∞`
(`ENNReal.one_sub_toReal_div_nonneg`); for `1 ≤ p₀ < p₁ < ∞` the ratio `θ = p₀/p₁` lies in
`(0, 1)` and `p₁ θ = p₀` (`ENNReal.toReal_div_toReal_mem_Ioo`,
`ENNReal.mul_ofReal_toReal_div_toReal`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

/-- The interpolation exponent is nonnegative: `0 ≤ 1 - p/r` for `p ≤ r ≤ ∞`, with `1/∞ = 0`. -/
theorem ENNReal.one_sub_toReal_div_nonneg {p r : ℝ≥0∞} (hpr : p ≤ r) :
    0 ≤ 1 - p.toReal / r.toReal := by
  rcases eq_or_ne r ∞ with rfl | hr
  · simp
  · exact sub_nonneg.2 (div_le_one_of_le₀ (ENNReal.toReal_mono hr hpr) ENNReal.toReal_nonneg)

/-- For `1 ≤ p₀ < p₁ < ∞` the ratio `θ = p₀/p₁` of the exponents lies in `(0, 1)`. -/
theorem ENNReal.toReal_div_toReal_mem_Ioo {p₀ p₁ : ℝ≥0∞} (hp₀ : 1 ≤ p₀) (hp₀₁ : p₀ < p₁)
    (hp₁ : p₁ ≠ ∞) : p₀.toReal / p₁.toReal ∈ Set.Ioo 0 1 := by
  have h0 : 0 < p₀.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le hp₀).ne' (hp₀₁.trans_le le_top).ne
  have h01 : p₀.toReal < p₁.toReal := ENNReal.toReal_strict_mono hp₁ hp₀₁
  exact ⟨div_pos h0 (h0.trans h01), (div_lt_one (h0.trans h01)).2 h01⟩

/-- `p₁ · (p₀/p₁) = p₀` for finite `p₀` and `0 < p₁ < ∞`: the exponent `p₁ θ` with
`θ = p₀/p₁` is `p₀`. -/
theorem ENNReal.mul_ofReal_toReal_div_toReal {p₀ p₁ : ℝ≥0∞} (hp₀ : p₀ ≠ ∞) (hp₁0 : p₁ ≠ 0)
    (hp₁ : p₁ ≠ ∞) : p₁ * ENNReal.ofReal (p₀.toReal / p₁.toReal) = p₀ := by
  have h1 : 0 < p₁.toReal := ENNReal.toReal_pos hp₁0 hp₁
  calc p₁ * ENNReal.ofReal (p₀.toReal / p₁.toReal)
      = ENNReal.ofReal p₁.toReal * ENNReal.ofReal (p₀.toReal / p₁.toReal) := by
        rw [ENNReal.ofReal_toReal hp₁]
    _ = p₀ := by
        rw [← ENNReal.ofReal_mul h1.le, mul_div_cancel₀ _ h1.ne', ENNReal.ofReal_toReal hp₀]

namespace MeasureTheory

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  {p r : ℝ≥0∞} {f : α → E}

/-- **Interpolation between `L_p` and `L_∞`**: for `‖f‖ ≤ M` a.e. and `0 < p ≤ r < ∞`,
`‖f‖_r ≤ M^(1 - p/r) ‖f‖_p^(p/r)`. -/
theorem eLpNorm_le_rpow_mul_eLpNorm_rpow (hf : AEStronglyMeasurable f μ) {M : ℝ≥0∞}
    (hM : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ M) (hp0 : p ≠ 0) (hpr : p ≤ r) (hr : r ≠ ∞) :
    eLpNorm f r μ ≤ M ^ (1 - p.toReal / r.toReal) * eLpNorm f p μ ^ (p.toReal / r.toReal) := by
  have hp : p ≠ ∞ := ne_top_of_le_ne_top hr hpr
  have hr0 : r ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.2 hp0) hpr).ne'
  have hpp : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hrr : 0 < r.toReal := ENNReal.toReal_pos hr0 hr
  have hpr' : p.toReal ≤ r.toReal := ENNReal.toReal_mono hr hpr
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hr0 hr hf,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hf]
  have hpt : ∀ᵐ x ∂μ, ‖f x‖ₑ ^ r.toReal ≤ M ^ (r.toReal - p.toReal) * ‖f x‖ₑ ^ p.toReal := by
    filter_upwards [hM] with x hx
    rw [← sub_add_cancel r.toReal p.toReal,
      ENNReal.rpow_add_of_nonneg _ _ (by linarith) hpp.le, sub_add_cancel]
    gcongr
  calc (∫⁻ x, ‖f x‖ₑ ^ r.toReal ∂μ) ^ (1 / r.toReal)
      ≤ (∫⁻ x, M ^ (r.toReal - p.toReal) * ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / r.toReal) := by
        gcongr ?_ ^ _
        exact lintegral_mono_ae hpt
    _ = (M ^ (r.toReal - p.toReal) * ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / r.toReal) := by
        rw [lintegral_const_mul'' _ (hf.eNorm.pow_const _)]
    _ = M ^ (1 - p.toReal / r.toReal) *
          ((∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)) ^ (p.toReal / r.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        congr 2 <;> field_simp

/-- **Bounded functions in `L_p` lie in `L_r` for every `r ≥ p`**: if `f ∈ L_p` with `p > 0` and
`‖f‖ ≤ M < ∞` almost everywhere, then `f ∈ L_r` for every `p ≤ r ≤ ∞`, by
`MeasureTheory.eLpNorm_le_rpow_mul_eLpNorm_rpow` for `r < ∞` and the essential supremum for
`r = ∞`. -/
theorem MemLp.mono_exponent_of_enorm_le (hf : MemLp f p μ) {M : ℝ≥0∞}
    (hM : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ M) (hMtop : M ≠ ∞) (hp0 : p ≠ 0) (hpr : p ≤ r) : MemLp f r μ := by
  refine memLp_iff.2 ?_
  rcases eq_or_ne r ∞ with rfl | hr
  · rw [eLpNorm_exponent_top hf.aestronglyMeasurable]
    exact (eLpNormEssSup_le_of_ae_eNorm_bound hM).trans_lt hMtop.lt_top
  · refine (eLpNorm_le_rpow_mul_eLpNorm_rpow hf.aestronglyMeasurable hM hp0 hpr hr).trans_lt
      (ENNReal.mul_lt_top ?_ ?_)
    · exact ENNReal.rpow_lt_top_of_nonneg (ENNReal.one_sub_toReal_div_nonneg hpr) hMtop
    · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hf.eLpNorm_ne_top

/-- The interpolation inequality in real numbers, for a bounded function on a finite measure
space: `‖f‖_r ≤ M^(1 - p/r) ‖f‖_p^(p/r)` for `0 < p ≤ r < ∞`. -/
theorem toReal_eLpNorm_le_rpow_mul [IsFiniteMeasure μ] (hf : AEStronglyMeasurable f μ) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂μ, ‖f x‖ ≤ M) (hp0 : p ≠ 0) (hpr : p ≤ r) (hr : r ≠ ∞) :
    (eLpNorm f r μ).toReal ≤
      M ^ (1 - p.toReal / r.toReal) * (eLpNorm f p μ).toReal ^ (p.toReal / r.toReal) := by
  have hM' : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ENNReal.ofReal M := by
    filter_upwards [hM] with x hx
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hx
  have hp : p ≠ ∞ := ne_top_of_le_ne_top hr hpr
  have hfp : eLpNorm f p μ ≠ ∞ :=
    ((memLp_const (p := p) (μ := μ) M).mono' hf hM).eLpNorm_ne_top
  have hexp : 0 ≤ 1 - p.toReal / r.toReal := ENNReal.one_sub_toReal_div_nonneg hpr
  have h := eLpNorm_le_rpow_mul_eLpNorm_rpow hf hM' hp0 hpr hr
  calc (eLpNorm f r μ).toReal
      ≤ (ENNReal.ofReal M ^ (1 - p.toReal / r.toReal) *
          eLpNorm f p μ ^ (p.toReal / r.toReal)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hexp
          ENNReal.ofReal_ne_top) (ENNReal.rpow_ne_top_of_nonneg (by positivity) hfp)) h
    _ = M ^ (1 - p.toReal / r.toReal) * (eLpNorm f p μ).toReal ^ (p.toReal / r.toReal) := by
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
          ENNReal.toReal_ofReal hM0]

end MeasureTheory
