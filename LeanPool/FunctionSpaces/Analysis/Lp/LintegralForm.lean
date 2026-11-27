/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# `L_p` norms through integrals of powers

For `0 < p < ∞` the `L_p` norm of `g` is `(∫ ‖g‖^p)^(1/p)`.  The function-space files use it in
three forms: as the identity `‖g‖_p^p = ∫ ‖g‖^p` (`MeasureTheory.eLpNorm_rpow_eq`, with the case
`p = 2` in `MeasureTheory.lintegral_enorm_sq_eq_eLpNorm_sq` and the case of `[0, ∞]`-valued `g` in
`MeasureTheory.eLpNorm_rpow_eq_lintegral`), as the bound `‖g‖_p ≤ B` whenever
`∫ ‖g‖^p ≤ B^p` (`MeasureTheory.eLpNorm_le_of_lintegral_le`), and as the comparison
`‖F‖_{L_p(ν)} ≤ C^(1/p) ‖G‖_{L_p(μ)}` whenever `∫ ‖F‖^p dν ≤ C ∫ ‖G‖^p dμ`
(`MeasureTheory.eLpNorm_le_rpow_mul_of_lintegral_enorm_le`, for `[0, ∞]`-valued functions
`MeasureTheory.eLpNorm_le_rpow_mul_of_lintegral_le`).  Mathlib states the identity as
`eLpNorm_nnreal_pow_eq_lintegral`, for an exponent in `[0, ∞)`; the lemmas here take the exponent
in `[0, ∞]` with `p ≠ 0`, `p ≠ ∞`, the form in which exponents appear in the function-space files,
and are short consequences of Mathlib's lemma.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace MeasureTheory

/-- `L_p` norms through `L_p` integrals: `‖g‖_p^p = ∫ ‖g‖^p` for `0 < p < ∞` and every
almost everywhere strongly measurable `g` with values in a space with an extended norm, such as
`ℂ` or `[0, ∞]`. This is Mathlib's `eLpNorm_nnreal_pow_eq_lintegral`, with the exponent given in
`[0, ∞]` instead of `[0, ∞)`. -/
theorem eLpNorm_rpow_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {ε : Type*}
    [TopologicalSpace ε] [ContinuousENorm ε] {g : α → ε} (hg : AEStronglyMeasurable g μ)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    eLpNorm g p μ ^ p.toReal = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ := by
  lift p to ℝ≥0 using hp
  exact eLpNorm_nnreal_pow_eq_lintegral (by exact_mod_cast hp0) hg

/-- `‖g‖_p^p = ∫ g^p` for `0 < p < ∞` and `g : α → [0, ∞]` measurable: the case `[0, ∞]` of
`MeasureTheory.eLpNorm_rpow_eq`, with `‖g(x)‖ₑ = g(x)`. -/
theorem eLpNorm_rpow_eq_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) :
    eLpNorm g p μ ^ p.toReal = ∫⁻ x, g x ^ p.toReal ∂μ := by
  simpa only [eNorm_eq_self] using eLpNorm_rpow_eq hg.aestronglyMeasurable hp0 hp

/-- **The `L_p` norm through the integral of the `p`-th power, as an inequality**: for
`0 < p < ∞`, every `B ∈ [0, ∞]` and every almost everywhere strongly measurable `g` with values
in a space with an extended norm, `∫ ‖g‖^p ≤ B^p` gives `‖g‖_p ≤ B`. This is
`MeasureTheory.eLpNorm_rpow_eq` combined with the monotonicity of `t ↦ t^p`. -/
theorem eLpNorm_le_of_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {ε : Type*}
    [TopologicalSpace ε] [ContinuousENorm ε] {g : α → ε}
    (hg : AEStronglyMeasurable g μ) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {B : ℝ≥0∞}
    (h : ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ ≤ B ^ p.toReal) : eLpNorm g p μ ≤ B := by
  rw [← ENNReal.rpow_le_rpow_iff (ENNReal.toReal_pos hp0 hp), eLpNorm_rpow_eq hg hp0 hp]
  exact h

/-- `L_2` norms through integrals of squares: `∫ ‖g‖² = ‖g‖_2²` for every almost everywhere
strongly measurable `g` with values in a space with an extended norm. This is Mathlib's
`eLpNorm_nnreal_pow_eq_lintegral` for `p = 2`, with natural-number powers in place of real
powers. -/
theorem lintegral_enorm_sq_eq_eLpNorm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε] {g : α → ε}
    (hg : AEStronglyMeasurable g μ) : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = eLpNorm g 2 μ ^ 2 := by
  simpa using (eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hg).symm

/-- **From integrals of powers to `L_p` norms, for two measure spaces**: if
`∫ ‖F‖^p dν ≤ C ∫ ‖G‖^p dμ` for `0 < p < ∞` and almost everywhere strongly measurable `F`, `G`,
then `‖F‖_{L_p(ν)} ≤ C^(1/p) ‖G‖_{L_p(μ)}`: take `p`-th roots in `MeasureTheory.eLpNorm_rpow_eq`. -/
theorem eLpNorm_le_rpow_mul_of_lintegral_enorm_le {α α' : Type*} [MeasurableSpace α]
    [MeasurableSpace α'] {μ : Measure α} {ν : Measure α'} {ε ε' : Type*} [TopologicalSpace ε]
    [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε'] {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) {F : α' → ε} {G : α → ε'} (hF : AEStronglyMeasurable F ν)
    (hG : AEStronglyMeasurable G μ) {C : ℝ≥0∞}
    (h : ∫⁻ x, ‖F x‖ₑ ^ p.toReal ∂ν ≤ C * ∫⁻ x, ‖G x‖ₑ ^ p.toReal ∂μ) :
    eLpNorm F p ν ≤ C ^ (1 / p.toReal) * eLpNorm G p μ := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [← ENNReal.rpow_le_rpow_iff hr, ENNReal.mul_rpow_of_nonneg _ _ hr.le, one_div,
    ENNReal.rpow_inv_rpow hr.ne', eLpNorm_rpow_eq hF hp0 hp, eLpNorm_rpow_eq hG hp0 hp]
  exact h

/-- **From integrals of powers to `L_p` norms**: if `∫ F^p ≤ C ∫ G^p` for `0 < p < ∞` and
almost everywhere measurable `F, G : α → [0, ∞]`, then `‖F‖_p ≤ C^(1/p) ‖G‖_p`: the case
`[0, ∞]` of `MeasureTheory.eLpNorm_le_rpow_mul_of_lintegral_enorm_le`, with `‖F(x)‖ₑ = F(x)`. -/
theorem eLpNorm_le_rpow_mul_of_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {F G : α → ℝ≥0∞} (hF : AEMeasurable F μ)
    (hG : AEMeasurable G μ) {C : ℝ≥0∞}
    (h : ∫⁻ x, F x ^ p.toReal ∂μ ≤ C * ∫⁻ x, G x ^ p.toReal ∂μ) :
    eLpNorm F p μ ≤ C ^ (1 / p.toReal) * eLpNorm G p μ :=
  eLpNorm_le_rpow_mul_of_lintegral_enorm_le hp0 hp hF.aestronglyMeasurable
    hG.aestronglyMeasurable (by simpa only [eNorm_eq_self] using h)

end MeasureTheory
