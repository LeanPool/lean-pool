/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Gaussian.StandardNormal
public import LeanPool.MathFin.Probability.Gaussian.GaussianCDFDeriv

/-!
# Partial moments of the standard normal

The integrals of the standard normal density `ϕ` over a right tail `(a, ∞)` that the closed forms
of the library are built from:

* `integrable_id_mul_gaussianPDFReal_volume`: `z ↦ z·ϕ(z)` is integrable.
* `integral_id_mul_gaussianPDFReal_Ioi`: the truncated first moment `∫_(a,∞) z·ϕ(z) dz = ϕ(a)`,
  by the fundamental theorem of calculus, since `(−ϕ)' = z·ϕ`.
* `integral_gaussianPDFReal_Ioi`: the tail mass `∫_(a,∞) ϕ = 1 − Φ(a)`.
* `integral_max_sub_mul_gaussianPDFReal`: the stop-loss transform
  `E[(Z − z)⁺] = ϕ(z) − z·(1 − Φ(z))` for `Z ~ N(0,1)`.

The Bachelier call (`Models/Bachelier/Bachelier`), the Rockafellar–Uryasev characterisation of
Gaussian CVaR (`Risk/RockafellarUryasev`) and the normal tail bounds
(`Probability/Gaussian/NormalTail`) are all read off these four facts.

## Main results

* `integrable_id_mul_gaussianPDFReal_volume`: `z ↦ z·ϕ(z)` is integrable.
* `integral_id_mul_gaussianPDFReal_Ioi`: `∫_(a,∞) z·ϕ(z) dz = ϕ(a)`.
* `integral_gaussianPDFReal_Ioi`: `∫_(a,∞) ϕ = 1 − Φ(a)`.
* `integral_max_sub_mul_gaussianPDFReal`: `∫ max (x − z) 0 · ϕ(x) dx = ϕ(z) − z·(1 − Φ(z))`,
  the stop-loss transform of `N(0, 1)`.

## Tags

truncated normal moment, stop-loss transform, normal tail, Bachelier model, Gaussian CVaR,
expected shortfall, MSC 60E05, MSC 91G70, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter
open scoped NNReal ENNReal Topology

/-! ### Integrability of `z ↦ z · ϕ(0, 1, z)` -/

/-- The function `z ↦ z · ϕ(0, 1, z)` is integrable on `ℝ` (against Lebesgue).
Derived by transferring `Integrable id (gaussianReal 0 1)` (the existence of the
first moment of `N(0, 1)`) through the withDensity identification of
`gaussianReal`. -/
lemma integrable_id_mul_gaussianPDFReal_volume :
    Integrable (fun z : ℝ ↦ z * gaussianPDFReal 0 1 z) volume := by
  have h_id_integrable : Integrable (id : ℝ → ℝ) (gaussianReal (0 : ℝ) 1) := by
    have h_memLp : MemLp (id : ℝ → ℝ) 2 (gaussianReal (0 : ℝ) 1) := memLp_id_gaussianReal 2
    exact (h_memLp.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrable le_rfl
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) (one_ne_zero : (1 : ℝ≥0) ≠ 0)] at h_id_integrable
  have h_pdf_meas : Measurable (gaussianPDF (0 : ℝ) 1) := by
    unfold gaussianPDF; fun_prop
  have h_pdf_lt_top : ∀ᵐ z ∂(volume : Measure ℝ), gaussianPDF (0 : ℝ) 1 z < ∞ := by
    refine ae_of_all _ (fun z ↦ ?_)
    unfold gaussianPDF; exact ENNReal.ofReal_lt_top
  rw [integrable_withDensity_iff_integrable_smul' h_pdf_meas h_pdf_lt_top] at h_id_integrable
  have h_eq : (fun z : ℝ ↦ (gaussianPDF (0 : ℝ) 1 z).toReal • id z)
            = (fun z : ℝ ↦ z * gaussianPDFReal 0 1 z) := by
    funext z
    change (gaussianPDF (0 : ℝ) 1 z).toReal • z = z * gaussianPDFReal 0 1 z
    unfold gaussianPDF
    rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
    simp [smul_eq_mul, mul_comm]
  rwa [h_eq] at h_id_integrable

/-! ### Truncated first moment of the standard normal -/

/-- **Truncated mean** of `N(0, 1)` on `(a, ∞)`:
`∫ z in Ioi a, z · ϕ(z) dz = ϕ(a)`.

Proved via FTC for improper integrals (`integral_Ioi_of_hasDerivAt_of_tendsto`)
using the antiderivative `z ↦ -ϕ(z)` of `z ↦ z · ϕ(z)`, and the fact that
`ϕ(z) → 0` as `z → ∞`. -/
lemma integral_id_mul_gaussianPDFReal_Ioi (a : ℝ) :
    ∫ z in Set.Ioi a, z * gaussianPDFReal 0 1 z = gaussianPDFReal 0 1 a := by
  -- Antiderivative of z · ϕ(0,1,z) is -ϕ(0,1,z)
  have h_deriv : ∀ x ∈ Set.Ioi a,
      HasDerivAt (fun z' ↦ -gaussianPDFReal 0 1 z') (x * gaussianPDFReal 0 1 x) x := by
    intro x _; exact hasDerivAt_neg_gaussianPDFReal_zero_one x
  have h_cont : ContinuousWithinAt (fun z' : ℝ ↦ -gaussianPDFReal 0 1 z') (Set.Ici a) a := by
    have : Continuous fun z' : ℝ ↦ -gaussianPDFReal 0 1 z' := by
      unfold gaussianPDFReal; fun_prop
    exact this.continuousWithinAt
  have h_int : IntegrableOn (fun z' : ℝ ↦ z' * gaussianPDFReal 0 1 z') (Set.Ioi a) volume := by
    have h_full : Integrable (fun z' : ℝ ↦ z' * gaussianPDFReal 0 1 z') volume :=
      integrable_id_mul_gaussianPDFReal_volume
    exact h_full.integrableOn
  have h_lim : Tendsto (fun z' : ℝ ↦ -gaussianPDFReal 0 1 z') atTop (𝓝 0) := by
    rw [show (0 : ℝ) = -0 from neg_zero.symm]
    refine Tendsto.neg ?_
    -- gaussianPDFReal 0 1 z = (sqrt(2π))⁻¹ · exp(-z²/2). Both factors handled separately.
    have h_atBot : Tendsto (fun z : ℝ ↦ -(z - 0)^2/2) atTop atBot := by
      have h_sub : Tendsto (fun z : ℝ ↦ (z - 0)^2) atTop atTop := by simp
      have h_neg : Tendsto (fun z : ℝ ↦ -((z - 0)^2)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp h_sub
      have h_div := h_neg.atBot_div_const (by norm_num : (0 : ℝ) < 2)
      simpa using h_div
    have h_exp : Tendsto (fun z : ℝ ↦ Real.exp (-(z - 0)^2/2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h_atBot
    have h_mul := h_exp.const_mul ((Real.sqrt (2 * π))⁻¹ : ℝ)
    rw [mul_zero] at h_mul
    convert h_mul using 1
    funext z; unfold gaussianPDFReal; simp [NNReal.coe_one]
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto h_cont h_deriv h_int h_lim
  -- hres : ∫ z in Ioi a, z * pdf z = 0 - (-pdf a) = pdf a
  linarith [hres]

/-! ### Tail mass and the stop-loss transform -/

/-- **Gaussian tail mass in pdf form**: `∫_{Ioi a} ϕ(x) dx = 1 − Φ(a)`. -/
lemma integral_gaussianPDFReal_Ioi (a : ℝ) :
    ∫ x in Set.Ioi a, gaussianPDFReal 0 1 x = 1 - Phi a := by
  have h_meas : (gaussianReal (0 : ℝ) 1 (Set.Ioi a)).toReal
      = ∫ x in Set.Ioi a, gaussianPDFReal 0 1 x := by
    rw [gaussianReal_apply_eq_integral _ one_ne_zero]
    exact ENNReal.toReal_ofReal <| setIntegral_nonneg measurableSet_Ioi
      (fun _ _ ↦ gaussianPDFReal_nonneg _ _ _)
  rw [← h_meas, gaussianReal_Ioi_toReal, Phi_neg]

/-- **Standard-normal expected shortfall**: `E[(Z − z)⁺] = ϕ(z) − z·(1 − Φ(z))`.
The positive part localizes the integral to the tail `Ioi z`, where it splits
into the truncated first moment (`= ϕ(z)`) minus `z` times the tail mass. -/
lemma integral_max_sub_mul_gaussianPDFReal (z : ℝ) :
    ∫ x, max (x - z) 0 * gaussianPDFReal 0 1 x
      = gaussianPDFReal 0 1 z - z * (1 - Phi z) := by
  have h_eq : (fun x ↦ max (x - z) 0 * gaussianPDFReal 0 1 x)
      = Set.indicator (Set.Ioi z) (fun x ↦ (x - z) * gaussianPDFReal 0 1 x) := by
    funext x
    by_cases hx : x ∈ Set.Ioi z
    · rw [Set.indicator_of_mem hx, max_eq_left (sub_nonneg.2 (Set.mem_Ioi.1 hx).le)]
    · have hxz : x ≤ z := not_lt.1 (fun h ↦ hx (Set.mem_Ioi.2 h))
      rw [Set.indicator_of_notMem hx, max_eq_right (sub_nonpos.2 hxz), zero_mul]
  rw [h_eq, integral_indicator measurableSet_Ioi]
  have h_int_x : IntegrableOn (fun x ↦ x * gaussianPDFReal 0 1 x) (Set.Ioi z) volume :=
    integrable_id_mul_gaussianPDFReal_volume.integrableOn
  have h_int_pdf : IntegrableOn (fun x ↦ z * gaussianPDFReal 0 1 x) (Set.Ioi z) volume :=
    ((integrable_gaussianPDFReal 0 1).const_mul z).integrableOn
  calc ∫ x in Set.Ioi z, (x - z) * gaussianPDFReal 0 1 x
      = ∫ x in Set.Ioi z,
          (x * gaussianPDFReal 0 1 x - z * gaussianPDFReal 0 1 x) := by
        congr 1; funext x; ring
    _ = (∫ x in Set.Ioi z, x * gaussianPDFReal 0 1 x)
          - ∫ x in Set.Ioi z, z * gaussianPDFReal 0 1 x :=
        integral_sub h_int_x h_int_pdf
    _ = gaussianPDFReal 0 1 z - z * (1 - Phi z) := by
        rw [integral_id_mul_gaussianPDFReal_Ioi, integral_const_mul,
          integral_gaussianPDFReal_Ioi]

end MathFin
