/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Probability.Distributions.Cauchy

/-!
# The Student-t law

The standard (unit-scale) Student-t law with `ν > 0` degrees of freedom is the law on `ℝ` with
density proportional to the kernel `(1 + x²/ν)^(-(ν+1)/2)`.

Mathlib has no Student-t law at this pin. This file builds it as `volume.withDensity` of the
normalized kernel, `studentTPDFReal ν x = k_ν(x) / C_ν` with `C_ν = ∫ k_ν`
(`studentTNormConst`), so that it integrates to one by construction. The kernel is integrable for
every `ν > 0` by Mathlib's Japanese-bracket bound `integrable_rpow_neg_one_add_norm_sq`. The
constant is then computed, `C_ν = √(νπ) Γ(ν/2) / Γ((ν+1)/2)`, by writing the kernel as a Gamma
mixture of Gaussian kernels and exchanging the integrals, so the density is the textbook one.

## Main definitions

* `studentTKernel`: the unnormalised kernel `k_ν(x) = (1 + x²/ν)^(-(ν+1)/2)`.
* `studentTNormConst`: the normalising constant `C_ν = ∫ k_ν` (equal to
  `√(νπ) Γ(ν/2) / Γ((ν+1)/2)` for `ν > 0`, by `studentTNormConst_eq`).
* `studentTPDFReal`, `studentTPDF`: the density `k_ν / C_ν`, real- and `ℝ≥0∞`-valued.
* `studentTMeasure`: the standard Student-t law, `volume.withDensity (studentTPDF ν)`; a
  probability measure for `ν > 0`.

## Main results

* `isProbabilityMeasure_studentTMeasure`: the Student-t law is a probability measure for `ν > 0`.
* `studentTNormConst_eq`, `studentTPDFReal_eq`: the normalizing constant and the density in
  closed form, `g_ν(x) = Γ((ν+1)/2) / (√(νπ) Γ(ν/2)) · (1 + x²/ν)^(-(ν+1)/2)`.
* `studentTMeasure_one`: at `ν = 1` it is Mathlib's standard Cauchy law `cauchyMeasure 0 1`.
* `integrable_mul_studentTPDFReal`: the law has a finite mean for `ν > 1`.
* `setIntegral_Ioi_mul_studentTPDFReal`: the tail first moment
  `∫_q^∞ t g_ν(t) dt = g_ν(q) (ν + q²)/(ν − 1)` for `ν > 1`, the integral behind the
  McNeil–Frey–Embrechts expected-shortfall closed form.

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts]

## Tags

Student-t distribution, heavy tails, Cauchy distribution, expected shortfall, degrees of freedom,
Gamma mixture, MSC 60E05, MSC 91G70
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal Topology

variable {ν : ℝ}

/-! ### The kernel and its normalizing constant -/

/-- The unnormalized Student-t kernel `k_ν(x) = (1 + x²/ν)^(-(ν+1)/2)`. -/
noncomputable def studentTKernel (ν x : ℝ) : ℝ := (1 + x ^ 2 / ν) ^ (-(ν + 1) / 2)

lemma studentTKernel_pos (hν : 0 < ν) (x : ℝ) : 0 < studentTKernel ν x :=
  rpow_pos_of_pos (by positivity : 0 < 1 + x ^ 2 / ν) _

lemma continuous_studentTKernel (hν : 0 < ν) : Continuous (studentTKernel ν) :=
  (by fun_prop : Continuous fun x : ℝ ↦ 1 + x ^ 2 / ν).rpow_const
    fun x ↦ Or.inl (by positivity : 0 < 1 + x ^ 2 / ν).ne'

/-- The kernel is integrable for every `ν > 0`: it is the Japanese bracket `(1 + ‖y‖²)^(-r/2)`
with `r = ν + 1 > 1 = dim ℝ`, at `y = x/√ν`. -/
lemma integrable_studentTKernel (hν : 0 < ν) : Integrable (studentTKernel ν) :=
  ((integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := ν + 1)
    (by simp; linarith)).comp_div (sqrt_pos.2 hν).ne').congr <| ae_of_all _ fun x ↦ by
      simp only [studentTKernel, norm_eq_abs, sq_abs, div_pow, sq_sqrt hν.le]

/-- The normalizing constant `C_ν = ∫ k_ν`; positive for `ν > 0`
(`studentTNormConst_pos`). For `ν ≤ 0` the value is junk. -/
noncomputable def studentTNormConst (ν : ℝ) : ℝ := ∫ x, studentTKernel ν x

lemma studentTNormConst_pos (hν : 0 < ν) : 0 < studentTNormConst ν :=
  (integral_pos_iff_support_of_nonneg (fun x ↦ (studentTKernel_pos hν x).le)
    (integrable_studentTKernel hν)).2 <| by
      rw [Function.support_eq_univ fun x ↦ (studentTKernel_pos hν x).ne']
      simp

/-! ### The normalizing constant in closed form -/

/-- The Gamma-mixture integrand: `k_ν(x) = Γ(s)⁻¹ ∫_0^∞ u^(s−1) e^(−(1 + x²/ν) u) du` with
`s = (ν+1)/2`. -/
private lemma studentTKernel_eq_integral (hν : 0 < ν) (x : ℝ) :
    studentTKernel ν x = (Gamma ((ν + 1) / 2))⁻¹ *
      ∫ u in Ioi 0, u ^ ((ν + 1) / 2 - 1) * exp (-((1 + x ^ 2 / ν) * u)) := by
  have hb : 0 < 1 + x ^ 2 / ν := by positivity
  rw [integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hb, studentTKernel, one_div,
    inv_rpow hb.le, ← rpow_neg hb.le, neg_div]
  field_simp

/-- The inner Gaussian integral: integrating the mixture integrand over `x` gives
`u^(s−1) e^(−u) √(π/(u/ν))`. -/
lemma integral_rpow_mul_exp_neg_mul_one_add_sq_div (hν : 0 < ν) (u : ℝ) :
    ∫ x, u ^ ((ν + 1) / 2 - 1) * exp (-((1 + x ^ 2 / ν) * u)) =
      u ^ ((ν + 1) / 2 - 1) * exp (-u) * √(π / (u / ν)) := by
  rw [← integral_gaussian (u / ν), ← integral_const_mul]
  congr 1 with x
  rw [mul_assoc, ← exp_add]
  congr 2
  field_simp
  ring

/-- The outer integrand, rearranged: for `u > 0`,
`u^(s−1) e^(−u) √(π/(u/ν)) = √(νπ) · e^(−u) u^(ν/2−1)`, the Gamma integrand at `ν/2`. -/
lemma rpow_mul_exp_mul_sqrt_pi_div_eq {u : ℝ} (hu : 0 < u) :
    u ^ ((ν + 1) / 2 - 1) * exp (-u) * √(π / (u / ν)) =
      √(ν * π) * (exp (-u) * u ^ (ν / 2 - 1)) := by
  have hsq : √(π / (u / ν)) = √(ν * π) * u ^ (-(1 / 2) : ℝ) := by
    rw [rpow_neg hu.le, ← sqrt_eq_rpow, div_div_eq_mul_div, mul_comm π, sqrt_div' _ hu.le,
      div_eq_mul_inv]
  rw [hsq, show ν / 2 - 1 = ((ν + 1) / 2 - 1) + -(1 / 2) by ring, rpow_add hu]
  ring

/-- **The Student-t normalizing constant**: `C_ν = √(νπ) Γ(ν/2) / Γ((ν+1)/2)`
(equivalently `√ν · B(1/2, ν/2)`). Proved by writing the kernel as a Gamma mixture of Gaussian
kernels and exchanging the two integrals (Fubini, integrability via `integrable_prod_iff'`). -/
theorem studentTNormConst_eq (hν : 0 < ν) :
    studentTNormConst ν = √(ν * π) * Gamma (ν / 2) / Gamma ((ν + 1) / 2) := by
  set f : ℝ → ℝ → ℝ := fun x u ↦ u ^ ((ν + 1) / 2 - 1) * exp (-((1 + x ^ 2 / ν) * u))
  have hmeas : AEStronglyMeasurable (Function.uncurry f)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (by fun_prop : Measurable (Function.uncurry f)).aestronglyMeasurable
  have hint : Integrable (Function.uncurry f) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine (integrable_prod_iff' hmeas).2 ⟨?_, ?_⟩
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u (hu : 0 < u) ↦ ?_)
      refine ((integrable_exp_neg_mul_sq (div_pos hu hν)).const_mul
        (u ^ ((ν + 1) / 2 - 1) * exp (-u))).congr (ae_of_all _ fun x ↦ ?_)
      simp only [f, Function.uncurry_apply_pair, mul_assoc, ← exp_add]
      congr 2
      field_simp
      ring
    · refine ((GammaIntegral_convergent (half_pos hν)).const_mul √(ν * π)).congr
        ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u (hu : 0 < u) ↦ ?_))
      simp only [Function.uncurry_apply_pair, f]
      rw [← rpow_mul_exp_mul_sqrt_pi_div_eq hu, ← integral_rpow_mul_exp_neg_mul_one_add_sq_div hν u]
      exact integral_congr_ae (ae_of_all _ fun x ↦ (norm_of_nonneg (by positivity)).symm)
  calc studentTNormConst ν
      = (Gamma ((ν + 1) / 2))⁻¹ * ∫ x, ∫ u in Ioi 0, f x u := by
        rw [studentTNormConst, ← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ (studentTKernel_eq_integral hν))
    _ = (Gamma ((ν + 1) / 2))⁻¹ * ∫ u in Ioi 0, ∫ x, f x u := by
        rw [integral_integral_swap hint]
    _ = (Gamma ((ν + 1) / 2))⁻¹ * ∫ u in Ioi 0, √(ν * π) * (exp (-u) * u ^ (ν / 2 - 1)) := by
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) ↦ ?_
        rw [integral_rpow_mul_exp_neg_mul_one_add_sq_div hν u, rpow_mul_exp_mul_sqrt_pi_div_eq hu]
    _ = √(ν * π) * Gamma (ν / 2) / Gamma ((ν + 1) / 2) := by
        rw [integral_const_mul, ← Gamma_eq_integral (half_pos hν)]
        field_simp

/-! ### The density and the law -/

/-- The standard Student-t density `g_ν(x) = k_ν(x) / C_ν`; a probability density for `ν > 0`
(`integral_studentTPDFReal`). For `ν ≤ 0` the value is junk. -/
noncomputable def studentTPDFReal (ν x : ℝ) : ℝ := studentTKernel ν x / studentTNormConst ν

/-- The Student-t density as an `ℝ≥0∞`-valued function. -/
noncomputable def studentTPDF (ν x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (studentTPDFReal ν x)

lemma studentTPDFReal_pos (hν : 0 < ν) (x : ℝ) : 0 < studentTPDFReal ν x :=
  div_pos (studentTKernel_pos hν x) (studentTNormConst_pos hν)

/-- **The textbook Student-t density**:
`g_ν(x) = Γ((ν+1)/2) / (√(νπ) Γ(ν/2)) · (1 + x²/ν)^(-(ν+1)/2)`. -/
theorem studentTPDFReal_eq (hν : 0 < ν) (x : ℝ) :
    studentTPDFReal ν x = Gamma ((ν + 1) / 2) / (√(ν * π) * Gamma (ν / 2)) *
      (1 + x ^ 2 / ν) ^ (-(ν + 1) / 2) := by
  rw [studentTPDFReal, studentTNormConst_eq hν, studentTKernel, div_div_eq_mul_div, mul_comm]
  ring

lemma integrable_studentTPDFReal (hν : 0 < ν) : Integrable (studentTPDFReal ν) :=
  (integrable_studentTKernel hν).div_const _

lemma integral_studentTPDFReal (hν : 0 < ν) : ∫ x, studentTPDFReal ν x = 1 := by
  simp only [studentTPDFReal, integral_div]
  exact div_self (studentTNormConst_pos hν).ne'

lemma lintegral_studentTPDF (hν : 0 < ν) : ∫⁻ x, studentTPDF ν x = 1 := by
  simp only [studentTPDF]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_studentTPDFReal hν)
    (ae_of_all _ fun x ↦ (studentTPDFReal_pos hν x).le), integral_studentTPDFReal hν,
    ENNReal.ofReal_one]

/-- The standard **Student-t law** with `ν` degrees of freedom; a probability measure for `ν > 0`
(`isProbabilityMeasure_studentTMeasure`). For `ν ≤ 0` the value is junk. -/
noncomputable def studentTMeasure (ν : ℝ) : Measure ℝ := volume.withDensity (studentTPDF ν)

lemma isProbabilityMeasure_studentTMeasure (hν : 0 < ν) :
    IsProbabilityMeasure (studentTMeasure ν) :=
  ⟨by rw [studentTMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_studentTPDF hν]⟩

@[fun_prop]
lemma measurable_studentTPDFReal (ν : ℝ) : Measurable (studentTPDFReal ν) := by
  unfold studentTPDFReal studentTKernel
  fun_prop

@[fun_prop]
lemma measurable_studentTPDF (ν : ℝ) : Measurable (studentTPDF ν) :=
  (measurable_studentTPDFReal ν).ennreal_ofReal

/-- The Student-t law has a density, so it charges no single point. -/
instance nullSingletonClass_studentTMeasure (ν : ℝ) : NullSingletonClass (studentTMeasure ν) :=
  inferInstanceAs (NullSingletonClass (volume.withDensity _))

/-! ### The Cauchy anchor -/

lemma studentTKernel_one (x : ℝ) : studentTKernel 1 x = (1 + x ^ 2)⁻¹ := by
  rw [studentTKernel, div_one, show (-(1 + 1) / 2 : ℝ) = -1 by norm_num, rpow_neg_one]

lemma studentTNormConst_one : studentTNormConst 1 = π := by
  simp only [studentTNormConst, studentTKernel_one, integral_univ_inv_one_add_sq]

/-- **At one degree of freedom the Student-t law is the standard Cauchy law**, Mathlib's
`cauchyMeasure 0 1`. -/
theorem studentTMeasure_one : studentTMeasure 1 = cauchyMeasure 0 1 := by
  rw [cauchyMeasure_of_scale_ne_zero 0 one_ne_zero, studentTMeasure]
  congr 1 with x
  simp only [studentTPDF, cauchyPDF, studentTPDFReal, cauchyPDFReal, studentTKernel_one,
    studentTNormConst_one, sub_zero, NNReal.coe_one, one_pow]
  congr 1
  ring

/-! ### The first moment -/

/-- For `ν > 1` the law has a finite mean: `|x| g_ν(x) ≤ (√ν / C_ν) (1 + x²/ν)^(-ν/2)`, a
Japanese bracket with `r = ν > 1`. -/
lemma integrable_mul_studentTPDFReal (hν : 1 < ν) :
    Integrable fun x ↦ x * studentTPDFReal ν x := by
  have hν0 : 0 < ν := by linarith
  have hC := studentTNormConst_pos hν0
  have h := ((integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := ν)
    (by simpa using hν)).comp_div (sqrt_pos.2 hν0).ne').const_mul (√ν / studentTNormConst ν)
  refine h.mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
  have hb : 0 < 1 + x ^ 2 / ν := by positivity
  have h1 : |x| ≤ √ν * (1 + x ^ 2 / ν) ^ (1 / 2 : ℝ) := by
    rw [← sqrt_eq_rpow, ← sqrt_mul hν0.le, ← sqrt_sq_eq_abs]
    refine sqrt_le_sqrt ?_
    rw [mul_add, mul_div_cancel₀ _ hν0.ne']
    linarith
  have h2 : (1 + x ^ 2 / ν) ^ (1 / 2 : ℝ) * studentTKernel ν x = (1 + x ^ 2 / ν) ^ (-ν / 2) := by
    rw [studentTKernel, ← rpow_add hb]
    ring_nf
  rw [norm_mul, norm_of_nonneg (studentTPDFReal_pos hν0 x).le]
  simp only [norm_eq_abs, sq_abs, div_pow, sq_sqrt hν0.le, studentTPDFReal]
  refine (mul_le_mul_of_nonneg_right h1 (div_pos (studentTKernel_pos hν0 x) hC).le).trans_eq ?_
  rw [← h2]
  ring

/-- **The tail first moment of the Student-t law**: for `ν > 1`,
`∫_q^∞ t g_ν(t) dt = g_ν(q) (ν + q²)/(ν − 1)`. The antiderivative of `t g_ν(t)` is
`−(ν/(ν−1)) C_ν⁻¹ (1 + t²/ν)^((1−ν)/2)`, which vanishes at `+∞` because `ν > 1`. -/
theorem setIntegral_Ioi_mul_studentTPDFReal (hν : 1 < ν) (q : ℝ) :
    ∫ t in Ioi q, t * studentTPDFReal ν t =
      studentTPDFReal ν q * ((ν + q ^ 2) / (ν - 1)) := by
  have hν0 : 0 < ν := by linarith
  have hν1 : ν - 1 ≠ 0 := by linarith
  have hC := (studentTNormConst_pos hν0).ne'
  set c := -(ν / (ν - 1)) / studentTNormConst ν
  have hderiv (t : ℝ) : HasDerivAt (fun t ↦ c * (1 + t ^ 2 / ν) ^ ((1 - ν) / 2))
      (t * studentTPDFReal ν t) t := by
    have hb : 0 < 1 + t ^ 2 / ν := by positivity
    have h := (((hasDerivAt_pow 2 t).div_const ν).const_add 1).rpow_const
      (p := (1 - ν) / 2) (Or.inl hb.ne') |>.const_mul c
    refine h.congr_deriv ?_
    simp only [studentTPDFReal, studentTKernel, show (1 - ν) / 2 - 1 = -(ν + 1) / 2 by ring, c]
    field_simp
    ring
  have hlim : Tendsto (fun t ↦ c * (1 + t ^ 2 / ν) ^ ((1 - ν) / 2)) atTop (𝓝 0) := by
    have hb : Tendsto (fun t : ℝ ↦ 1 + t ^ 2 / ν) atTop atTop :=
      tendsto_atTop_add_const_left _ _
        ((tendsto_pow_atTop two_ne_zero).atTop_div_const hν0)
    have := (tendsto_rpow_neg_atTop (y := (ν - 1) / 2) (by linarith)).comp hb
    simpa [show -((ν - 1) / 2) = (1 - ν) / 2 by ring] using this.const_mul c
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hderiv q).continuousAt.continuousWithinAt
    (fun t _ ↦ hderiv t) (integrable_mul_studentTPDFReal hν).integrableOn hlim]
  have hb : 0 < 1 + q ^ 2 / ν := by positivity
  rw [studentTPDFReal, studentTKernel, show (1 - ν) / 2 = -(ν + 1) / 2 + 1 by ring,
    rpow_add_one hb.ne']
  simp only [c]
  field_simp
  ring

end MathFin
