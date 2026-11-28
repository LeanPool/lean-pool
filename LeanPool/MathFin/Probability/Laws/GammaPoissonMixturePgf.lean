/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Jumps.PoissonPgf
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Moments.Basic

/-!
# CreditRisk+ sector probability-generating function (Poisson–Gamma mixture)

CreditRisk+ (Credit Suisse First Boston, 1997) models each sector's systematic
risk factor as a random intensity `Λ ∼ Gamma(a, r)` (shape `a`, Mathlib's
*rate* parametrisation `r = 1/β` for the technical document's scale `β`).
Conditional on `Λ = λ`, the sector default count `N` is Poisson(`λ`), with
conditional pgf `E[z^N | Λ = λ] = exp(λ(z−1))`
(`PoissonPgf.integral_pow_poissonMeasure`, `Probability/Jumps/PoissonPgf.lean`).

**The mixture, as an iterated integral.** The unconditional sector pgf is the
tower property `G_N(z) = E_Λ[E[z^N | Λ]]`. Here it is stated as the iterated
integral

  `∫ λ, (∫ n, z ^ n ∂Poisson(λ)) ∂Gamma(a, r) = (r / (r − (z − 1))) ^ a`,

whose inner integral is the Poisson pgf and whose outer integral is the Gamma
moment-generating function at `z − 1`. The mixed law of `N` itself (a
`Measure.bind` of the Poisson kernel against the Gamma law) and a pair of random
variables `(N, Λ)` with this conditional structure are not constructed.

The loss-banding approximation that turns the exact per-sector pgf into
CreditRisk+'s practical recursion is **out of scope** here, as is the portfolio
pgf across independent sectors.

## Main results

* `integral_exp_mul_gammaMeasure`, `mgf_id_gammaMeasure`: the Gamma(`a`, `r`)
  moment-generating function, `∫ λ, exp(s·λ) ∂Gamma(a,r) = (r / (r − s)) ^ a`
  for `s < r` (Mathlib has the Gamma law but no Gamma MGF).
* `integral_integral_pow_poissonMeasure_gammaMeasure`: the Poisson–Gamma
  mixture sector pgf, as the iterated integral above, for `z < r + 1`.
* `integral_integral_pow_poissonMeasure_gammaMeasure_eq_negBinomial`: the same
  pgf in the technical document's `p = β / (1 + β)` scale parametrisation,
  `((1 − p) / (1 − p·z)) ^ a`.
* `poissonMeasure_real_compl_singleton_zero`: `PD_i = 1 − e^{−λ_i}`, i.e.
  `P(N_i ≠ 0) = 1 − e^{−λ_i}` for `N_i ∼ Poisson(λ_i)`.

## References

* [N. L. Johnson, S. Kotz and N. Balakrishnan, *Continuous Univariate Distributions,
  Vol.~1*][JohnsonKotzBalakrishnan1994], ch. 17

## Tags

CreditRisk+, Poisson–Gamma mixture, negative binomial, probability generating function,
default count, sector risk factor, MSC 91G40, MSC 60E10, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

namespace GammaPoissonMixturePgf

/-- **Gamma moment-generating function.** For `Λ ∼ Gamma(a, r)` (shape `a`,
rate `r`) and `s < r`, `E[exp(s·Λ)] = (r / (r − s)) ^ a`. Proved the same way
Mathlib normalises the Gamma pdf (`lintegral_gammaPDF_eq_one`): factor the
pdf's `exp(−r·λ)` against `exp(s·λ)` into `exp(−(r−s)·λ)` and apply the Gamma
integral `integral_rpow_mul_exp_neg_mul_Ioi` at rate `r − s`. -/
theorem integral_exp_mul_gammaMeasure {a r s : ℝ} (ha : 0 < a) (hr : 0 < r) (hs : s < r) :
    ∫ lam, rexp (s * lam) ∂(gammaMeasure a r) = (r / (r - s)) ^ a := by
  have hrs : 0 < r - s := by linarith
  have hmeasg : Measurable (fun lam : ℝ ↦ ENNReal.ofReal (rexp (s * lam))) :=
    ((measurable_id'.const_mul s).exp).ennreal_ofReal
  have hmeasf : Measurable (gammaPDF a r) :=
    (measurable_gammaPDFReal a r).ennreal_ofReal
  have hmeasF : Measurable
      (fun lam : ℝ ↦ r ^ a / Gamma a * lam ^ (a - 1) * exp (-((r - s) * lam))) :=
    ((measurable_id'.pow_const (a - 1)).const_mul _).mul
      (measurable_id'.const_mul (r - s)).neg.exp
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun lam ↦ (Real.exp_pos _).le)
      ((measurable_id'.const_mul s).exp.aestronglyMeasurable)]
  have hL : ∫⁻ lam, ENNReal.ofReal (rexp (s * lam)) ∂(gammaMeasure a r)
      = ∫⁻ lam in Ici (0 : ℝ), ENNReal.ofReal
          (r ^ a / Gamma a * lam ^ (a - 1) * exp (-((r - s) * lam))) := by
    rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hmeasf hmeasg,
      ← lintegral_add_compl _ (measurableSet_Ici (a := (0 : ℝ))), compl_Ici]
    have hleft : ∫⁻ lam in Iio (0 : ℝ),
        (gammaPDF a r * fun lam ↦ ENNReal.ofReal (rexp (s * lam))) lam = 0 := by
      rw [setLIntegral_congr_fun (g := fun _ ↦ (0 : ℝ≥0∞)) measurableSet_Iio]
      · simp
      · intro lam (hlam : lam < 0)
        simp [Pi.mul_apply, gammaPDF_of_neg hlam]
    have hright : ∫⁻ lam in Ici (0 : ℝ),
        (gammaPDF a r * fun lam ↦ ENNReal.ofReal (rexp (s * lam))) lam
        = ∫⁻ lam in Ici (0 : ℝ), ENNReal.ofReal
            (r ^ a / Gamma a * lam ^ (a - 1) * exp (-((r - s) * lam))) := by
      refine setLIntegral_congr_fun measurableSet_Ici (fun lam (hlam : 0 ≤ lam) ↦ ?_)
      simp only [Pi.mul_apply, gammaPDF_of_nonneg hlam]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show -((r - s) * lam) = -(r * lam) + s * lam by ring, Real.exp_add]
      ring
    rw [hright, hleft, add_zero]
  rw [hL, ← integral_eq_lintegral_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ici).mpr
        (ae_of_all _ fun lam (hlam : 0 ≤ lam) ↦ by positivity))
      hmeasF.aestronglyMeasurable]
  have hF : (fun lam : ℝ ↦ r ^ a / Gamma a * lam ^ (a - 1) * exp (-((r - s) * lam)))
      = fun lam : ℝ ↦ (r ^ a / Gamma a) * (lam ^ (a - 1) * exp (-((r - s) * lam))) := by
    funext lam; ring
  rw [hF, MeasureTheory.integral_const_mul, integral_Ici_eq_integral_Ioi,
    integral_rpow_mul_exp_neg_mul_Ioi ha hrs]
  have hGpos : (0 : ℝ) < Gamma a := Gamma_pos_of_pos ha
  rw [mul_comm ((1 / (r - s)) ^ a) (Gamma a), ← mul_assoc, div_mul_cancel₀ _ hGpos.ne',
    ← Real.mul_rpow hr.le (by positivity), mul_one_div]

/-- The Gamma moment-generating function in Mathlib's `mgf` form, the sibling of
`mgf_id_gaussianReal`: `mgf id (gammaMeasure a r) s = (r / (r − s)) ^ a` for `s < r`. -/
theorem mgf_id_gammaMeasure {a r s : ℝ} (ha : 0 < a) (hr : 0 < r) (hs : s < r) :
    mgf id (gammaMeasure a r) s = (r / (r - s)) ^ a :=
  integral_exp_mul_gammaMeasure ha hr hs

/-- **CreditRisk+ sector pgf** (Poisson–Gamma mixture, exact, before loss-banding): for
`z < r + 1`, the Poisson pgf `E[z^N | Λ = λ] = ∫ n, z ^ n ∂Poisson(λ)` integrated against
`Λ ∼ Gamma(a, r)` is `(r / (r − (z − 1))) ^ a`. This is the tower property
`E[z^N] = E_Λ[E[z^N | Λ]]` written as an iterated integral; the mixed law of `N` is not
constructed. The Gamma law lives on `[0, ∞)`, so `λ.toNNReal = λ` almost everywhere and the outer
integral is the Gamma MGF at `z − 1`. -/
theorem integral_integral_pow_poissonMeasure_gammaMeasure {a r z : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hz : z < r + 1) :
    ∫ lam, (∫ n, z ^ n ∂poissonMeasure lam.toNNReal) ∂gammaMeasure a r =
      (r / (r - (z - 1))) ^ a := by
  have hmeasf : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  have hpos : ∀ᵐ lam ∂gammaMeasure a r, 0 ≤ lam := by
    rw [gammaMeasure, ae_withDensity_iff hmeasf]
    exact ae_of_all _ fun lam hlam ↦ not_lt.1 fun hneg ↦ hlam (gammaPDF_of_neg hneg)
  rw [← integral_exp_mul_gammaMeasure ha hr (show z - 1 < r by linarith)]
  refine integral_congr_ae ?_
  filter_upwards [hpos] with lam hlam
  rw [PoissonPgf.integral_pow_poissonMeasure, Real.coe_toNNReal _ hlam, mul_comm lam]

/-- **Sector pgf, negative-binomial-style `p`-form.** With `β > 0` the mixture scale and
`p = β / (1 + β)`, the sector pgf is `((1 − p) / (1 − p·z)) ^ a`, matching the CreditRisk+
technical document's parametrisation. Mathlib's `gammaMeasure` is rate-parametrised, so the
Gamma law used is `gammaMeasure a (1 / β)`. -/
theorem integral_integral_pow_poissonMeasure_gammaMeasure_eq_negBinomial {a β z : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hz : z < 1 + 1 / β) :
    ∫ lam, (∫ n, z ^ n ∂poissonMeasure lam.toNNReal) ∂gammaMeasure a (1 / β) =
      ((1 - β / (1 + β)) / (1 - β / (1 + β) * z)) ^ a := by
  have hr : (0 : ℝ) < 1 / β := by positivity
  rw [integral_integral_pow_poissonMeasure_gammaMeasure ha hr (by rw [add_comm]; linarith)]
  congr 1
  have hβ1 : (1 : ℝ) + β ≠ 0 := by positivity
  field_simp
  ring

/-- **`PD_i = 1 − e^{−λ_i}`**: for `N ∼ Poisson(λ)`, the default probability `P(N ≠ 0)` equals
`1 − e^{−λ}`, since `P(N = 0) = e^{−λ}` and probabilities sum to `1`. -/
theorem poissonMeasure_real_compl_singleton_zero (lam : ℝ≥0) :
    (poissonMeasure lam).real {0}ᶜ = 1 - rexp (-(lam : ℝ)) := by
  have h0 : (poissonMeasure lam).real {0} = rexp (-(lam : ℝ)) := by
    rw [poissonMeasure_real_singleton]; simp
  rw [measureReal_compl (MeasurableSet.singleton 0), probReal_univ, h0]

end GammaPoissonMixturePgf

end MathFin
