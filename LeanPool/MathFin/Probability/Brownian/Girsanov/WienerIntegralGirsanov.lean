/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Wiener.WienerIntegralExpMoment
public import LeanPool.MathFin.Probability.Laws.Esscher

/-!
# Wiener integrals under the constant-`λ` Girsanov measure

Fix a pre-Brownian motion `B` under `μ`, a horizon `T` and a constant `λ`, and let

  `Q_λ = μ.withDensity(exp(−λB_T − λ²T/2))`,

the constant-`θ` Girsanov measure of `Probability/Brownian/Girsanov/GirsanovConstantTheta` (there,
with a filtration,
`B_t + λt` is shown to have the increments of a `Q_λ`-Brownian motion on `[0, T]`,
`Btheta_isQBrownianMotion`). This file computes the `Q_λ`-law of every Wiener integral with a
deterministic kernel: the measure change shifts its mean by `−λ∫₀ᵀ f` and keeps its variance,

  under `Q_λ`, `∫₀ᵀ f dB ~ N(−λ∫₀ᵀ f, ∫₀ᵀ f²)`   (`wienerIntegralLp_hasLaw_girsanov`).

This is the Cameron–Martin shift of a Wiener integral: `dB = dB^λ − λ dt` with `B^λ` the
`Q_λ`-Brownian motion.

## Proof

`B_T` is the Wiener integral of the indicator `𝟙 = 𝟙_{(0,T]}`
(`eval_ae_eq_wienerIntegralLp_stepIndicator`). By linearity, `−λB_T + t·∫f dB` is a.s. the single
Wiener integral `∫(tf − λ𝟙) dB`, so the `Q_λ`-moment-generating function of `∫f dB` is one Gaussian
exponential moment under `μ`:

  `𝔼_{Q_λ}[e^{t∫f dB}] = e^{−λ²T/2}·e^{‖tf − λ𝟙‖²/2} = e^{−tλ⟪𝟙,f⟫ + t²‖f‖²/2}`,

using `‖𝟙‖² = T`. No joint law of `(B_T, ∫f dB)` is needed. The moment-generating function
determines the law (`measure_eq_of_mgf_id_eq`). At `t = 0` the same identity gives
`Q_λ(Ω) = 1` (`isProbabilityMeasure_withDensity_girsanov`). That result needs only the
pre-Brownian hypothesis; `girsanovMeasure_isProbabilityMeasure` states it for a filtered
pre-Brownian motion.

## Main results

* `integral_exp_mul_wienerIntegralLp_withDensity_girsanov`: under
  `Q_λ = μ.withDensity(exp(−λB_T − λ²T/2))`, `𝔼[exp(t·∫f dB)] = exp(−tλ⟪𝟙_{(0,T]}, f⟫ + t²‖f‖²/2)`.
* `isProbabilityMeasure_withDensity_girsanov`: `Q_λ` is a probability measure for a
  pre-Brownian motion.
* `wienerIntegralLp_hasLaw_girsanov`: under `Q_λ`, `∫₀ᵀ f dB ~ N(−λ∫₀ᵀ f, ∫₀ᵀ f²)`.

## Tags

Girsanov theorem, Cameron–Martin shift, Wiener integral, measure change, drift shift,
Doléans density, MSC 60H05, MSC 60G15, MSC 91G20
-/

@[expose] public section

namespace MathFin
namespace WienerIntegralL2

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **The `Q_λ`-moment-generating function of a Wiener integral**:
`𝔼_{Q_λ}[exp(t·∫f dB)] = exp(−tλ⟪𝟙_{(0,T]}, f⟫ + t²‖f‖²/2)`. -/
lemma integral_exp_mul_wienerIntegralLp_withDensity_girsanov (hB : IsPreBrownianReal B μ)
    (lam : ℝ) (T : ℝ≥0) (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) (t : ℝ) :
    ∫ ω, Real.exp (t * wienerIntegralLp B hB T f ω)
        ∂(μ.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-lam * B T ω - lam ^ 2 * (T : ℝ) / 2)))
      = Real.exp (-(t * lam * ⟪stepIndicatorLp T (StepIndex.whole T), f⟫_ℝ)
          + t ^ 2 * ‖f‖ ^ 2 / 2) := by
  have hZ : AEMeasurable (fun ω ↦ Real.exp (-lam * B T ω - lam ^ 2 * (T : ℝ) / 2)) μ := by
    have := hB.aemeasurable T
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul₀ hZ.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  have hpt : (fun ω ↦ (ENNReal.ofReal (Real.exp (-lam * B T ω - lam ^ 2 * (T : ℝ) / 2))).toReal
        • Real.exp (t * wienerIntegralLp B hB T f ω))
      =ᵐ[μ] fun ω ↦ Real.exp (-(lam ^ 2 * (T : ℝ) / 2)) * Real.exp (1 * wienerIntegralLp B hB T
          (t • f + (-lam) • stepIndicatorLp T (StepIndex.whole T)) ω) := by
    filter_upwards [eval_ae_eq_wienerIntegralLp_stepIndicator hB T,
      wienerIntegralLp_smul_add_smul_ae hB T t (-lam) f (stepIndicatorLp T (StepIndex.whole T))]
      with ω hBT hlin
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, hlin, hBT, ← Real.exp_add,
      ← Real.exp_add]
    congr 1
    ring
  rw [integral_congr_ae hpt, integral_const_mul, integral_exp_mul_wienerIntegralLp,
    norm_smul_add_smul_sq_real, norm_stepIndicatorLp_whole_sq,
    real_inner_comm (stepIndicatorLp T (StepIndex.whole T)) f, ← Real.exp_add]
  congr 1
  ring

/-- **The constant-`λ` Girsanov measure is a probability measure**, for a pre-Brownian motion: the
`t = 0` case of `integral_exp_mul_wienerIntegralLp_withDensity_girsanov`, `∫ 1 dQ_λ = 1`. -/
theorem isProbabilityMeasure_withDensity_girsanov (hB : IsPreBrownianReal B μ) (lam : ℝ)
    (T : ℝ≥0) :
    IsProbabilityMeasure
      (μ.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-lam * B T ω - lam ^ 2 * (T : ℝ) / 2))) := by
  have h := integral_exp_mul_wienerIntegralLp_withDensity_girsanov hB lam T 0 0
  simp only [zero_mul, neg_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_div, add_zero, Real.exp_zero, integral_const, smul_eq_mul, mul_one] at h
  constructor
  rwa [measureReal_def, ENNReal.toReal_eq_one_iff] at h

/-- **Wiener integrals under the Girsanov measure (Cameron–Martin shift).** Under
`Q_λ = μ.withDensity(exp(−λB_T − λ²T/2))`, the Wiener integral of a deterministic kernel
`f ∈ L²((0, T])` is Gaussian with its mean shifted by `−λ∫₀ᵀ f` and its variance unchanged:

  `∫₀ᵀ f dB ~ N(−λ·∫₀ᵀ f, ∫₀ᵀ f²)`   under `Q_λ`. -/
theorem wienerIntegralLp_hasLaw_girsanov (hB : IsPreBrownianReal B μ) (lam : ℝ) (T : ℝ≥0)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    HasLaw (fun ω ↦ wienerIntegralLp B hB T f ω)
      (gaussianReal (-(lam * ∫ s in Set.Ioc (0 : ℝ) (T : ℝ), f s))
        (∫ s in Set.Ioc (0 : ℝ) (T : ℝ), f s ^ 2).toNNReal)
      (μ.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-lam * B T ω - lam ^ 2 * (T : ℝ) / 2))) := by
  have := isProbabilityMeasure_withDensity_girsanov hB lam T
  have hae : AEMeasurable (fun ω ↦ wienerIntegralLp B hB T f ω)
      (μ.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-lam * B T ω - lam ^ 2 * (T : ℝ) / 2))) :=
    (Lp.aestronglyMeasurable _).aemeasurable.mono_ac (withDensity_absolutelyContinuous _ _)
  refine ⟨hae, (measure_eq_of_mgf_id_eq integrable_exp_mul_gaussianReal ?_).symm⟩
  rw [mgf_id_gaussianReal, mgf_id_map hae]
  funext t
  simp only [mgf]
  rw [integral_exp_mul_wienerIntegralLp_withDensity_girsanov, inner_stepIndicatorLp_whole,
    lp_two_norm_sq, Real.coe_toNNReal _ (integral_nonneg fun _ ↦ sq_nonneg _)]
  congr 1
  ring

end WienerIntegralL2

end MathFin
