/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.VasicekSDEGaussian

/-!
# The mean of a sum of two squared OU fluctuations (the Feller-borderline CIR mean)

Each component is an Ornstein–Uhlenbeck fluctuation in its Wiener representation,

`Xᵢ t := x_{i0} e^{−(k/2)t} + s ∫₀ᵗ e^{−(k/2)(t−u)} dBᵢ_u`,

which is the Vasicek short rate of `Models/Rates/VasicekSDEGaussian` at mean level `0`,
speed `k/2` and volatility `s`; its law `N(x_{i0}e^{−(k/2)t}, (s²/k)(1 − e^{−kt}))` is
`vasicekShortRate_hasLaw_gaussian`. With `v₀ := x_{10}² + x_{20}²` and `θ := 2s²/k`
(so `2kθ = (2s)²`, the Feller-borderline parametrization of
`dV = k(θ − V) dt + 2s√V dW`), `V t := (X₁ t)² + (X₂ t)²` has mean
`𝔼[V t] = θ(1 − e^{−kt}) + v₀e^{−kt}` (`cirVariance_mean`), the mean of the CIR process
from `v₀`.

The statements are per-time: `V t` is a random variable for each `t`. That `V` solves the
CIR SDE is not proved; it needs `B₁`, `B₂` independent (Lévy's characterization of the
driving Brownian motion of `√V`), which the mean computation does not use.

## Main definitions

* `ouProcess`: the Ornstein–Uhlenbeck fluctuation
  `X_t = x₀e^{−(k/2)t} + s ∫₀ᵗ e^{−(k/2)(t−u)} dB_u` in its Wiener representation.
* `cirTheta`: the long-run level `θ := 2s²/k` of the Feller-borderline parametrization.
* `cirVariance`: the sum of squares `V_t = (X₁_t)² + (X₂_t)²` of two OU fluctuations.

## Main results

Public API (all in namespace `MathFin.CIRSquaredOU`):

* `ouProcess`, `ouProcess_integral_sq` — the OU fluctuation and its second moment;
* `cirTheta`, `cirTheta_borderline`, `cirVariance`, `cirVariance_nonneg`,
  `cirVariance_mean` — the long-run level, the sum of squares, its nonnegativity and
  its mean.

## References

* [J. C. Cox, J. E. Ingersoll and S. A. Ross, *A theory of the term structure of interest
  rates*][CoxIngersollRoss1985]

## Tags

CIR process, Ornstein–Uhlenbeck, squared Bessel, Feller condition, sum of squares, mean-reverting,
MSC 60J60, MSC 60G15, MSC 91G30
-/

@[expose] public section

namespace MathFin.CIRSquaredOU

open MeasureTheory ProbabilityTheory
open scoped NNReal
open MathFin WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- The OU fluctuation `X_t = x₀e^{−(k/2)t} + s ∫₀ᵗ e^{−(k/2)(t−u)} dB_u`: the Vasicek short
rate in its Wiener representation at mean level `0`, speed `k/2`, volatility `s`. -/
noncomputable def ouProcess (hB : IsPreBrownianReal B μ) (k s x0 : ℝ)
    (hk : 0 < k) (t : ℝ≥0) (ω : Ω) : ℝ :=
  vasicekSDEMean x0 0 (k / 2) t
    + s * wienerIntegralLp B hB t (vasicekKernelLp (k / 2) (half_pos hk).le t) ω

/-- The OU second moment `𝔼[X_t²] = x₀²e^{−kt} + (s²/k)(1 − e^{−kt})`, from the Gaussian
law `vasicekShortRate_hasLaw_gaussian`. -/
theorem ouProcess_integral_sq (hB : IsPreBrownianReal B μ) {k : ℝ} (hk : 0 < k)
    (s x0 : ℝ) (t : ℝ≥0) :
    ∫ ω, (ouProcess hB k s x0 hk t ω) ^ 2 ∂μ
      = x0 ^ 2 * Real.exp (-(k * (t : ℝ)))
        + s ^ 2 / k * (1 - Real.exp (-(k * (t : ℝ)))) := by
  have hlaw : HasLaw (fun ω ↦ ouProcess hB k s x0 hk t ω) _ μ :=
    vasicekShortRate_hasLaw_gaussian hB x0 0 s (half_pos hk) t
  rw [integral_sq_of_hasLaw_gaussianReal hlaw, Real.coe_toNNReal _
    (vasicekSDEVariance_nonneg s (half_pos hk) (NNReal.coe_nonneg t))]
  have he : Real.exp (-(k / 2 * (t : ℝ))) ^ 2 = Real.exp (-(k * (t : ℝ))) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  simp only [vasicekSDEMean, vasicekSDEVariance, zero_mul, add_zero, mul_pow, he]
  field_simp

/-- The OU fluctuation is square integrable: a constant plus a multiple of an `L²` element. -/
theorem ouProcess_sq_integrable (hB : IsPreBrownianReal B μ) {k : ℝ} (hk : 0 < k)
    (s x0 : ℝ) (t : ℝ≥0) :
    Integrable (fun ω ↦ (ouProcess hB k s x0 hk t ω) ^ 2) μ := by
  have h1 : MemLp (wienerIntegralLp B hB t (vasicekKernelLp (k / 2) (half_pos hk).le t)) 2 μ :=
    Lp.memLp _
  have h2 := (memLp_const (vasicekSDEMean x0 0 (k / 2) t)).add (h1.const_mul s)
  exact h2.integrable_sq

variable {B1 B2 : ℝ≥0 → Ω → ℝ}

/-- The long-run level `θ := 2s²/k`, the Feller-borderline parametrization of
`dV = k(θ − V) dt + 2s√V dW`. -/
noncomputable def cirTheta (s k : ℝ) : ℝ := 2 * s ^ 2 / k

/-- The borderline identity `2kθ = (2s)²` (false at `k = 0`, where `θ = 0` by
Lean's `x/0 = 0`). -/
theorem cirTheta_borderline (s k : ℝ) (hk : k ≠ 0) :
    2 * k * cirTheta s k = (2 * s) ^ 2 := by
  rw [cirTheta]
  field_simp

/-- The sum of squares `V_t := (X₁_t)² + (X₂_t)²` of two OU fluctuations, `Xᵢ` driven by
`Bᵢ` from `x_{i0}`. -/
noncomputable def cirVariance (hB1 : IsPreBrownianReal B1 μ)
    (hB2 : IsPreBrownianReal B2 μ) (k s x10 x20 : ℝ) (hk : 0 < k)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  (ouProcess hB1 k s x10 hk t ω) ^ 2 + (ouProcess hB2 k s x20 hk t ω) ^ 2

omit [IsProbabilityMeasure μ] in
/-- `V_t(ω) ≥ 0` for every `(t, ω)`. -/
theorem cirVariance_nonneg (hB1 : IsPreBrownianReal B1 μ)
    (hB2 : IsPreBrownianReal B2 μ) (k s x10 x20 : ℝ) (hk : 0 < k)
    (t : ℝ≥0) (ω : Ω) :
    0 ≤ cirVariance hB1 hB2 k s x10 x20 hk t ω :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The mean `𝔼[V_t] = θ(1 − e^{−kt}) + v₀e^{−kt}`, `θ = 2s²/k`, `v₀ = x_{10}² + x_{20}²`:
the sum of the two component second moments. Independence of `B₁`, `B₂` is not used. -/
theorem cirVariance_mean (hB1 : IsPreBrownianReal B1 μ)
    (hB2 : IsPreBrownianReal B2 μ) {k : ℝ} (hk : 0 < k) (s x10 x20 : ℝ)
    (t : ℝ≥0) :
    ∫ ω, cirVariance hB1 hB2 k s x10 x20 hk t ω ∂μ
      = cirTheta s k * (1 - Real.exp (-(k * (t : ℝ))))
        + (x10 ^ 2 + x20 ^ 2) * Real.exp (-(k * (t : ℝ))) := by
  simp only [cirVariance]
  rw [integral_add (ouProcess_sq_integrable hB1 hk s x10 t)
      (ouProcess_sq_integrable hB2 hk s x20 t),
    ouProcess_integral_sq hB1 hk s x10 t, ouProcess_integral_sq hB2 hk s x20 t, cirTheta]
  ring

end MathFin.CIRSquaredOU
