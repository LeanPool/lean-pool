/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.VasicekSDEGaussian

/-!
# AR(1) ↔ OU parameter inversion

A discretely-sampled Ornstein-Uhlenbeck (Vasicek) process with long-run level
`θ`, observed on a grid of spacing `Δt`, is an AR(1) process
`x_{n+1} − θ = φ (x_n − θ) + ε_n`. One step of that statement is derived here from the
library's OU law (`vasicekShortRate_hasLaw_gaussian`, `Models/Rates/VasicekSDEGaussian.lean`):
from a deterministic start `r₀`, the residual `ε = (r_Δt − θ) − φ·(r₀ − θ)`, `φ = e^{−kΔt}`,
is Gaussian `N(0, vasicekSDEVariance σ k Δt)` (`ouStepResidual_hasLaw`), and the dictionary
below recovers `σ²` from its variance (`ouSigmaSqFromVar_variance_ouStepResidual`). The
multi-step statement — independent innovations along a path started from the random
previous state — needs the OU Markov transition law and is not formalized. This file
records the standard dictionary between the AR(1) fit `(φ, Var(resid))` and the
continuous-time OU parameters `(k, σ)`:

  `φ = e^{−kΔt}`                        (mean-reversion discount)
  `k = −ln(φ)/Δt`                       (inverse: mean-reversion speed)
  `σ² = 2k·Var(resid) / (1 − e^{−2kΔt})`  (diffusion coefficient)
  `half-life = ln 2 / k`

The dictionary is algebra on the closed forms `vasicekSDEMean` and
`vasicekSDEVariance` of `Models/Rates/VasicekSDE.lean`: `ouPhiFromK` is literally the
decay factor appearing in `vasicekSDEMean`, and `ouSigmaSqFromVar` inverts
`vasicekSDEVariance` for `σ²` given an observed residual variance. The last section ties
it to the OU law.

## Main definitions

* `ouPhiFromK`: the AR(1) discount factor `φ = exp (-(k Δt))` from the OU speed `k`.
* `kFromPhi`: the OU speed `-log φ / Δt` from `φ`.
* `ouSigmaSqFromVar`: `σ² = 2k Var(resid) / (1 - exp (-2kΔt))` from the fitted residual variance.
* `ouStepResidual`: the AR(1) residual `(r_Δt - θ) - φ (r₀ - θ)` of one Vasicek/OU step from a
  deterministic start `r₀`, with `φ = ouPhiFromK k Δt`.

## Main results

* `ouPhiFromK`, `kFromPhi` : the `φ ↔ k` dictionary: `kFromPhi ∘ ouPhiFromK`
  is the identity for `Δt ≠ 0` (`kFromPhi_ouPhiFromK`), and `ouPhiFromK ∘ kFromPhi`
  is the identity on `φ > 0` for `Δt ≠ 0` (`ouPhiFromK_kFromPhi`).
* `ouPhiFromK_halfLife` : the decay factor at `Models.Rates.Vasicek`'s existing
  `meanReversionHalfLife` (`ln 2 / k`) is `1/2`, for `k ≠ 0`.
* `ouSigmaSqFromVar_vasicekSDEVariance` : `ouSigmaSqFromVar` recovers `σ²` from
  `vasicekSDEVariance σ k Δt`, for `k ≠ 0` and `1 − e^{−2kΔt} ≠ 0` (one direction
  of the round trip: recovering a residual variance from `ouSigmaSqFromVar` is not
  stated).
* `ouStepResidual_hasLaw` : one OU step from `r₀` is an AR(1) step — the residual
  `(r_Δt − θ) − ouPhiFromK k Δt · (r₀ − θ)` of the short rate in its Wiener representation
  has law `N(0, vasicekSDEVariance σ k Δt)`, for `k > 0`.
* `ouSigmaSqFromVar_variance_ouStepResidual` : `ouSigmaSqFromVar` applied to the variance
  of that residual returns `σ²`, for `k, Δt > 0`.

## References

* [P. Glasserman, *Monte Carlo Methods in Financial Engineering*][Glasserman2003], §3.3

## Tags

AR(1) process, Ornstein–Uhlenbeck, mean reversion speed, half-life, parameter calibration, Vasicek,
MSC 62M10, MSC 91G30, JEL C22
-/

@[expose] public section

namespace MathFin

/-! ### The `φ ↔ k` dictionary -/

/-- **AR(1) discount factor from OU speed**: `φ = e^{−kΔt}`. -/
noncomputable def ouPhiFromK (k Δt : ℝ) : ℝ := Real.exp (-(k * Δt))

/-- **OU mean-reversion speed from AR(1) discount factor**: `k = −ln(φ)/Δt`. -/
noncomputable def kFromPhi (φ Δt : ℝ) : ℝ := -Real.log φ / Δt

/-- **Diffusion coefficient from fitted residual variance**:
`σ² = 2k·Var(resid) / (1 − e^{−2kΔt})`, inverting `vasicekSDEVariance` for
`σ²` given the AR(1) fit's residual variance at spacing `Δt`. -/
noncomputable def ouSigmaSqFromVar (k residVar Δt : ℝ) : ℝ :=
  2 * k * residVar / (1 - Real.exp (-(2 * k * Δt)))

/-- **`ouSigmaSqFromVar` inverts `vasicekSDEVariance`**: feeding it the
closed-form Vasicek/OU variance at spacing `Δt` recovers the diffusion
coefficient `σ²` it came from, for `k ≠ 0` and `1 − e^{−2kΔt} ≠ 0` (e.g.
`k, Δt` both nonzero). -/
theorem ouSigmaSqFromVar_vasicekSDEVariance (σ k Δt : ℝ) (hk : k ≠ 0)
    (hden : 1 - Real.exp (-(2 * k * Δt)) ≠ 0) :
    ouSigmaSqFromVar k (vasicekSDEVariance σ k Δt) Δt = σ ^ 2 := by
  unfold ouSigmaSqFromVar vasicekSDEVariance
  field_simp

/-- Recovering `k` from the `φ` it generates: `kFromPhi (ouPhiFromK k Δt) Δt = k`,
for any `Δt ≠ 0`. -/
theorem kFromPhi_ouPhiFromK (k Δt : ℝ) (hΔt : Δt ≠ 0) :
    kFromPhi (ouPhiFromK k Δt) Δt = k := by
  unfold kFromPhi ouPhiFromK
  rw [Real.log_exp]
  field_simp

/-- Recovering `φ` from the `k` it generates: `ouPhiFromK (kFromPhi φ Δt) Δt = φ`,
for `φ > 0` and `Δt ≠ 0`. -/
theorem ouPhiFromK_kFromPhi (φ Δt : ℝ) (hφ : 0 < φ) (hΔt : Δt ≠ 0) :
    ouPhiFromK (kFromPhi φ Δt) Δt = φ := by
  unfold ouPhiFromK kFromPhi
  rw [neg_div, neg_mul, neg_neg, div_mul_cancel₀ _ hΔt, Real.exp_log hφ]

/-- The decay factor at `Models.Rates.Vasicek`'s existing `meanReversionHalfLife`
is exactly `1/2`, for `k ≠ 0`. -/
theorem ouPhiFromK_halfLife (k : ℝ) (hk : k ≠ 0) :
    ouPhiFromK k (meanReversionHalfLife k) = 1 / 2 := by
  unfold ouPhiFromK meanReversionHalfLife
  rw [mul_div_cancel₀ _ hk, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2), one_div]

/-! ### One OU step is an AR(1) step -/

section OneStep

open MeasureTheory ProbabilityTheory
open scoped NNReal
open WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **The AR(1) residual of one OU step**: `ε = (r_Δt − θ) − φ·(r₀ − θ)` with
`φ = ouPhiFromK k Δt`, for the short rate after one step `Δt` from the deterministic start
`r₀`, carried in the Wiener representation of `vasicekShortRate_hasLaw_gaussian`
(`r_Δt = vasicekSDEMean r₀ θ k Δt + σ ∫₀^Δt e^{−k(Δt−s)} dB_s`). -/
noncomputable def ouStepResidual (hB : IsPreBrownianReal B μ) (r₀ θ σ : ℝ) {k : ℝ}
    (hk : 0 < k) (Δt : ℝ≥0) (ω : Ω) : ℝ :=
  (vasicekSDEMean r₀ θ k Δt + σ * wienerIntegralLp B hB Δt (vasicekKernelLp k hk.le Δt) ω - θ)
    - ouPhiFromK k Δt * (r₀ - θ)

/-- **One OU step is an AR(1) step.** The residual `(r_Δt − θ) − φ·(r₀ − θ)` of one OU step
from `r₀` is centred Gaussian with variance `vasicekSDEVariance σ k Δt`: the deterministic
part of `r_Δt − θ` is exactly `φ·(r₀ − θ)` (`vasicekSDEMean r₀ θ k Δt = θ + φ·(r₀ − θ)`), and
the rest is the Gaussian law of `vasicekShortRate_hasLaw_gaussian` shifted to mean zero. -/
theorem ouStepResidual_hasLaw (hB : IsPreBrownianReal B μ) (r₀ θ σ : ℝ) {k : ℝ}
    (hk : 0 < k) (Δt : ℝ≥0) :
    HasLaw (ouStepResidual hB r₀ θ σ hk Δt)
      (gaussianReal 0 (vasicekSDEVariance σ k Δt).toNNReal) μ := by
  have h := gaussianReal_sub_const (vasicekShortRate_hasLaw_gaussian hB r₀ θ σ hk Δt)
    (vasicekSDEMean r₀ θ k Δt)
  rw [sub_self] at h
  convert h using 1
  funext ω
  simp only [ouStepResidual, vasicekSDEMean, ouPhiFromK]
  ring

/-- **The calibration dictionary recovers `σ²` from the residual's variance.** For `k > 0`
and `Δt > 0`, `ouSigmaSqFromVar k Var[ε] Δt = σ²`, where `ε` is the one-step residual of
`ouStepResidual_hasLaw`: its variance is `vasicekSDEVariance σ k Δt`, which
`ouSigmaSqFromVar_vasicekSDEVariance` inverts. -/
theorem ouSigmaSqFromVar_variance_ouStepResidual (hB : IsPreBrownianReal B μ)
    (r₀ θ σ : ℝ) {k : ℝ} (hk : 0 < k) {Δt : ℝ≥0} (hΔt : 0 < (Δt : ℝ)) :
    ouSigmaSqFromVar k (Var[ouStepResidual hB r₀ θ σ hk Δt; μ]) Δt = σ ^ 2 := by
  rw [(ouStepResidual_hasLaw hB r₀ θ σ hk Δt).variance_eq, variance_id_gaussianReal,
    Real.coe_toNNReal _ (vasicekSDEVariance_nonneg σ hk hΔt.le)]
  refine ouSigmaSqFromVar_vasicekSDEVariance σ k Δt hk.ne' (sub_pos.mpr ?_).ne'
  exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos (mul_pos two_pos hk) hΔt))

end OneStep

end MathFin
