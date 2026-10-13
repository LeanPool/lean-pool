/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.Representative
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.TailLocalization

/-!
# Tail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The explicit resolvent tail function

Let `z` solve `mu z - div (a grad z) = g` on an open bounded domain `Om` with
zero trace, let `x` be a point of `Om` and `r > 0` a radius with
`euclideanBall x r` inside `Om`, and let the source `g` vanish almost
everywhere on that ball.  With the maximum-principle bound `|z| <= 1 / mu`,
the value of `mu * z` at `x` decays in the dimensionless variable

`s = sqrt mu * r`,

and this file makes that decay explicit: `agmonTailFunction d lam Lam alpha`
is a closed-form function of `s` alone, with constants depending only on the
dimension `d`, the two ellipticity constants `lam` and `Lam`, and the Hölder
exponent `alpha`.

The hypotheses that restrict the estimate.  The dimension satisfies
`2 <= d`, the Hölder exponent lies in `Set.Ico (1 / 2) 1`, and the coefficient
field is not merely uniformly elliptic with constants `lam` and `Lam`: it is
required to be within small contrast of the identity, that is
`CoefficientIdentityDistanceLE Om a delta` for some
`delta <= smallContrastThreshold d alpha`.  The small-contrast hypothesis is
what supplies the interior Schauder estimate behind the gradient and the
forcing terms, and it is the reason the chain does not apply to a merely
uniformly elliptic field.  Subject to those hypotheses the right-hand side is
free of the domain, the coefficient field, the source and the solution.

Why `s` is the only variable.  The equation is scale invariant, and `mu r ^ 2`
is the only dimensionless combination of the mass and the radius, so every
term of the pointwise constant must be a function of `s` after multiplication
by `mu`.  Each of the three terms is checked against that requirement: the
weighted `L²` term carries `M <= 1 / mu` from the maximum principle, the
layer gradient bound `Ceta` which scales like `r ^ (-2)`, and the layer volume
`volLayer` which scales like `r ^ d`, and it contributes `s ^ (-1)`; the
Schauder gradient term carries the Caccioppoli gradient size, itself
proportional to `1 / mu` times `r ^ ((d - 2) / 2)`, and contributes a constant;
the Schauder forcing term carries the forcing bound one and contributes
`s ^ 2`.  Nothing else survives.

The geometry.  The localization is one on the ball of radius `3 r / 4` and
vanishes outside the ball of radius `r`, so its transition layer sits where
the source vanishes; the phase is the inward radial phase about `x` with
regularization `r / 8`; the interior estimate is applied on the ball of radius
`r / 2`.  The point is then at phase `-(r / 4)` and the layer at phase
`-(3 r / 4) + r / 8`, a gap of `3 r / 8`.

The exponential domination `agmonTailFunction_le_exp` is what a consumer of
the tail estimate needs: beyond `s = 1` the tail function is at most
`agmonTailDominationConstant d lam Lam alpha` times
`exp (-(agmonTailRate d lam Lam alpha / 2) * s)`.

The bound does not mention the domain except through the containment of the
ball.

## Main results

- `DivergenceFormProcess.Decay.agmonTailFunction`
- `DivergenceFormProcess.Decay.resolventTail_of_zeroTrace`
- `DivergenceFormProcess.Decay.resolventTail_of_zeroTrace_representative`
- `DivergenceFormProcess.Decay.agmonTailFunction_le_exp`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal

variable {d : ℕ}

/-! ### The tail function -/

/-- The coefficient of the `s⁻¹` term of the tail function: the weighted `L²`
term of the pointwise estimate, after the mass `mu` and the radius `r` have
been absorbed into `s = sqrt mu * r`. -/
def agmonTailL2Coefficient (d : ℕ) (lam Lam : ℝ) : ℝ :=
  32 * Real.sqrt 2 * (2 : ℝ) ^ d * Lam * smoothTransitionProfile.derivBound *
      ((d : ℝ) * Real.sqrt d) / Real.sqrt lam

/-- The constant term of the tail function: the Schauder gradient term of the
pointwise estimate, whose local gradient size is supplied by the Caccioppoli
bound.  It carries no power of `s` at all. -/
def agmonTailGradientCoefficient (d : ℕ) (lam Lam alpha : ℝ) : ℝ  :=
  16 * smallContrastZerothSchauderConstant d * Real.sqrt ((2 : ℝ) ^ d) *
      (1 / 2 : ℝ) ^ alpha * Lam * smoothTransitionProfile.derivBound *
      ((d : ℝ) * Real.sqrt d) *
      Real.sqrt ((volume (smallContrastUnitBall d)).toReal) / lam

/-- The coefficient of the `s ^ 2` term of the tail function: the Schauder
forcing term of the pointwise estimate, whose forcing bound is one. -/
def agmonTailForcingCoefficient (d : ℕ) (alpha : ℝ) : ℝ  :=
  smallContrastZerothSchauderConstant d * (1 / 2 : ℝ) ^ alpha / 4

/-- The decay rate of the tail function in `s = sqrt mu * r`: the Agmon rate
`sqrt (lam * mu) / (2 sqrt 2 * Lam)` reduced by the Hölder exponent factor
`alpha / (alpha + d / 2)` and read across the gap `3 r / 8` between the point
and the transition layer of the localization. -/
def agmonTailRate (d : ℕ) (lam Lam alpha : ℝ) : ℝ :=
  3 * Real.sqrt lam / (16 * Real.sqrt 2 * Lam) *
    (alpha / (alpha + (d : ℝ) / 2))

/-! ### Signs -/

/-- The `s⁻¹` coefficient is nonnegative. -/
theorem agmonTailL2Coefficient_nonneg (d : ℕ) {lam Lam : ℝ} (hLam : 0 ≤ Lam) :
    0 ≤ agmonTailL2Coefficient d lam Lam := by
  have hD : (0 : ℝ) ≤ smoothTransitionProfile.derivBound :=
    smoothTransitionProfile.derivBound_nonneg
  unfold agmonTailL2Coefficient
  positivity

/-- The constant coefficient is nonnegative. -/
theorem agmonTailGradientCoefficient_nonneg (d : ℕ) {lam Lam alpha : ℝ}
    (hlam : 0 < lam) (hLam : 0 ≤ Lam) :
    0 ≤ agmonTailGradientCoefficient d lam Lam alpha  := by
  have hD : (0 : ℝ) ≤ smoothTransitionProfile.derivBound :=
    smoothTransitionProfile.derivBound_nonneg
  have hCS : (0 : ℝ) ≤ smallContrastZerothSchauderConstant d :=
    smallContrastZerothSchauderConstant_nonneg d
  have hP : (0 : ℝ) < (1 / 2 : ℝ) ^ alpha :=
    Real.rpow_pos_of_pos (by norm_num) alpha
  unfold agmonTailGradientCoefficient
  positivity

/-- The `s ^ 2` coefficient is nonnegative. -/
theorem agmonTailForcingCoefficient_nonneg (d : ℕ) (alpha : ℝ) :
    0 ≤ agmonTailForcingCoefficient d alpha  := by
  have hCS : (0 : ℝ) ≤ smallContrastZerothSchauderConstant d :=
    smallContrastZerothSchauderConstant_nonneg d
  have hP : (0 : ℝ) < (1 / 2 : ℝ) ^ alpha :=
    Real.rpow_pos_of_pos (by norm_num) alpha
  unfold agmonTailForcingCoefficient
  positivity

/-- The tail rate is positive. -/
theorem agmonTailRate_pos (d : ℕ) {lam Lam alpha : ℝ} (hlam : 0 < lam)
    (hLam : 0 < Lam) (halpha : 0 < alpha) :
    0 < agmonTailRate d lam Lam alpha := by
  have hsl : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.2 hlam
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hdim : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hden : (0 : ℝ) < alpha + (d : ℝ) / 2 := by linarith only [halpha, hdim]
  unfold agmonTailRate
  exact mul_pos
    (div_pos (by linarith only [hsl])
      (mul_pos (mul_pos (by norm_num) hs2) hLam))
    (div_pos halpha hden)

/-! ### The frozen scale identification -/

private theorem rpow_shift_frozen {r alpha : ℝ} (hr : 0 < r) :
    r ^ (1 - alpha - (d : ℝ) / 2) * (r / 2 : ℝ) ^ alpha =
      r ^ (1 - (d : ℝ) / 2) * (1 / 2 : ℝ) ^ alpha := by
  have hr0 : (0 : ℝ) ≤ r := hr.le
  rw [show (r / 2 : ℝ) = r * (1 / 2) by ring,
    Real.mul_rpow hr0 (by norm_num),
    show (1 - alpha - (d : ℝ) / 2) =
      (1 - (d : ℝ) / 2) - alpha by ring,
    Real.rpow_sub hr, ← mul_assoc]
  have hpow : 0 < r ^ alpha := Real.rpow_pos_of_pos hr alpha
  field_simp

private theorem rpow_ratio_frozen {r r₀ : ℝ} (hr : 0 < r) (hr₀ : 0 < r₀)
    (q : ℝ) :
    (r / (2 * r₀)) ^ q = r ^ q / ((2 : ℝ) ^ q * r₀ ^ q) := by
  rw [Real.div_rpow hr.le (mul_nonneg (by norm_num) hr₀.le),
    Real.mul_rpow (by norm_num) hr₀.le]

/-- The pointwise constant before its dimensional variables are collected. -/
def agmonFrozenDecayConstant (d : ℕ) (D alpha E G r₀ : ℝ) : ℝ  :=
  D / Real.sqrt ((volume (smallContrastUnitBall d)).toReal) /
        Real.sqrt ((r₀ / 2) ^ d) +
    smallContrastZerothSchauderConstant d *
        (r₀ ^ (1 - alpha - (d : ℝ) / 2) * E +
          r₀ ^ (2 - alpha) * G) *
      (r₀ / 2) ^ alpha

private theorem sqrt_agmonTailCutoffGradientBound_mul_layerVolume [NeZero d]
    {r : ℝ} (hr : 0 < r) :
    Real.sqrt (agmonTailCutoffGradientBound d r *
        agmonTailLayerVolume d r) =
      16 * smoothTransitionProfile.derivBound * (d : ℝ) * Real.sqrt (d : ℝ) *
        Real.sqrt ((volume (smallContrastUnitBall d)).toReal) *
        Real.sqrt (r ^ d) / r := by
  have hV : (0 : ℝ) < (volume (smallContrastUnitBall d)).toReal :=
    unitBallVolume_pos
  have hD : (0 : ℝ) ≤ smoothTransitionProfile.derivBound :=
    smoothTransitionProfile.derivBound_nonneg
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hQrsq : Real.sqrt (r ^ d) ^ 2 = r ^ d :=
    Real.sq_sqrt (pow_nonneg hr.le d)
  have hWsq : Real.sqrt ((volume (smallContrastUnitBall d)).toReal) ^ 2 =
      (volume (smallContrastUnitBall d)).toReal := Real.sq_sqrt hV.le
  have hDdsq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt hdpos.le
  have hnn : (0 : ℝ) ≤ 16 * smoothTransitionProfile.derivBound * (d : ℝ) *
      Real.sqrt (d : ℝ) *
      Real.sqrt ((volume (smallContrastUnitBall d)).toReal) *
      Real.sqrt (r ^ d) / r := by positivity
  rw [show agmonTailCutoffGradientBound d r * agmonTailLayerVolume d r =
      (16 * smoothTransitionProfile.derivBound * (d : ℝ) * Real.sqrt (d : ℝ) *
        Real.sqrt ((volume (smallContrastUnitBall d)).toReal) *
        Real.sqrt (r ^ d) / r) ^ 2 by
    unfold agmonTailCutoffGradientBound agmonTailLayerVolume
    field_simp
    rw [hDdsq, hWsq, hQrsq]
    ring]
  exact Real.sqrt_sq hnn

private theorem sqrt_eight_mul_sq_div_mul_agmon_layer [NeZero d]
    {Lam L T r : ℝ} (hLam : 0 < Lam) (hL : 0 < L) (hT : 0 < T)
    (hr : 0 < r) :
    Real.sqrt (8 * Lam ^ 2 / (L ^ 2 * T ^ 2) *
        agmonTailCutoffGradientBound d r * agmonTailLayerVolume d r) =
      2 * Real.sqrt 2 * Lam / (L * T) *
        (16 * smoothTransitionProfile.derivBound * (d : ℝ) * Real.sqrt (d : ℝ) *
          Real.sqrt ((volume (smallContrastUnitBall d)).toReal) *
          Real.sqrt (r ^ d) / r) := by
  rw [show 8 * Lam ^ 2 / (L ^ 2 * T ^ 2) * agmonTailCutoffGradientBound d r *
      agmonTailLayerVolume d r =
      8 * Lam ^ 2 / (L ^ 2 * T ^ 2) *
        (agmonTailCutoffGradientBound d r * agmonTailLayerVolume d r) by ring,
    Real.sqrt_mul (by positivity),
    sqrt_agmonTailCutoffGradientBound_mul_layerVolume (d := d) hr]
  congr 1
  have hnn : (0 : ℝ) ≤ 2 * Real.sqrt 2 * Lam / (L * T) := by positivity
  rw [show 8 * Lam ^ 2 / (L ^ 2 * T ^ 2) =
      (2 * Real.sqrt 2 * Lam / (L * T)) ^ 2 by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring]
  exact Real.sqrt_sq hnn

/-- Scale identification for the frozen pointwise constant. -/
theorem mul_agmonDecayConstant_frozen_eq [NeZero d]
    {lam Lam nu mu r r₀ alpha : ℝ}
    (hlam : 0 < lam) (hLam : 0 < Lam) (hmu : 0 < mu)
    (hr : 0 < r) (hr₀ : 0 < r₀) :
    mu * agmonFrozenDecayConstant d
        (1 / mu * Real.sqrt (8 * Lam ^ 2 / (lam * mu) *
          agmonTailCutoffGradientBound d r * agmonTailLayerVolume d r))
        alpha (agmonTailGradientSize d lam Lam mu r) (1 / nu) r₀ =
      agmonTailL2Coefficient d lam Lam / (Real.sqrt mu * r) *
          ((Real.sqrt mu * r) / (2 * (Real.sqrt mu * r₀))) ^ ((d : ℝ) / 2) +
        agmonTailGradientCoefficient d lam Lam alpha *
          ((Real.sqrt mu * r) / (2 * (Real.sqrt mu * r₀))) ^
            ((d : ℝ) / 2 - 1) +
        4 * agmonTailForcingCoefficient d alpha * (Real.sqrt mu * r₀) ^ 2 / nu := by
  obtain ⟨T, hTpos, rfl⟩ : ∃ T : ℝ, 0 < T ∧ T ^ 2 = mu :=
    ⟨Real.sqrt mu, Real.sqrt_pos.2 hmu, Real.sq_sqrt hmu.le⟩
  obtain ⟨L, hLpos, rfl⟩ : ∃ L : ℝ, 0 < L ∧ L ^ 2 = lam :=
    ⟨Real.sqrt lam, Real.sqrt_pos.2 hlam, Real.sq_sqrt hlam.le⟩
  have hT : Real.sqrt (T ^ 2) = T := Real.sqrt_sq hTpos.le
  have hL : Real.sqrt (L ^ 2) = L := Real.sqrt_sq hLpos.le
  have hV : (0 : ℝ) < (volume (smallContrastUnitBall d)).toReal :=
    unitBallVolume_pos
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hQr : (0 : ℝ) < Real.sqrt (r ^ d) := Real.sqrt_pos.2 (pow_pos hr d)
  have hQr₀ : (0 : ℝ) < Real.sqrt (r₀ ^ d) := Real.sqrt_pos.2 (pow_pos hr₀ d)
  have hW : (0 : ℝ) < Real.sqrt ((volume (smallContrastUnitBall d)).toReal) :=
    Real.sqrt_pos.2 hV
  have hDd : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdpos
  have hQr₀sq : Real.sqrt (r₀ ^ d) ^ 2 = r₀ ^ d :=
    Real.sq_sqrt (pow_nonneg hr₀.le d)
  have hWsq : Real.sqrt ((volume (smallContrastUnitBall d)).toReal) ^ 2 =
      (volume (smallContrastUnitBall d)).toReal := Real.sq_sqrt hV.le
  have hDdsq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt hdpos.le
  have hsqrtGrad : Real.sqrt (agmonTailCutoffGradientBound d r *
      agmonTailLayerVolume d r) =
      16 * smoothTransitionProfile.derivBound * (d : ℝ) * Real.sqrt (d : ℝ) *
        Real.sqrt ((volume (smallContrastUnitBall d)).toReal) *
        Real.sqrt (r ^ d) / r :=
    sqrt_agmonTailCutoffGradientBound_mul_layerVolume (d := d) hr
  have hsqrtMass : Real.sqrt (8 * Lam ^ 2 / (L ^ 2 * T ^ 2) *
      agmonTailCutoffGradientBound d r * agmonTailLayerVolume d r) =
      2 * Real.sqrt 2 * Lam / (L * T) *
        (16 * smoothTransitionProfile.derivBound * (d : ℝ) * Real.sqrt (d : ℝ) *
          Real.sqrt ((volume (smallContrastUnitBall d)).toReal) *
          Real.sqrt (r ^ d) / r) :=
    sqrt_eight_mul_sq_div_mul_agmon_layer hLam hLpos hTpos hr
  have hrHalf : r ^ ((d : ℝ) / 2) = Real.sqrt (r ^ d) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast r d,
      ← Real.rpow_mul hr.le]
    congr 1
    ring
  have hr₀Half : r₀ ^ ((d : ℝ) / 2) = Real.sqrt (r₀ ^ d) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast r₀ d,
      ← Real.rpow_mul hr₀.le]
    congr 1
    ring
  have hratio : T * r / (2 * (T * r₀)) = r / (2 * r₀) := by
    field_simp
  have hforce : r₀ ^ (2 - alpha) * (r₀ / 2 : ℝ) ^ alpha =
      r₀ ^ 2 * (1 / 2 : ℝ) ^ alpha := by
    have hr₀0 : (0 : ℝ) ≤ r₀ := hr₀.le
    rw [show (r₀ / 2 : ℝ) = r₀ * (1 / 2) by ring,
      Real.mul_rpow hr₀0 (by norm_num), Real.rpow_sub hr₀]
    have hp : 0 < r₀ ^ alpha := Real.rpow_pos_of_pos hr₀ alpha
    field_simp
    rw [Real.rpow_two]
  have hgradPower (E : ℝ) :
      r₀ ^ (1 - alpha - (d : ℝ) / 2) * E * (r₀ / 2 : ℝ) ^ alpha =
        r₀ ^ (1 - (d : ℝ) / 2) * (1 / 2 : ℝ) ^ alpha * E := by
    calc
      r₀ ^ (1 - alpha - (d : ℝ) / 2) * E * (r₀ / 2 : ℝ) ^ alpha =
          (r₀ ^ (1 - alpha - (d : ℝ) / 2) *
            (r₀ / 2 : ℝ) ^ alpha) * E := by ring
      _ = r₀ ^ (1 - (d : ℝ) / 2) * (1 / 2 : ℝ) ^ alpha * E := by
        rw [rpow_shift_frozen (d := d) hr₀]
  have hforcePower (G : ℝ) :
      r₀ ^ (2 - alpha) * G * (r₀ / 2 : ℝ) ^ alpha =
        r₀ ^ 2 * (1 / 2 : ℝ) ^ alpha * G := by
    calc
      r₀ ^ (2 - alpha) * G * (r₀ / 2 : ℝ) ^ alpha =
          (r₀ ^ (2 - alpha) * (r₀ / 2 : ℝ) ^ alpha) * G := by ring
      _ = r₀ ^ 2 * (1 / 2 : ℝ) ^ alpha * G := by rw [hforce]
  have hholderPower (E G : ℝ) :
      smallContrastZerothSchauderConstant d *
          (r₀ ^ (1 - alpha - (d : ℝ) / 2) * E +
            r₀ ^ (2 - alpha) * G) * (r₀ / 2 : ℝ) ^ alpha =
        smallContrastZerothSchauderConstant d *
          (r₀ ^ (1 - (d : ℝ) / 2) * (1 / 2 : ℝ) ^ alpha * E +
            r₀ ^ 2 * (1 / 2 : ℝ) ^ alpha * G) := by
    calc
      _ = smallContrastZerothSchauderConstant d *
          ((r₀ ^ (1 - alpha - (d : ℝ) / 2) * E) *
              (r₀ / 2 : ℝ) ^ alpha +
            (r₀ ^ (2 - alpha) * G) * (r₀ / 2 : ℝ) ^ alpha) := by ring
      _ = _ := by rw [hgradPower E, hforcePower G]
  have hsqrtLocal : Real.sqrt ((r₀ / 2) ^ d) =
      Real.sqrt (r₀ ^ d) / Real.sqrt ((2 : ℝ) ^ d) := by
    rw [div_pow, Real.sqrt_div (pow_nonneg hr₀.le d)]
  have hrShift : r ^ ((d : ℝ) / 2 - 1) = Real.sqrt (r ^ d) / r := by
    rw [Real.rpow_sub hr, Real.rpow_one, hrHalf]
  have hr₀Shift : r₀ ^ ((d : ℝ) / 2 - 1) = Real.sqrt (r₀ ^ d) / r₀ := by
    rw [Real.rpow_sub hr₀, Real.rpow_one, hr₀Half]
  have h2Half : (2 : ℝ) ^ ((d : ℝ) / 2) = Real.sqrt ((2 : ℝ) ^ d) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (2 : ℝ) d,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have h2Shift : (2 : ℝ) ^ ((d : ℝ) / 2 - 1) =
      Real.sqrt ((2 : ℝ) ^ d) / 2 := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one, h2Half]
  have hr₀InvShift : r₀ ^ (1 - (d : ℝ) / 2) =
      r₀ / Real.sqrt (r₀ ^ d) := by
    rw [Real.rpow_sub hr₀, Real.rpow_one, hr₀Half]
  have h2PowSq : Real.sqrt ((2 : ℝ) ^ d) ^ 2 = (2 : ℝ) ^ d :=
    Real.sq_sqrt (pow_nonneg (by norm_num) d)
  simp only [agmonFrozenDecayConstant, agmonTailGradientSize,
    agmonTailL2Coefficient, agmonTailGradientCoefficient,
    agmonTailForcingCoefficient]
  rw [hsqrtMass, hsqrtGrad, hT, hL, hratio,
    rpow_ratio_frozen hr hr₀, rpow_ratio_frozen hr hr₀,
    hsqrtLocal, hholderPower, hrHalf, hr₀Half]
  rw [hrShift, hr₀Shift, hr₀InvShift, h2Half, h2Shift]
  have h2half : (0 : ℝ) < (2 : ℝ) ^ ((d : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h2shift : (0 : ℝ) < (2 : ℝ) ^ ((d : ℝ) / 2 - 1) :=
    Real.rpow_pos_of_pos (by norm_num) _
  field_simp
  ring_nf
  rw [h2PowSq]
  ring

/-! ### The scale-free identification of the pointwise constant -/

/-- The exponent of the pointwise estimate, read across the gap `3 r / 8`, is
the tail rate evaluated at `s = sqrt mu * r`. -/
theorem agmonRate_mul_eq (d : ℕ) {lam Lam mu r alpha : ℝ} (hlam : 0 < lam) :
    agmonRate lam Lam mu * alpha / (alpha + (d : ℝ) / 2) * (3 * r / 8) =
      agmonTailRate d lam Lam alpha * (Real.sqrt mu * r) := by
  unfold agmonRate agmonTailRate
  rw [Real.sqrt_mul hlam.le]
  ring

end DivergenceFormProcess.Decay
