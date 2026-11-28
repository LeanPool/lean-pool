/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Credit.CVA
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# DVA as a CVA mirror

Debt valuation adjustment is the counterparty's expected loss on the bank's *own* default, a gain
to the bank: `CVA.cva` applied to the bank's own default time and hazard and to the exposure seen
from the bank's side, `-V`. In `cva`'s convention `V > 0` means the counterparty owes the bank; the
bank owes the counterparty when `V < 0`, the regime `-V > 0`. On the bank's own default the
counterparty does not recover that liability in full, a loss to the counterparty booked as a gain
to the bank, whose liability is extinguished. The file defines `dva` from `cva` and derives its
integral and Gaussian forms from `cva`'s.

`cva`'s independence hypothesis (the default time independent of the exposure, no wrong-way risk)
carries over unchanged, read as "the bank's own default is independent of the exposure". The
bank's and the counterparty's default times are not jointly modelled, so nothing is stated about a
correlated bilateral picture (both defaults together, wrong-way risk on either leg); that needs
their joint law and is out of scope.

## Main definitions

* `expectedNegativeExposure`: `ENE(s) = E_ν[(−V_s)⁺]`, the mirror of `CVA.expectedExposure`: the
  expected exposure the counterparty has to the bank.
* `dva`: the bank's own-default mirror of `cva`, taken at the bank's own default time and hazard
  with the exposure `-V` seen from the bank's side.

## Main results

* `expectedNegativeExposure_eq_sub_integral`: `ENE(s) = EE(s) − E[V_s]` for integrable `V_s`, from
  the pointwise identity `(−x)⁺ = x⁺ − x`; `expectedNegativeExposure_gaussian` is its closed form
  for `V_s = a + b√s Z` with `Z ~ N(0, 1)`, `b > 0` and `s > 0`.
* `dva_eq_integral_expectedNegativeExposure`: with the bank's default independent of the
  exposure and a deterministic continuous hazard,
  `DVA = LGD_B · ∫₀ᵀ D(s) · ENE(s) · λ(s)Q(s) ds`, the integral of the expected negative exposure
  (`CVA.integral_exposure_eq` at `-V`).
* `dva_gaussian`: the Gaussian closed form, from `CVA.cva_gaussian` at the mirrored exposure
  `-(m(s) + σ(s)√s Z) = -m(s) + σ(s)√s·(-Z)`, with `gaussianReal_neg` keeping the driver standard
  normal.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull] (bilateral CVA/DVA).

## Tags

debt valuation adjustment, bilateral CVA, own default, expected negative exposure,
counterparty risk, credit adjustment, MSC 91G40, JEL G32
-/

@[expose] public section

namespace MathFin.CVA

open MeasureTheory Real ProbabilityTheory MathFin.DefaultDensity

variable {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
  {ν : Measure Ω₁} {μ : Measure Ω₂}

/-- Expected negative exposure `ENE(s) = E_ν[(-V_s)⁺]`, the mirror of `expectedExposure`. -/
noncomputable def expectedNegativeExposure (V : ℝ → Ω₁ → ℝ) (ν : Measure Ω₁) (s : ℝ) : ℝ :=
  ∫ ω, max (-(V s ω)) 0 ∂ν

/-- **ENE = EE − E[V]**: for `V_s` integrable, from `(-x)⁺ = x⁺ - x` pointwise and integral
linearity. -/
theorem expectedNegativeExposure_eq_sub_integral {V : ℝ → Ω₁ → ℝ} {s : ℝ}
    (hV : Integrable (V s) ν) :
    expectedNegativeExposure V ν s = expectedExposure V ν s - ∫ ω, V s ω ∂ν := by
  rw [expectedNegativeExposure, expectedExposure, ← integral_sub hV.pos_part hV]
  congr with ω
  linarith [max_zero_sub_max_neg_zero_eq_self (V s ω)]

/-- **Gaussian expected negative exposure**: for `Z ~ N(0,1)`, `s > 0`, `b > 0`,
`E[(a + b√s Z)⁻] = E[(a+b√s Z)⁺] - a`, specializing `expectedNegativeExposure_eq_sub_integral`
to the exposure model of `CVA.expectedExposure_gaussian`, since `E[a + b√s Z] = a`. -/
theorem expectedNegativeExposure_gaussian [IsProbabilityMeasure ν] {Z : Ω₁ → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) ν) {a b s : ℝ} (hb : 0 < b) (hs : 0 < s) :
    expectedNegativeExposure (fun s ω ↦ a + b * √s * Z ω) ν s
      = a * Phi (a / (b * √s)) + b * √s * gaussianPDFReal 0 1 (a / (b * √s)) - a := by
  have hZi : Integrable Z ν := hZ.hasGaussianLaw.integrable
  have hVi : Integrable (fun ω ↦ a + b * √s * Z ω) ν :=
    (integrable_const a).add (hZi.const_mul (b * √s))
  have hmean : ∫ ω, (a + b * √s * Z ω) ∂ν = a := by
    rw [(gaussianReal_const_add (gaussianReal_const_mul hZ (b * √s)) a).integral_eq,
      integral_id_gaussianReal]
    ring
  rw [expectedNegativeExposure_eq_sub_integral hVi, hmean, expectedExposure,
    expectedExposure_gaussian hZ hb hs]

/-- **DVA**: the bank's own-default mirror of `cva`, at the bank's own default time `τBank` and
the exposure `-V` seen from the bank's side. Default is independent of the exposure because `cva`
is an integral over the product measure `ν.prod μ`. -/
noncomputable def dva (LGDBank : ℝ) (D : ℝ → ℝ) (V : ℝ → Ω₁ → ℝ) (τBank : Ω₂ → ℝ) (T : ℝ)
    (ν : Measure Ω₁) (μ : Measure Ω₂) : ℝ :=
  cva LGDBank D (fun s ω ↦ -(V s ω)) τBank T ν μ

/-- **DVA is the integral of the expected negative exposure**: with the bank's default time
`τBank` of deterministic continuous hazard `h ≥ 0` (CDF hypothesis `hcdf`), measurable `D`,
jointly measurable `V`, `T ≥ 0` and the integrand jointly integrable,
`DVA = LGD_B · ∫₀ᵀ D(s) · ENE(s) · λ(s)Q(s) ds`. This is `integral_exposure_eq` at `-V`, whose
expected exposure is `expectedNegativeExposure V`. -/
theorem dva_eq_integral_expectedNegativeExposure [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] {h : ℝ → ℝ} (hh : Continuous h) (hnn : ∀ s, 0 ≤ h s)
    {τBank : Ω₂ → ℝ} (hτ : Measurable τBank)
    (hcdf : ∀ a, 0 ≤ a → μ {ω | τBank ω ≤ a} = 1 - ENNReal.ofReal (hazardSurvival h a))
    {D : ℝ → ℝ} (hD : Measurable D) {V : ℝ → Ω₁ → ℝ} (hV : Measurable (Function.uncurry V))
    (LGDBank : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hint : Integrable (fun p : Ω₁ × Ω₂ ↦
      (Set.Iic T).indicator D (τBank p.2) * max (-V (τBank p.2) p.1) 0) (ν.prod μ)) :
    dva LGDBank D V τBank T ν μ
      = LGDBank * ∫ s in (0:ℝ)..T, D s * expectedNegativeExposure V ν s * defaultDensity h s :=
  congrArg (LGDBank * ·)
    (integral_exposure_eq (V := fun s ω ↦ -(V s ω)) hh hnn hτ hcdf hD hV.neg hT hint)

/-- **DVA with Gaussian exposure, no wrong-way risk**: `dva` equals `LGDBank · ∫₀..T D(s) ·
[(-m(s))·Φ((-m(s))/(σ(s)√s)) + σ(s)√s·φ((-m(s))/(σ(s)√s))] · defaultDensity h s ds` —
`cva_gaussian`'s right-hand side with `m` replaced by `-m`, from `cva_gaussian` at the mirrored
exposure `-(m(s) + σ(s)√s Z) = -m(s) + σ(s)√s·(-Z)`; `gaussianReal_neg` keeps the driver `-Z`
standard normal. -/
theorem dva_gaussian [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {h : ℝ → ℝ} (hh : Continuous h) (hnn : ∀ s, 0 ≤ h s) {τBank : Ω₂ → ℝ}
    (hτ : Measurable τBank)
    (hcdf : ∀ a, 0 ≤ a → μ {ω | τBank ω ≤ a} = 1 - ENNReal.ofReal (hazardSurvival h a))
    {D : ℝ → ℝ} (hD : Measurable D) {C : ℝ} (hDb : ∀ s, |D s| ≤ C) {m σ : ℝ → ℝ}
    (hm : Measurable m) (hσ : Measurable σ) {M S : ℝ} (hmb : ∀ s, |m s| ≤ M)
    (hσpos : ∀ s, 0 < σ s) (hσb : ∀ s, σ s ≤ S) {Z : Ω₁ → ℝ} (hZm : Measurable Z)
    (hZ : HasLaw Z (gaussianReal 0 1) ν) (LGDBank : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    dva LGDBank D (fun s ω ↦ m s + σ s * √s * Z ω) τBank T ν μ
      = LGDBank * ∫ s in (0:ℝ)..T, D s * ((-m s) * Phi ((-m s) / (σ s * √s))
          + σ s * √s * gaussianPDFReal 0 1 ((-m s) / (σ s * √s))) * defaultDensity h s := by
  have hZ' : HasLaw (fun ω ↦ -(Z ω)) (gaussianReal 0 1) ν :=
    (neg_zero : -(0:ℝ) = 0) ▸ gaussianReal_neg hZ
  have heq : (fun s ω ↦ -(m s + σ s * √s * Z ω)) = fun s ω ↦ (-m s) + σ s * √s * (-(Z ω)) := by
    funext s ω; ring
  have hmb' : ∀ s, |(-m s)| ≤ M := fun s ↦ (abs_neg (m s)).le.trans (hmb s)
  rw [dva, heq]
  exact cva_gaussian hh hnn hτ hcdf hD hDb hm.neg hσ hmb' hσpos hσb hZm.neg hZ' LGDBank hT

end MathFin.CVA
