/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Standard normal primitives: CDF, tail, and the Gaussian MGF

The pricing-independent core of the Black–Scholes computation: the standard
normal CDF `Φ`, its symmetry and tail identities, the completing-the-square
shift, and the moment-generating function `∫ exp(c·z) ∂N(0,1) = exp(c²/2)`.

These are **foundations**, not pricing: every closed-form Gaussian
expectation in the BS family (`Call`, `Forward`, the Greeks, the lognormal
moments) reduces to the four lemmas below. They previously lived inside
`Models/BlackScholes/Call.lean` and `Models/BlackScholes/Forward.lean`, which forced the
*Foundations* files that need them (`GaussianCDFDeriv`, `StandardGaussianMGF`)
to import the pricing layer — a layering inversion. Hoisting them here lets
`Call`/`Forward` and the Foundations Gaussian files all build on a common,
pricing-free base.

## Main definitions

* `Phi`: the standard normal CDF, `Φ(x) = P(Z ≤ x)` for `Z ~ N(0, 1)`, as the real value of
  `gaussianReal 0 1 (Iic x)`.

## Main results

* `Phi_neg`, `Phi_add_Phi_neg`, `Phi_le_one`, `Phi_eq_integral` — the reflection `Φ(−x) = 1 − Φ(x)`,
  the bound `Φ ≤ 1`, and `Φ` as an integral of the density.
* `setIntegral_gaussianPDFReal_eq_toReal` — the `∫ pdf = N(s).toReal` bridge
  every closed-form Gaussian integral factors through.
* `gaussianPDFReal_zero_one_neg` — evenness of the standard-normal density
  `ϕ(-z) = ϕ(z)`; `continuous_gaussianPDFReal` — a Gaussian density is continuous.
* `gaussianReal_Ioi_toReal` — the right tail `Q(Ioi a) = Φ(-a)`.
* `exp_mul_gaussianPDFReal_zero_one` — the completing-the-square shift.
* `integral_exp_mul_gaussianPDFReal_Ioi` — the shifted Gaussian tail integral
  `∫_{Ioi a} exp(c·z)·pdf = exp(c²/2)·Φ(c − a)` (the asset-payoff primitive).
* `integral_exp_mul_gaussianPDFReal_univ` — the standard-normal MGF
  `∫ exp(c·z)·pdf = exp(c²/2)`.

## Tags

standard normal CDF, Gaussian tail, moment generating function, completing the square,
normal distribution function, Black–Scholes building block, MSC 60E05, MSC 60E10, MSC 91G20
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-! ### Standard normal CDF -/

/-- The standard normal cumulative distribution function `Φ(x) = P(Z ≤ x)`
where `Z ~ N(0, 1)`. -/
noncomputable def Phi (x : ℝ) : ℝ :=
  (gaussianReal 0 1 (Set.Iic x)).toReal

lemma Phi_def (x : ℝ) : Phi x = (gaussianReal 0 1 (Set.Iic x)).toReal := rfl

lemma Phi_nonneg (x : ℝ) : 0 ≤ Phi x := ENNReal.toReal_nonneg

/-- The set-integral of the standard-normal density over a measurable set `s`
equals the (real) Gaussian measure of `s`: `∫_{z ∈ s} ϕ(μ,1,z) dz = N(μ,1)(s)`.
The `.toReal`-of-`gaussianReal` bridge that every closed-form Gaussian integral
factors through (`Phi_eq_integral`, the call/put/digital tails, the MGF shift). -/
lemma setIntegral_gaussianPDFReal_eq_toReal {s : Set ℝ} (hs : MeasurableSet s) (μ : ℝ) :
    ∫ z in s, gaussianPDFReal μ 1 z = (gaussianReal μ 1 s).toReal := by
  rw [gaussianReal_apply_eq_integral μ (one_ne_zero : (1 : ℝ≥0) ≠ 0) s]
  exact (ENNReal.toReal_ofReal (setIntegral_nonneg hs
    (fun _ _ ↦ gaussianPDFReal_nonneg _ _ _))).symm

/-- `Φ(x)` as the Lebesgue integral of the standard-normal density over `(-∞, x]`. -/
lemma Phi_eq_integral (x : ℝ) :
    Phi x = ∫ z in Set.Iic x, gaussianPDFReal 0 1 z := by
  rw [Phi_def, setIntegral_gaussianPDFReal_eq_toReal measurableSet_Iic (0 : ℝ)]

/-- `Φ(-x) = 1 − Φ(x)`. Symmetry of the standard normal around 0. -/
lemma Phi_neg (x : ℝ) : Phi (-x) = 1 - Phi x := by
  -- Standard normal is symmetric: gaussianReal 0 1 is invariant under negation
  have hmap : (gaussianReal (0 : ℝ) 1).map (fun y ↦ -y) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  -- Iic(-x) under negation pulls back to Ici x
  have h_preimage : (fun y : ℝ ↦ -y) ⁻¹' Set.Iic (-x) = Set.Ici x := by
    ext y; simp [Set.mem_Ici]
  -- gaussianReal 0 1 (Iic(-x)) = gaussianReal 0 1 (Ici x)
  have h_eq : gaussianReal (0 : ℝ) 1 (Set.Iic (-x)) = gaussianReal 0 1 (Set.Ici x) := by
    conv_lhs => rw [← hmap]
    rw [Measure.map_apply measurable_neg measurableSet_Iic, h_preimage]
  -- Ici x and Iio x partition univ; under NullSingletonClass, Q(Iio x) = Q(Iic x)
  have h_one_nz : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have : NullSingletonClass (gaussianReal (0 : ℝ) 1) :=
    nullSingletonClass_gaussianReal h_one_nz
  have h_iio_iic : gaussianReal (0 : ℝ) 1 (Set.Iic x) = gaussianReal 0 1 (Set.Iio x) := by
    have h_decomp : Set.Iic x = Set.Iio x ∪ {x} := by
      ext y; simp [Set.mem_Iic, le_iff_lt_or_eq, eq_comm]
    have h_disj : Disjoint (Set.Iio x) ({x} : Set ℝ) :=
      Set.disjoint_singleton_right.mpr (lt_irrefl x)
    rw [h_decomp, measure_union h_disj (measurableSet_singleton _),
        measure_singleton, add_zero]
  have h_total : gaussianReal (0 : ℝ) 1 (Set.Iio x) + gaussianReal 0 1 (Set.Ici x)
      = 1 := by
    rw [← measure_union (Set.Iio_disjoint_Ici le_rfl) measurableSet_Ici,
        Set.Iio_union_Ici, measure_univ]
  -- gaussianReal 0 1 (Iic(-x)) = gaussianReal 0 1 (Ici x) = 1 - gaussianReal 0 1 (Iic x)
  rw [Phi_def, h_eq, Phi_def]
  have h_iic_finite : gaussianReal (0 : ℝ) 1 (Set.Iic x) ≠ ⊤ := (measure_lt_top _ _).ne
  have h_sum : gaussianReal (0 : ℝ) 1 (Set.Iic x) + gaussianReal 0 1 (Set.Ici x) = 1 := by
    rw [h_iio_iic]; exact h_total
  have h_eq_sub : gaussianReal (0 : ℝ) 1 (Set.Ici x) = 1 - gaussianReal 0 1 (Set.Iic x) := by
    refine ENNReal.eq_sub_of_add_eq h_iic_finite ?_
    rw [add_comm]; exact h_sum
  rw [h_eq_sub, ENNReal.toReal_sub_of_le (by
        rw [show (1 : ℝ≥0∞) = gaussianReal (0 : ℝ) 1 Set.univ from measure_univ.symm]
        exact measure_mono (Set.subset_univ _)) (by simp)]
  rfl

/-- `Φ(x) + Φ(-x) = 1`. -/
lemma Phi_add_Phi_neg (x : ℝ) : Phi x + Phi (-x) = 1 := by
  rw [Phi_neg]; ring

/-- **Standard normal CDF upper bound** `Φ(x) ≤ 1`, from `Φ(x) + Φ(-x) = 1`
and `Φ(-x) ≥ 0`. The pricing-free home of the bound used across the BS price
rectangle (`PriceBounds`) and the KMV-Merton default probability (`KMVMerton`). -/
lemma Phi_le_one (x : ℝ) : Phi x ≤ 1 := by
  have h_sum : Phi x + Phi (-x) = 1 := Phi_add_Phi_neg x
  have h_neg : 0 ≤ Phi (-x) := Phi_nonneg _
  linarith

/-- **Standard normal PDF evenness**: `ϕ(-z) = ϕ(z)`, since the density depends
on `z` only through `z²`. Model-agnostic — consumed by the Greeks and the
put-strike convexity. -/
lemma gaussianPDFReal_zero_one_neg (z : ℝ) :
    gaussianPDFReal 0 1 (-z) = gaussianPDFReal 0 1 z := by
  unfold gaussianPDFReal
  congr 2
  ring

/-- A Gaussian density is continuous. -/
lemma continuous_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) : Continuous (gaussianPDFReal μ v) := by
  rw [gaussianPDFReal_def]
  fun_prop

/-! ### Tail probabilities of the standard normal -/

/-- `Q(Ioi a) = 1 − Φ(a) = Φ(-a)`. The right tail of the standard normal. -/
lemma gaussianReal_Ioi_toReal (a : ℝ) :
    (gaussianReal 0 1 (Set.Ioi a)).toReal = Phi (-a) := by
  have h_compl : Set.Ioi a = (Set.Iic a)ᶜ := by ext y; simp
  rw [h_compl, prob_compl_eq_one_sub measurableSet_Iic]
  rw [ENNReal.toReal_sub_of_le (by
        rw [show (1 : ℝ≥0∞) = gaussianReal (0 : ℝ) 1 Set.univ from measure_univ.symm]
        exact measure_mono (Set.subset_univ _)) (by simp)]
  rw [Phi_neg, ENNReal.toReal_one, Phi_def]

/-! ### Completing the square -/

/-- The exponential shift identity: `exp(c·z) · gaussianPDFReal 0 1 z =
exp(c²/2) · gaussianPDFReal c 1 z`. This is the algebraic content of
"completing the square" `c·z − z²/2 = c²/2 − (z − c)²/2`. -/
lemma exp_mul_gaussianPDFReal_zero_one (c z : ℝ) :
    Real.exp (c * z) * gaussianPDFReal 0 1 z =
      Real.exp (c^2 / 2) * gaussianPDFReal c 1 z := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one]
  have key : c * z + -(z - 0)^2 / 2 = c^2 / 2 + -(z - c)^2 / 2 := by ring
  set P : ℝ := (Real.sqrt (2 * π))⁻¹ with P_def
  calc Real.exp (c * z) * ((Real.sqrt (2 * π))⁻¹ * Real.exp (-(z - 0)^2 / 2))
      = P * (Real.exp (c * z) * Real.exp (-(z - 0)^2 / 2)) := by rw [P_def]; ring
    _ = P * Real.exp (c * z + -(z - 0)^2 / 2) := by rw [Real.exp_add]
    _ = P * Real.exp (c^2 / 2 + -(z - c)^2 / 2) := by rw [key]
    _ = P * (Real.exp (c^2 / 2) * Real.exp (-(z - c)^2 / 2)) := by rw [Real.exp_add]
    _ = Real.exp (c^2 / 2) * ((Real.sqrt (2 * π))⁻¹ * Real.exp (-(z - c)^2 / 2)) := by
        rw [P_def]; ring

/-- The shifted Gaussian tail integral — the core BS computational primitive:
  `∫ z in Ioi a, exp(c·z) · gaussianPDFReal 0 1 z dz = exp(c²/2) · Φ(c − a)`.

Combines `exp_mul_gaussianPDFReal_zero_one` (algebraic completing-the-square)
with `gaussianReal_map_add_const` (push forward via shift). -/
lemma integral_exp_mul_gaussianPDFReal_Ioi (a c : ℝ) :
    ∫ z in Set.Ioi a, Real.exp (c * z) * gaussianPDFReal 0 1 z
      = Real.exp (c^2 / 2) * Phi (c - a) := by
  rw [setIntegral_congr_fun measurableSet_Ioi
        (fun z _ ↦ exp_mul_gaussianPDFReal_zero_one c z), integral_const_mul]
  congr 1
  have h_int_eq : ∫ z in Set.Ioi a, gaussianPDFReal c 1 z
      = (gaussianReal c (1 : ℝ≥0) (Set.Ioi a)).toReal :=
    setIntegral_gaussianPDFReal_eq_toReal measurableSet_Ioi c
  have h_shift : gaussianReal c (1 : ℝ≥0) (Set.Ioi a) =
                 gaussianReal 0 1 (Set.Ioi (a - c)) := by
    have hmap : (gaussianReal (0 : ℝ) 1).map (fun y ↦ y + c) = gaussianReal c 1 := by
      rw [gaussianReal_map_add_const, zero_add]
    rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Ioi]
    congr 1; ext y; simp [Set.mem_Ioi, sub_lt_iff_lt_add, add_comm]
  rw [h_int_eq, h_shift, gaussianReal_Ioi_toReal, neg_sub]

/-! ### Standard-normal moment generating function -/

/-- **MGF of the standard normal**: `∫ z, exp(c·z) · pdf(0,1,z) dz = exp(c²/2)`.

Combines `exp_mul_gaussianPDFReal_zero_one` (completing-the-square) with
Mathlib's `integral_gaussianPDFReal_eq_one`.

Mathlib's `mgf_gaussianReal` gives the same value as an integral against the
`gaussianReal` *measure*; this is the explicit Lebesgue/pdf form the Black–Scholes
integrals consume directly, and the completing-the-square shift it factors through
(`exp_mul_gaussianPDFReal_zero_one`) plus the truncated `Ioi` sibling above are the
load-bearing primitives with no Mathlib analogue. -/
lemma integral_exp_mul_gaussianPDFReal_univ (c : ℝ) :
    ∫ z, Real.exp (c * z) * gaussianPDFReal 0 1 z = Real.exp (c^2 / 2) := by
  rw [show (fun z ↦ Real.exp (c * z) * gaussianPDFReal 0 1 z)
        = (fun z ↦ Real.exp (c^2 / 2) * gaussianPDFReal c 1 z) from
      funext (exp_mul_gaussianPDFReal_zero_one c),
      integral_const_mul,
      integral_gaussianPDFReal_eq_one c (one_ne_zero : (1 : ℝ≥0) ≠ 0), mul_one]

end MathFin
