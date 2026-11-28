/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Probability.Moments.Variance

/-! # Cauchy–Schwarz in expectation

The real `L²` inequality `∫|f·g| ≤ √(∫ f²)·√(∫ g²)`, read off Mathlib's Hölder inequality
`integral_mul_norm_le_Lp_mul_Lq` at exponents `2, 2`, and its cases against the constant `1`:
`(∫ f)² ≤ ν(univ)·∫ f²` on a finite measure, and `∫|f| ≤ √(∫ f²)` on a probability measure.
Mathlib's `L²` Cauchy–Schwarz is stated for inner products of `Lp` classes, and Jensen
(`ConvexOn.map_integral_le`) gives only the probability case of the second, so the real forms are
assembled once here.

Consumed by the drift `L²` energy bound (`DriftProcessPredictable`, at `ν = timeMeasure.restrict`),
the SDE-uniqueness drift estimate (`SDEUniqueness`, at `ν = volume.restrict (Ioc 0 s)`), and the
`L¹` bounds of the adapted quadratic variation (`AdaptedQuadraticVariation`).

The same inequality at the centred variables `X − E X`, `Y − E Y` is Cauchy–Schwarz for the
covariance, `cov(X, Y) ≤ √Var X · √Var Y` (`covariance_le_sqrt_mul_sqrt`). Expanding
`Var(X + Y)` makes the standard deviation subadditive (`sqrt_variance_add_le`). Mathlib has the
covariance calculus but neither inequality. Consumed by the standard-deviation principle and the
Gaussian VaR subadditivity.

## Main results

* `integral_abs_mul_le_sqrt_mul_sqrt`: `∫|f·g| ≤ √(∫ f²)·√(∫ g²)` for `f, g` in `L²(ν)`.
* `sq_integral_le_measureReal_mul`: `(∫ f)² ≤ ν(univ)·∫ f²` on a finite measure.
* `integral_abs_le_sqrt_integral_sq`: `∫|f| ≤ √(∫ f²)` on a probability measure.
* `covariance_le_sqrt_mul_sqrt`: `cov(X, Y) ≤ √Var X · √Var Y` for `X, Y` in `L²(P)`.
* `sqrt_variance_add_le`: `√Var(X + Y) ≤ √Var X + √Var Y` for `X, Y` in `L²(P)`.

## References

* [*QRM Exercise Book*][QRMExerciseBook], Ex. 8.11

## Tags

Cauchy–Schwarz inequality, Hölder inequality, covariance bound, standard deviation subadditivity,
L2 bound, MSC 60E15, MSC 28A25
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathFin

variable {α : Type*} {m : MeasurableSpace α} {ν : Measure α}

/-- **Cauchy–Schwarz in expectation**: `∫|f·g| ≤ √(∫ f²)·√(∫ g²)`, Hölder at exponents `2, 2`. -/
theorem integral_abs_mul_le_sqrt_mul_sqrt {f g : α → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ∫ a, |f a * g a| ∂ν ≤ √(∫ a, f a ^ 2 ∂ν) * √(∫ a, g a ^ 2 ∂ν) := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := ν) Real.HolderConjugate.two_two (f := f) (g := g)
    (by rwa [ENNReal.ofReal_ofNat]) (by rwa [ENNReal.ofReal_ofNat])
  have hsq (x : ℝ) : |x| ^ (2 : ℝ) = x ^ 2 := by rw [Real.rpow_two, sq_abs]
  simpa only [Real.norm_eq_abs, hsq, ← Real.sqrt_eq_rpow, ← abs_mul] using h

/-- **Cauchy–Schwarz on a finite measure**: `(∫ f)² ≤ ν(univ)·∫ f²`, the case `g ≡ 1`. -/
theorem sq_integral_le_measureReal_mul [IsFiniteMeasure ν] {f : α → ℝ} (hf : MemLp f 2 ν) :
    (∫ a, f a ∂ν) ^ 2 ≤ (ν Set.univ).toReal * ∫ a, (f a) ^ 2 ∂ν := by
  have h := integral_abs_mul_le_sqrt_mul_sqrt hf (memLp_const (1 : ℝ))
  simp only [mul_one, one_pow, integral_const, smul_eq_mul] at h
  calc (∫ a, f a ∂ν) ^ 2 = |∫ a, f a ∂ν| ^ 2 := (sq_abs _).symm
    _ ≤ (√(∫ a, f a ^ 2 ∂ν) * √(ν.real Set.univ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_integral_le_integral_abs.trans h) 2
    _ = (ν Set.univ).toReal * ∫ a, (f a) ^ 2 ∂ν := by
        rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
          Real.sq_sqrt measureReal_nonneg, mul_comm, measureReal_def]

/-- `∫|f| ≤ √(∫ f²)` on a probability measure, the case `g ≡ 1`. -/
theorem integral_abs_le_sqrt_integral_sq [IsProbabilityMeasure ν] {f : α → ℝ}
    (hf : MemLp f 2 ν) : ∫ a, |f a| ∂ν ≤ √(∫ a, f a ^ 2 ∂ν) := by
  simpa using integral_abs_mul_le_sqrt_mul_sqrt hf (memLp_const (1 : ℝ))

section Covariance

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X Y : Ω → ℝ}

/-- **Cauchy–Schwarz for covariance**: `cov(X, Y) ≤ √Var X · √Var Y`, the inequality
`integral_abs_mul_le_sqrt_mul_sqrt` for the centred variables. -/
theorem covariance_le_sqrt_mul_sqrt (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    cov[X, Y; P] ≤ √Var[X; P] * √Var[Y; P] := by
  rw [variance_eq_integral hX.aemeasurable, variance_eq_integral hY.aemeasurable]
  exact (le_abs_self _).trans <| abs_integral_le_integral_abs.trans <|
    integral_abs_mul_le_sqrt_mul_sqrt (hX.sub (memLp_const _)) (hY.sub (memLp_const _))

/-- **The standard deviation is subadditive**: `sd(X + Y) ≤ sd(X) + sd(Y)`. -/
theorem sqrt_variance_add_le (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    √Var[fun ω ↦ X ω + Y ω; P] ≤ √Var[X; P] + √Var[Y; P] := by
  rw [variance_fun_add hX hY]
  have hcs := covariance_le_sqrt_mul_sqrt hX hY
  refine Real.sqrt_le_iff.2 ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  nlinarith [Real.sq_sqrt (variance_nonneg X P), Real.sq_sqrt (variance_nonneg Y P)]

end Covariance

end MathFin
