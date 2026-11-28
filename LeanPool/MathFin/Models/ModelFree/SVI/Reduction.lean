/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.Order.Star.Real

/-! # Raw SVI and the rationalised Durrleman condition

Part of the SVI polynomial-sign certificate (#174).

Rationalization of the smooth raw-SVI Durrleman expression.
The first and second slope expressions are explicit; their identification with
analytic derivatives is proved in Derivatives.lean.

## Main definitions

* `Params`: the five raw SVI parameters `(a, b, ρ, m, σ)`, with no sign conditions built in.
* `variance`: raw SVI total variance `a + b(ρ(k - m) + √((k - m)² + σ²))` at log-strike `k`.
* `slope`, `curvature`: the explicit first and second derivatives of `variance`.
* `durrleman`: Durrleman's function `(1 - k w'/(2w))² - (w'²/4)(1/w + 1/4) + w''/2`.
* `strike`: the log-strike `K p t / (2t)` parametrised by `t > 0`.
* `numerator`: the rationalised Durrleman numerator, a polynomial in `t`.

## Main results

* `variance_at_strike`, `slope_at_strike`, `curvature_at_strike`: for `σ > 0` and `t > 0`, the
  values of `variance`, `slope` and `curvature` at `strike p t`.
* `durrleman_at_strike`: for `σ > 0`, `t > 0` and `A p t ≠ 0`,
  `durrleman p (strike p t) = numerator p t / (16σ (A p t)² (D t)³)`.
* `sign_at_strike`: for `σ > 0` and positive variance at `strike p t`,
  `durrleman p (strike p t) ≥ 0` iff `numerator p t ≥ 0`.
* `strike_surjective`: for `σ > 0`, every `k` is `strike p t` for some `t > 0`.
* `durrleman_nonneg_iff`: for `σ > 0` and positive variance everywhere, `durrleman p k ≥ 0` for all
  `k` iff `numerator p t ≥ 0` for all `t > 0`.

## Tags

raw SVI, Durrleman condition, rationalization, variance slope, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI

/-- The five parameters `(a, b, ρ, m, σ)` of a raw SVI slice. No sign conditions are built in. -/
structure Params where
  /-- The level `a`. -/
  a : ℝ
  /-- The wing scale `b`. -/
  b : ℝ
  /-- The skew `ρ`. -/
  rho : ℝ
  /-- The centre `m`. -/
  m : ℝ
  /-- The curvature scale `σ`. -/
  sigma : ℝ

/-- Raw SVI total variance `w(k) = a + b(ρ(k − m) + √((k − m)² + σ²))` at log-strike `k`. -/
noncomputable def variance (p : Params) (k : ℝ) : ℝ :=
  p.a + p.b * (p.rho * (k - p.m) + Real.sqrt ((k - p.m)^2 + p.sigma^2))
/-- The explicit first derivative `w'(k)` (`Derivatives.variance_hasDerivAt`, for `σ > 0`). -/
noncomputable def slope (p : Params) (k : ℝ) : ℝ :=
  p.b * (p.rho + (k - p.m) / Real.sqrt ((k - p.m)^2 + p.sigma^2))
/-- The explicit second derivative `w''(k)` (`Derivatives.slope_hasDerivAt`, for `σ > 0`). -/
noncomputable def curvature (p : Params) (k : ℝ) : ℝ :=
  p.b * p.sigma^2 / (Real.sqrt ((k - p.m)^2 + p.sigma^2))^3
/-- Durrleman's function `g = (1 − k w'/(2w))² − (w'²/4)(1/w + 1/4) + w''/2`. It is meaningful
only where `w(k) > 0`: division by zero is `0` in Lean. -/
noncomputable def durrleman (p : Params) (k : ℝ) : ℝ :=
  (1 - k * slope p k / (2 * variance p k))^2 -
    (slope p k)^2 / 4 * (1 / variance p k + 1 / 4) + curvature p k / 2

/-- The rationalising factor `1 + t²`. -/
def D (t : ℝ) : ℝ := 1 + t^2
/-- The numerator of the variance in the parameter `t`: `w = A/(2t)` at `strike p t`. -/
def A (p : Params) (t : ℝ) : ℝ :=
  p.b * p.sigma * (1 + p.rho) * t^2 + 2 * p.a * t + p.b * p.sigma * (1 - p.rho)
/-- The numerator of the slope in the parameter `t`: `w' = B/D` at `strike p t`. -/
def B (p : Params) (t : ℝ) : ℝ :=
  p.b * ((1 + p.rho) * t^2 - (1 - p.rho))
/-- The numerator of the log-strike in the parameter `t`. -/
def K (p : Params) (t : ℝ) : ℝ := p.sigma * t^2 + 2 * p.m * t - p.sigma
/-- The log-strike `K p t/(2t)` parametrised by `t > 0`. -/
noncomputable def strike (p : Params) (t : ℝ) : ℝ := K p t / (2 * t)
/-- The rationalised Durrleman numerator, a polynomial in `t` with the sign of `g` at `strike p t`
(`sign_at_strike`). -/
def numerator (p : Params) (t : ℝ) : ℝ :=
  4 * p.sigma * D t * (2 * A p t * D t - K p t * B p t)^2 -
    p.sigma * A p t * (B p t)^2 * D t * (A p t + 8*t) +
    64 * p.b * t^3 * (A p t)^2

theorem D_pos (t : ℝ) : 0 < D t := by unfold D; positivity

theorem sqrt_at_strike (p : Params) (hs : 0 < p.sigma) (t : ℝ) (ht : 0 < t) :
    Real.sqrt ((strike p t - p.m)^2 + p.sigma^2) = p.sigma * D t / (2*t) := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity)
    (le_of_lt (div_pos (mul_pos hs (D_pos t)) (by positivity)))).mpr
  unfold strike K D
  field_simp
  ring

theorem variance_at_strike (p : Params) (hs : 0 < p.sigma) (t : ℝ) (ht : 0 < t) :
    variance p (strike p t) = A p t / (2*t) := by
  unfold variance
  rw [sqrt_at_strike p hs t ht]
  unfold strike K D A
  field_simp
  ring

theorem slope_at_strike (p : Params) (hs : 0 < p.sigma) (t : ℝ) (ht : 0 < t) :
    slope p (strike p t) = B p t / D t := by
  unfold slope
  rw [sqrt_at_strike p hs t ht]
  have hd := ne_of_gt (D_pos t)
  unfold strike K B
  field_simp [ne_of_gt hs, ne_of_gt ht, hd]
  unfold D
  ring

theorem curvature_at_strike (p : Params) (hs : 0 < p.sigma) (t : ℝ) (ht : 0 < t) :
    curvature p (strike p t) = 8 * p.b * t^3 / (p.sigma * (D t)^3) := by
  unfold curvature
  rw [sqrt_at_strike p hs t ht]
  field_simp
  ring

theorem durrleman_at_strike (p : Params) (hs : 0 < p.sigma) (t : ℝ)
    (ht : 0 < t) (ha : A p t ≠ 0) :
    durrleman p (strike p t) = numerator p t / (16*p.sigma*(A p t)^2*(D t)^3) := by
  unfold durrleman
  rw [variance_at_strike p hs t ht, slope_at_strike p hs t ht,
    curvature_at_strike p hs t ht]
  unfold strike numerator
  field_simp [ha, ne_of_gt ht, ne_of_gt hs, ne_of_gt (D_pos t)]
  ring

theorem sign_at_strike (p : Params) (hs : 0 < p.sigma) (t : ℝ)
    (ht : 0 < t) (hw : 0 < variance p (strike p t)) :
    0 ≤ durrleman p (strike p t) ↔ 0 ≤ numerator p t := by
  rw [variance_at_strike p hs t ht] at hw
  have ha : 0 < A p t := (div_pos_iff.mp hw).resolve_right (by intro h; linarith [h.2]) |>.1
  rw [durrleman_at_strike p hs t ht (ne_of_gt ha)]
  have hd := D_pos t
  exact (le_div_iff₀ (by positivity)).trans (by simp)

/-- Every finite strike is represented by a positive parameter. -/
theorem strike_surjective (p : Params) (hs : 0 < p.sigma) (k : ℝ) :
    ∃ t : ℝ, 0 < t ∧ strike p t = k := by
  let y := (k - p.m) / p.sigma
  let z := Real.sqrt (1 + y^2)
  have hz : z^2 = 1 + y^2 := Real.sq_sqrt (by positivity)
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have ht : 0 < y + z := by nlinarith
  refine ⟨y + z, ht, ?_⟩
  have hy : p.sigma * y = k - p.m := by dsimp [y]; field_simp
  unfold strike K
  apply (div_eq_iff (by positivity : 2 * (y + z) ≠ 0)).mpr
  nlinarith [sq_nonneg (y + z)]

/-- The SVI-specific global reduction, including non-generic parameters. -/
theorem durrleman_nonneg_iff (p : Params) (hs : 0 < p.sigma)
    (hw : ∀ k : ℝ, 0 < variance p k) :
    (∀ k : ℝ, 0 ≤ durrleman p k) ↔ (∀ t : ℝ, 0 < t → 0 ≤ numerator p t) := by
  constructor
  · intro h t ht
    exact (sign_at_strike p hs t ht (hw _)).mp (h _)
  · intro h k
    obtain ⟨t, ht, rfl⟩ := strike_surjective p hs k
    exact (sign_at_strike p hs t ht (hw _)).mpr (h t ht)

end SVI
end MathFin
