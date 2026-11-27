/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Special.BesselKDefs
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Tactic.Linter.Style

/-!
# The modified Bessel functions `K_ν` and the Bessel bounds of Section 6 (including (6.2))

Section 6 preamble of the manuscript (label `eq:Bessel-scaled`). With the integral representation
[DLMF 10.32.9]
`K_j(x) = ∫₀^∞ e^{-x cosh u} cosh(j u) du`, the manuscript states, for `x > 0`,
`K₁(x) ≤ e^{-x} (x⁻¹ + √(π/(2x)))` and `K₂(x) ≤ e^{-x} (2x⁻² + 4x⁻¹ + √(π/(2x)))`, hence (6.2)
`x K₁(x) ≤ 3 (1+x)^{1/2} e^{-x}` and `x² K₂(x) ≤ 8 (1+x)^{3/2} e^{-x}`; and, for `Re z > 0`,
`|K_j(z)| ≤ K_j(Re z)`.

Mathlib (at the pinned commit) has `Complex.besselJ` but no modified Bessel function of the second
kind, so `K_ν` is *defined* here by the manuscript's own integral representation: `besselK ν z`
for complex `z` and its real form `besselKReal ν x` (`besselK_ofReal`). The order `ν` is any real
number; the manuscript uses `ν = 1, 2`.

## Main statements

* `integrableOn_besselK_integrand`, `integrableOn_besselKReal_integrand`: for `Re z > 0` (resp.
  `x > 0`) and every real `ν` the integrand is integrable on `(0, ∞)`.
* `besselKReal_nonneg`: `0 ≤ K_ν(x)`; `besselK_ofReal`: `besselK ν x = besselKReal ν x`.
* `norm_besselK_le`: `‖K_ν(z)‖ ≤ K_ν(Re z)`.
* `besselKReal_one_le`, `besselKReal_two_le`: the two explicit bounds, with the manuscript's
  constants.
* `mul_besselKReal_one_le`, `sq_mul_besselKReal_two_le`: the bounds (6.2).
* `norm_besselK_one_le`, `norm_besselK_two_le`: the explicit bounds for complex `z`, `Re z > 0`.

## Proof route

Instead of substituting `v = cosh u - 1`, the pointwise bounds are written in the variable `u`:
for `u ≥ 0`, `cosh u ≤ sinh u + cosh (u/2)` and `cosh 2u ≤ 2 sinh u (cosh u + 1) + cosh (u/2)`.
These are exactly the bounds `(1+v)/√(v(v+2)) ≤ 1 + (2v)^{-1/2}` and
`(2v²+4v+1)/√(v(v+2)) ≤ 2v + 4 + (2v)^{-1/2}` of the rational factors of the integrands, whose
right-hand sides the manuscript gives, multiplied by `sinh u = √(v(v+2))`, because
`sinh u/√(2v) = cosh (u/2)` and `(2v + 4) sinh u = 2 sinh u (cosh u + 1)`. The resulting
integrals are `∫ e^{-x cosh u} sinh u = e^{-x}/x` and
`∫ e^{-x cosh u} 2 sinh u (cosh u + 1) = e^{-x} (2/x² + 4/x)` (fundamental theorem of calculus
on `(0, ∞)`), and `∫ e^{-x cosh u} cosh (u/2) = e^{-x} √(π/(2x))` (substitution
`w = sinh (u/2)` and the Gaussian integral); in the variable `v` of the manuscript's
substitution these are `e^{-x} ∫₀^∞ e^{-xv} dv`, `e^{-x} ∫₀^∞ e^{-xv} (2v + 4) dv` and
`e^{-x} ∫₀^∞ e^{-xv} (2v)^{-1/2} dv`. Integrability for general `ν` uses the Gaussian bound
`e^{-x cosh u} cosh (ν u) ≤ e^{-x + ν²/x} e^{-(x/4) u²}` for `u ≥ 0`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace VacuumBellSeparation

namespace BesselK

/-- Half-angle form of `cosh`: `cosh u = 1 + 2 sinh² (u/2)`. -/
theorem cosh_eq_one_add_two_mul_sinh_half_sq (u : ℝ) :
    Real.cosh u = 1 + 2 * Real.sinh (u / 2) ^ 2 := by
  have h := Real.cosh_two_mul (u / 2)
  rw [show 2 * (u / 2) = u by ring, Real.cosh_sq] at h
  rw [h]
  ring

/-- For `u ≥ 0`, `1 + u²/2 ≤ cosh u`. -/
theorem one_add_sq_div_two_le_cosh {u : ℝ} (hu : 0 ≤ u) : 1 + u ^ 2 / 2 ≤ Real.cosh u := by
  have h1 : u / 2 ≤ Real.sinh (u / 2) := Real.self_le_sinh_iff.mpr (by positivity)
  have h2 : 0 ≤ u / 2 := by positivity
  have h3 := mul_self_le_mul_self h2 h1
  rw [cosh_eq_one_add_two_mul_sinh_half_sq u]
  nlinarith

/-- `cosh u → ∞` as `u → ∞`. -/
theorem tendsto_cosh_atTop : Tendsto Real.cosh atTop atTop := by
  refine Filter.tendsto_atTop_mono (fun u => ?_) Filter.tendsto_id
  change u ≤ Real.cosh u
  rcases le_or_gt 0 u with hu | hu
  · nlinarith [one_add_sq_div_two_le_cosh hu, sq_nonneg (u - 1)]
  · linarith [Real.one_le_cosh u]

/-- Gaussian domination of the integrand of `besselKReal`: for `x > 0`, `u ≥ 0` and real `ν`,
`‖e^{-x cosh u} cosh(ν u)‖ ≤ e^{-x + ν²/x} e^{-(x/4) u²}`. -/
theorem norm_integrand_le_gaussian (ν : ℝ) {x u : ℝ} (hx : 0 < x) (hu : 0 ≤ u) :
    ‖Real.exp (-(x * Real.cosh u)) * Real.cosh (ν * u)‖ ≤
      Real.exp (-x + ν ^ 2 / x) * Real.exp (-(x / 4) * u ^ 2) := by
  have hc := one_add_sq_div_two_le_cosh hu
  have key : ∀ μ : ℝ, μ ^ 2 = ν ^ 2 →
      Real.exp (-(x * Real.cosh u)) * Real.exp (μ * u) ≤
        Real.exp (-x + ν ^ 2 / x) * Real.exp (-(x / 4) * u ^ 2) := by
    intro μ hμ
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have h1 : x * (1 + u ^ 2 / 2) ≤ x * Real.cosh u := mul_le_mul_of_nonneg_left hc hx.le
    have h2 : μ * u ≤ ν ^ 2 / x + x / 4 * u ^ 2 := by
      rw [div_add' _ _ _ hx.ne', le_div_iff₀ hx]
      nlinarith [sq_nonneg (μ - x * u / 2)]
    linarith
  have k1 := key ν rfl
  have k2 := key (-ν) (by ring)
  rw [neg_mul] at k2
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le),
    Real.cosh_eq (ν * u)]
  linarith

/-- Norm of the integrand of `besselK`:
`‖e^{-z cosh u} cosh(ν u)‖ = e^{-(Re z) cosh u} cosh(ν u)`. -/
theorem norm_complex_integrand (ν : ℝ) (z : ℂ) (u : ℝ) :
    ‖Complex.exp (-(z * Real.cosh u)) * Real.cosh (ν * u)‖ =
      Real.exp (-(z.re * Real.cosh u)) * Real.cosh (ν * u) := by
  rw [Complex.norm_mul, Complex.norm_exp, Complex.norm_of_nonneg (Real.cosh_pos _).le,
    Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

end BesselK

open BesselK

/-- **Integrability, real argument.** For `x > 0` and every real `ν`, the integrand
`u ↦ e^{-x cosh u} cosh(ν u)` of `besselKReal` is integrable on `(0, ∞)`. -/
theorem integrableOn_besselKReal_integrand (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => Real.exp (-(x * Real.cosh u)) * Real.cosh (ν * u)) (Ioi 0) := by
  have hg : Integrable (fun u : ℝ => Real.exp (-x + ν ^ 2 / x) * Real.exp (-(x / 4) * u ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < x / 4)).const_mul _
  refine Integrable.mono' hg.integrableOn (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioi fun u hu =>
    norm_integrand_le_gaussian ν hx (le_of_lt hu)

/-- **Integrability, complex argument** (absolute convergence of the integral representation).
For `Re z > 0` and every real `ν`, the integrand `u ↦ e^{-z cosh u} cosh(ν u)` of `besselK` is
integrable on `(0, ∞)`. -/
theorem integrableOn_besselK_integrand (ν : ℝ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-(z * Real.cosh u)) * Real.cosh (ν * u)) (Ioi 0) :=
  Integrable.mono' (integrableOn_besselKReal_integrand ν hz)
    (Continuous.aestronglyMeasurable (by fun_prop))
    (ae_of_all _ fun u => (norm_complex_integrand ν z u).le)

/-- `K_ν(x) ≥ 0` for every real `x` (in particular for `x > 0`): the integrand is positive. -/
theorem besselKReal_nonneg (ν x : ℝ) : 0 ≤ besselKReal ν x := by
  rw [besselKReal]
  exact setIntegral_nonneg measurableSet_Ioi fun u _ =>
    mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le

/-- At real arguments the complex `besselK` is the real `besselKReal`. -/
theorem besselK_ofReal (ν x : ℝ) : besselK ν x = besselKReal ν x := by
  have hpt : ∀ u : ℝ, Complex.exp (-((x : ℂ) * (Real.cosh u : ℂ))) * (Real.cosh (ν * u) : ℂ) =
      ((Real.exp (-(x * Real.cosh u)) * Real.cosh (ν * u) : ℝ) : ℂ) := by
    intro u
    rw [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]
  rw [besselK, besselKReal, ← integral_complex_ofReal]
  exact integral_congr_ae (ae_of_all _ hpt)

/-- **`|K_ν(z)| ≤ K_ν(Re z)`** (Section 6 preamble, stated there for `Re z > 0` and `ν = 1, 2`):
the norm of the integral is at most the integral of the norm, which is the integrand of
`K_ν(Re z)`. It holds for every complex `z` and real `ν`; for `Re z ≤ 0` both sides are the junk
value `0`. -/
theorem norm_besselK_le (ν : ℝ) (z : ℂ) : ‖besselK ν z‖ ≤ besselKReal ν z.re := by
  rw [besselK, besselKReal]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  exact integral_congr_ae (ae_of_all _ fun u => norm_complex_integrand ν z u)

namespace BesselK

/-- For `u ≥ 0`: `cosh u ≤ sinh u + cosh (u/2)`. In the variable `v = cosh u - 1` this is the
bound `(1 + v)/√(v(v+2)) ≤ 1 + (2v)^{-1/2}` of the rational factor, whose right-hand side the
manuscript gives, multiplied by `sinh u = √(v(v+2))`. -/
theorem cosh_le_sinh_add_cosh_half {u : ℝ} (hu : 0 ≤ u) :
    Real.cosh u ≤ Real.sinh u + Real.cosh (u / 2) := by
  have h1 := Real.cosh_sub_sinh u
  have h2 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h3 := Real.one_le_cosh (u / 2)
  linarith

/-- For `u ≥ 0`: `cosh 2u ≤ 2 sinh u (cosh u + 1) + cosh (u/2)`. In the variable `v = cosh u - 1`
this is the bound `(2v² + 4v + 1)/√(v(v+2)) ≤ 2v + 4 + (2v)^{-1/2}` of the rational factor, whose
right-hand side the manuscript gives, multiplied by `sinh u = √(v(v+2))`. -/
theorem cosh_two_mul_le {u : ℝ} (hu : 0 ≤ u) :
    Real.cosh (2 * u) ≤ 2 * Real.sinh u * (Real.cosh u + 1) + Real.cosh (u / 2) := by
  have h1 := Real.cosh_sub_sinh u
  have h2 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h3 : (Real.cosh u - Real.sinh u) ^ 2 ≤ 1 := by
    rw [h1]
    exact pow_le_one₀ (Real.exp_pos _).le h2
  have h4 := Real.one_le_cosh (u / 2)
  have h5 : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu
  rw [Real.cosh_two_mul]
  nlinarith

/-- `u ↦ -x⁻¹ e^{-x cosh u}` is a primitive of `u ↦ e^{-x cosh u} sinh u` (for `x ≠ 0`). -/
theorem hasDerivAt_primitive_sinh {x : ℝ} (hx : x ≠ 0) (u : ℝ) :
    HasDerivAt (fun u => -x⁻¹ * Real.exp (-(x * Real.cosh u)))
      (Real.exp (-(x * Real.cosh u)) * Real.sinh u) u := by
  have h := (((Real.hasDerivAt_cosh u).const_mul x).fun_neg.exp).const_mul (-x⁻¹)
  refine h.congr_deriv ?_
  linear_combination Real.exp (-(x * Real.cosh u)) * Real.sinh u * mul_inv_cancel₀ hx

/-- The primitive `-x⁻¹ e^{-x cosh u}` tends to `0` as `u → ∞` (for `x > 0`). -/
theorem tendsto_primitive_sinh {x : ℝ} (hx : 0 < x) :
    Tendsto (fun u => -x⁻¹ * Real.exp (-(x * Real.cosh u))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun u => x * Real.cosh u) atTop atTop :=
    tendsto_cosh_atTop.const_mul_atTop hx
  have h2 : Tendsto (fun u => Real.exp (-(x * Real.cosh u))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  have h3 := h2.const_mul (-x⁻¹)
  rwa [mul_zero] at h3

/-- `e^{-x cosh u} sinh u ≥ 0` for `u ≥ 0`. -/
theorem integrand_sinh_nonneg (x : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ Real.exp (-(x * Real.cosh u)) * Real.sinh u :=
  mul_nonneg (Real.exp_pos _).le (Real.sinh_nonneg_iff.mpr hu)

/-- `u ↦ e^{-x cosh u} sinh u` is integrable on `(0, ∞)` for `x > 0`. -/
theorem integrableOn_integrand_sinh {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u => Real.exp (-(x * Real.cosh u)) * Real.sinh u) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun u _ => hasDerivAt_primitive_sinh hx.ne' u)
    (fun _ hu => integrand_sinh_nonneg x (le_of_lt hu)) (tendsto_primitive_sinh hx)

/-- `∫₀^∞ e^{-x cosh u} sinh u du = e^{-x}/x` for `x > 0`; in the variable `v = cosh u - 1` this is
`e^{-x} ∫₀^∞ e^{-xv} dv`. -/
theorem integral_integrand_sinh {x : ℝ} (hx : 0 < x) :
    ∫ u in Ioi (0 : ℝ), Real.exp (-(x * Real.cosh u)) * Real.sinh u = Real.exp (-x) / x := by
  have hderiv : ∀ u ∈ Ici (0 : ℝ), HasDerivAt (fun u => -x⁻¹ * Real.exp (-(x * Real.cosh u)))
      (Real.exp (-(x * Real.cosh u)) * Real.sinh u) u :=
    fun u _ => hasDerivAt_primitive_sinh hx.ne' u
  have hpos : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ Real.exp (-(x * Real.cosh u)) * Real.sinh u :=
    fun _ hu => integrand_sinh_nonneg x (le_of_lt hu)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos (tendsto_primitive_sinh hx),
    Real.cosh_zero, mul_one]
  ring

/-- `u ↦ -2x⁻² (x cosh u + (x + 1)) e^{-x cosh u}` is a primitive of
`u ↦ e^{-x cosh u} · 2 sinh u (cosh u + 1)` (for `x ≠ 0`). -/
theorem hasDerivAt_primitive_two {x : ℝ} (hx : x ≠ 0) (u : ℝ) :
    HasDerivAt
      (fun u => -2 * x⁻¹ ^ 2 * ((x * Real.cosh u + (x + 1)) * Real.exp (-(x * Real.cosh u))))
      (Real.exp (-(x * Real.cosh u)) * (2 * Real.sinh u * (Real.cosh u + 1))) u := by
  have hP : HasDerivAt (fun y => x * Real.cosh y + (x + 1)) (x * Real.sinh u) u :=
    HasDerivAt.add_const (x + 1) ((Real.hasDerivAt_cosh u).const_mul x)
  have hE : HasDerivAt (fun y => Real.exp (-(x * Real.cosh y)))
      (Real.exp (-(x * Real.cosh u)) * -(x * Real.sinh u)) u :=
    ((Real.hasDerivAt_cosh u).const_mul x).fun_neg.exp
  have h := (hP.fun_mul hE).const_mul (-2 * x⁻¹ ^ 2)
  refine h.congr_deriv ?_
  linear_combination 2 * Real.sinh u * Real.exp (-(x * Real.cosh u)) * (Real.cosh u + 1) *
    (x * x⁻¹ + 1) * mul_inv_cancel₀ hx

/-- The primitive of `hasDerivAt_primitive_two` tends to `0` as `u → ∞` (for `x > 0`). -/
theorem tendsto_primitive_two {x : ℝ} (hx : 0 < x) :
    Tendsto
      (fun u => -2 * x⁻¹ ^ 2 * ((x * Real.cosh u + (x + 1)) * Real.exp (-(x * Real.cosh u))))
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun u => x * Real.cosh u) atTop atTop :=
    tendsto_cosh_atTop.const_mul_atTop hx
  have h2 : Tendsto (fun t : ℝ => t ^ 1 * Real.exp (-t) + (x + 1) * Real.exp (-t)) atTop
      (𝓝 (0 + (x + 1) * 0)) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).add
      (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (x + 1))
  have h3 := (h2.comp h1).const_mul (-2 * x⁻¹ ^ 2)
  rw [show -2 * x⁻¹ ^ 2 * (0 + (x + 1) * 0) = (0 : ℝ) by ring] at h3
  refine h3.congr fun u => ?_
  simp only [Function.comp_apply, pow_one]
  ring

/-- `e^{-x cosh u} · 2 sinh u (cosh u + 1) ≥ 0` for `u ≥ 0`. -/
theorem integrand_two_nonneg (x : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ Real.exp (-(x * Real.cosh u)) * (2 * Real.sinh u * (Real.cosh u + 1)) :=
  mul_nonneg (Real.exp_pos _).le
    (mul_nonneg (mul_nonneg zero_le_two (Real.sinh_nonneg_iff.mpr hu))
      (add_pos (Real.cosh_pos u) one_pos).le)

/-- `u ↦ e^{-x cosh u} · 2 sinh u (cosh u + 1)` is integrable on `(0, ∞)` for `x > 0`. -/
theorem integrableOn_integrand_two {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u => Real.exp (-(x * Real.cosh u)) * (2 * Real.sinh u * (Real.cosh u + 1)))
      (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun u _ => hasDerivAt_primitive_two hx.ne' u)
    (fun _ hu => integrand_two_nonneg x (le_of_lt hu)) (tendsto_primitive_two hx)

/-- `∫₀^∞ e^{-x cosh u} · 2 sinh u (cosh u + 1) du = e^{-x} (2/x² + 4/x)` for `x > 0`; in the
variable `v = cosh u - 1` this is `e^{-x} ∫₀^∞ e^{-xv} (2v + 4) dv`. -/
theorem integral_integrand_two {x : ℝ} (hx : 0 < x) :
    ∫ u in Ioi (0 : ℝ), Real.exp (-(x * Real.cosh u)) * (2 * Real.sinh u * (Real.cosh u + 1)) =
      Real.exp (-x) * (2 / x ^ 2 + 4 / x) := by
  have hderiv : ∀ u ∈ Ici (0 : ℝ), HasDerivAt
      (fun u => -2 * x⁻¹ ^ 2 * ((x * Real.cosh u + (x + 1)) * Real.exp (-(x * Real.cosh u))))
      (Real.exp (-(x * Real.cosh u)) * (2 * Real.sinh u * (Real.cosh u + 1))) u :=
    fun u _ => hasDerivAt_primitive_two hx.ne' u
  have hpos : ∀ u ∈ Ioi (0 : ℝ),
      0 ≤ Real.exp (-(x * Real.cosh u)) * (2 * Real.sinh u * (Real.cosh u + 1)) :=
    fun _ hu => integrand_two_nonneg x (le_of_lt hu)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos (tendsto_primitive_two hx),
    Real.cosh_zero, mul_one]
  linear_combination 4 * x⁻¹ * Real.exp (-x) * mul_inv_cancel₀ hx.ne'

/-- `u ↦ e^{-x cosh u} cosh (u/2)` is integrable on `(0, ∞)` for `x > 0` (the order `ν = 1/2`
case of `integrableOn_besselKReal_integrand`). -/
theorem integrableOn_integrand_cosh_half {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u => Real.exp (-(x * Real.cosh u)) * Real.cosh (u / 2)) (Ioi 0) := by
  have h := integrableOn_besselKReal_integrand (1 / 2) hx
  have heq : (fun u : ℝ => Real.exp (-(x * Real.cosh u)) * Real.cosh (1 / 2 * u)) =
      fun u => Real.exp (-(x * Real.cosh u)) * Real.cosh (u / 2) :=
    funext fun u => by rw [show (1 : ℝ) / 2 * u = u / 2 by ring]
  rwa [heq] at h

/-- `∫₀^∞ e^{-x cosh u} cosh (u/2) du = e^{-x} √(π/(2x))` for `x > 0` (that is,
`K_{1/2}(x) = √(π/(2x)) e^{-x}`), by the substitution `w = sinh (u/2)` and the Gaussian integral.
In the variable `v = cosh u - 1` of the manuscript's substitution this is
`e^{-x} ∫₀^∞ e^{-xv} (2v)^{-1/2} dv = e^{-x} √(π/(2x))`. -/
theorem integral_integrand_cosh_half {x : ℝ} (_hx : 0 < x) :
    ∫ u in Ioi (0 : ℝ), Real.exp (-(x * Real.cosh u)) * Real.cosh (u / 2) =
      Real.exp (-x) * Real.sqrt (Real.pi / (2 * x)) := by
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun u => Real.sinh (u / 2))
      (Real.cosh (u / 2) * (1 / 2)) (Ioi 0) u := fun u _ =>
    ((hasDerivAt_id' u).div_const 2).sinh.hasDerivWithinAt
  have hinj : Set.InjOn (fun u : ℝ => Real.sinh (u / 2)) (Ioi 0) := by
    intro a _ b _ hab
    have h : Real.sinh (a / 2) = Real.sinh (b / 2) := hab
    have := Real.sinh_injective h
    linarith
  have himage : (fun u : ℝ => Real.sinh (u / 2)) '' Ioi 0 = Ioi 0 := by
    ext w
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact Real.sinh_pos_iff.mpr (half_pos hu)
    · intro hw
      refine ⟨2 * Real.arsinh w, mul_pos two_pos (Real.arsinh_pos_iff.mpr hw), ?_⟩
      rw [show 2 * Real.arsinh w / 2 = Real.arsinh w by ring, Real.sinh_arsinh]
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun w => Real.exp (-(2 * x) * w ^ 2))
  rw [himage, integral_gaussian_Ioi] at key
  simp only [smul_eq_mul] at key
  have hpt : ∀ u : ℝ, Real.exp (-(x * Real.cosh u)) * Real.cosh (u / 2) =
      2 * Real.exp (-x) *
        (|Real.cosh (u / 2) * (1 / 2)| * Real.exp (-(2 * x) * Real.sinh (u / 2) ^ 2)) := by
    intro u
    rw [abs_of_pos (mul_pos (Real.cosh_pos _) one_half_pos),
      cosh_eq_one_add_two_mul_sinh_half_sq u,
      show -(x * (1 + 2 * Real.sinh (u / 2) ^ 2)) = -x + -(2 * x) * Real.sinh (u / 2) ^ 2 by ring,
      Real.exp_add]
    ring
  calc ∫ u in Ioi (0 : ℝ), Real.exp (-(x * Real.cosh u)) * Real.cosh (u / 2)
      = ∫ u in Ioi (0 : ℝ), 2 * Real.exp (-x) *
          (|Real.cosh (u / 2) * (1 / 2)| * Real.exp (-(2 * x) * Real.sinh (u / 2) ^ 2)) :=
        integral_congr_ae (ae_of_all _ hpt)
    _ = 2 * Real.exp (-x) * ∫ u in Ioi (0 : ℝ),
          |Real.cosh (u / 2) * (1 / 2)| * Real.exp (-(2 * x) * Real.sinh (u / 2) ^ 2) :=
        integral_const_mul _ _
    _ = 2 * Real.exp (-x) * (Real.sqrt (Real.pi / (2 * x)) / 2) :=
        congrArg (fun t => 2 * Real.exp (-x) * t) key.symm
    _ = Real.exp (-x) * Real.sqrt (Real.pi / (2 * x)) := by ring

/-- For `x > 0`: `x √(π/(2x)) ≤ 2 √(1 + x)` (as `π x/2 ≤ 4 (1 + x)`). -/
theorem mul_sqrt_pi_div_le {x : ℝ} (hx : 0 < x) :
    x * Real.sqrt (Real.pi / (2 * x)) ≤ 2 * Real.sqrt (1 + x) := by
  have hS2 : Real.sqrt (Real.pi / (2 * x)) ^ 2 = Real.pi / (2 * x) :=
    Real.sq_sqrt (by positivity)
  have hR2 : Real.sqrt (1 + x) ^ 2 = 1 + x := Real.sq_sqrt (by positivity)
  have hpi : Real.pi * x ≤ 4 * x := mul_le_mul_of_nonneg_right Real.pi_le_four hx.le
  have hsq : x ^ 2 * (Real.pi / (2 * x)) = Real.pi * x / 2 := by
    linear_combination Real.pi * x / 2 * mul_inv_cancel₀ hx.ne'
  refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
  rw [mul_pow, mul_pow, hS2, hR2, hsq]
  linarith

end BesselK

/-- **Bessel bound for `K₁`** (Section 6, the display bounding `K₁` and `K₂` that precedes (6.2)):
for `x > 0`,
`K₁(x) ≤ e^{-x} (x⁻¹ + √(π/(2x)))`. -/
theorem besselKReal_one_le {x : ℝ} (hx : 0 < x) :
    besselKReal 1 x ≤ Real.exp (-x) * (x⁻¹ + Real.sqrt (Real.pi / (2 * x))) := by
  have hB := integrableOn_integrand_sinh hx
  have hC := integrableOn_integrand_cosh_half hx
  have hle : ∀ u ∈ Ioi (0 : ℝ), Real.exp (-(x * Real.cosh u)) * Real.cosh (1 * u) ≤
      Real.exp (-(x * Real.cosh u)) * Real.sinh u +
        Real.exp (-(x * Real.cosh u)) * Real.cosh (u / 2) := by
    intro u hu
    rw [one_mul, ← mul_add]
    exact mul_le_mul_of_nonneg_left (cosh_le_sinh_add_cosh_half (le_of_lt hu))
      (Real.exp_pos _).le
  calc besselKReal 1 x
      ≤ ∫ u in Ioi (0 : ℝ), (Real.exp (-(x * Real.cosh u)) * Real.sinh u +
          Real.exp (-(x * Real.cosh u)) * Real.cosh (u / 2)) :=
        setIntegral_mono_on (integrableOn_besselKReal_integrand 1 hx) (hB.fun_add hC)
          measurableSet_Ioi hle
    _ = Real.exp (-x) / x + Real.exp (-x) * Real.sqrt (Real.pi / (2 * x)) := by
        rw [integral_add hB hC, integral_integrand_sinh hx, integral_integrand_cosh_half hx]
    _ = Real.exp (-x) * (x⁻¹ + Real.sqrt (Real.pi / (2 * x))) := by ring

/-- **Bessel bound for `K₂`** (Section 6, the display bounding `K₁` and `K₂` that precedes (6.2)):
for `x > 0`,
`K₂(x) ≤ e^{-x} (2x⁻² + 4x⁻¹ + √(π/(2x)))`. -/
theorem besselKReal_two_le {x : ℝ} (hx : 0 < x) :
    besselKReal 2 x ≤
      Real.exp (-x) * (2 / x ^ 2 + 4 / x + Real.sqrt (Real.pi / (2 * x))) := by
  have hA := integrableOn_integrand_two hx
  have hC := integrableOn_integrand_cosh_half hx
  have hle : ∀ u ∈ Ioi (0 : ℝ), Real.exp (-(x * Real.cosh u)) * Real.cosh (2 * u) ≤
      Real.exp (-(x * Real.cosh u)) * (2 * Real.sinh u * (Real.cosh u + 1)) +
        Real.exp (-(x * Real.cosh u)) * Real.cosh (u / 2) := by
    intro u hu
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (cosh_two_mul_le (le_of_lt hu)) (Real.exp_pos _).le
  calc besselKReal 2 x
      ≤ ∫ u in Ioi (0 : ℝ),
          (Real.exp (-(x * Real.cosh u)) * (2 * Real.sinh u * (Real.cosh u + 1)) +
            Real.exp (-(x * Real.cosh u)) * Real.cosh (u / 2)) :=
        setIntegral_mono_on (integrableOn_besselKReal_integrand 2 hx) (hA.fun_add hC)
          measurableSet_Ioi hle
    _ = Real.exp (-x) * (2 / x ^ 2 + 4 / x) +
          Real.exp (-x) * Real.sqrt (Real.pi / (2 * x)) := by
        rw [integral_add hA hC, integral_integrand_two hx, integral_integrand_cosh_half hx]
    _ = Real.exp (-x) * (2 / x ^ 2 + 4 / x + Real.sqrt (Real.pi / (2 * x))) := by ring

/-- **(6.2), first bound**: for `x > 0`, `x K₁(x) ≤ 3 (1 + x)^{1/2} e^{-x}`. -/
theorem mul_besselKReal_one_le {x : ℝ} (hx : 0 < x) :
    x * besselKReal 1 x ≤ 3 * (1 + x) ^ ((1 : ℝ) / 2) * Real.exp (-x) := by
  have hK := besselKReal_one_le hx
  have hxS := mul_sqrt_pi_div_le hx
  have hR1 : 1 ≤ Real.sqrt (1 + x) := Real.one_le_sqrt.mpr (by linarith)
  have hE : 0 < Real.exp (-x) := Real.exp_pos _
  rw [← Real.sqrt_eq_rpow]
  calc x * besselKReal 1 x
      ≤ x * (Real.exp (-x) * (x⁻¹ + Real.sqrt (Real.pi / (2 * x)))) :=
        mul_le_mul_of_nonneg_left hK hx.le
    _ = Real.exp (-x) * (1 + x * Real.sqrt (Real.pi / (2 * x))) := by
        linear_combination Real.exp (-x) * mul_inv_cancel₀ hx.ne'
    _ ≤ Real.exp (-x) * (3 * Real.sqrt (1 + x)) :=
        mul_le_mul_of_nonneg_left (by linarith) hE.le
    _ = 3 * Real.sqrt (1 + x) * Real.exp (-x) := by ring

/-- **(6.2), second bound**: for `x > 0`, `x² K₂(x) ≤ 8 (1 + x)^{3/2} e^{-x}`. -/
theorem sq_mul_besselKReal_two_le {x : ℝ} (hx : 0 < x) :
    x ^ 2 * besselKReal 2 x ≤ 8 * (1 + x) ^ ((3 : ℝ) / 2) * Real.exp (-x) := by
  have hK := besselKReal_two_le hx
  have hxS := mul_sqrt_pi_div_le hx
  have hR1 : 1 ≤ Real.sqrt (1 + x) := Real.one_le_sqrt.mpr (by linarith)
  have hE : 0 < Real.exp (-x) := Real.exp_pos _
  have hpow : (1 + x) ^ ((3 : ℝ) / 2) = (1 + x) * Real.sqrt (1 + x) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (show (0 : ℝ) < 1 + x by linarith),
      Real.rpow_one, Real.sqrt_eq_rpow]
  have key : 2 + 4 * x + x ^ 2 * Real.sqrt (Real.pi / (2 * x)) ≤
      8 * ((1 + x) * Real.sqrt (1 + x)) := by
    have h1 : x * (x * Real.sqrt (Real.pi / (2 * x))) ≤ x * (2 * Real.sqrt (1 + x)) :=
      mul_le_mul_of_nonneg_left hxS hx.le
    have h2 : x * 1 ≤ x * Real.sqrt (1 + x) := mul_le_mul_of_nonneg_left hR1 hx.le
    linarith
  rw [hpow]
  calc x ^ 2 * besselKReal 2 x
      ≤ x ^ 2 * (Real.exp (-x) * (2 / x ^ 2 + 4 / x + Real.sqrt (Real.pi / (2 * x)))) :=
        mul_le_mul_of_nonneg_left hK (sq_nonneg x)
    _ = Real.exp (-x) * (2 + 4 * x + x ^ 2 * Real.sqrt (Real.pi / (2 * x))) := by
        linear_combination (2 * Real.exp (-x) * (x * x⁻¹ + 1) + 4 * Real.exp (-x) * x) *
          mul_inv_cancel₀ hx.ne'
    _ ≤ Real.exp (-x) * (8 * ((1 + x) * Real.sqrt (1 + x))) :=
        mul_le_mul_of_nonneg_left key hE.le
    _ = 8 * ((1 + x) * Real.sqrt (1 + x)) * Real.exp (-x) := by ring

/-- The `K₁` bound for complex arguments: for `Re z > 0`,
`‖K₁(z)‖ ≤ e^{-Re z} ((Re z)⁻¹ + √(π/(2 Re z)))` (`norm_besselK_le` and `besselKReal_one_le`). -/
theorem norm_besselK_one_le {z : ℂ} (hz : 0 < z.re) :
    ‖besselK 1 z‖ ≤ Real.exp (-z.re) * (z.re⁻¹ + Real.sqrt (Real.pi / (2 * z.re))) :=
  (norm_besselK_le 1 z).trans (besselKReal_one_le hz)

/-- The `K₂` bound for complex arguments: for `Re z > 0`,
`‖K₂(z)‖ ≤ e^{-Re z} (2 (Re z)⁻² + 4 (Re z)⁻¹ + √(π/(2 Re z)))` (`norm_besselK_le` and
`besselKReal_two_le`). -/
theorem norm_besselK_two_le {z : ℂ} (hz : 0 < z.re) :
    ‖besselK 2 z‖ ≤
      Real.exp (-z.re) * (2 / z.re ^ 2 + 4 / z.re + Real.sqrt (Real.pi / (2 * z.re))) :=
  (norm_besselK_le 2 z).trans (besselKReal_two_le hz)

end VacuumBellSeparation
