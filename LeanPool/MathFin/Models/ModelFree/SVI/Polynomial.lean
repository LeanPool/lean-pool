/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.Reduction
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.ComputeDegree

/-! # The numerator as a polynomial

Part of the SVI polynomial-sign certificate (#174).

`polynomial p` is a real polynomial of degree at most ten whose value at every real `t` is
`numerator p t`, with its coefficients of degree `0` and `10` computed (the latter may vanish).

## Main definitions

* `polyD`: the polynomial `1 + X²`.
* `polyA`, `polyB`, `polyK`: polynomials whose values are `A p`, `B p` and `K p`.
* `polynomial`: the rationalised Durrleman numerator as a real polynomial in `t`.

## Main results

* `eval_polynomial`: `(polynomial p).eval t = numerator p t` for every `t`.
* `degree_le_ten`: `(polynomial p).natDegree ≤ 10`.
* `coeff_zero`: `(polynomial p).coeff 0 = b²σ³(1-ρ)²(4 - b²(1-ρ)²)`.
* `coeff_ten`: `(polynomial p).coeff 10 = b²σ³(1+ρ)²(4 - b²(1+ρ)²)`.

## Tags

Durrleman numerator, SVI numerator polynomial, degree ten polynomial, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

/-- The polynomial `1 + X²`, with values `D`. -/
noncomputable def polyD : ℝ[X] := 1 + X^2
/-- The polynomial with values `A p`. -/
noncomputable def polyA (p : Params) : ℝ[X] :=
  C (p.b*p.sigma*(1+p.rho))*X^2 + C (2*p.a)*X + C (p.b*p.sigma*(1-p.rho))
/-- The polynomial with values `B p`. -/
noncomputable def polyB (p : Params) : ℝ[X] :=
  C p.b * (C (1+p.rho)*X^2 - C (1-p.rho))
/-- The polynomial with values `K p`. -/
noncomputable def polyK (p : Params) : ℝ[X] := C p.sigma*X^2 + C (2*p.m)*X - C p.sigma
/-- The rationalised Durrleman numerator as a polynomial, with values `numerator p`
(`eval_polynomial`). -/
noncomputable def polynomial (p : Params) : ℝ[X] :=
  C (4*p.sigma)*polyD*(2*polyA p*polyD - polyK p*polyB p)^2 -
    C p.sigma*polyA p*(polyB p)^2*polyD*(polyA p + C 8*X) +
    C (64*p.b)*X^3*(polyA p)^2

theorem eval_polynomial (p : Params) (t : ℝ) :
    (polynomial p).eval t = numerator p t := by
  simp [polynomial, polyD, polyA, polyB, polyK, numerator, D, A, B, K]

theorem degree_le_ten (p : Params) : (polynomial p).natDegree ≤ 10 := by
  unfold polynomial polyD polyA polyB polyK
  compute_degree

theorem coeff_zero (p : Params) :
    (polynomial p).coeff 0 = p.b^2*p.sigma^3*(1-p.rho)^2*(4-p.b^2*(1-p.rho)^2) := by
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_polynomial]
  unfold numerator A B K D
  ring

theorem coeff_ten (p : Params) :
    (polynomial p).coeff 10 = p.b^2*p.sigma^3*(1+p.rho)^2*(4-p.b^2*(1+p.rho)^2) := by
  unfold polynomial polyD polyA polyB polyK
  compute_degree <;> norm_num
  ring

end SVI
end MathFin
