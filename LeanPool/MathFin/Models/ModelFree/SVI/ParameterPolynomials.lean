/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.ClearedSignature
public import LeanPool.MathFin.Models.ModelFree.SVI.Polynomial

/-! # The certificate over the ring of parameter polynomials

Part of the SVI polynomial-sign certificate (#174).

`ParameterRing` is `MvPolynomial (Fin 5) ℝ`. The numerator polynomial and the four weights are
defined with coefficients in it and map to their real counterparts at every parameter point. The
fixed-size denominator-cleared Hermite matrices of its derivative (`universalMatrices n i`) map to
`certificateMatrices (polynomial p) i` only on the degree branch
`n = (polynomial p).derivative.natDegree` (`universalMatrices_eval`), and likewise their
characteristic coefficients (`determinantCoefficient_eval`).

## Main definitions

* `ParameterRing`: the ring `ℝ[a, b, ρ, m, σ]`, `MvPolynomial (Fin 5) ℝ`.
* `parameterEval`: evaluation of a parameter polynomial at the parameters `p`.
* `universalPolynomial`: the numerator polynomial with coefficients in `ParameterRing`.
* `universalWeights`, `universalMatrices`: the four weights `X²P²`, `XP²`, `X²P`, `XP` and the
  four fixed-size Hermite matrices of the derivative, with entries in `ParameterRing`.
* `fixedCompanion`, `fixedHermite`: companion and Hermite matrices of a fixed size `n` over any
  commutative ring, with the leading coefficient read at index `n`.
* `determinantCoefficient`: the coefficients of the characteristic polynomials of
  `universalMatrices`, as parameter polynomials.

## Main results

* `universalPolynomial_eval`: mapping `universalPolynomial` by `parameterEval p` gives
  `polynomial p`.
* `fixedHermite_eq_cleared`: if `f.natDegree = n` and `q.natDegree ≤ 22`, then
  `fixedHermite f q n = clearedHermite f q n`.
* `universalWeights_eval`: the weights map to `X²P²`, `XP²`, `X²P`, `XP` for `P = polynomial p`.
* `universalMatrices_eval`: at size `n = (polynomial p).derivative.natDegree`, the matrices map
  to `certificateMatrices (polynomial p) i`.
* `determinantCoefficient_eval`: at that size, `determinantCoefficient` evaluates to the
  coefficient `r` of the characteristic polynomial of `certificateMatrices (polynomial p) i`.

## Tags

multivariate polynomial ring, universal Hermite matrices, SVI parameter polynomials, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

/-- The ring `ℝ[a, b, ρ, m, σ]` of polynomials in the five SVI parameters. -/
abbrev ParameterRing := MvPolynomial (Fin 5) ℝ

/-- The parameter point of `p` as a valuation of the five variables. -/
def parameterValues (p : Params) : Fin 5 → ℝ := ![p.a, p.b, p.rho, p.m, p.sigma]
/-- Evaluation of a parameter polynomial at the parameters `p`. -/
noncomputable def parameterEval (p : Params) : ParameterRing →+* ℝ :=
  MvPolynomial.eval (parameterValues p)

/-- The numerator polynomial with coefficients in the parameter ring; it specialises to
`polynomial p` (`universalPolynomial_eval`). -/
noncomputable def universalPolynomial : Polynomial ParameterRing :=
  let a : ParameterRing := MvPolynomial.X (0 : Fin 5)
  let b : ParameterRing := MvPolynomial.X (1 : Fin 5)
  let rho : ParameterRing := MvPolynomial.X (2 : Fin 5)
  let m : ParameterRing := MvPolynomial.X (3 : Fin 5)
  let sigma : ParameterRing := MvPolynomial.X (4 : Fin 5)
  let D : Polynomial ParameterRing := 1 + X^2
  let A := C (b*sigma*(1+rho))*X^2 + C (2*a)*X + C (b*sigma*(1-rho))
  let B := C b * (C (1+rho)*X^2 - C (1-rho))
  let K := C sigma*X^2 + C (2*m)*X - C sigma
  C (4*sigma)*D*(2*A*D-K*B)^2 - C sigma*A*B^2*D*(A+C 8*X) + C (64*b)*X^3*A^2

theorem universalPolynomial_eval (p : Params) :
    universalPolynomial.map (parameterEval p) = polynomial p := by
  simp [universalPolynomial, parameterEval, parameterValues, polynomial, polyA, polyB, polyD, polyK]

/-- Fixed-degree companion numerator: the leading coefficient is read at n,
so this is polynomial even before imposing the degree branch. -/
noncomputable def fixedCompanion {R : Type*} [CommRing R] (f : R[X]) (n : ℕ) :
    Matrix (Fin n) (Fin n) R :=
  fun i j ↦ if j.val+1=n then -f.coeff i.val
    else if i.val=j.val+1 then f.coeff n else 0

/-- A fixed finite sum replaces support-dependent summation. -/
noncomputable def fixedHermite {R : Type*} [CommRing R] (f q : R[X]) (n : ℕ) :
    Matrix (Fin n) (Fin n) R := fun i j ↦
  ∑ r ∈ Finset.range 23, q.coeff r * (f.coeff n)^(38-(i.val+j.val+r)) *
    Matrix.trace ((fixedCompanion f n)^(i.val+j.val+r))

theorem fixedCompanion_map {R S : Type*} [CommRing R] [CommRing S]
    (h : R →+* S) (f : R[X]) (n : ℕ) :
    (fixedCompanion f n).map h = fixedCompanion (f.map h) n := by
  ext i j
  simp [fixedCompanion, apply_ite h]

theorem fixedHermite_map {R S : Type*} [CommRing R] [CommRing S]
    (h : R →+* S) (f q : R[X]) (n : ℕ) :
    (fixedHermite f q n).map h = fixedHermite (f.map h) (q.map h) n := by
  ext i j
  simp only [Matrix.map_apply, fixedHermite, map_sum, map_mul, map_pow, coeff_map]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  rw [AddMonoidHom.map_trace, Matrix.map_pow, fixedCompanion_map]

theorem fixedHermite_eq_cleared (f q : ℝ[X]) (n : ℕ) (hn : f.natDegree = n)
    (hq : q.natDegree ≤ 22) : fixedHermite f q n = clearedHermite f q n := by
  classical
  have hcomp : fixedCompanion f n = scaledCompanion f n := by
    ext i j
    simp [fixedCompanion, scaledCompanion, ← hn, coeff_natDegree]
  ext i j
  simp only [fixedHermite, clearedHermite, ← hn, coeff_natDegree, hcomp]
  symm
  apply Finset.sum_subset
  · intro r hr
    have := le_natDegree_of_ne_zero (mem_support_iff.mp hr)
    simp only [Finset.mem_range]
    omega
  · intro r hr hnot
    simp [notMem_support_iff.mp hnot]

/-- The four weights `X²P²`, `XP²`, `X²P`, `XP` for the universal polynomial `P`. -/
noncomputable def universalWeights : Fin 4 → Polynomial ParameterRing :=
  ![X^2*universalPolynomial^2, X*universalPolynomial^2,
    X^2*universalPolynomial, X*universalPolynomial]

/-- Four matrices with entries literally in the five-variable polynomial ring. -/
noncomputable def universalMatrices (n : ℕ) (i : Fin 4) : Matrix (Fin n) (Fin n) ParameterRing :=
  fixedHermite universalPolynomial.derivative (universalWeights i) n

theorem universalWeights_eval (p : Params) (i : Fin 4) :
    (universalWeights i).map (parameterEval p) =
      ![X^2*(polynomial p)^2, X*(polynomial p)^2, X^2*polynomial p, X*polynomial p] i := by
  fin_cases i <;> simp [universalWeights, universalPolynomial_eval]

theorem universalMatrices_eval (p : Params) (i : Fin 4) :
    (universalMatrices (polynomial p).derivative.natDegree i).map (parameterEval p) =
      certificateMatrices (polynomial p) i := by
  rw [universalMatrices, fixedHermite_map, ← derivative_map, universalPolynomial_eval,
    universalWeights_eval, fixedHermite_eq_cleared _ _ _ rfl
      (weight_size_bound _ (degree_le_ten p) i)]
  fin_cases i <;> rfl

/-- Every coefficient tested by the determinant certificate is an explicitly
constructed polynomial in the original five parameters, on its degree branch. -/
noncomputable def determinantCoefficient (n : ℕ) (i : Fin 4) (r : ℕ) : ParameterRing :=
  (universalMatrices n i).charpoly.coeff r

theorem determinantCoefficient_eval (p : Params) (i : Fin 4) (r : ℕ) :
    parameterEval p (determinantCoefficient (polynomial p).derivative.natDegree i r) =
      (certificateMatrices (polynomial p) i).charpoly.coeff r := by
  rw [determinantCoefficient, ← coeff_map, ← Matrix.charpoly_map, universalMatrices_eval]

end SVI
end MathFin
