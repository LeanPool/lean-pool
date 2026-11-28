/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.SigmaZeroCertificate
public import LeanPool.MathFin.Models.ModelFree.SVI.SigmaZeroConvexity

/-! # The sign formula for every nonnegative scale

Part of the SVI polynomial-sign certificate (#174).

`extendedCertificateFormula` adds the zero-scale branch, two quadratic sign tests, to the smooth
formula. `extendedCertificateFormula_iff_bsSmile_convex`: it holds exactly when `σ ≥ 0`, `b ≥ 0`,
`ρ² ≤ 1`, the variance is positive, and the SVI-smiled Black–Scholes call is convex in strike.

## Main definitions

* `zeroAtom`: the sign formula "`f` is zero".
* `quadraticRayFormula`: a finite sign formula for a quadratic being nonnegative on a closed ray.
* `sigmaZeroBranchFormula`, `sigmaZeroFormula`: the sign formulas for one wing and for the
  zero-scale slice `σ = 0`.
* `extendedCertificateFormula`: the smooth determinant branch together with the zero-scale
  branch.

## Main results

* `zeroAtom_eval`, `quadraticRayFormula_eval`, `sigmaZeroBranchFormula_eval`: what each formula
  evaluates to.
* `sigmaZeroFormula_eval`: `sigmaZeroFormula` holds iff `σ = 0`, `a > 0`, `b ≥ 0`, `1 - ρ² ≥ 0` and
  `sigmaZeroCertificate p`.
* `sigmaZeroFormula_iff_bsSmile_convex`: `sigmaZeroFormula` holds iff `σ = 0`, `b ≥ 0`,
  `1 - ρ² ≥ 0`, the variance is positive, and `bsSmile p` is convex on `(0, ∞)`.
* `extendedCertificateFormula_iff_bsSmile_convex`: `extendedCertificateFormula` holds iff
  `σ ≥ 0`, `b ≥ 0`, `1 - ρ² ≥ 0`, the variance is positive, and `bsSmile p` is convex on
  `(0, ∞)`.

## References

* [R. Martin, *A polynomial-sign certificate for butterfly-free raw SVI*][MartinButterflyFreeSVI]

## Tags

raw SVI, zero-scale branch, butterfly arbitrage, sign formula, convex call price, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI

/-- The atom "`f` is zero". -/
noncomputable def zeroAtom (f : ParameterRing) : SignFormula := .atom f .zero

@[simp] theorem zeroAtom_eval (f : ParameterRing) (p : Params) :
    (zeroAtom f).eval p = true ↔ parameterEval p f = 0 := by
  simp [zeroAtom, SignFormula.eval, sign_eq_zero_iff]

/-- Finite sign formula for a quadratic nonnegative on a closed ray. -/
noncomputable def quadraticRayFormula (a u v z : ParameterRing) : SignFormula :=
  .and (nonnegativeAtom u) (.and (nonnegativeAtom (u*a^2+v*a+z))
    (.or (.and (zeroAtom u) (nonnegativeAtom v))
      (.and (positiveAtom u) (.or (nonnegativeAtom (v+2*u*a))
        (nonnegativeAtom (4*u*z-v^2))))))

theorem quadraticRayFormula_eval (a u v z : ParameterRing) (p : Params) :
    (quadraticRayFormula a u v z).eval p = true ↔
    0 ≤ parameterEval p u ∧
    0 ≤ parameterEval p u * (parameterEval p a)^2 +
      parameterEval p v * parameterEval p a + parameterEval p z ∧
    ((parameterEval p u = 0 ∧ 0 ≤ parameterEval p v) ∨
      (0 < parameterEval p u ∧
        (0 ≤ parameterEval p v + 2*parameterEval p u*parameterEval p a ∨
         0 ≤ 4*parameterEval p u*parameterEval p z-(parameterEval p v)^2))) := by
  simp only [quadraticRayFormula, SignFormula.eval, Bool.and_eq_true,
    Bool.or_eq_true, nonnegativeAtom_eval, positiveAtom_eval, zeroAtom_eval,
    map_add, map_mul, map_pow, map_sub, map_ofNat]

/-- The sign formula for one wing of slope `s` at zero scale: its branch quadratic is nonnegative on
the ray `w ≥ a`. -/
noncomputable def sigmaZeroBranchFormula (s : ParameterRing) : SignFormula :=
  let a : ParameterRing := MvPolynomial.X (0 : Fin 5)
  let m : ParameterRing := MvPolynomial.X (3 : Fin 5)
  quadraticRayFormula a (1-MvPolynomial.C (1/4 : ℝ)*s^2)
    (2*(a-s*m)-s^2) ((a-s*m)^2)

/-- The sign formula for the zero-scale slice: `σ = 0`, `b ≥ 0`, `ρ² ≤ 1`, `a > 0`, and both wing
conditions (`sigmaZeroFormula_eval`). -/
noncomputable def sigmaZeroFormula : SignFormula :=
  let a : ParameterRing := MvPolynomial.X (0 : Fin 5)
  let b : ParameterRing := MvPolynomial.X (1 : Fin 5)
  let rho : ParameterRing := MvPolynomial.X (2 : Fin 5)
  let sigma : ParameterRing := MvPolynomial.X (4 : Fin 5)
  .and (zeroAtom sigma) (.and (positiveAtom a) (.and (nonnegativeAtom b)
    (.and (nonnegativeAtom (1-rho^2))
      (.and (sigmaZeroBranchFormula (b*(rho-1)))
        (sigmaZeroBranchFormula (b*(rho+1)))))))

theorem sigmaZeroBranchFormula_eval (s : ParameterRing) (p : Params) :
    (sigmaZeroBranchFormula s).eval p = true ↔
      sigmaZeroBranchCondition p (parameterEval p s) := by
  rw [sigmaZeroBranchFormula, quadraticRayFormula_eval]
  simp [sigmaZeroBranchCondition, parameterEval, parameterValues, div_eq_mul_inv, mul_comm]

theorem sigmaZeroFormula_eval (p : Params) : sigmaZeroFormula.eval p = true ↔
    p.sigma = 0 ∧ 0 < p.a ∧ 0 ≤ p.b ∧ 0 ≤ 1-p.rho^2 ∧ sigmaZeroCertificate p := by
  simp only [sigmaZeroFormula, SignFormula.eval, Bool.and_eq_true,
    zeroAtom_eval, positiveAtom_eval, nonnegativeAtom_eval, sigmaZeroBranchFormula_eval]
  simp [parameterEval, parameterValues, sigmaZeroCertificate, leftSlope, rightSlope]

/-- Smooth determinant branch together with the piecewise-linear zero-scale branch. -/
noncomputable def extendedCertificateFormula : SignFormula :=
  .or fullCertificateFormula sigmaZeroFormula

theorem sigmaZeroFormula_iff_bsSmile_convex (p : Params) :
    sigmaZeroFormula.eval p = true ↔
      p.sigma = 0 ∧ 0 ≤ p.b ∧ 0 ≤ 1-p.rho^2 ∧
      (∀ k : ℝ, 0 < variance p k) ∧ ConvexOn ℝ (Set.Ioi 0) (bsSmile p) := by
  rw [sigmaZeroFormula_eval]
  constructor
  · rintro ⟨hs,ha,hb,hr,hc⟩
    have hw := (sigmaZero_variance_pos_iff p hs hb hr).mpr ha
    exact ⟨hs,hb,hr,hw,(sigmaZero_bsSmile_convex_iff p hs hb hw).mpr
      ((sigmaZeroCertificate_iff p hs hb hr ha).mp hc)⟩
  · rintro ⟨hs,hb,hr,hw,hc⟩
    have ha := (sigmaZero_variance_pos_iff p hs hb hr).mp hw
    exact ⟨hs,ha,hb,hr,(sigmaZeroCertificate_iff p hs hb hr ha).mpr
      ((sigmaZero_bsSmile_convex_iff p hs hb hw).mp hc)⟩

/-- Complete nonnegative-scale SVI domain, including the kinked zero-scale
case, as an explicit finite Boolean formula of parameter-polynomial signs. -/
theorem extendedCertificateFormula_iff_bsSmile_convex (p : Params) :
    extendedCertificateFormula.eval p = true ↔
      0 ≤ p.sigma ∧ 0 ≤ p.b ∧ 0 ≤ 1-p.rho^2 ∧
      (∀ k : ℝ, 0 < variance p k) ∧ ConvexOn ℝ (Set.Ioi 0) (bsSmile p) := by
  simp only [extendedCertificateFormula, SignFormula.eval, Bool.or_eq_true,
    fullCertificateFormula_iff_bsSmile_convex, sigmaZeroFormula_iff_bsSmile_convex]
  constructor
  · rintro (⟨hs,h⟩ | ⟨hs,h⟩)
    · exact ⟨hs.le,h⟩
    · exact ⟨by rw [hs],h⟩
  · rintro ⟨hs,h⟩
    rcases eq_or_lt_of_le hs with hz | hp
    · exact Or.inr ⟨hz.symm,h⟩
    · exact Or.inl ⟨hp,h⟩

end SVI
end MathFin
