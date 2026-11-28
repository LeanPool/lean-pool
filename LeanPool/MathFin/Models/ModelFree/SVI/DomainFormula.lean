/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.FiniteCertificate

/-! # The finite sign formula for the smooth domain

Part of the SVI polynomial-sign certificate (#174).

`fullCertificateFormula`, a finite Boolean combination of signs of polynomials in the five
parameters, holds exactly when `σ > 0`, `b ≥ 0`, `ρ² ≤ 1`, the variance is positive at every
log-strike and `g(k) ≥ 0` for every `k` (`fullCertificateFormula_iff`).

## Main definitions

* `positiveAtom`, `nonnegativeAtom`: the sign formulas "`f` is positive" and "`f` is zero or
  positive" for a parameter polynomial `f`.
* `domainFormula`: the sign formula for `σ > 0`, `b ≥ 0`, `ρ² ≤ 1` together with the variance gate.
* `fullCertificateFormula`: `domainFormula` conjoined with `certificateFormula`.

## Main results

* `positiveAtom_eval`, `nonnegativeAtom_eval`: the atoms evaluate to `0 < parameterEval p f` and
  `0 ≤ parameterEval p f`.
* `domainFormula_iff`: `domainFormula` holds iff `0 < σ`, `0 ≤ b`, `0 ≤ 1 - ρ²` and
  `varianceGate p`.
* `fullCertificateFormula_iff`: `fullCertificateFormula` holds iff `σ > 0`, `b ≥ 0`, `1 - ρ² ≥ 0`,
  the variance is positive at every `k`, and `durrleman p k ≥ 0` for every `k`.

## Tags

raw SVI parameters, Durrleman condition, sign formula, quantifier elimination, butterfly arbitrage,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI

/-- The atom "`f` is positive". -/
noncomputable def positiveAtom (f : ParameterRing) : SignFormula := .atom f .pos
/-- The formula "`f` is zero or positive". -/
noncomputable def nonnegativeAtom (f : ParameterRing) : SignFormula :=
  .or (.atom f .zero) (.atom f .pos)

@[simp] theorem positiveAtom_eval (f : ParameterRing) (p : Params) :
    (positiveAtom f).eval p = true ↔ 0 < parameterEval p f := by
  simp [positiveAtom, SignFormula.eval, sign_eq_one_iff]

@[simp] theorem nonnegativeAtom_eval (f : ParameterRing) (p : Params) :
    (nonnegativeAtom f).eval p = true ↔ 0 ≤ parameterEval p f := by
  simp only [nonnegativeAtom, SignFormula.eval, Bool.or_eq_true, decide_eq_true_eq]
  change SignType.sign (parameterEval p f) = 0 ∨ SignType.sign (parameterEval p f) = 1 ↔ _
  rw [sign_eq_zero_iff, sign_eq_one_iff]
  constructor
  · rintro (h | h) <;> linarith
  · intro h
    rcases h.eq_or_lt with he | he
    · exact Or.inl he.symm
    · exact Or.inr he

/-- The sign formula for the parameter domain `σ > 0`, `b ≥ 0`, `ρ² ≤ 1` together with the variance
gate (`domainFormula_iff`). -/
noncomputable def domainFormula : SignFormula :=
  let a : ParameterRing := MvPolynomial.X (0 : Fin 5)
  let b : ParameterRing := MvPolynomial.X (1 : Fin 5)
  let rho : ParameterRing := MvPolynomial.X (2 : Fin 5)
  let sigma : ParameterRing := MvPolynomial.X (4 : Fin 5)
  .and (positiveAtom sigma) (.and (nonnegativeAtom b) (.and (nonnegativeAtom (1-rho^2))
    (.or (.and (.atom b .zero) (positiveAtom a))
      (.and (positiveAtom b) (.or (nonnegativeAtom a)
        (positiveAtom (b^2*sigma^2*(1-rho^2)-a^2)))))))

theorem domainFormula_iff (p : Params) : domainFormula.eval p = true ↔
    0 < p.sigma ∧ 0 ≤ p.b ∧ 0 ≤ 1-p.rho^2 ∧ varianceGate p := by
  have hnonneg (x : ℝ) : (x=0 ∨ 0<x) ↔ 0≤x := by
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      rcases h.eq_or_lt with he | he
      · exact Or.inl he.symm
      · exact Or.inr he
  simp only [domainFormula, positiveAtom, nonnegativeAtom, SignFormula.eval,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    SignType.pos_eq_one, SignType.zero_eq_zero, sign_eq_one_iff, sign_eq_zero_iff, hnonneg]
  simp [parameterEval, parameterValues, varianceGate, sub_pos]

/-- The entire smooth positive-variance domain with nonnegative Durrleman
factor, represented as a finite Boolean combination of polynomial signs. -/
noncomputable def fullCertificateFormula : SignFormula := .and domainFormula certificateFormula

theorem fullCertificateFormula_iff (p : Params) : fullCertificateFormula.eval p = true ↔
    0 < p.sigma ∧ 0 ≤ p.b ∧ 0 ≤ 1-p.rho^2 ∧
      (∀ k : ℝ, 0 < variance p k) ∧ (∀ k : ℝ, 0 ≤ durrleman p k) := by
  simp only [fullCertificateFormula, SignFormula.eval, Bool.and_eq_true, domainFormula_iff]
  constructor
  · rintro ⟨⟨hs,hb,hr,hg⟩,hc⟩
    exact ⟨hs,hb,hr,(varianceGate_iff p hs hb hr).mp hg,
      (certificateFormula_iff p hs hb hr hg).mp hc⟩
  · rintro ⟨hs,hb,hr,hw,hg⟩
    have hv := (varianceGate_iff p hs hb hr).mpr hw
    exact ⟨⟨hs,hb,hr,hv⟩,(certificateFormula_iff p hs hb hr hv).mpr hg⟩

end SVI
end MathFin
