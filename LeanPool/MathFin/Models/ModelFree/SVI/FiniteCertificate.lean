/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.DegreeProgram
public import LeanPool.MathFin.Models.ModelFree.SVI.SignatureProgram
public import LeanPool.MathFin.Models.ModelFree.SVI.MatrixCertificate

/-! # The certificate as a fixed finite program

Part of the SVI polynomial-sign certificate (#174).

`certificateProgram` branches only on signs of parameter polynomials, and `certificateFormula`
is its expansion into a `SignFormula`. For `σ > 0`, `b ≥ 0`, `ρ² ≤ 1` and under the variance gate,
it is equivalent to `g(k) ≥ 0` for every `k` (`certificateFormula_iff`).

## Main definitions

* `certificateProgram`: a fixed finite sign program that branches only on signs of parameter
  polynomials.
* `certificateFormula`: the expansion of `certificateProgram` into a `SignFormula`.

## Main results

* `certificateProgram_eval`: `certificateProgram` evaluates at `p` to
  `decide (matrixCertificate (polynomial p))`.
* `certificateFormula_iff`: for `σ > 0`, `b ≥ 0`, `1 - ρ² ≥ 0` and `varianceGate p`,
  `certificateFormula` holds iff `durrleman p k ≥ 0` for every `k`.

## Tags

sign program, Durrleman condition, raw SVI, certificate formula, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

open scoped Classical in
/-- A fixed finite program. All branching uses polynomial signs; no roots,
minima, eigenvalues, or real quantifiers occur in this definition. -/
noncomputable def certificateProgram : SignProgram Bool :=
  (degreeProgram 10).bind fun ds ↦
    if ds.1 = 0 then .pure (decide (ds.2 ≠ .neg))
    else if ds.2 = .pos then
      (signQuery (universalPolynomial.coeff 0)).bind fun s ↦
        if s = .neg then .pure false
        else (countProgram (ds.1-1)).bind fun z ↦ .pure (decide (z=0))
    else .pure false

open scoped Classical in
theorem certificateProgram_eval (p : Params) :
    certificateProgram.eval p = decide (matrixCertificate (polynomial p)) := by
  classical
  simp only [certificateProgram, SignProgram.eval_bind,
    degreeProgram_eval p 10 (degree_le_ten p)]
  unfold matrixCertificate
  by_cases hd : (polynomial p).natDegree = 0
  · simp only [hd, ↓reduceIte, SignProgram.eval]
    have hc : (polynomial p).leadingCoeff = (polynomial p).coeff 0 := by
      rw [leadingCoeff, hd]
    simp only [hc, SignType.neg_eq_neg_one]
    have hiff : (SignType.sign ((polynomial p).coeff 0) ≠ -1) ↔
        0 ≤ (polynomial p).coeff 0 := (not_congr sign_eq_neg_one_iff).trans not_lt
    simp only [hiff]
  · simp only [hd, ↓reduceIte]
    by_cases hl : SignType.sign (polynomial p).leadingCoeff = .pos
    · have hlp : 0 < (polynomial p).leadingCoeff := sign_eq_one_iff.mp hl
      simp only [hl, ↓reduceIte, SignProgram.eval_bind, signQuery_eval, universalCoefficient_eval]
      by_cases h0 : SignType.sign ((polynomial p).coeff 0) = .neg
      · have h0n : (polynomial p).coeff 0 < 0 := sign_eq_neg_one_iff.mp h0
        simp [h0, SignProgram.eval, not_le.mpr h0n]
      · have h0p : 0 ≤ (polynomial p).coeff 0 := by
          by_contra h
          exact h0 (sign_eq_neg_one_iff.mpr (lt_of_not_ge h))
        simp only [h0, ↓reduceIte, SignProgram.eval_bind, ← natDegree_derivative,
          countProgram_eval, SignProgram.eval]
        simp [hlp, h0p]
    · have hln : ¬ 0 < (polynomial p).leadingCoeff := by
        intro h; exact hl (sign_eq_one_iff.mpr h)
      rw [ite_eq_right hl]
      simp [SignProgram.eval, hln]

open scoped Classical in
/-- The expanded finite Boolean formula, kept compact as a structural definition. -/
noncomputable def certificateFormula : SignFormula := certificateProgram.toFormula

open scoped Classical in
theorem certificateFormula_iff (p : Params) (hs : 0 < p.sigma)
    (hb : 0 ≤ p.b) (hr : 0 ≤ 1 - p.rho ^ 2) (hg : varianceGate p) :
    certificateFormula.eval p = true ↔ ∀ k : ℝ, 0 ≤ durrleman p k := by
  rw [certificateFormula, SignProgram.eval_toFormula, certificateProgram_eval, decide_eq_true_eq]
  exact svi_matrixCertificate_iff p hs hb hr hg

end SVI
end MathFin
