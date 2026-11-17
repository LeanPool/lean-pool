/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.Tactic.Linarith
public import LeanPool.AaronsonAmbainis.RowDefs

/-!
# Markov's inequality at an endpoint

This file proves `markovEndpoint : MarkovEndpoint`: a real polynomial `p` of degree at most `D`
with `|p| ≤ 1` on `[0,2]` satisfies `|p'(0)| ≤ D²`. This is the second assertion of Lemma 6.1 of
the paper. The paper proves the lemma directly, by interpolation at the points `cos (k π / D)`;
here the assertion is deduced from Mathlib's extremal property of the Chebyshev polynomials
(`Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`, with `k = 1`, `x = 1`),
applied to `p.comp (1 - X)` and to its negative.
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Row

open Polynomial

/-- One-sided form: `-p'(0) ≤ D²` if `|p| ≤ 1` on `[0,2]` and `natDegree p ≤ D`. -/
theorem neg_derivative_eval_zero_le (D : ℕ) (p : ℝ[X]) (hdeg : p.natDegree ≤ D)
    (hbnd : ∀ s : ℝ, 0 ≤ s → s ≤ 2 → |p.eval s| ≤ 1) :
    -(p.derivative.eval 0) ≤ (D : ℝ) ^ 2 := by
  have h1X : (1 - X : ℝ[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have hnat : (p.comp (1 - X)).natDegree ≤ D :=
    calc (p.comp (1 - X)).natDegree ≤ p.natDegree * (1 - X : ℝ[X]).natDegree := natDegree_comp_le
      _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ h1X
      _ ≤ D := by simpa using hdeg
  have hP : (p.comp (1 - X)).degree ≤ (D : WithBot ℕ) := degree_le_of_natDegree_le hnat
  have hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(p.comp (1 - X)).eval x| ≤ 1 := by
    intro x hx
    rw [eval_comp]
    simp only [eval_sub, eval_one, eval_X]
    exact hbnd (1 - x) (by linarith [hx.2]) (by linarith [hx.1])
  have h := Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one (k := 1) (x := 1)
    le_rfl hP hb
  simp only [Function.iterate_one] at h
  rw [derivative_comp_one_sub_X, Chebyshev.derivative_T_eval_one] at h
  simpa using h

end Row

open Polynomial in
/-- Markov's inequality at the endpoint `0` of `[0,2]`. -/
theorem markovEndpoint : MarkovEndpoint := by
  intro D p hdeg hbnd
  have h1 := Row.neg_derivative_eval_zero_le D p hdeg hbnd
  have h2 := Row.neg_derivative_eval_zero_le D (-p) (by simpa using hdeg)
    (fun s hs0 hs2 => by simpa using hbnd s hs0 hs2)
  rw [derivative_neg, eval_neg, neg_neg] at h2
  exact abs_le.mpr ⟨by linarith, h2⟩

end AaronsonAmbainis
