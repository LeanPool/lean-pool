/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.FieldTheory.Perfect

/-!
# Squarefree polynomials over a perfect field

A candidate for `Mathlib.FieldTheory.Perfect`: a squarefree polynomial over a perfect field and its
derivative have no common root (`Squarefree.eval_ne_zero_or_eval_derivative_ne_zero`), since it is
separable.
-/

@[expose] public section

open Polynomial

/-- A squarefree polynomial over a perfect field and its derivative have no common root. -/
theorem Squarefree.eval_ne_zero_or_eval_derivative_ne_zero {K : Type*} [Field K]
    [PerfectField K] {p : K[X]} (hp : Squarefree p) (x : K) :
    p.eval x ≠ 0 ∨ p.derivative.eval x ≠ 0 := by
  by_cases h : p.eval x = 0
  · refine .inr ?_
    simpa [eval₂_eq_eval_map] using (PerfectField.separable_iff_squarefree.mpr
      hp).eval₂_derivative_ne_zero (RingHom.id K) (by simpa [eval₂_eq_eval_map] using h)
  · exact .inl h

end
