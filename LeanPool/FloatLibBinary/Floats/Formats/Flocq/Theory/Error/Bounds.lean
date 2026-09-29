/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FloatLib Team
-/

/-
Upstream FloatLib code retains its MIT license below. The Lean Pool integration changes are
covered by the standard header above.

MIT License

Copyright (c) 2026 FloatLib

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Rounding.Core
import Mathlib.Algebra.Order.Algebra
import Mathlib.Tactic.Attr.Register

/-!
# Floating-Point Error Bounds

Single-step rounding in FloatLib’s Flocq-style model satisfies absolute and relative error bounds.

`Theory.Rounding.Core` proves a half-ULP bound for every rounding function satisfying
`ValidRndToNearest`.

The half-ULP bound yields relative-error forms, including the
$\operatorname{fl}(x)=x(1+\delta)$ factorization. To bound the error of a single rounded operation
such as `round rnd (x + y)`, apply `error_bound_ulp` at the exact expression.

Bounds for dot products, matrix operations, and backward stability require a concrete evaluation
order and format hypotheses. They belong with the corresponding algorithm rather than in this
generic one-step rounding file.

## References

- N. J. Higham, "Accuracy and Stability of Numerical Algorithms", SIAM, 2nd ed., 2002.
- D. Goldberg, "What Every Computer Scientist Should Know About Floating-Point Arithmetic",
  ACM Computing Surveys, 1991.
- IEEE Std 754-2019, "IEEE Standard for Floating-Point Arithmetic" (for the intended meaning of
  rounding modes and ULP terminology).
-/

@[expose] public section


namespace FloatLib.Floats.Formats.Flocq.ErrorBounds

open FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]

/-! ## Single Operation Error Bounds -/

/--
Relative error for a nonzero exact value.

The proof argument prevents a computation with a nonzero error at exact value zero from being
misreported as having zero relative error. Use an absolute-error statement when the exact value may
vanish.
-/
noncomputable def relativeError (exact computed : ℝ) (_ : exact ≠ 0) : ℝ :=
  abs (computed - exact) / abs exact

omit [ValidExp fexp] in
/--
Relative error bound for a single `round` step (ULP form).

This is the “divide the half-ULP absolute bound by `|x|`” version of the classic rounding model.
It is often the easiest lemma to use when a proof is naturally phrased in relative terms.
-/
theorem relative_error_round_ulp (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) (hx : x ≠ 0) :
    relativeError x (round (β := β) (fexp := fexp) rnd x) hx ≤
      ulp β fexp x / (2 * abs x) := by
  have h_rel :
      relativeError x (round (β := β) (fexp := fexp) rnd x) hx =
        abs (round (β := β) (fexp := fexp) rnd x - x) / abs x := by
    rfl
  rw [h_rel]
  set a : ℝ := ulp β fexp x
  have h_bound := error_bound_ulp (β := β) (fexp := fexp) (rnd := rnd) x
  have h_div :
      abs (round (β := β) (fexp := fexp) rnd x - x) / abs x ≤ (a / 2) / abs x := by
    simpa [a] using div_le_div_of_nonneg_right h_bound (abs_nonneg x)
  have h_eq : (a / 2) / abs x = a / (2 * abs x) := by
    simp [div_div]
  simpa [a, h_eq] using h_div

omit [ValidExp fexp] in
/--
Relative error factorisation for rounding, with a ULP-based bound.

This is the standard model $\operatorname{fl}(x)=x(1+\delta)$, with $|\delta|$ bounded using the
ULP at $x$.
-/
theorem round_relative_error_ulp (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) (hx : x
  ≠ 0) :
    ∃ δ : ℝ,
      abs δ ≤ ulp β fexp x / (2 * abs x) ∧
      round (β := β) (fexp := fexp) rnd x = x * (1 + δ) := by
  refine ⟨(round (β := β) (fexp := fexp) rnd x - x) / x, ?_, ?_⟩
  · have h_abs := error_bound_ulp (β := β) (fexp := fexp) (rnd := rnd) x
    have h_div :
        abs (round (β := β) (fexp := fexp) rnd x - x) / abs x ≤
          (ulp β fexp x / 2) / abs x :=
      div_le_div_of_nonneg_right h_abs (abs_nonneg x)
    have h_rhs :
        (ulp β fexp x / 2) / abs x =
          ulp β fexp x / (2 * abs x) := by
      simp [div_div]
    calc
      abs ((round (β := β) (fexp := fexp) rnd x - x) / x)
          = abs (round (β := β) (fexp := fexp) rnd x - x) / abs x := by
              simp [abs_div]
      _ ≤ (ulp β fexp x / 2) / abs x := h_div
      _ = ulp β fexp x / (2 * abs x) := h_rhs
  · have :
        x * (1 + (round (β := β) (fexp := fexp) rnd x - x) / x) =
          round (β := β) (fexp := fexp) rnd x := by
      field_simp [hx]; ring
    simpa using this.symm

end FloatLib.Floats.Formats.Flocq.ErrorBounds
