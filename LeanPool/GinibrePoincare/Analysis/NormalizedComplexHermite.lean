/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NormalizedComplexHermite.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

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

public import LeanPool.GinibrePoincare.Analysis.ComplexHermiteLowering
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp

/-!
# Normalized univariate complex Hermite polynomials

For the centered complex Gaussian of precision `n`, the raw polynomial has
variance `1 / n`.  Multiplication by

`sqrt(n)^p / sqrt(p!) * (sqrt(n)^q / sqrt(q!))`

gives the paper's orthonormal normalization.  This file proves its two formal
lowering identities, including the exact coefficients `sqrt(n * p)` and
`sqrt(n * q)`.
-/


@[expose] public section


namespace GinibrePoincare

namespace ComplexHermite

/-- The one-index normalization factor for complex Hermite polynomials of
Gaussian precision `n`. -/
noncomputable def oneDimNormalization (n p : ℕ) : ℝ :=
  Real.sqrt n ^ p / Real.sqrt p.factorial

/-- The paper-normalized complex Hermite polynomial for Gaussian precision
`n`.  The positivity assumption on `n` is recorded in the definition's
interface because the variance is `1 / n`. -/
noncomputable def normalized (n : ℕ) (_hn : 0 < n) (p q : ℕ) : Poly :=
  MvPolynomial.C
      ((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ) *
    raw ((n : ℝ)⁻¹) p q

private theorem oneDimNormalization_succ (n p : ℕ) (hn : 0 < n) :
    (p + 1 : ℝ) * oneDimNormalization n (p + 1) =
      Real.sqrt (n * (p + 1) : ℕ) * oneDimNormalization n p := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : (0 : ℝ) < p.factorial := by positivity
  have hsp : Real.sqrt (p.factorial : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp0)
  have hsps : Real.sqrt ((p + 1).factorial : ℝ) ≠ 0 := by positivity
  have hsn : Real.sqrt (n : ℝ) ^ 2 = n := by
    rw [sq, Real.mul_self_sqrt (le_of_lt hn0)]
  have hsp_sq : Real.sqrt (p.factorial : ℝ) ^ 2 = p.factorial := by
    rw [sq, Real.mul_self_sqrt (by positivity)]
  have hsps_sq : Real.sqrt ((p + 1).factorial : ℝ) ^ 2 = (p + 1).factorial := by
    rw [sq, Real.mul_self_sqrt (by positivity)]
  have hsnp_sq : Real.sqrt (n * (p + 1) : ℕ) ^ 2 = n * (p + 1) := by
    rw [sq, Real.mul_self_sqrt (by positivity)]
    norm_cast
  have hroot :
      (p + 1 : ℝ) * Real.sqrt n * Real.sqrt p.factorial =
        Real.sqrt (n * (p + 1) : ℕ) * Real.sqrt (p + 1).factorial := by
    have hleft : 0 ≤ (p + 1 : ℝ) * Real.sqrt n * Real.sqrt p.factorial := by positivity
    have hright : 0 ≤ Real.sqrt (n * (p + 1) : ℕ) *
        Real.sqrt (p + 1).factorial := by positivity
    apply (sq_eq_sq₀ hleft hright).mp
    calc
      _ = (p + 1 : ℝ) ^ 2 * Real.sqrt n ^ 2 *
          Real.sqrt p.factorial ^ 2 := by ring
      _ = (p + 1 : ℝ) ^ 2 * n * p.factorial := by rw [hsn, hsp_sq]
      _ = Real.sqrt (n * (p + 1) : ℕ) ^ 2 *
          Real.sqrt (p + 1).factorial ^ 2 := by
        rw [hsnp_sq, hsps_sq, Nat.factorial_succ]
        push_cast
        ring
      _ = _ := by ring
  unfold oneDimNormalization
  rw [pow_succ]
  field_simp
  nlinarith

/-- Formal holomorphic lowering for the normalized complex Hermite
polynomial. -/
theorem pderiv_Z_normalized (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    MvPolynomial.pderiv (0 : ComplexHermiteIndex) (normalized n hn p q) =
      MvPolynomial.C (Real.sqrt (n * p : ℕ) : ℂ) *
        normalized n hn (p - 1) q := by
  cases p with
  | zero =>
      rw [normalized, MvPolynomial.pderiv_C_mul, pderiv_Z_raw_zero_left]
      simp
  | succ p =>
      rw [normalized, MvPolynomial.pderiv_C_mul, pderiv_Z_raw, normalized]
      rw [Nat.succ_sub_one]
      have hnorm := oneDimNormalization_succ n p hn
      have hreal :
          (oneDimNormalization n (p + 1) * oneDimNormalization n q) * (p + 1 : ℝ) =
            Real.sqrt (n * (p + 1) : ℕ) *
              (oneDimNormalization n p * oneDimNormalization n q) := by
        calc
          _ = ((p + 1 : ℝ) * oneDimNormalization n (p + 1)) *
              oneDimNormalization n q := by ring
          _ = (Real.sqrt (n * (p + 1) : ℕ) * oneDimNormalization n p) *
              oneDimNormalization n q := by rw [hnorm]
          _ = _ := by ring
      have hc :
          ((MvPolynomial.C
              ((oneDimNormalization n (p + 1) * oneDimNormalization n q : ℝ) : ℂ) *
              MvPolynomial.C ((p + 1 : ℕ) : ℂ)) : Poly) =
            ((MvPolynomial.C (Real.sqrt (n * (p + 1) : ℕ) : ℂ) *
              MvPolynomial.C
                ((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ)) : Poly) := by
        rw [← MvPolynomial.C_mul, ← MvPolynomial.C_mul]
        congr 1
        exact_mod_cast hreal
      rw [show ((p + 1 : ℕ) : Poly) = MvPolynomial.C ((p + 1 : ℕ) : ℂ) by rfl]
      calc
        _ = (MvPolynomial.C
              ((oneDimNormalization n (p + 1) * oneDimNormalization n q : ℝ) : ℂ) *
              MvPolynomial.C ((p + 1 : ℕ) : ℂ)) * raw ((n : ℝ)⁻¹) p q := by ring
        _ = (MvPolynomial.C (Real.sqrt (n * (p + 1) : ℕ) : ℂ) *
              MvPolynomial.C
                ((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ)) *
              raw ((n : ℝ)⁻¹) p q := by rw [hc]
        _ = _ := by ring

/-- Formal antiholomorphic lowering for the normalized complex Hermite
polynomial. -/
theorem pderiv_W_normalized (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    MvPolynomial.pderiv (1 : ComplexHermiteIndex) (normalized n hn p q) =
      MvPolynomial.C (Real.sqrt (n * q : ℕ) : ℂ) *
        normalized n hn p (q - 1) := by
  cases q with
  | zero =>
      rw [normalized, MvPolynomial.pderiv_C_mul, pderiv_W_raw_zero_right]
      simp
  | succ q =>
      rw [normalized, MvPolynomial.pderiv_C_mul, pderiv_W_raw, normalized]
      rw [Nat.succ_sub_one]
      have hnorm := oneDimNormalization_succ n q hn
      have hreal :
          (oneDimNormalization n p * oneDimNormalization n (q + 1)) * (q + 1 : ℝ) =
            Real.sqrt (n * (q + 1) : ℕ) *
              (oneDimNormalization n p * oneDimNormalization n q) := by
        calc
          _ = oneDimNormalization n p *
              ((q + 1 : ℝ) * oneDimNormalization n (q + 1)) := by ring
          _ = oneDimNormalization n p *
              (Real.sqrt (n * (q + 1) : ℕ) * oneDimNormalization n q) := by rw [hnorm]
          _ = _ := by ring
      have hc :
          ((MvPolynomial.C
              ((oneDimNormalization n p * oneDimNormalization n (q + 1) : ℝ) : ℂ) *
              MvPolynomial.C ((q + 1 : ℕ) : ℂ)) : Poly) =
            ((MvPolynomial.C (Real.sqrt (n * (q + 1) : ℕ) : ℂ) *
              MvPolynomial.C
                ((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ)) : Poly) := by
        rw [← MvPolynomial.C_mul, ← MvPolynomial.C_mul]
        congr 1
        exact_mod_cast hreal
      rw [show ((q + 1 : ℕ) : Poly) = MvPolynomial.C ((q + 1 : ℕ) : ℂ) by rfl]
      calc
        _ = (MvPolynomial.C
              ((oneDimNormalization n p * oneDimNormalization n (q + 1) : ℝ) : ℂ) *
              MvPolynomial.C ((q + 1 : ℕ) : ℂ)) * raw ((n : ℝ)⁻¹) p q := by ring
        _ = (MvPolynomial.C (Real.sqrt (n * (q + 1) : ℕ) : ℂ) *
              MvPolynomial.C
                ((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ)) *
              raw ((n : ℝ)⁻¹) p q := by rw [hc]
        _ = _ := by ring

end ComplexHermite
end GinibrePoincare
