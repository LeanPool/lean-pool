/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevSlices.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixPolynomialNull

/-! # Finite discriminant crossings on almost every real coordinate line -/

@[expose] public section
open MeasureTheory MvPolynomial
namespace GinibrePoincare
noncomputable section

/-- A nonzero complex polynomial has only finitely many zeros on every
nonconstant affine real line in the complex plane. -/
theorem complexPolynomial_affine_real_zeros_finite (p : Polynomial ℂ) (hp : p ≠ 0)
    (c v : ℂ) (hv : v ≠ 0) :
    {t : ℝ | p.eval (c + (t : ℂ) * v) = 0}.Finite := by
  have hi : Function.Injective (fun t : ℝ => c + (t : ℂ) * v) := by
    intro s t h
    have hst := mul_right_cancel₀ hv (add_left_cancel h)
    exact_mod_cast hst
  exact (Polynomial.finite_setOfPred_isRoot hp).preimage hi.injOn

/-- For an actual nonzero multivariate complex polynomial, almost every
remaining-coordinate configuration admits only finitely many crossings on
EVERY nonconstant real affine line in the distinguished coordinate. -/
theorem complexMvPolynomial_real_line_crossings_finite_ae (d : ℕ)
    (p : MvPolynomial (Fin (d + 1)) ℂ) (hp : p ≠ 0) :
    ∀ᵐ y ∂Measure.pi (fun _ : Fin d => (volume : Measure ℂ)),
      ∀ c v : ℂ, v ≠ 0 →
        {t : ℝ | MvPolynomial.eval (Fin.cons (c + (t : ℂ) * v) y) p = 0}.Finite := by
  let q := MvPolynomial.finSuccEquiv ℂ d p
  have hq : q ≠ 0 := by
    intro h
    exact hp ((MvPolynomial.finSuccEquiv ℂ d).injective (by simpa [q] using h))
  obtain ⟨k, hk⟩ : ∃ k, q.coeff k ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hq (AddMonoidAlgebra.ext (Finsupp.ext fun k => by simpa using h k))
  filter_upwards [complexMvPolynomial_fin_eval_ne_zero_ae volume d (q.coeff k) hk] with y hy
  have hmap : q.map (MvPolynomial.eval y) ≠ 0 := by
    intro hz
    have hc := congrArg (fun f : Polynomial ℂ => f.coeff k) hz
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc
    exact hy hc
  intro c v hv
  simpa only [MvPolynomial.eval_eq_eval_mv_eval'] using
    complexPolynomial_affine_real_zeros_finite (q.map (MvPolynomial.eval y)) hmap c v hv

end
end GinibrePoincare
