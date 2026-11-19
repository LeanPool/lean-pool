/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteRodriguesSmooth.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteRodriguesNormalization

/-!
# Hermite Rodrigues smooth

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `contDiff_iterate_dhol_gaussian`, `contDiff_iterate_mixed_gaussian`.
-/

@[expose] public section
open scoped ContDiff ComplexConjugate
namespace GinibrePoincare
namespace ComplexHermite
noncomputable section

theorem rodrigues_contDiff_diagonal (P : Poly) :
    ContDiff ℝ ∞ (diagonalEvalPublic P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    convert! (contDiff_const : ContDiff ℝ ∞ (fun _ : ℂ => a)) using 1
    funext z
    simp [diagonalEvalPublic, diagonalEval]
  | add P Q hP hQ =>
    convert! hP.add hQ using 1
    all_goals funext z; simp [diagonalEvalPublic, diagonalEval]
  | mul_X P i hP =>
    have hi : ContDiff ℝ ∞ (fun z : ℂ => (![z, conj z] : Fin 2 → ℂ) i) := by
      fin_cases i
      · exact contDiff_id
      · exact Complex.conjCLE.contDiff
    convert! hP.mul hi using 1
    all_goals funext z; simp [diagonalEvalPublic, diagonalEval]

theorem contDiff_iterate_dhol_gaussian (n q : ℕ) :
    ContDiff ℝ ∞ (dholOne^[q] (rodriguesGaussian n)) := by
  rw [iterate_dholOne_rodriguesGaussian]
  exact (contDiff_const.mul (Complex.conjCLE.contDiff.pow q)).mul (contDiff_rodriguesGaussian n)

theorem contDiff_iterate_mixed_gaussian (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    ContDiff ℝ ∞ (dbarOnePublic^[p] (dholOne^[q] (rodriguesGaussian n))) := by
  rw [iterate_wirtinger_rodrigues_raw n hn]
  exact (contDiff_const.mul (rodrigues_contDiff_diagonal (raw ((n : ℝ)⁻¹) p q))).mul
    (contDiff_rodriguesGaussian n)

end
end ComplexHermite
end GinibrePoincare
