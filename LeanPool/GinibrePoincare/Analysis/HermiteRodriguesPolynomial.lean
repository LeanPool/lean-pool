/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteRodriguesPolynomial.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteRodriguesIteration

/-!
# Hermite Rodrigues polynomial

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `rodrigues_dbar_add`, `rodrigues_dbar_id`, `rodrigues_dbar_conj`,
`rodrigues_dbar_diagonalEvalPublic`.
-/

@[expose] public section
open scoped ComplexConjugate ContDiff
namespace GinibrePoincare
namespace ComplexHermite
noncomputable section

theorem rodrigues_dbar_add {f g : ℂ → ℂ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (z : ℂ) :
    dbarOnePublic (fun w => f w+g w) z=dbarOnePublic f z+dbarOnePublic g z := by
  change dbarOnePublic (f+g) z = _
  simp only [dbarOnePublic, dbarOne]
  rw [fderiv_add (hf z) (hg z)]
  simp only [add_apply]
  ring

@[simp] theorem rodrigues_dbar_id (z : ℂ) : dbarOnePublic id z = 0 := by
  rw [dbarOnePublic, dbarOne, (hasFDerivAt_id z).fderiv]
  simp

@[simp] theorem rodrigues_dbar_conj (z : ℂ) : dbarOnePublic conj z = 1 := by
  change dbarOnePublic (fun z => Complex.conjCLE z) z = 1
  rw [dbarOnePublic, dbarOne, Complex.conjCLE.fderiv]
  norm_num [Complex.conjCLE_apply]

/-- Diagonal evaluation turns formal differentiation in `W` into the
real-Fréchet Wirtinger derivative. -/
theorem rodrigues_dbar_diagonalEvalPublic (P : Poly) (z : ℂ) :
    dbarOnePublic (diagonalEvalPublic P) z =
      diagonalEvalPublic (MvPolynomial.pderiv (1 : ComplexHermiteIndex) P) z := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [show diagonalEvalPublic (MvPolynomial.C a) = fun _ : ℂ => a by
        funext w
        simp [diagonalEvalPublic, diagonalEval]]
      simp [dbarOnePublic, dbarOne, diagonalEvalPublic, diagonalEval]
  | add P Q hP hQ =>
      rw [show diagonalEvalPublic (P + Q) = fun z => diagonalEvalPublic P z + diagonalEvalPublic Q z
          by
        funext w
        simp [diagonalEvalPublic, diagonalEval]]
      rw [rodrigues_dbar_add ((contDiff_diagonalEvalPublic P).differentiable (by simp))
        ((contDiff_diagonalEvalPublic Q).differentiable (by simp)), hP, hQ]
      simp [diagonalEvalPublic, diagonalEval]
  | mul_X P i hP =>
      by_cases hi : i = (0 : ComplexHermiteIndex)
      · subst i
        rw [show diagonalEvalPublic (P * MvPolynomial.X (0 : ComplexHermiteIndex)) =
            fun z => diagonalEvalPublic P z * id z by
          funext w
          simp [diagonalEvalPublic, diagonalEval]]
        rw [dbarOnePublic_mul ((contDiff_diagonalEvalPublic P).differentiable (by simp))
            differentiable_id,
          hP, rodrigues_dbar_id]
        simp [diagonalEvalPublic, diagonalEval]
        ring
      · have hi' : i = (1 : ComplexHermiteIndex) := by
          have hne : i.val ≠ 0 := by
            intro hzero
            apply hi
            apply Fin.ext
            simpa using hzero
          apply Fin.ext
          omega
        subst i
        rw [show diagonalEvalPublic (P * MvPolynomial.X (1 : ComplexHermiteIndex)) =
            fun z => diagonalEvalPublic P z * conj z by
          funext w
          simp [diagonalEvalPublic, diagonalEval]]
        rw [dbarOnePublic_mul (g := conj) ((contDiff_diagonalEvalPublic P).differentiable (by simp))
          Complex.conjCLE.differentiable, hP, rodrigues_dbar_conj]
        simp [diagonalEvalPublic, diagonalEval]
        ring

theorem rodrigues_dbar_raw (ρ : ℝ) (p q : ℕ) (z : ℂ) :
    dbarOnePublic (eval ρ p q) z = (q : ℂ)*eval ρ p (q-1) z := by
  change dbarOnePublic (diagonalEvalPublic (raw ρ p q)) z = _
  rw [rodrigues_dbar_diagonalEvalPublic, pderiv_W_raw]
  simp [diagonalEvalPublic, diagonalEval, eval]

theorem rodrigues_dbar_weighted_raw (n p q : ℕ) (z : ℂ) :
    dbarOnePublic (fun w => eval ((n : ℝ)⁻¹) p q w*rodriguesGaussian n w) z =
      ((q : ℂ)*eval ((n : ℝ)⁻¹) p (q-1) z-
        (n : ℂ)*z*eval ((n : ℝ)⁻¹) p q z)*rodriguesGaussian n z := by
  have hP : Differentiable ℝ (eval ((n : ℝ)⁻¹) p q) :=
    (contDiff_diagonalEvalPublic (raw ((n : ℝ)⁻¹) p q)).differentiable (by simp)
  have hG := (contDiff_rodriguesGaussian n).differentiable (by simp)
  rw [dbarOnePublic_mul hP hG, rodrigues_dbar_raw, dbarOne_rodriguesGaussian]
  ring

end
end ComplexHermite
end GinibrePoincare
