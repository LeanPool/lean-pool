/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevCandidateLines.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevLineRemovability
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Removal of collisions for the actual directional derivative representative -/

@[expose] public section
open MeasureTheory Filter MvPolynomial
namespace GinibrePoincare
noncomputable section

theorem polynomial_collision_candidate_line_weak_identity_ae (d : ℕ)
    (p : MvPolynomial (Fin (d + 1)) ℂ) (hp : p ≠ 0)
    (F : (Fin (d + 1) → ℂ) → ℝ) (hF : Continuous F)
    (hd : ∀ z, MvPolynomial.eval z p ≠ 0 → DifferentiableAt ℝ F z) :
    ∀ᵐ y ∂Measure.pi (fun _ : Fin d => (volume : Measure ℂ)),
      ∀ c v : ℂ, v ≠ 0 →
      let g := fun t : ℝ => fderiv ℝ F (Fin.cons (c + (t : ℂ) * v) y)
        (Fin.cons v 0)
      LocallyIntegrable g volume →
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ∀ a b : ℝ, a ≤ b →
        tsupport ψ ⊆ Set.Ioo a b →
        (∫ t : ℝ, g t * ψ t) =
          -(∫ t : ℝ, F (Fin.cons (c + (t : ℂ) * v) y) * deriv ψ t) := by
  classical
  filter_upwards [complexMvPolynomial_real_line_crossings_finite_ae d p hp] with y hy
  intro c v hv
  dsimp only
  intro hg ψ hψ a b hab hsupp
  let f : ℝ → ℝ := fun t => F (Fin.cons (c + (t : ℂ) * v) y)
  let S : Finset ℝ := (hy c v hv).toFinset
  apply weak_derivative_test_identity_off_finite S f _ ψ
    (hF.comp (by fun_prop)) hg _ hψ a b hab hsupp
  intro t ht
  have hpz : MvPolynomial.eval (Fin.cons (c + (t : ℂ) * v) y) p ≠ 0 := by
    simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using ht
  have hl : HasDerivAt
      (fun s : ℝ => (Fin.cons (c + (s : ℂ) * v) y : Fin (d + 1) → ℂ))
      (Fin.cons v 0) t := by
    apply hasDerivAt_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change HasDerivAt (fun s : ℝ => c + (s : ℂ) * v) v t
      convert (hasDerivAt_const t c).add
        ((Complex.ofRealCLM.hasFDerivAt.hasDerivAt).mul_const v) using 1 <;> first | rfl | simp only
            [zero_add, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul]
    · simpa using hasDerivAt_const t (y j)
  exact (hd _ hpz).hasFDerivAt.comp_hasDerivAt t hl

end
end GinibrePoincare
