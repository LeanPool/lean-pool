/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevLineRemovability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevSlices
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevFTC
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-! # Actual weak derivatives across polynomial spectral collisions

A nonzero complex polynomial has only finitely many crossings on almost every
transverse affine coordinate line, by the imported slicing theorem. Along such
a line, the observable is continuous and differentiable outside that finite set.
The finite-exception fundamental theorem then integrates its locally integrable
derivative across the crossings. Compact support of the scalar test removes
the endpoint terms and gives the ordinary weak identity on the line.
-/

@[expose] public section
open MeasureTheory Filter MvPolynomial
namespace GinibrePoincare
noncomputable section

/-- Continuous functions differentiable away from a genuine nonzero polynomial
zero set satisfy the ordinary weak derivative identity on almost every affine
real coordinate slice as soon as their actual derivatives are locally integrable.
No Sobolev membership or analytic identity is assumed. -/
theorem polynomial_collision_line_weak_identity_ae (d : ℕ)
    (p : MvPolynomial (Fin (d + 1)) ℂ) (hp : p ≠ 0)
    (F : (Fin (d + 1) → ℂ) → ℝ) (hF : Continuous F)
    (hd : ∀ z, MvPolynomial.eval z p ≠ 0 → DifferentiableAt ℝ F z) :
    ∀ᵐ y ∂Measure.pi (fun _ : Fin d => (volume : Measure ℂ)),
      ∀ c v : ℂ, v ≠ 0 →
      LocallyIntegrable (deriv (fun t : ℝ => F (Fin.cons (c + (t : ℂ) * v) y))) volume →
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ∀ a b : ℝ, a ≤ b →
        tsupport ψ ⊆ Set.Ioo a b →
        (∫ t : ℝ, deriv (fun s : ℝ => F (Fin.cons (c + (s : ℂ) * v) y)) t * ψ t) =
          -(∫ t : ℝ, F (Fin.cons (c + (t : ℂ) * v) y) * deriv ψ t) := by
  classical
  filter_upwards [complexMvPolynomial_real_line_crossings_finite_ae d p hp] with y hy
  intro c v hv hloc ψ hψ a b hab hsupp
  let f : ℝ → ℝ := fun t => F (Fin.cons (c + (t : ℂ) * v) y)
  let S : Finset ℝ := (hy c v hv).toFinset
  have hc : Continuous f := hF.comp (by fun_prop)
  apply weak_derivative_test_identity_off_finite S f (deriv f) ψ hc hloc _ hψ a b hab hsupp
  intro t ht
  have hpz : MvPolynomial.eval (Fin.cons (c + (t : ℂ) * v) y) p ≠ 0 := by
    simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using ht
  have he : DifferentiableAt ℝ (fun s : ℝ => (s : ℂ)) t :=
    Complex.ofRealCLM.differentiableAt
  exact ((hd _ hpz).comp t (by fun_prop)).hasDerivAt

end
end GinibrePoincare
