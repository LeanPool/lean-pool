/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticHomogeneousPolynomial.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticHolomorphicHomogeneity
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Literal homogeneous polynomials from entire phase eigenfunctions -/

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- The literal coordinate polynomial of a homogeneous multilinear diagonal. -/
def homogeneousMultilinearPolynomial {n d : ℕ}
    (P : ContinuousMultilinearMap ℂ (fun _ : Fin d => Fin n → ℂ) ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ r : Fin d → Fin n,
    MvPolynomial.C (P (fun i => Pi.single (r i) 1)) * ∏ i : Fin d, MvPolynomial.X (r i)

theorem homogeneousMultilinearPolynomial_homogeneous {n d : ℕ}
    (P : ContinuousMultilinearMap ℂ (fun _ : Fin d => Fin n → ℂ) ℂ) :
    (homogeneousMultilinearPolynomial P).IsHomogeneous d := by
  apply MvPolynomial.IsHomogeneous.sum
  intro r hr
  apply MvPolynomial.IsHomogeneous.C_mul
  simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i : Fin d => MvPolynomial.X (r i) : Fin d → MvPolynomial (Fin n) ℂ)
    (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X ℂ (r i))

theorem homogeneousMultilinearPolynomial_eval {n d : ℕ}
    (P : ContinuousMultilinearMap ℂ (fun _ : Fin d => Fin n → ℂ) ℂ) (z : Fin n → ℂ) :
    MvPolynomial.eval z (homogeneousMultilinearPolynomial P) = P (fun _ => z) := by
  have hz : z = ∑ j : Fin n, z j • Pi.single j (1 : ℂ) := by
    ext k
    simp [Pi.single_apply]
  have he : P (fun _ => z) = ∑ r : Fin d → Fin n,
      (∏ i : Fin d, z (r i)) * P (fun i => Pi.single (r i) 1) := by
    conv_lhs => rw [hz]
    change P.toMultilinearMap (fun _ : Fin d => ∑ j : Fin n, z j • Pi.single j 1) = _
    rw [MultilinearMap.map_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [MultilinearMap.map_smul_univ]
    rfl
  rw [he]
  simp only [homogeneousMultilinearPolynomial, map_sum, map_mul, MvPolynomial.eval_C,
    map_prod, MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro r hr
  exact mul_comm _ _

/-- Genuine analyticity and unit-phase covariance force a literal finite
homogeneous coordinate polynomial, with no weighted-space assumption. -/
theorem entire_phase_has_homogeneous_mvPolynomial {n d : ℕ}
    (F : (Fin n → ℂ) → ℂ) (hF : Differentiable ℂ F) (hA : AnalyticAt ℂ F 0)
    (hp : ∀ (u : ℂ) (z : Fin n → ℂ), ‖u‖ = 1 → F (u • z) = u ^ d * F z) :
    ∃ P : MvPolynomial (Fin n) ℂ, P.IsHomogeneous d ∧ ∀ z, F z = MvPolynomial.eval z P := by
  obtain ⟨P, hP⟩ := entire_phase_has_homogeneous_multilinear_representation F hF hA d hp
  exact ⟨homogeneousMultilinearPolynomial P, homogeneousMultilinearPolynomial_homogeneous P,
    fun z => (hP z).trans (homogeneousMultilinearPolynomial_eval P z).symm⟩
end
end GinibrePoincare
