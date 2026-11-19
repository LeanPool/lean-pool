/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBochnerKodairaIdentity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeBochnerKodairaIntegration

/-!
# Alternative Bochner Kodaira identity

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `bkGaussian_integrated_identity`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff ComplexConjugate BigOperators
namespace GinibrePoincare
noncomputable section

/-- The two genuine Gaussian IBP steps in (6.8), valid for smooth
noncompact representatives once their displayed polynomial-size tests are L². -/
theorem bkGaussian_number_pair {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f)
    (D N : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (Q R : Fin n → Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hD : ∀ j, (D j : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n] dbarComponent f j)
    (hN : ∀ j, (N j : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
      gaussianDbarAdjointTest j (dbarComponent f j))
    (hQ : ∀ j k, (Q j k : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
      dbarComponent (dbarComponent f j) k)
    (hR : ∀ j k, (R j k : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
      gaussianDbarAdjointTest k (dbarComponent (dbarComponent f j) k))
    (hZ : ∀ j, MemLp (fun z => conj (z j) * dbarComponent f j z) 2 (complexGaussianMeasure n))
    (hZZ : ∀ j k, MemLp (fun z => conj (z k) * dbarComponent (dbarComponent f j) k z)
      2 (complexGaussianMeasure n)) (j k : Fin n) :
    inner ℂ (N j) (N k) = (‖Q j k‖ ^ 2 : ℂ) +
      if j = k then (n : ℂ) * (‖D j‖ ^ 2 : ℂ) else 0 := by
  classical
  let P := R j k + if j = k then (n : ℂ) • D k else 0
  have hP : (P : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
      dbarComponent (gaussianDbarAdjointTest k (dbarComponent f k)) j := by
    filter_upwards [Lp.coeFn_add (R j k) (if j = k then (n : ℂ) • D k else 0),
      hR j k, hD k, Lp.coeFn_smul (n : ℂ) (D k),
      Lp.coeFn_zero ℂ 2 (complexGaussianMeasure n)] with z h1 h2 h3 h4 h5
    rw [h1, Pi.add_apply, h2, bkDbar_adjoint_comm (bkDbar_contDiff hf k) j k]
    rw [show dbarComponent (dbarComponent f k) j = dbarComponent (dbarComponent f j) k by
      funext z; exact bkDbar_comm hf j k z]
    by_cases hjk : j = k
    · simp [hjk, h4, h3, Pi.smul_apply, smul_eq_mul]
    · simp [hjk]
  have hfirst := bkGaussian_adjoint_pairing_representatives hn j
    (gaussianDbarAdjointTest k (dbarComponent f k)) (dbarComponent f j)
    (bkAdjoint_contDiff (bkDbar_contDiff hf k) k) (bkDbar_contDiff hf j)
    (N k) P (D j) (N j) (hN k) hP (hD j) (hN j) (hZ j)
  have hsecond := bkGaussian_adjoint_pairing_representatives hn k
    (dbarComponent f j) (dbarComponent (dbarComponent f j) k)
    (bkDbar_contDiff hf j) (bkDbar_contDiff (bkDbar_contDiff hf j) k)
    (D j) (Q j k) (Q j k) (R j k) (hD j) (hQ j k) (hQ j k) (hR j k) (hZZ j k)
  have hsecond' := congrArg conj hsecond
  simp only [inner_conj_symm, inner_self_eq_norm_sq_to_K] at hsecond'
  rw [← hfirst]
  change inner ℂ (D j) (R j k + if j = k then (n : ℂ) • D k else 0) = _
  rw [inner_add_right, ← hsecond']
  by_cases hjk : j = k
  · subst k
    simp [inner_smul_right, inner_self_eq_norm_sq_to_K]
  · simp [hjk]

/-- Actual integrated Bochner–Kodaira identity with noncompact polynomial
tests. No Hermite energy or deficit identity is used in this derivation. -/
theorem bkGaussian_integrated_identity {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f)
    (D N : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (Q R : Fin n → Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hD : ∀ j, (D j : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n] dbarComponent f j)
    (hN : ∀ j, (N j : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
      gaussianDbarAdjointTest j (dbarComponent f j))
    (hQ : ∀ j k, (Q j k : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
      dbarComponent (dbarComponent f j) k)
    (hR : ∀ j k, (R j k : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
      gaussianDbarAdjointTest k (dbarComponent (dbarComponent f j) k))
    (hZ : ∀ j, MemLp (fun z => conj (z j) * dbarComponent f j z) 2 (complexGaussianMeasure n))
    (hZZ : ∀ j k, MemLp (fun z => conj (z k) * dbarComponent (dbarComponent f j) k z)
      2 (complexGaussianMeasure n)) :
    ‖∑ j : Fin n, N j‖ ^ 2 =
      (∑ j : Fin n, ∑ k : Fin n, ‖Q j k‖ ^ 2) + (n : ℝ) * ∑ j : Fin n, ‖D j‖ ^ 2 := by
  have hi : (‖∑ j : Fin n, N j‖ ^ 2 : ℂ) =
      ((∑ j : Fin n, ∑ k : Fin n, ‖Q j k‖ ^ 2) + (n : ℝ) * ∑ j : Fin n, ‖D j‖ ^ 2 : ℝ) := by
    rw [show (‖∑ j : Fin n, N j‖ ^ 2 : ℂ) =
      inner ℂ (∑ j : Fin n, N j) (∑ j : Fin n, N j) from
        (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (∑ j : Fin n, N j)).symm]
    rw [sum_inner]
    simp_rw [inner_sum, bkGaussian_number_pair hn f hf D N Q R hD hN hQ hR hZ hZZ]
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  exact_mod_cast hi

end
end GinibrePoincare

