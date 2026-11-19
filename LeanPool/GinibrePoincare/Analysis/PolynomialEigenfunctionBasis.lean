/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/PolynomialEigenfunctionBasis.lean.
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

public import LeanPool.GinibrePoincare.Analysis.PolynomialEigenfunctionSpan
public import LeanPool.GinibrePoincare.Analysis.PolynomialEquilibriumOrthogonality
public import LeanPool.GinibrePoincare.Analysis.LaguerreGammaNondegeneracy

/-! # The concrete Hermite–Laguerre algebraic basis
For `n ≥ 2`, the actual family is linearly independent and spans precisely
`ℂ[S,conj S,R]`. Every polynomial observable has unique finite coefficients.
This is an algebraic basis theorem, not a closed-generator-domain assertion.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- The equilibrium squared norm of each concrete member is nonzero. -/
theorem polynomialEigenfunction_inner_self_ne_zero (n : ℕ) (hn : 2 ≤ n)
    (ped : PolynomialEigenfunctionData n) :
    (∫ z : Configuration n, conj (polynomialEigenfunction n ped z) *
      polynomialEigenfunction n ped z ∂ginibreMeasure n) ≠ 0 := by
  cases ped with
  | mk a b m =>
    rw [integral_polynomialEigenfunction_inner n hn a b m a b m]
    simp only [and_self, ite_true, one_mul]
    exact Complex.ofReal_ne_zero.mpr
      (Laguerre.integral_polynomial_sq_pos _ m (recenteredGammaShape_pos n hn)).ne'

/-- The concrete Hermite–Laguerre family is linearly independent. -/
theorem polynomialEigenfunction_linearIndependent (n : ℕ) (hn : 2 ≤ n) :
    LinearIndependent ℂ (polynomialEigenfunction n) := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum i hi
  have hint (j : PolynomialEigenfunctionData n) :
      Integrable (fun z => c j * (conj (polynomialEigenfunction n i z) *
        polynomialEigenfunction n j z)) (ginibreMeasure n) :=
    (integrable_polynomialEigenfunction_inner n hn i.a i.b i.m j.a j.b j.m).const_mul (c j)
  have hz : (∫ z : Configuration n, ∑ j ∈ s, c j *
      (conj (polynomialEigenfunction n i z) * polynomialEigenfunction n j z)
      ∂ginibreMeasure n) = 0 := by
    have hf : (fun z : Configuration n => ∑ j ∈ s, c j *
        (conj (polynomialEigenfunction n i z) * polynomialEigenfunction n j z)) = 0 := by
      funext z
      have he := congrFun hsum z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at he
      calc
        _ = conj (polynomialEigenfunction n i z) * (∑ j ∈ s, c j * polynomialEigenfunction n j z) :=
            by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = 0 := by rw [he, mul_zero]
    rw [hf]; simp
  rw [integral_finsetSum s (fun j _ => hint j)] at hz
  simp_rw [integral_const_mul] at hz
  have he : (∑ j ∈ s, c j * (∫ z : Configuration n,
      conj (polynomialEigenfunction n i z) * polynomialEigenfunction n j z ∂ginibreMeasure n)) =
        c i * (∫ z : Configuration n, conj (polynomialEigenfunction n i z) *
          polynomialEigenfunction n i z ∂ginibreMeasure n) := by
    apply Finset.sum_eq_single_of_mem i hi
    intro j hj hji
    have hindices : ¬ (i.a = j.a ∧ i.b = j.b ∧ i.m = j.m) := by
      rintro ⟨ha, hb, hm⟩
      apply hji
      cases i; cases j
      simp_all
    rw [polynomialEigenfunction_equilibrium_orthogonal n hn _ _ _ _ _ _ hindices, mul_zero]
  rw [he] at hz
  exact (mul_eq_zero.mp hz).resolve_right (polynomialEigenfunction_inner_self_ne_zero n hn i)

/-- The actual family as a basis of its three-observable polynomial space. -/
def polynomialEigenfunctionBasis (n : ℕ) (hn : 2 ≤ n) :
    Module.Basis (PolynomialEigenfunctionData n) ℂ (sumRadiusPolynomialSpace n) :=
  (Module.Basis.span (polynomialEigenfunction_linearIndependent n hn)).map
    (LinearEquiv.ofEq _ _ (polynomialEigenfunctionSpan_eq n))

@[simp] theorem polynomialEigenfunctionBasis_apply (n : ℕ) (hn : 2 ≤ n)
    (ped : PolynomialEigenfunctionData n) :
    (polynomialEigenfunctionBasis n hn ped : Configuration n → ℂ) =
      polynomialEigenfunction n ped := by
  simp [polynomialEigenfunctionBasis, LinearEquiv.ofEq, Set.equivOfEq, Equiv.subtypeEquivProp]

/-- Every actual polynomial observable has unique finite Hermite–Laguerre coefficients. -/
theorem polynomialEigenfunction_unique_finite_expansion (n : ℕ) (hn : 2 ≤ n)
    (f : Configuration n → ℂ) (hf : IsPolynomialInSConjSR f) :
    ∃! c : PolynomialEigenfunctionData n →₀ ℂ,
      ∀ z, f z = c.sum (fun ped coeff => coeff * polynomialEigenfunction n ped z) := by
  obtain ⟨c, hc⟩ := polynomialEigenfunction_finite_expansion n f hf
  refine ⟨c, hc,?_⟩
  intro d hd
  apply (polynomialEigenfunction_linearIndependent n hn)
  ext z
  simpa [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, smul_eq_mul]
    using (hd z).symm.trans (hc z)

end
end GinibrePoincare
