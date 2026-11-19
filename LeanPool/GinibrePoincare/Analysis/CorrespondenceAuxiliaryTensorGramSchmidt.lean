/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryTensorGramSchmidt.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryTensorExpansion
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryHermiteDegreeOrder
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryTriangularGramSchmidt

/-!
# Correspondence auxiliary tensor Gram Schmidt

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `gaussian_tensor_mixed_monomial_gramSchmidt`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section
open ComplexHermite

private def zeroContraction {n : ℕ} (p q : Fin n → ℕ) :
    TensorHermiteContraction p q := fun j => ⟨0, by omega⟩

private def degreeHermiteFamily (n : ℕ) (hn : 0 < n) (i : DegreeHermiteIndex n) :=
  multivariateNormalizedL2 n hn i.val.1 i.val.2

private def degreeMonomialFamily (n : ℕ) (hn : 0 < n) (i : DegreeHermiteIndex n) :=
  multivariateMixedMonomialL2 n hn i.val.1 i.val.2

private theorem contraction_degree_lt {n : ℕ} (p q : Fin n → ℕ)
    (k : TensorHermiteContraction p q) (hk : k ≠ zeroContraction p q)
    (a b : Fin n → ℕ) (ha : ∀ j, a j ≤ p j - (k j).val)
    (hb : ∀ j, b j ≤ q j - (k j).val) :
    hermiteTotalDegree (a, b) < hermiteTotalDegree (p, q) := by
  have hsome : ∃ j, (k j).val ≠ 0 := by
    by_contra h
    apply hk
    funext j
    apply Fin.ext
    simp only [zeroContraction]
    simpa using (not_exists.mp h j)
  obtain ⟨j, hj⟩ := hsome
  have hle (i : Fin n) : a i ≤ p i := (ha i).trans (Nat.sub_le _ _)
  have hlt : a j < p j := by
    have hkbound := (k j).isLt
    have haj := ha j
    omega
  have hp : ∑ i, a i < ∑ i, p i :=
    Finset.sum_lt_sum (fun i _ => hle i) ⟨j, Finset.mem_univ j, hlt⟩
  have hq : ∑ i, b i ≤ ∑ i, q i :=
    Finset.sum_le_sum (fun i _ => (hb i).trans (Nat.sub_le _ _))
  exact Nat.add_lt_add_of_lt_of_le hp hq

private theorem degreeMonomial_triangular (n : ℕ) (hn : 0 < n)
    (i : DegreeHermiteIndex n) :
    degreeMonomialFamily n hn i - ((tensorHermiteScale n i.val.1 i.val.2 : ℂ)⁻¹) •
      degreeHermiteFamily n hn i ∈
      Submodule.span ℂ (degreeHermiteFamily n hn '' Set.Iio i) := by
  classical
  let p := i.val.1
  let q := i.val.2
  let rest := ∑ k ∈ (Finset.univ : Finset (TensorHermiteContraction p q)).erase
    (zeroContraction p q), tensorHermiteScalar p q k •
      multivariateMixedMonomialL2 n hn (fun j => p j-(k j).val)
        (fun j => q j-(k j).val)
  have hrest : rest ∈ Submodule.span ℂ (degreeHermiteFamily n hn '' Set.Iio i) := by
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.smul_mem
    apply Submodule.span_mono _ (multivariateMixedMonomialL2_mem_hermite_rectangle n hn
      (fun j => p j-(k j).val) (fun j => q j-(k j).val))
    rintro v ⟨a, b, ha, hb, rfl⟩
    refine ⟨⟨(a, b)⟩,?_, rfl⟩
    apply degreeHermite_lt_of_degree_lt
    exact contraction_degree_lt p q k (Finset.mem_erase.mp hk).1 a b ha hb
  have hg : degreeHermiteFamily n hn i = (tensorHermiteScale n p q : ℂ) •
      (degreeMonomialFamily n hn i+rest) := by
    change multivariateNormalizedL2 n hn p q = _
    rw [multivariateNormalizedL2_tensor_expansion]
    congr 1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (zeroContraction p q))]
    simp [tensorHermiteScalar, zeroContraction, degreeMonomialFamily, rest, p, q]
  have he : degreeMonomialFamily n hn i - ((tensorHermiteScale n p q : ℂ)⁻¹) •
      degreeHermiteFamily n hn i = -rest := by
    rw [hg, smul_smul]
    simp only [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
      (tensorHermiteScale_pos n hn p q).ne'), one_smul]
    abel
  rw [he]
  exact Submodule.neg_mem _ hrest

/-- Ordinary normalized Gram–Schmidt on all mixed tensor monomials of the
concrete Gaussian precision `n`, ordered by degree and an injective tie-breaker,
recovers the actual normalized tensor Hermite family. -/
theorem gaussian_tensor_mixed_monomial_gramSchmidt (n : ℕ) (hn : 0 < n)
    (i : DegreeHermiteIndex n) :
    InnerProductSpace.gramSchmidtNormed ℂ
      (fun j : DegreeHermiteIndex n => multivariateMixedMonomialL2 n hn j.val.1 j.val.2) i =
      multivariateNormalizedL2 n hn i.val.1 i.val.2 := by
  have hg : Orthonormal ℂ (degreeHermiteFamily n hn) :=
    (orthonormal_hermiteL2Family_gaussian n hn).comp DegreeHermiteIndex.val
      (fun i j h => DegreeHermiteIndex.ext h)
  have h := gramSchmidtNormed_of_positive_triangular
    (degreeMonomialFamily n hn) (degreeHermiteFamily n hn) hg
    (fun i => (tensorHermiteScale n i.val.1 i.val.2)⁻¹)
    (fun i => inv_pos.mpr (tensorHermiteScale_pos n hn _ _))
    (fun i => by simpa only [Complex.ofReal_inv] using degreeMonomial_triangular n hn i)
  exact congrFun h i

end
end GinibrePoincare
