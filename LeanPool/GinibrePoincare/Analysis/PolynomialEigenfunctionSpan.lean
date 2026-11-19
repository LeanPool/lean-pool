/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/PolynomialEigenfunctionSpan.lean.
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

public import LeanPool.GinibrePoincare.Analysis.PolynomialEigenfunctions
public import LeanPool.GinibrePoincare.Analysis.HermiteMonomialSpan
public import Mathlib.LinearAlgebra.Finsupp.Span

/-! # Finite Hermite–Laguerre expansions of the actual polynomial algebra -/

@[expose] public section
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- Evaluation of the three formal variables at the paper's actual observables. -/
def sumRadiusEvaluation (n : ℕ) : MvPolynomial (Fin 3) ℂ →ₗ[ℂ] (Configuration n → ℂ) where
  toFun Q z := MvPolynomial.eval ![SObservable z, conj (SObservable z), (RPoly z : ℂ)] Q
  map_add' P Q := by ext z; simp
  map_smul' c Q := by ext z; simp

/-- The actual polynomial algebra in `S`, `conj S` and `R`, as a complex subspace. -/
def sumRadiusPolynomialSpace (n : ℕ) : Submodule ℂ (Configuration n → ℂ) :=
  (sumRadiusEvaluation n).range

/-- The span of the concrete Hermite–Laguerre eigenfunctions. -/
def polynomialEigenfunctionSpan (n : ℕ) : Submodule ℂ (Configuration n → ℂ) :=
  Submodule.span ℂ (Set.range (polynomialEigenfunction n))

theorem mem_sumRadiusPolynomialSpace_iff (n : ℕ) (f : Configuration n → ℂ) :
    f ∈ sumRadiusPolynomialSpace n ↔ IsPolynomialInSConjSR f := by
  constructor
  · rintro ⟨Q, hQ⟩
    exact ⟨Q, fun z => (congrFun hQ z).symm⟩
  · rintro ⟨Q, hQ⟩
    exact ⟨Q, funext fun z => (hQ z).symm⟩

private theorem hermite_times_radialPolynomial_mem_span (n a b : ℕ) (P : Polynomial ℝ) :
    (fun z : Configuration n => ComplexHermite.normalizedEval 1 (by decide) a b (SObservable z) *
      Complex.ofReal (P.eval (RPoly z))) ∈ polynomialEigenfunctionSpan n := by
  let k := recenteredGammaShape n
  have hp : P ∈ Submodule.span ℝ (Set.range (Laguerre.polynomial k)) := by
    have hb : (Laguerre.basis k : ℕ → Polynomial ℝ) = Laguerre.polynomial k :=
      funext (Laguerre.basis_apply k)
    rw [← hb]
    exact
      (show P ∈ Submodule.span ℝ (Set.range (Laguerre.basis k)) by
        rw [(Laguerre.basis k).span_eq]; trivial)
  induction hp using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨m, rfl⟩ := hP
    exact Submodule.subset_span ⟨⟨a, b, m⟩, rfl⟩
  | zero =>
    convert (polynomialEigenfunctionSpan n).zero_mem using 1
    ext z; simp
  | add P Q _ _ hP hQ =>
    convert (polynomialEigenfunctionSpan n).add_mem hP hQ using 1
    ext z
    simp [mul_add]
  | smul c P _ hP =>
    convert (polynomialEigenfunctionSpan n).smul_mem (c : ℂ) hP using 1
    ext z
    simp [smul_eq_mul]
    ring

/-- Every mixed sum/radius monomial is a finite combination of the concrete family. -/
theorem sum_radius_monomial_mem_span (n a b m : ℕ) :
    (fun z : Configuration n => (SObservable z)^a * (conj (SObservable z))^b *
      (RPoly z : ℂ)^m) ∈ polynomialEigenfunctionSpan n := by
  have hH := ComplexHermite.mixedMonomial_mem_normalizedEvalRectangleSpan 1 (by decide) a b
  change (fun s : ℂ => s^a * (conj s)^b) ∈ Submodule.span ℂ _ at hH
  have hprod : ∀ f ∈ ComplexHermite.normalizedEvalRectangleSpan 1 (by decide) a b,
      (fun z : Configuration n => f (SObservable z) * (RPoly z : ℂ)^m) ∈
        polynomialEigenfunctionSpan n := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨c, hc, d, hd, rfl⟩ := hf
      simpa using hermite_times_radialPolynomial_mem_span n c d (Polynomial.X^m)
    | zero =>
      convert (polynomialEigenfunctionSpan n).zero_mem using 1
      ext z; simp
    | add f g _ _ hf hg =>
      convert (polynomialEigenfunctionSpan n).add_mem hf hg using 1
      ext z
      simp [add_mul]
    | smul c f _ hf =>
      convert (polynomialEigenfunctionSpan n).smul_mem c hf using 1
      ext z
      simp [smul_eq_mul, mul_assoc]
  exact hprod _ hH

/-- The Hermite–Laguerre family spans the entire actual polynomial algebra. -/
theorem polynomialEigenfunctionSpan_eq (n : ℕ) :
    polynomialEigenfunctionSpan n = sumRadiusPolynomialSpace n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨ped, rfl⟩
    exact (mem_sumRadiusPolynomialSpace_iff n _).mpr (polynomialEigenfunction_isPolynomial n ped)
  · rintro f ⟨Q, rfl⟩
    induction Q using MvPolynomial.induction_on' with
    | add Q P hQ hP =>
      rw [map_add]
      exact (polynomialEigenfunctionSpan n).add_mem hQ hP
    | monomial d c =>
      have hm := (polynomialEigenfunctionSpan n).smul_mem c
        (sum_radius_monomial_mem_span n (d 0) (d 1) (d 2))
      convert hm using 1
      ext z
      simp only [sumRadiusEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
        MvPolynomial.eval_monomial, Pi.smul_apply, smul_eq_mul]
      rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
      simp [Fin.prod_univ_succ, mul_assoc]

/-- A polynomial observable admits an actual finite Hermite–Laguerre expansion. -/
theorem polynomialEigenfunction_finite_expansion (n : ℕ) (f : Configuration n → ℂ)
    (hf : IsPolynomialInSConjSR f) :
    ∃ c : PolynomialEigenfunctionData n →₀ ℂ,
      ∀ z, f z = c.sum (fun ped coeff => coeff * polynomialEigenfunction n ped z) := by
  have hs : f ∈ polynomialEigenfunctionSpan n := by
    rw [polynomialEigenfunctionSpan_eq]
    exact (mem_sumRadiusPolynomialSpace_iff n f).mpr hf
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hs
  refine ⟨c, ?_⟩
  intro z
  have he := (congrFun hc z).symm
  simpa [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he

end
end GinibrePoincare
