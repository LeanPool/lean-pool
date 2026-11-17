/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityPolynomial.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HolomorphicVandermondeDivision
public import LeanPool.GinibrePoincare.Concrete.CenterOfMass
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Ginibre Equality Polynomial
-/


@[expose] public section

namespace GinibrePoincare
noncomputable section
open scoped BigOperators

/-- A degree-one homogeneous configuration polynomial has only linear terms. -/
theorem ginibreEquality_homogeneous_one_expansion {n : ℕ}
    (P : ConfigurationPolynomial n) (hP : P.IsHomogeneous 1) :
    P = ∑ i : Fin n, MvPolynomial.C (P.coeff (Finsupp.single i 1)) * MvPolynomial.X i := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hd : d.degree = 1
  · have hdmem : d ∈ Set.range (fun i : Fin n => Finsupp.single i 1) := by
      rw [Finsupp.range_single_one]
      exact hd
    obtain ⟨i, rfl⟩ := hdmem
    simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X,
      Finsupp.single_eq_single_iff]
  · rw [hP.coeff_eq_zero hd]
    rw [MvPolynomial.coeff_sum]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, ite_eq_right, mul_zero]
    intro h
    apply hd
    rw [← h]
    simp

/-- Symmetry forces all degree-one coefficients to agree. -/
theorem ginibreEquality_symmetric_linear_coeff {n : ℕ}
    (P : ConfigurationPolynomial n) (hP : IsSymmetricConfigurationPolynomial P)
    (i j : Fin n) :
    P.coeff (Finsupp.single i 1) = P.coeff (Finsupp.single j 1) := by
  classical
  let σ : ParticlePermutation n := Equiv.swap i j
  have hs := congrArg (fun Q : ConfigurationPolynomial n => Q.coeff (Finsupp.single (σ i) 1)) (hP σ)
  change (MvPolynomial.rename σ P).coeff (Finsupp.single (σ i) 1) = _ at hs
  have hr := MvPolynomial.coeff_rename_mapDomain σ σ.injective P (Finsupp.single i 1)
  rw [Finsupp.mapDomain_single] at hr
  rw [hr] at hs
  simpa [σ] using hs

/-- The entire symmetric holomorphic homogeneous degree-one sector consists
of scalar multiples of the coordinate-sum polynomial. -/
theorem ginibreEquality_symmetric_homogeneous_one {n : ℕ} (hn : 0 < n)
    (P : ConfigurationPolynomial n) (hP : IsSymmetricConfigurationPolynomial P)
    (hdegree : P.IsHomogeneous 1) :
    ∃ c : ℂ, P = MvPolynomial.C c * ∑ i : Fin n, MvPolynomial.X i := by
  let i : Fin n := ⟨0, hn⟩
  refine ⟨P.coeff (Finsupp.single i 1), ?_⟩
  calc
    P = ∑ j : Fin n, MvPolynomial.C (P.coeff (Finsupp.single j 1)) *
        MvPolynomial.X j := ginibreEquality_homogeneous_one_expansion P hdegree
    _ = MvPolynomial.C (P.coeff (Finsupp.single i 1)) * ∑ j : Fin n, MvPolynomial.X j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [ginibreEquality_symmetric_linear_coeff P hP j i]

/-- The actual observable in this sector is a scalar coordinate sum. -/
theorem ginibreEquality_symmetric_homogeneous_one_eval {n : ℕ} (hn : 0 < n)
    (P : ConfigurationPolynomial n) (hP : IsSymmetricConfigurationPolynomial P)
    (hdegree : P.IsHomogeneous 1) :
    ∃ c : ℂ, ∀ z : Configuration n, MvPolynomial.eval z P = c * coordinateSum z := by
  obtain ⟨c, hc⟩ := ginibreEquality_symmetric_homogeneous_one hn P hP hdegree
  refine ⟨c, ?_⟩
  intro z
  rw [hc]
  simp [coordinateSum]

/-- An alternating Vandermonde multiple with homogeneous degree-one quotient
has precisely the first symmetric holomorphic form. -/
theorem ginibreEquality_alternating_degree_one_quotient {n : ℕ} (hn : 0 < n)
    (Q : ConfigurationPolynomial n)
    (hAlt : IsAlternatingConfigurationPolynomial (polynomialVandermonde n * Q))
    (hdegree : Q.IsHomogeneous 1) :
    ∃ c : ℂ, polynomialVandermonde n * Q =
      MvPolynomial.C c * polynomialVandermonde n * ∑ i : Fin n, MvPolynomial.X i := by
  obtain ⟨c, hc⟩ := ginibreEquality_symmetric_homogeneous_one hn Q
    (isSymmetric_quotient_of_vandermonde_mul_alternating hAlt) hdegree
  refine ⟨c, ?_⟩
  rw [hc]
  ring


/-- Removing the constant term from a polynomial of total degree at most one
leaves a homogeneous linear polynomial. -/
theorem ginibreEquality_affine_homogeneous_part {n : ℕ}
    (P : ConfigurationPolynomial n) (hdegree : P.totalDegree ≤ 1) :
    (P - MvPolynomial.C (P.coeff 0)).IsHomogeneous 1 := by
  classical
  intro d hd
  have hd0 : d ≠ 0 := by
    intro hz
    subst d
    simp at hd
  have hcoeff : P.coeff d ≠ 0 := by
    simpa [MvPolynomial.coeff_sub, MvPolynomial.coeff_C, hd0, Ne.symm hd0] using hd
  have hle : d.degree ≤ 1 :=
    (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoeff)).trans hdegree
  have hpos : d.degree ≠ 0 := by
    simpa [Finsupp.degree_eq_zero_iff] using hd0
  have heq : d.degree = 1 := by omega
  rw [Finsupp.degree_eq_weight_one, ← Pi.one_def] at heq
  exact heq

/-- Every symmetric holomorphic polynomial of total degree at most one is
an affine coordinate-sum observable, with no unproved analytic assumptions. -/
theorem ginibreEquality_symmetric_affine {n : ℕ} (hn : 0 < n)
    (P : ConfigurationPolynomial n) (hP : IsSymmetricConfigurationPolynomial P)
    (hdegree : P.totalDegree ≤ 1) :
    ∃ a c : ℂ, P = MvPolynomial.C a + MvPolynomial.C c * ∑ i : Fin n, MvPolynomial.X i := by
  have hsym : IsSymmetricConfigurationPolynomial (P - MvPolynomial.C (P.coeff 0)) := by
    intro σ
    rw [map_sub, hP σ]
    congr 1
    simp [permuteConfigurationPolynomial]
  obtain ⟨c, hc⟩ := ginibreEquality_symmetric_homogeneous_one hn
    (P - MvPolynomial.C (P.coeff 0)) hsym
    (ginibreEquality_affine_homogeneous_part P hdegree)
  refine ⟨P.coeff 0, c, ?_⟩
  exact (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)


/-- Pointwise affine center-of-mass classification of the degree-at-most-one
symmetric holomorphic polynomial sector. -/
theorem ginibreEquality_symmetric_affine_eval {n : ℕ} (hn : 0 < n)
    (P : ConfigurationPolynomial n) (hP : IsSymmetricConfigurationPolynomial P)
    (hdegree : P.totalDegree ≤ 1) :
    ∃ a c : ℂ, ∀ z : Configuration n, MvPolynomial.eval z P = a + c * coordinateSum z := by
  obtain ⟨a, c, hc⟩ := ginibreEquality_symmetric_affine hn P hP hdegree
  refine ⟨a, c, ?_⟩
  intro z
  rw [hc]
  simp [coordinateSum]

end
end GinibrePoincare
