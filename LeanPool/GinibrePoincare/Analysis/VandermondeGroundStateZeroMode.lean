/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/VandermondeGroundStateZeroMode.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianHermiteMoments
public import LeanPool.GinibrePoincare.Analysis.VandermondeL2
public import LeanPool.GinibrePoincare.Analysis.HermiteParsevalModes
public import LeanPool.GinibrePoincare.Analysis.HolomorphicVandermondeDivision

/-!
# Vandermonde Ground State Zero Mode
-/


@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace GinibrePoincare

noncomputable section

open ComplexHermite

/-- A holomorphic coordinate monomial is an algebraic zero-antiholomorphic
Hermite vector. -/
theorem exists_memLp_holomorphicMonomial_mem_antiDegreeZeroSpan
    (n : ℕ) (hn : 0 < n) (p : Fin n → ℕ) :
    ∃ hmem : MemLp (fun z : Configuration n => ∏ i, z i ^ p i) 2
        (complexGaussianMeasure n),
      hmem.toLp (fun z : Configuration n => ∏ i, z i ^ p i) ∈
        hermiteAntiDegreeSpan n hn 0 := by
  have hpoint : (fun z : Configuration n => ∏ i, z i ^ p i) ∈
      multivariateNormalizedRectangleSpan n hn p 0 := by
    rw [multivariateNormalizedRectangleSpan_eq_mixedMonomialRectangleSpan]
    apply Submodule.subset_span
    refine ⟨p, 0, fun _ => le_rfl, fun _ => le_rfl, ?_⟩
    funext z
    simp
  have lift : ∀ {F : Configuration n → ℂ},
      F ∈ multivariateNormalizedRectangleSpan n hn p 0 →
      ∃ hmem : MemLp F 2 (complexGaussianMeasure n),
        hmem.toLp F ∈ hermiteAntiDegreeSpan n hn 0 := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem f hf =>
        rcases hf with ⟨a, b, ha, hb, rfl⟩
        have hb0 : b = 0 := by funext i; exact Nat.eq_zero_of_le_zero (hb i)
        subst b
        refine ⟨memLp_two_multivariateNormalized n hn a 0, ?_⟩
        apply Submodule.subset_span
        exact ⟨(a, 0), by simp [totalAntiDegree], rfl⟩
    | zero => exact ⟨MemLp.zero, by simp⟩
    | add x y hx hy ihx ihy =>
        rcases ihx with ⟨hxmem, hxspan⟩
        rcases ihy with ⟨hymem, hyspan⟩
        refine ⟨hxmem.add hymem, ?_⟩
        rw [MemLp.toLp_add hxmem hymem]
        exact (hermiteAntiDegreeSpan n hn 0).add_mem hxspan hyspan
    | smul c x hx ih =>
        rcases ih with ⟨hxmem, hxspan⟩
        refine ⟨hxmem.const_smul c, ?_⟩
        rw [MemLp.toLp_const_smul c hxmem]
        exact (hermiteAntiDegreeSpan n hn 0).smul_mem c hxspan
  exact lift hpoint

/-- Evaluation of every holomorphic configuration polynomial is an
algebraic zero-antiholomorphic Hermite vector. -/
theorem exists_memLp_configurationPolynomial_mem_antiDegreeZeroSpan
    (n : ℕ) (hn : 0 < n) (P : ConfigurationPolynomial n) :
    ∃ hmem : MemLp (fun z : Configuration n => MvPolynomial.eval z P) 2
        (complexGaussianMeasure n),
      hmem.toLp (fun z : Configuration n => MvPolynomial.eval z P) ∈
        hermiteAntiDegreeSpan n hn 0 := by
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
      obtain ⟨hm, hspan⟩ :=
        exists_memLp_holomorphicMonomial_mem_antiDegreeZeroSpan n hn
          (fun i => u i)
      have heval : (fun z : Configuration n =>
          MvPolynomial.eval z (MvPolynomial.monomial u c)) =
          fun z => c * ∏ i, z i ^ u i := by
        funext z
        rw [MvPolynomial.eval_monomial]
        congr 1
        rw [Finsupp.prod]
        apply Finset.prod_subset (Finset.subset_univ _)
        intro i hi hnot
        have hz : u i = 0 := by simpa using hnot
        rw [hz, pow_zero]
      rw [heval]
      refine ⟨hm.const_smul c, ?_⟩
      change (hm.const_smul c).toLp
        (c • fun z : Configuration n => ∏ i, z i ^ u i) ∈ _
      rw [MemLp.toLp_const_smul c hm]
      exact (hermiteAntiDegreeSpan n hn 0).smul_mem c hspan
  | add P Q ihP ihQ =>
      rcases ihP with ⟨hP, hPspan⟩
      rcases ihQ with ⟨hQ, hQspan⟩
      have heval : (fun z : Configuration n => MvPolynomial.eval z (P + Q)) =
          (fun z => MvPolynomial.eval z P) + fun z => MvPolynomial.eval z Q := by
        funext z
        simp
      rw [heval]
      refine ⟨hP.add hQ, ?_⟩
      rw [MemLp.toLp_add hP hQ]
      exact (hermiteAntiDegreeSpan n hn 0).add_mem hPspan hQspan

/-- The normalized Vandermonde ground state, regarded as a Gaussian `L²`
vector.  Its representative is
`groundStateNormalization n⁻¹ * vandermonde`. -/
def normalizedVandermondeGroundStateL2 (n : ℕ) (hn : 0 < n) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  ((groundStateNormalization n : ℂ)⁻¹) •
    ((exists_memLp_configurationPolynomial_mem_antiDegreeZeroSpan n hn
      (polynomialVandermonde n)).choose.toLp
        (fun z : Configuration n =>
          MvPolynomial.eval z (polynomialVandermonde n)))

/-- The normalized Vandermonde ground state is a zero-antiholomorphic-degree
Hermite vector. -/
theorem normalizedVandermondeGroundStateL2_mem_hermiteAntiDegreeClosedSpan
    (n : ℕ) (hn : 0 < n) :
    normalizedVandermondeGroundStateL2 n hn ∈
      hermiteAntiDegreeClosedSpan n hn 0 := by
  apply (hermiteAntiDegreeClosedSpan n hn 0).toSubmodule.smul_mem
  exact (hermiteAntiDegreeSpan n hn 0).le_topologicalClosure
    (exists_memLp_configurationPolynomial_mem_antiDegreeZeroSpan n hn
      (polynomialVandermonde n)).choose_spec

/-- Pointwise representative of the normalized Vandermonde ground state. -/
theorem normalizedVandermondeGroundStateL2_coeFn (n : ℕ) (hn : 0 < n) :
    (normalizedVandermondeGroundStateL2 n hn : Configuration n → ℂ) =ᵐ[
      complexGaussianMeasure n]
      normalizedVandermondeMultiplier n := by
  unfold normalizedVandermondeGroundStateL2
  let hP := (exists_memLp_configurationPolynomial_mem_antiDegreeZeroSpan n hn
    (polynomialVandermonde n)).choose
  filter_upwards [Lp.coeFn_smul ((groundStateNormalization n : ℂ)⁻¹)
      (hP.toLp (fun z : Configuration n =>
        MvPolynomial.eval z (polynomialVandermonde n))),
    hP.coeFn_toLp] with z hsmul heval
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [heval]
  rw [eval_polynomialVandermonde]
  rfl

end
end GinibrePoincare
