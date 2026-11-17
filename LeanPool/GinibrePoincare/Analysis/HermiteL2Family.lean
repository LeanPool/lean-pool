/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteL2Family.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteBinomialIdentity
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianMoments
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The multivariate Hermite family in Gaussian `L²`

This file packages the normalized Hermite tensors as an orthonormal family,
conditional on the explicit mixed-moment formula.  It also defines the closed
spans and orthogonal projections associated with a fixed total
antiholomorphic degree.  No completeness assertion for the Hermite family is
made here.
-/


@[expose] public section


open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GinibrePoincare
namespace ComplexHermite

noncomputable section

/-- The joint pair of holomorphic and antiholomorphic multi-indices. -/
abbrev HermiteMultiIndex (n : ℕ) :=
  (Fin n → ℕ) × (Fin n → ℕ)

/-- The normalized multivariate Hermite family as vectors of Gaussian `L²`. -/
def hermiteL2Family (n : ℕ) (hn : 0 < n) :
    HermiteMultiIndex n → Lp ℂ 2 (complexGaussianMeasure n) :=
  fun pq => (memLp_two_multivariateNormalized n hn pq.1 pq.2).toLp
    (multivariateNormalized n hn pq.1 pq.2)

theorem hermiteL2Family_coeFn (n : ℕ) (hn : 0 < n)
    (pq : HermiteMultiIndex n) :
    hermiteL2Family n hn pq =ᵐ[complexGaussianMeasure n]
      multivariateNormalized n hn pq.1 pq.2 :=
  (memLp_two_multivariateNormalized n hn pq.1 pq.2).coeFn_toLp

/-- The `L²` inner product of two packaged Hermite tensors is their concrete
Gaussian integral. -/
theorem inner_hermiteL2Family_eq_integral (n : ℕ) (hn : 0 < n)
    (a b : HermiteMultiIndex n) :
    inner ℂ (hermiteL2Family n hn a) (hermiteL2Family n hn b) =
      ∫ z, conj (multivariateNormalized n hn a.1 a.2 z) *
          multivariateNormalized n hn b.1 b.2 z
        ∂complexGaussianMeasure n := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hermiteL2Family_coeFn n hn a,
    hermiteL2Family_coeFn n hn b] with z ha hb
  rw [RCLike.inner_apply, ha, hb]
  ring

/-- Under the mixed-moment formula, the packaged multivariate Hermites have
the Kronecker-delta inner products. -/
theorem inner_hermiteL2Family (n : ℕ) (hn : 0 < n)
    (hMom : MixedMomentFormula n) (a b : HermiteMultiIndex n) :
    inner ℂ (hermiteL2Family n hn a) (hermiteL2Family n hn b) =
      if a = b then 1 else 0 := by
  rw [inner_hermiteL2Family_eq_integral,
    multivariate_orthogonality_of_mixedMoments n hn hMom]
  by_cases h : a = b
  · subst b
    simp
  · have hab : ¬(a.1 = b.1 ∧ a.2 = b.2) := by
      intro hpq
      exact h (Prod.ext hpq.1 hpq.2)
    simp [h, hab]

/-- Under the mixed-moment formula, all normalized multivariate Hermite
tensors form an orthonormal indexed family in Gaussian `L²`. -/
theorem orthonormal_hermiteL2Family (n : ℕ) (hn : 0 < n)
    (hMom : MixedMomentFormula n) :
    Orthonormal ℂ (hermiteL2Family n hn) := by
  rw [orthonormal_iff_ite]
  exact inner_hermiteL2Family n hn hMom

/-- The normalized multivariate Hermite family is unconditionally
orthonormal for the concrete Gaussian measure. -/
theorem orthonormal_hermiteL2Family_gaussian (n : ℕ) (hn : 0 < n) :
    Orthonormal ℂ (hermiteL2Family n hn) := by
  apply orthonormal_hermiteL2Family n hn
  intro a b
  rw [show (∫ z : ℂ, z ^ a * (conj z) ^ b
      ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      complexGaussianMixedMoment n a b by rfl]
  rw [complexGaussianMixedMoment_formula hn]
  simp [div_eq_mul_inv]

/-- Total antiholomorphic degree of a joint Hermite multi-index. -/
def totalAntiDegree {n : ℕ} (pq : HermiteMultiIndex n) : ℕ :=
  ∑ i, pq.2 i

/-- Algebraic span of normalized Hermites of fixed total antiholomorphic
degree. -/
def hermiteAntiDegreeSpan (n : ℕ) (hn : 0 < n) (d : ℕ) :
    Submodule ℂ (Lp ℂ 2 (complexGaussianMeasure n)) :=
  Submodule.span ℂ
    (hermiteL2Family n hn '' {pq | totalAntiDegree pq = d})

/-- Closed `L²` subspace generated by normalized Hermites of fixed total
antiholomorphic degree. -/
def hermiteAntiDegreeClosedSpan (n : ℕ) (hn : 0 < n) (d : ℕ) :
    ClosedSubmodule ℂ (Lp ℂ 2 (complexGaussianMeasure n)) where
  toSubmodule := (hermiteAntiDegreeSpan n hn d).topologicalClosure
  isClosed' := (hermiteAntiDegreeSpan n hn d).isClosed_topologicalClosure

/-- Orthogonal projection onto the closed span of Hermites having total
antiholomorphic degree `d`. -/
def hermiteAntiDegreeProjection (n : ℕ) (hn : 0 < n) (d : ℕ) :
    Lp ℂ 2 (complexGaussianMeasure n) →L[ℂ]
      Lp ℂ 2 (complexGaussianMeasure n) :=
  (hermiteAntiDegreeClosedSpan n hn d).starProjection

/-- A Hermite tensor of total antiholomorphic degree `d` belongs to the
corresponding closed span. -/
theorem hermiteL2Family_mem_antiDegreeClosedSpan (n : ℕ) (hn : 0 < n)
    (pq : HermiteMultiIndex n) (d : ℕ) (hd : totalAntiDegree pq = d) :
    hermiteL2Family n hn pq ∈ hermiteAntiDegreeClosedSpan n hn d := by
  apply (hermiteAntiDegreeSpan n hn d).le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨pq, hd, rfl⟩

/-- The degree projection fixes each normalized Hermite tensor in that
degree. -/
theorem hermiteAntiDegreeProjection_apply_family (n : ℕ) (hn : 0 < n)
    (pq : HermiteMultiIndex n) (d : ℕ) (hd : totalAntiDegree pq = d) :
    hermiteAntiDegreeProjection n hn d (hermiteL2Family n hn pq) =
      hermiteL2Family n hn pq := by
  exact Submodule.starProjection_eq_self_iff.mpr
    (hermiteL2Family_mem_antiDegreeClosedSpan n hn pq d hd)

end
end ComplexHermite
end GinibrePoincare
