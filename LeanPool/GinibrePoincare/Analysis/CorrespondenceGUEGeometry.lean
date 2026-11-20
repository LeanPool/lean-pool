/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEGeometry.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEConvexity
public import LeanPool.GinibrePoincare.Analysis.GinibreCollisionCutoff
public import LeanPool.GinibrePoincare.Analysis.GinibreSmoothDistributionalGradient
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
/-!
# Correspondence GUE geometry

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueRawDensity_symmetric`, `gueRawDensity_zero_iff_collision`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open Set

/-- The embedding of a real point `x` into complex configurations, `i ↦ (x i : ℂ)`. -/
def gueComplexEmbedding (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : Configuration n :=
  fun i => (x i : ℂ)

theorem gue_pairs_eq_vandermonde (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (∏ p ∈ guePairs n, (x p.2-x p.1)^2) = vandermondeWeight (gueComplexEmbedding n x) := by
  unfold guePairs vandermondeWeight
  rw [vandermonde_eq_product]
  simp only [map_prod, gueComplexEmbedding,← Complex.ofReal_sub, Complex.normSq_ofReal]
  rw [Finset.prod_filter]
  have hp := Finset.prod_product (Finset.univ : Finset (Fin n)) Finset.univ
    (fun p : Fin n × Fin n => if p.1<p.2 then (x p.2-x p.1)^2 else 1)
  simp only [Finset.univ_product_univ] at hp
  rw [hp]
  apply Finset.prod_congr rfl
  intro i hi
  have hI : Finset.Ioi i = Finset.univ.filter (fun j : Fin n => i<j) := by
    ext j
    simp
  rw [hI, Finset.prod_filter]
  simp only [pow_two]

/-- The real GUE density is symmetric, by the genuine Vandermonde sign law. -/
theorem gueRawDensity_symmetric (n : ℕ) (σ : Fin n ≃ Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    gueRawDensity n (WithLp.toLp 2 (fun i => x (σ i))) = gueRawDensity n x := by
  unfold gueRawDensity
  rw [gue_pairs_eq_vandermonde, gue_pairs_eq_vandermonde]
  have hs : ∑ i, (WithLp.toLp 2 (fun i => x (σ i)) i)^2 = ∑ i, (x i)^2 := by
    simpa only [PiLp.toLp_apply] using Equiv.sum_comp σ (fun i => (x i)^2)
  rw [hs]
  congr 1
  exact vandermondeWeight_symmetric n σ (gueComplexEmbedding n x)

/-- Collisions lie in the exact zero set of the real GUE density. -/
theorem gueRawDensity_zero_iff_collision (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    gueRawDensity n x=0 ↔ ∃ i j : Fin n, i≠j ∧ x i=x j := by
  unfold gueRawDensity
  rw [gue_pairs_eq_vandermonde, mul_eq_zero]
  simp only [Real.exp_ne_zero, false_or]
  unfold vandermondeWeight
  rw [Complex.normSq_eq_zero, vandermonde_eq_zero_iff, mem_collisionSet_iff]
  simp [gueComplexEmbedding, and_comm]

end
end GinibrePoincare
