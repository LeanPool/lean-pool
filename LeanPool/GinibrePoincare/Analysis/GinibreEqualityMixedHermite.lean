/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityMixedHermite.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityMixedPolynomial
public import LeanPool.GinibrePoincare.Analysis.HermiteEnergy

/-!
# Ginibre Equality Mixed Hermite
-/


@[expose] public section

noncomputable section
namespace GinibrePoincare
open MvPolynomial ComplexHermite
open scoped BigOperators ComplexConjugate

/-- The mixed polynomial representing a product of normalized one-coordinate Hermite
polynomials. -/
def ginibreMixedHermitePolynomial (n : ℕ) (hn : 0 < n) (p q : Fin n → ℕ) : GinibreMixedPolynomial
  n :=
  ∏ j : Fin n, MvPolynomial.rename (fun k : Fin 2 => (j, k)) (normalized n hn (p j) (q j))

theorem ginibreMixedHermitePolynomial_eval (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) (z : Configuration n) :
    ginibreMixedPolynomialEval (ginibreMixedHermitePolynomial n hn p q) z =
      multivariateNormalized n hn p q z := by
  unfold ginibreMixedPolynomialEval ginibreMixedHermitePolynomial multivariateNormalized
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [MvPolynomial.eval_rename]
  unfold normalizedEval
  have hv : ((fun k : Fin n × Fin 2 => if k.2=0 then z k.1 else conj (z k.1)) ∘
      fun k : Fin 2 => (j, k)) = ![z j, conj (z j)] := by
    funext k
    fin_cases k <;> simp
  rw [hv]

private theorem ginibreMixedHermiteCoordinate_specialize_degree (n : ℕ) (hn : 0 < n)
    (p q : ℕ) (j : Fin n) (z : Configuration n) :
    (ginibreMixedPolynomialSpecialize z
      (MvPolynomial.rename (fun k : Fin 2 => (j, k)) (normalized n hn p q))).totalDegree ≤ q := by
  classical
  unfold ginibreMixedPolynomialSpecialize
  rw [MvPolynomial.aeval_rename]
  unfold normalized raw
  rw [map_mul, map_sum]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp only [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  simp only [map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Z, W,
    MvPolynomial.aeval_X, Function.comp_apply]
  simp only [ite_true, show (1 : Fin 2)≠0 by decide, ite_false]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp only [←map_pow,←map_mul, MvPolynomial.totalDegree_C, totalDegree_X_pow, zero_add]
  exact Nat.sub_le q k

/-- The formal mixed Hermite tensor has antiholomorphic degree at most its
actual antiholomorphic multi-index degree after every holomorphic specialization. -/
theorem ginibreMixedHermitePolynomial_specialize_degree (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) (z : Configuration n) :
    (ginibreMixedPolynomialSpecialize z (ginibreMixedHermitePolynomial n hn p q)).totalDegree ≤
      ∑ j : Fin n, q j := by
  unfold ginibreMixedHermitePolynomial
  rw [map_prod]
  exact (MvPolynomial.totalDegree_finsetProd _ _).trans
    (Finset.sum_le_sum (fun j _ => ginibreMixedHermiteCoordinate_specialize_degree n hn (p j) (q
      j) j z))

/-- The mixed polynomial associated with a finitely supported Hermite expansion. -/
def ginibreMixedFiniteHermitePolynomial (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) : GinibreMixedPolynomial n :=
  c.sum (fun pq a => C a * ginibreMixedHermitePolynomial n hn pq.1 pq.2)

theorem ginibreMixedFiniteHermitePolynomial_eval (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (z : Configuration n) :
    ginibreMixedPolynomialEval (ginibreMixedFiniteHermitePolynomial n hn c) z =
      finiteHermiteFunction n hn c z := by
  classical
  simp only [ginibreMixedPolynomialEval, ginibreMixedFiniteHermitePolynomial, Finsupp.sum,
    map_sum, map_mul, MvPolynomial.eval_C]
  unfold finiteHermiteFunction
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro pq hpq
  rw [←ginibreMixedPolynomialEval, ginibreMixedHermitePolynomial_eval]

/-- An actual finite Hermite combination with antiholomorphic degrees ≤K
has a formal mixed polynomial representative with the same specialization bound. -/
theorem ginibreMixedFiniteHermitePolynomial_specialize_degree (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (K : ℕ)
    (hc : ∀ pq ∈ c.support, totalAntiDegree pq ≤ K) (z : Configuration n) :
    (ginibreMixedPolynomialSpecialize z (ginibreMixedFiniteHermitePolynomial n hn c)).totalDegree
      ≤ K := by
  classical
  unfold ginibreMixedFiniteHermitePolynomial Finsupp.sum
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro pq hpq
  rw [map_mul]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp only [ginibreMixedPolynomialSpecialize, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
    MvPolynomial.totalDegree_C, zero_add]
  exact (ginibreMixedHermitePolynomial_specialize_degree n hn pq.1 pq.2 z).trans (hc pq hpq)

end GinibrePoincare
