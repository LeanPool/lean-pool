/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteRodriguesMultivariate.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteRodriguesSmooth
public import LeanPool.GinibrePoincare.Analysis.HermiteRodriguesTensor

/-! Literal sequential coordinate Wirtinger derivatives of the multivariate Gaussian. -/

@[expose] public section
open scoped BigOperators ContDiff ComplexConjugate
namespace GinibrePoincare
namespace ComplexHermite
noncomputable section

/-- The one-variable Wirtinger operator `∂̄` when `bar` is true and `∂` otherwise. -/
def rodriguesOneOperator (bar : Bool) : (ℂ → ℂ) → ℂ → ℂ :=
  if bar then dbarOnePublic else dholOne

/-- The Wirtinger operator `∂̄_j` in coordinate `j` when `bar` is true and `∂_j` otherwise. -/
def rodriguesCoordinateOperator {m : ℕ} (bar : Bool) (j : Fin m) :
    (Configuration m → ℂ) → Configuration m → ℂ :=
  if bar then (fun F z => dbarComponent F j z) else (fun F z => dholComponent F j z)

/-- Applies to `F`, for each coordinate `j` in the list `l`, the `a j`-th iterate of
`rodriguesCoordinateOperator bar j`; the last entry of `l` acts first. -/
def rodriguesCoordinateSequence {m : ℕ} (bar : Bool) (a : Fin m → ℕ)
    (l : List (Fin m)) (F : Configuration m → ℂ) : Configuration m → ℂ :=
  l.foldr (fun j G => (rodriguesCoordinateOperator bar j)^[a j] G) F

theorem rodriguesCoordinate_tensor_iterate {m : ℕ} (bar : Bool)
    (f : Fin m → ℂ → ℂ) (hf : ∀ i, Differentiable ℝ (f i)) (j : Fin m) (r : ℕ)
    (hiter : ∀ k ≤ r, Differentiable ℝ ((rodriguesOneOperator bar)^[k] (f j))) :
    (rodriguesCoordinateOperator bar j)^[r] (fun z => ∏ i, f i (z i)) =
      fun z => ((rodriguesOneOperator bar)^[r] (f j)) (z j)*∏ i∈Finset.univ.erase j, f i (z i) := by
  cases bar
  · exact dholComponent_tensor_iterate f hf j r hiter
  · exact dbarComponent_tensor_iterate f hf j r hiter

theorem rodriguesCoordinateSequence_tensor {m : ℕ} (bar : Bool)
    (a : Fin m → ℕ) (f : Fin m → ℂ → ℂ)
    (hf : ∀ i k, Differentiable ℝ ((rodriguesOneOperator bar)^[k] (f i)))
    (l : List (Fin m)) (hl : l.Nodup) :
    rodriguesCoordinateSequence bar a l (fun z => ∏ i, f i (z i)) =
      fun z => ∏ i, ((rodriguesOneOperator bar)^[if i∈l then a i else 0] (f i)) (z i) := by
  induction l with
  | nil => simp [rodriguesCoordinateSequence]
  | cons j l ih =>
    have hj : j ∉ l := (List.nodup_cons.mp hl).1
    have hl' := (List.nodup_cons.mp hl).2
    change (rodriguesCoordinateOperator bar j)^[a j]
      (rodriguesCoordinateSequence bar a l (fun z => ∏ i, f i (z i))) = _
    rw [ih hl']
    rw [rodriguesCoordinate_tensor_iterate bar _ (fun i => hf i _) j (a j)]
    · funext z
      rw [← Finset.mul_prod_erase Finset.univ
        (fun i => ((rodriguesOneOperator bar)^[if i∈j::l then a i else 0] (f i)) (z i))
            (Finset.mem_univ j)]
      congr 1
      · simp [hj]
      · apply Finset.prod_congr rfl
        intro i hi
        have hij : i ≠ j := (Finset.mem_erase.mp hi).1
        simp [hij]
    · intro k hk
      simpa [hj] using hf j k

/-- The actual normalized Gaussian before differentiation. -/
def rodriguesMultivariateGaussian (n : ℕ) (z : Configuration n) : ℂ :=
  (Real.exp (-(n : ℝ)*configurationNormSq z) : ℂ)

theorem rodriguesMultivariateGaussian_eq_product (n : ℕ) :
    rodriguesMultivariateGaussian n = fun z => ∏ i, rodriguesGaussian n (z i) := by
  funext z
  unfold rodriguesMultivariateGaussian rodriguesGaussian configurationNormSq
  rw [← Complex.ofReal_prod,← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

/-- The literal ordered multivariate mixed derivative appearing in the appendix. -/
def rodriguesMultivariateDerivative (n : ℕ) (p q : Fin n → ℕ) : Configuration n → ℂ :=
  rodriguesCoordinateSequence true p (List.finRange n)
    (rodriguesCoordinateSequence false q (List.finRange n) (rodriguesMultivariateGaussian n))

theorem rodriguesMultivariateDerivative_eq_product (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) :
    rodriguesMultivariateDerivative n p q =
      fun z => ∏ i, (dbarOnePublic^[p i] (dholOne^[q i] (rodriguesGaussian n))) (z i) := by
  unfold rodriguesMultivariateDerivative
  rw [rodriguesMultivariateGaussian_eq_product,
    rodriguesCoordinateSequence_tensor false q _
      (fun i k => (contDiff_iterate_dhol_gaussian n k).differentiable (by simp))
      (List.finRange n) (List.nodup_finRange n)]
  simp only [List.mem_finRange, ite_true, rodriguesOneOperator, Bool.false_eq_true, ite_false]
  rw [rodriguesCoordinateSequence_tensor true p _
      (fun i k => (contDiff_iterate_mixed_gaussian n hn k (q i)).differentiable (by simp))
      (List.finRange n) (List.nodup_finRange n)]
  simp only [List.mem_finRange, ite_true, rodriguesOneOperator]

theorem rodriguesMultivariate_normalization_product (n : ℕ) (p q : Fin n → ℕ) :
    (∏ i, (-1 : ℂ)^(p i + q i)/
      ((Real.sqrt ((p i).factorial*(q i).factorial : ℕ) : ℂ)*(Real.sqrt (n : ℝ) : ℂ)^(p i + q i))) =
      (-1 : ℂ)^(∑ i : Fin n, (p i + q i))/
        ((Real.sqrt ((∏ i : Fin n, (p i).factorial)*(∏ i : Fin n, (q i).factorial) : ℕ) : ℂ)*
          (Real.sqrt (n : ℝ) : ℂ)^(∑ i : Fin n, (p i + q i))) := by
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  congr 2
  rw [← Complex.ofReal_prod]
  rw [← Real.sqrt_prod Finset.univ (fun i _ => Nat.cast_nonneg ((p i).factorial*(q i).factorial))]
  congr 2
  push_cast
  rw [Finset.prod_mul_distrib]

/-- Literal factorial-normalized multivariate Rodrigues formula, using the actual
ordered coordinate derivatives of exp(−n|z|²), with no regularity assumptions. -/
theorem multivariateNormalized_rodrigues (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) (z : Configuration n) :
    multivariateNormalized n hn p q z =
      (-1 : ℂ)^(∑ i : Fin n, (p i + q i))/
        ((Real.sqrt ((∏ i : Fin n, (p i).factorial)*(∏ i : Fin n, (q i).factorial) : ℕ) : ℂ)*
          (Real.sqrt (n : ℝ) : ℂ)^(∑ i : Fin n, (p i + q i)))*
      (Real.exp ((n : ℝ)*configurationNormSq z) : ℂ)*
      rodriguesMultivariateDerivative n p q z := by
  unfold multivariateNormalized
  simp_rw [normalizedEval_rodrigues_factorial n hn]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    rodriguesMultivariate_normalization_product]
  rw [rodriguesMultivariateDerivative_eq_product n hn]
  congr 1
  rw [← Complex.ofReal_prod,← Real.exp_sum]
  congr 1
  unfold configurationNormSq
  rw [Finset.mul_sum]

/-- Literal identification of the univariate Hermite family with a single
coordinate of the multivariate family, as stated in the appendix. -/
theorem multivariateNormalized_single_coordinate (n : ℕ) (hn : 0 < n)
    (j : Fin n) (a b : ℕ) (z : Configuration n) :
    multivariateNormalized n hn (Pi.single j a) (Pi.single j b) z =
      normalizedEval n hn a b (z j) := by
  unfold multivariateNormalized
  rw [Finset.prod_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · simp

end
end ComplexHermite
end GinibrePoincare
