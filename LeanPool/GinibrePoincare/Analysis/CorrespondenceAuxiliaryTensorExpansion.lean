/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryTensorExpansion.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryHermiteRectangleL2
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs

/-!
# Correspondence auxiliary tensor expansion

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `tensorHermiteScale_pos`, `multivariateNormalizedL2_tensor_expansion`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- The product `∏ j, oneDimNormalization n (p j) * oneDimNormalization n (q j)` of
one-dimensional Hermite normalization constants. -/
def tensorHermiteScale (n : ℕ) (p q : Fin n → ℕ) : ℝ :=
  ∏ j, oneDimNormalization n (p j) * oneDimNormalization n (q j)

theorem tensorHermiteScale_pos (n : ℕ) (hn : 0 < n) (p q : Fin n → ℕ) :
    0 < tensorHermiteScale n p q := by
  unfold tensorHermiteScale oneDimNormalization
  apply Finset.prod_pos
  intro j hj
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

/-- Contraction orders in the tensor expansion: a choice of `k j ≤ min (p j) (q j)` for each
coordinate `j`. -/
abbrev TensorHermiteContraction {n : ℕ} (p q : Fin n → ℕ) :=
  ∀ j, Fin (min (p j) (q j)+1)

/-- The coefficient `∏ j, (-n⁻¹) ^ k j * (k j)! * (p j).choose (k j) * (q j).choose (k j)` of the
contraction `k` in the tensor expansion. -/
def tensorHermiteScalar {n : ℕ} (p q : Fin n → ℕ)
    (k : TensorHermiteContraction p q) : ℂ :=
  ∏ j, (-((n : ℝ)⁻¹ : ℂ))^(k j).val * ((k j).val.factorial : ℂ) *
    (Nat.choose (p j) (k j).val : ℂ) * (Nat.choose (q j) (k j).val : ℂ)

theorem multivariateNormalized_tensor_expansion (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) (z : Configuration n) :
    multivariateNormalized n hn p q z = (tensorHermiteScale n p q : ℂ) *
      ∑ k : TensorHermiteContraction p q, tensorHermiteScalar p q k *
        ∏ j, z j^(p j-(k j).val) * conj (z j)^(q j-(k j).val) := by
  classical
  simp only [multivariateNormalized, normalizedEval_eq_sum]
  rw [Finset.prod_mul_distrib]
  have hsum (j : Fin n) :
      (∑ k ∈ Finset.range (min (p j) (q j)+1),
        (-((n : ℝ)⁻¹ : ℂ))^k * (k.factorial : ℂ) * (Nat.choose (p j) k : ℂ) *
          (Nat.choose (q j) k : ℂ) * z j^(p j-k) * conj (z j)^(q j-k)) =
      ∑ k : Fin (min (p j) (q j)+1),
        (-((n : ℝ)⁻¹ : ℂ))^k.val * (k.val.factorial : ℂ) *
          (Nat.choose (p j) k.val : ℂ) * (Nat.choose (q j) k.val : ℂ) *
          (z j^(p j-k.val) * conj (z j)^(q j-k.val)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [hsum]
  rw [Fintype.prod_sum]
  congr 1
  · simp [tensorHermiteScale]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.prod_mul_distrib]
    rfl

theorem multivariateNormalizedL2_tensor_expansion (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) :
    multivariateNormalizedL2 n hn p q = (tensorHermiteScale n p q : ℂ) •
      ∑ k : TensorHermiteContraction p q, tensorHermiteScalar p q k •
        multivariateMixedMonomialL2 n hn (fun j => p j-(k j).val)
          (fun j => q j-(k j).val) := by
  classical
  apply Lp.ext
  have hall : ∀ᵐ z ∂complexGaussianMeasure n, ∀ k : TensorHermiteContraction p q,
      (tensorHermiteScalar p q k • multivariateMixedMonomialL2 n hn
        (fun j => p j-(k j).val) (fun j => q j-(k j).val)) z =
      tensorHermiteScalar p q k * ∏ j, z j^(p j-(k j).val) *
        conj (z j)^(q j-(k j).val) := by
    rw [ae_all_iff]
    intro k
    filter_upwards [Lp.coeFn_smul (tensorHermiteScalar p q k)
      (multivariateMixedMonomialL2 n hn (fun j => p j-(k j).val)
        (fun j => q j-(k j).val)),
      (memLp_two_multivariateMixedMonomial n hn (fun j => p j-(k j).val)
        (fun j => q j-(k j).val)).coeFn_toLp] with z h1 h2
    rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul]
    change tensorHermiteScalar p q k * (memLp_two_multivariateMixedMonomial n hn
      (fun j => p j-(k j).val) (fun j => q j-(k j).val)).toLp _ z = _
    rw [h2]
  filter_upwards [multivariateNormalizedL2_coeFn n hn p q,
    Lp.coeFn_smul (tensorHermiteScale n p q : ℂ)
      (∑ k : TensorHermiteContraction p q, tensorHermiteScalar p q k •
        multivariateMixedMonomialL2 n hn (fun j => p j-(k j).val)
          (fun j => q j-(k j).val)),
    Lp.coeFn_fun_finsetSum Finset.univ (fun k : TensorHermiteContraction p q =>
      tensorHermiteScalar p q k • multivariateMixedMonomialL2 n hn
        (fun j => p j-(k j).val) (fun j => q j-(k j).val)), hall]
    with z hF hs hsum hall
  rw [hF, hs]
  simp only [Pi.smul_apply, smul_eq_mul, hsum]
  simp_rw [hall]
  exact multivariateNormalized_tensor_expansion n hn p q z

end
end GinibrePoincare
