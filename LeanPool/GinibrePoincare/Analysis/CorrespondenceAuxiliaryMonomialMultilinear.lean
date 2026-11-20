/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryMonomialMultilinear.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianEntireRepresentatives
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Correspondence auxiliary monomial multilinear

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `holomorphicMonomialMultilinear_diagonal`, `holomorphicMonomialMultilinear_norm_le`,
`finite_holomorphic_degree_fiber`.
-/

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- A coordinate word gives an actual continuous homogeneous multilinear map
whose diagonal is the corresponding holomorphic coordinate monomial. -/
def coordinateWordMultilinear {n k : ℕ} (word : Fin k → Fin n) :
    ContinuousMultilinearMap ℂ (fun _ : Fin k => Configuration n) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ).compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj (word i))

@[simp] theorem coordinateWordMultilinear_apply {n k : ℕ} (word : Fin k → Fin n)
    (v : Fin k → Configuration n) :
    coordinateWordMultilinear word v = ∏ i, v i (word i) := by
  simp [coordinateWordMultilinear, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    List.prod_ofFn]

/-- Uniform operator bound needed to construct the genuine multivariate
holomorphic Taylor series; this holds also in degree zero. -/
theorem coordinateWordMultilinear_norm_le {n k : ℕ} (word : Fin k → Fin n) :
    ‖coordinateWordMultilinear word‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by norm_num)
  intro v
  rw [coordinateWordMultilinear_apply, norm_prod, one_mul]
  gcongr with i
  exact norm_le_pi_norm (v i) (word i)

/-- The canonical finite coordinate word with precisely the specified
multiplicities. -/
def monomialCoordinateWord {n : ℕ} (p : Fin n → ℕ) :
    Fin (∑ i, p i) → Fin n :=
  fun j => ((Fintype.equivFinOfCardEq
    (show Fintype.card (Σ i : Fin n, Fin (p i)) = ∑ i, p i by simp)).symm j).1

/-- The continuous multilinear map whose value on the diagonal `(z, …, z)` is the holomorphic
monomial `∏ i, z i ^ p i`. -/
def holomorphicMonomialMultilinear {n : ℕ} (p : Fin n → ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (∑ i, p i) => Configuration n) ℂ :=
  coordinateWordMultilinear (monomialCoordinateWord p)

@[simp] theorem holomorphicMonomialMultilinear_diagonal {n : ℕ}
    (p : Fin n → ℕ) (z : Configuration n) :
    holomorphicMonomialMultilinear p (fun _ => z) = ∏ i, z i ^ p i := by
  rw [holomorphicMonomialMultilinear, coordinateWordMultilinear_apply]
  let e := Fintype.equivFinOfCardEq
    (show Fintype.card (Σ i : Fin n, Fin (p i)) = ∑ i, p i by simp)
  change (∏ j : Fin (∑ i, p i), z (e.symm j).1) = _
  rw [e.symm.prod_comp (fun j : Σ i : Fin n, Fin (p i) => z j.1)]
  simp [Fintype.prod_sigma]

theorem holomorphicMonomialMultilinear_norm_le {n : ℕ} (p : Fin n → ℕ) :
    ‖holomorphicMonomialMultilinear p‖ ≤ 1 :=
  coordinateWordMultilinear_norm_le _

/-- Every homogeneous multivariate degree contains only finitely many
monomials, including the zero-dimensional case. -/
theorem finite_holomorphic_degree_fiber (n k : ℕ) :
    Set.Finite {p : Fin n → ℕ | ∑ i, p i = k} := by
  let f : {p : Fin n → ℕ // ∑ i, p i = k} → (Fin n → Fin (k+1)) :=
    fun p i => ⟨p.val i, by
      have hi : p.val i ≤ ∑ j, p.val j := Finset.single_le_sum
        (fun j _ => Nat.zero_le (p.val j)) (Finset.mem_univ i)
      omega⟩
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun h i)
  exact Set.finite_coe_iff.mp (Finite.of_injective f hf)

end
end GinibrePoincare
