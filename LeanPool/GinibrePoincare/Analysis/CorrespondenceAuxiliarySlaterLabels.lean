/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliarySlaterLabels.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeSlaterEigenfunctions
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Correspondence auxiliary Slater labels

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `slater_minimal_degree_iff`, `slater_canonical_ground_determinant`.
-/

@[expose] public section

open scoped BigOperators
namespace GinibrePoincare
noncomputable section

private theorem strictMono_fin_nat_lower {n : ℕ} (f : Fin n → ℕ)
    (hf : StrictMono f) (i : Fin n) : i.val ≤ f i := by
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hkn : k < n := by omega
    have hprev := ih hkn
    have hlt := hf (show (⟨k, hkn⟩ : Fin n) < ⟨k+1, hk⟩ by simp)
    simp only [] at hprev ⊢
    omega

/-- The exceptional minimal holomorphic Slater orbital set is precisely
`{0,…,n−1}`, without requiring a particular order of its labels. -/
theorem slater_minimal_orbital_labels_iff {n : ℕ} (p : Fin n → ℕ)
    (hp : Function.Injective p) :
    (∑ i, p i) = ∑ i : Fin n, i.val ↔
      Finset.univ.image p = Finset.range n := by
  classical
  let s := Finset.univ.image p
  have hs : s.card = n := by simp [s, Finset.card_image_of_injective _ hp]
  let f := s.orderEmbOfFin hs
  have hl : ∀ i : Fin n, i.val ≤ f i := strictMono_fin_nat_lower f f.strictMono
  have hsum : (∑ i : Fin n, f i) = ∑ i : Fin n, p i := by
    calc
      _ = ∑ k ∈ Finset.univ.image f, k := (Finset.sum_image f.injective.injOn).symm
      _ = ∑ k ∈ s, k := by rw [Finset.image_orderEmbOfFin_univ]
      _ = ∑ i : Fin n, p i := Finset.sum_image hp.injOn
  constructor
  · intro h
    have he : ∀ i : Fin n, f i = i.val := by
      have hsame : (∑ i : Fin n, i.val) = ∑ i : Fin n, f i := by omega
      have hall := (Finset.sum_eq_sum_iff_of_le (fun i _ => hl i)).mp hsame
      intro i
      exact (hall i (Finset.mem_univ i)).symm
    change s = Finset.range n
    rw [← Finset.image_orderEmbOfFin_univ s hs]
    change Finset.univ.image (fun i => f i) = Finset.range n
    simp_rw [he]
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ i.isLt, fun hk => ⟨⟨k, hk⟩, rfl⟩⟩
  · intro h
    calc
      _ = ∑ k ∈ Finset.univ.image p, k := (Finset.sum_image hp.injOn).symm
      _ = ∑ k ∈ Finset.range n, k := by rw [h]
      _ = ∑ i : Fin n, i.val := (Fin.sum_univ_eq_sum_range (fun i => i) n).symm

/-- Section 4's exceptional degree equality, with its displayed triangular
number normalization. -/
theorem slater_minimal_degree_iff {n : ℕ} (p : Fin n → ℕ)
    (hp : Function.Injective p) :
    (∑ i, p i) = n * (n - 1) / 2 ↔
      Finset.univ.image p = Finset.range n := by
  have hsum : (∑ i : Fin n, i.val) = n * (n - 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]
  rw [← hsum]
  exact slater_minimal_orbital_labels_iff p hp

/-- Exact Vandermonde alternant for the exceptional, increasingly ordered
orbital tuple. Its coefficient includes every Hermite and Slater factor. -/
theorem slater_canonical_ground_determinant {n : ℕ} (hn : 0 < n)
    (z : Configuration n) :
    slaterDeterminant hn ((fun i : Fin n => i.val), 0) z =
      ((Real.sqrt (slaterMultiplicity n) : ℂ)⁻¹ *
        ∏ i : Fin n, (ComplexHermite.oneDimNormalization n i.val : ℂ)) *
      vandermonde z := by
  unfold slaterDeterminant
  simp only [ComplexHermite.normalizedEval_zero_right, Pi.zero_apply]
  change (Real.sqrt (slaterMultiplicity n) : ℂ)⁻¹ *
    (Matrix.of (fun i j : Fin n =>
      (ComplexHermite.oneDimNormalization n i.val : ℂ) * z j ^ i.val)).det = _
  have hm := Matrix.det_mul_column (fun i : Fin n =>
    (ComplexHermite.oneDimNormalization n i.val : ℂ))
    (Matrix.of (fun i j : Fin n => z j ^ i.val))
  simp only [Matrix.of_apply] at hm
  rw [hm]
  have hd : (Matrix.of (fun i j : Fin n => z j ^ i.val)).det = vandermonde z := by
    change (Matrix.vandermonde z).transpose.det = vandermonde z
    rw [Matrix.det_transpose, Matrix.det_vandermonde, vandermonde_eq_product]
  rw [hd]
  ring

end
end GinibrePoincare
