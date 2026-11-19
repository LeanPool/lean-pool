/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteEntropyTensorization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.EntropyProductDecomposition
public import Mathlib.Analysis.Convex.Jensen

/-!
# Finite entropy tensorization

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `uniformFiniteEntropy_eq`, `uniformFiniteLSI_tensorization`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- The continuous extension of `x log x`, including at zero. -/
def entropyPhi (x : ℝ) : ℝ := x * Real.log x

/-- The perspective identity remains valid when its numerator vanishes. -/
theorem entropyPhi_div (u v : ℝ) (hv : v ≠ 0) :
    v * entropyPhi (u / v) = entropyPhi u - u * Real.log v := by
  by_cases hu : u = 0
  · simp [hu, entropyPhi]
  · unfold entropyPhi
    rw [Real.log_div hu hv]
    field_simp

/-- Finite log-sum inequality, with vanishing columns handled without positivity
certificates or regularization assumptions. -/
theorem finite_log_sum {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hzero : ∀ i, b i = 0 → a i = 0) (hB : 0 < ∑ i, b i) :
    entropyPhi (∑ i, a i) - (∑ i, a i) * Real.log (∑ i, b i) ≤
      ∑ i, (entropyPhi (a i) - a i * Real.log (b i)) := by
  let B := ∑ i, b i
  have hweights : ∑ i, b i / B = 1 := by
    rw [← Finset.sum_div]
    exact div_self hB.ne'
  have havg : ∑ i, (b i / B) * (a i / b i) = (∑ i, a i) / B := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hbi : b i = 0
    · simp [hbi, hzero i hbi]
    · field_simp
  have hj := Real.convexOn_mul_log.map_sum_le
    (t := Finset.univ) (w := fun i => b i / B) (p := fun i => a i / b i)
    (fun i _ => div_nonneg (hb i) hB.le) hweights
    (fun i _ => div_nonneg (ha i) (hb i))
  simp only [smul_eq_mul, havg] at hj
  have hterm (i : ι) : (b i / B) * entropyPhi (a i / b i) =
      (entropyPhi (a i) - a i * Real.log (b i)) / B := by
    by_cases hbi : b i = 0
    · simp [hbi, hzero i hbi, entropyPhi]
    · rw [← entropyPhi_div (a i) (b i) hbi]
      ring
  change entropyPhi ((∑ i, a i) / B) ≤ ∑ i, (b i / B) * entropyPhi (a i / b i) at hj
  simp_rw [hterm] at hj
  rw [← Finset.sum_div] at hj
  have hm := (mul_le_mul_of_nonneg_left hj hB.le)
  rw [entropyPhi_div _ B hB.ne', mul_div_cancel₀ _ hB.ne'] at hm
  exact hm

/-- The matrix form of entropy tensorization, before probability normalization. -/
theorem entropy_matrix_tensorization {α β : Type*} [Fintype α] [Fintype β]
    (h : α → β → ℝ) (hh : ∀ x y, 0 ≤ h x y) :
    (∑ x, entropyPhi (∑ y, h x y)) + (∑ y, entropyPhi (∑ x, h x y)) ≤
      (∑ x, ∑ y, entropyPhi (h x y)) + entropyPhi (∑ x, ∑ y, h x y) := by
  let T := ∑ x, ∑ y, h x y
  have hT : 0 ≤ T := Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => hh x y))
  by_cases ht : T = 0
  · have hz : ∀ x y, h x y = 0 := by
      intro x y
      have hx := (Finset.sum_eq_zero_iff_of_nonneg
        (fun x _ => Finset.sum_nonneg (fun y _ => hh x y))).mp ht x (Finset.mem_univ x)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hh x y)).mp hx y (Finset.mem_univ y)
    simp [hz, entropyPhi]
  · have htpos : 0 < T := lt_of_le_of_ne hT (Ne.symm ht)
    have hrow (x : α) := finite_log_sum (h x) (fun y => ∑ x, h x y) (hh x)
      (fun y => Finset.sum_nonneg (fun x _ => hh x y))
      (fun y hy => (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hh x y)).mp hy x (Finset.mem_univ
          x))
      (by rw [Finset.sum_comm]; exact htpos)
    have hm := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hrow x)
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul] at hm
    have hcross : (∑ x, ∑ y, h x y * Real.log (∑ x, h x y)) =
        ∑ y, entropyPhi (∑ x, h x y) := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, entropyPhi]
    rw [hcross] at hm
    have he : (∑ x, ∑ y, h x y) * Real.log (∑ y, ∑ x, h x y) =
        entropyPhi (∑ x, ∑ y, h x y) := by
      rw [Finset.sum_comm (f := h)]
      rfl
    rw [he] at hm
    linarith

/-- Entropy with respect to the uniform probability law on a finite set. -/
def uniformFiniteEntropy {α : Type*} [Fintype α] (h : α → ℝ) : ℝ :=
  ((∑ x, entropyPhi (h x)) - entropyPhi (∑ x, h x) +
    (∑ x, h x) * Real.log (Fintype.card α)) / Fintype.card α

/-- Entropy tensorizes over two finite uniform probability spaces. -/
theorem uniformFiniteEntropy_tensorization {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (h : α → β → ℝ) (hh : ∀ x y, 0 ≤ h x y) :
    uniformFiniteEntropy (fun p : α × β => h p.1 p.2) ≤
      (∑ y, uniformFiniteEntropy (fun x => h x y)) / Fintype.card β +
      (∑ x, uniformFiniteEntropy (h x)) / Fintype.card α := by
  have ha : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hb : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have hm := entropy_matrix_tensorization h hh
  unfold uniformFiniteEntropy
  simp only [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    Real.log_mul ha.ne' hb.ne', ← Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [Finset.sum_comm (f := fun y x => entropyPhi (h x y)),
    Finset.sum_comm (f := fun y x => h x y)]
  have he :
      ((∑ x, ∑ y, entropyPhi (h x y)) - entropyPhi (∑ x, ∑ y, h x y) +
        (∑ x, ∑ y, h x y) * (Real.log (Fintype.card α) + Real.log (Fintype.card β))) ≤
      ((∑ x, ∑ y, entropyPhi (h x y)) - (∑ y, entropyPhi (∑ x, h x y)) +
        (∑ x, ∑ y, h x y) * Real.log (Fintype.card α)) +
      ((∑ x, ∑ y, entropyPhi (h x y)) - (∑ x, entropyPhi (∑ y, h x y)) +
        (∑ x, ∑ y, h x y) * Real.log (Fintype.card β)) := by linarith
  convert (div_le_div_of_nonneg_right he (mul_pos ha hb).le) using 1
  field_simp

/-- The finite formula is exactly average `x log x` minus `x log x` of the average. -/
theorem uniformFiniteEntropy_eq {α : Type*} [Fintype α] [Nonempty α]
    (h : α → ℝ) :
    uniformFiniteEntropy h = (∑ x, entropyPhi (h x)) / Fintype.card α -
      entropyPhi ((∑ x, h x) / Fintype.card α) := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he := entropyPhi_div (∑ x, h x) (Fintype.card α) hn
  unfold uniformFiniteEntropy
  field_simp
  nlinarith [he]

/-- Local LSI bounds pass to a product through entropy tensorization. -/
theorem uniformFiniteLSI_tensorization {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (Eα : (α → ℝ) → ℝ) (Eβ : (β → ℝ) → ℝ)
    (hα : ∀ f, uniformFiniteEntropy (fun x => (f x) ^ 2) ≤ Eα f)
    (hβ : ∀ f, uniformFiniteEntropy (fun y => (f y) ^ 2) ≤ Eβ f)
    (f : α × β → ℝ) :
    uniformFiniteEntropy (fun p => (f p) ^ 2) ≤
      (∑ y, Eα (fun x => f (x, y))) / Fintype.card β +
      (∑ x, Eβ (fun y => f (x, y))) / Fintype.card α := by
  refine (uniformFiniteEntropy_tensorization (fun x y => (f (x, y)) ^ 2)
    (fun x y => sq_nonneg _)).trans ?_
  exact add_le_add
    (div_le_div_of_nonneg_right (Finset.sum_le_sum (fun y _ => hα _)) (Nat.cast_nonneg _))
    (div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hβ _)) (Nat.cast_nonneg _))

end
end GinibrePoincare
