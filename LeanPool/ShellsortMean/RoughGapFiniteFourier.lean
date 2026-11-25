/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.FiniteFourier
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Zero-mode removal and Parseval for the actual mass in residue classes. -/

@[expose] public noncomputable section
namespace Shellsort.RoughGapFiniteFourier

open Finset ZMod Shellsort.FiniteFourier
open scoped ComplexConjugate

variable {h : ℕ} [NeZero h]

private theorem dft_bilinear (f : ZMod h → ℂ) :
    (∑ k, dft f k * dft f (-k)) = (h : ℂ) * ∑ j, f j ^ 2 := by
  rw [dft_transpose f (fun k => dft f (-k)), dft_comp_neg, dft_dft, mul_sum]
  apply sum_congr rfl
  intro j _
  simp only [neg_neg, smul_eq_mul]
  ring

private theorem centered_squares (f : ZMod h → ℂ) :
    (h : ℂ) * ∑ j, (f j - (∑ z, f z) / h) ^ 2 =
      (h : ℂ) * (∑ j, f j ^ 2) - (∑ z, f z) ^ 2 := by
  let avg := (∑ z, f z) / (h : ℂ)
  change (h : ℂ) * ∑ j, (f j - avg) ^ 2 = _
  have expand (j : ZMod h) : (f j - avg) ^ 2 = (f j) ^ 2 - (2 * avg) * f j + avg ^ 2 := by ring
  simp_rw [expand]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  dsimp [avg]
  field_simp [NeZero.ne (h : ℂ)]
  ring

private theorem dft_real_neg (f : ZMod h → ℝ) (k : ZMod h) :
    dft (fun j => (f j : ℂ)) (-k) = conj (dft (fun j => (f j : ℂ)) k) := by
  simpa only [Complex.conj_ofReal] using dft_conj_neg (fun j => (f j : ℂ)) k

/-- Energy after dropping the zero Fourier coefficient, with an unnormalized
transform and the actual arithmetic mean of all residue masses. -/
theorem nonzero_frequency_energy (f : ZMod h → ℝ) :
    (∑ k ∈ univ.erase (0 : ZMod h), Complex.normSq (dft (fun j => (f j : ℂ)) k)) =
      (h : ℝ) * ∑ j, (f j - (∑ z, f z) / h) ^ 2 := by
  let fc := fun j => (f j : ℂ)
  have addall := add_sum_erase univ (fun k : ZMod h => dft fc k * dft fc (-k)) (mem_univ 0)
  have erase : (∑ k ∈ univ.erase (0 : ZMod h), dft fc k * dft fc (-k)) =
      (h : ℂ) * ∑ j, (fc j - (∑ z, fc z) / h) ^ 2 := by
    rw [centered_squares, ← dft_bilinear]
    rw [← addall, neg_zero, dft_apply_zero]
    ring
  have swap (k : ZMod h) : dft fc k * dft fc (-k) = (Complex.normSq (dft fc k) : ℂ) := by
    change dft fc k * dft (fun j => (f j : ℂ)) (-k) = _
    rw [dft_real_neg]
    exact Complex.mul_conj _
  simp_rw [swap] at erase
  apply Complex.ofReal_injective
  push_cast
  exact erase

/-- Sum the raw vector inside each genuine residue class. -/
def bins {ι : Type*} [Fintype ι] (col : ι → ZMod h) (v : ι → ℝ) (r : ZMod h) : ℝ :=
  ∑ i, if col i = r then v i else 0

private theorem bins_total {ι : Type*} [Fintype ι] (col : ι → ZMod h) (v : ι → ℝ) :
    (∑ r, bins col v r) = ∑ i, v i := by
  unfold bins
  rw [sum_comm]
  simp

private theorem bins_spectrum {ι : Type*} [Fintype ι] (col : ι → ZMod h) (v : ι → ℝ) (k : ZMod h) :
    dft (fun r => (bins col v r : ℂ)) k = ∑ i, stdAddChar (-(col i * k)) * (v i : ℂ) := by
  simp only [dft_apply, smul_eq_mul, bins, Complex.ofReal_sum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [apply_ite]

/-- Explicit finite form used before grouping reduced rational frequencies.
For physical array indices, choose col i = (i.val : ZMod h). -/
theorem actual_nonzero_spectrum {ι : Type*} [Fintype ι] (col : ι → ZMod h) (v : ι → ℝ) :
    (∑ k ∈ univ.erase (0 : ZMod h), Complex.normSq
      (∑ i, stdAddChar (-(col i * k)) * (v i : ℂ))) =
        (h : ℝ) * ∑ r, (bins col v r - (∑ i, v i) / h) ^ 2 := by
  simpa only [bins_spectrum, bins_total] using nonzero_frequency_energy (bins col v)



end Shellsort.RoughGapFiniteFourier
