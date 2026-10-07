/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Whole-space transport pairing

The ordered transport energy pairs a derivative of the velocity with
a derivative of the transport tensor. This file gives the scalar `L²`
pairing estimate used before summing the ordered derivative words.
-/

public section

open MeasureTheory CKN CKN.Foundation.Parabolic
open scoped ENNReal


noncomputable section

namespace ESS

private instance lpsPairingHolderTwoTwoOne :
    ENNReal.HolderTriple 2 2 1 := by
  refine ⟨?_⟩
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num,
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1)]
  norm_num

/-- A whole-space `L²` pairing is bounded by the product of the
square roots of its two squared integrals
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_integral_pairing_le (f g : Vec3 → ℝ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    (∫ x, f x * g x) ≤
      Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, g x ^ 2) := by
  have hprod : Integrable (fun x => f x * g x) volume := by
    have h := hf.integrable_mul hg
    convert h using 1
  have hnormprod : Integrable (fun x => ‖f x‖ * ‖g x‖) volume := by
    have h := hf.norm.integrable_mul hg.norm
    convert h using 1
  have hpoint (x : Vec3) : f x * g x ≤ ‖f x‖ * ‖g x‖ := by
    simpa only [Real.norm_eq_abs, ← abs_mul] using le_abs_self (f x * g x)
  have hle := integral_mono hprod hnormprod hpoint
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hh := integral_mul_norm_le_Lp_mul_Lq hpq
    (by simpa only [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num] using hf)
    (by simpa only [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num] using hg)
  calc
    (∫ x, f x * g x) ≤ ∫ x, ‖f x‖ * ‖g x‖ := hle
    _ ≤ Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, g x ^ 2) := by
      simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs,
        Real.sqrt_eq_rpow] using hh

/-- A finite sum of whole-space `L²` pairings is bounded by the
square roots of the two summed energies
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_finset_integral_pairing_le {ι : Type*}
    (s : Finset ι) (F G : ι → Vec3 → ℝ)
    (hF : ∀ i ∈ s, MemLp (F i) 2 volume)
    (hG : ∀ i ∈ s, MemLp (G i) 2 volume) :
    (∑ i ∈ s, ∫ x, F i x * G i x) ≤
      Real.sqrt (∑ i ∈ s, ∫ x, F i x ^ 2) *
        Real.sqrt (∑ i ∈ s, ∫ x, G i x ^ 2) := by
  let A : ι → ℝ := fun i => ∫ x, F i x ^ 2
  let B : ι → ℝ := fun i => ∫ x, G i x ^ 2
  have hA (i : ι) : 0 ≤ A i := integral_nonneg fun x => sq_nonneg _
  have hB (i : ι) : 0 ≤ B i := integral_nonneg fun x => sq_nonneg _
  have hsumA : 0 ≤ ∑ i ∈ s, A i := Finset.sum_nonneg fun i _ => hA i
  have hsumB : 0 ≤ ∑ i ∈ s, B i := Finset.sum_nonneg fun i _ => hB i
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (A i)) (fun i => Real.sqrt (B i))
  have hCS' :
      (∑ i ∈ s, Real.sqrt (A i) * Real.sqrt (B i)) ^ 2 ≤
        (∑ i ∈ s, A i) * (∑ i ∈ s, B i) := by
    simpa only [Real.sq_sqrt (hA _), Real.sq_sqrt (hB _)] using hCS
  have hroot :
      (∑ i ∈ s, Real.sqrt (A i) * Real.sqrt (B i)) ≤
        Real.sqrt (∑ i ∈ s, A i) * Real.sqrt (∑ i ∈ s, B i) := by
    rw [← Real.sqrt_mul hsumA]
    exact Real.le_sqrt_of_sq_le hCS'
  calc
    (∑ i ∈ s, ∫ x, F i x * G i x) ≤
        ∑ i ∈ s, Real.sqrt (A i) * Real.sqrt (B i) := by
      exact Finset.sum_le_sum fun i hi =>
        lps_integral_pairing_le (F i) (G i) (hF i hi) (hG i hi)
    _ ≤ Real.sqrt (∑ i ∈ s, A i) * Real.sqrt (∑ i ∈ s, B i) := hroot

end ESS
