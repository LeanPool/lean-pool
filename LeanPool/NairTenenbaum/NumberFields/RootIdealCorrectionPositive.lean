/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.EulerSummabilityCriterion
public import LeanPool.NairTenenbaum.NumberFields.RootIdealCorrectionTail
public import LeanPool.NairTenenbaum.NumberFields.RootIdealLocalPolynomial
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! # Positivity of the global convolution correction -/

@[expose] public section

namespace NairTenenbaum

open Filter NumberField Polynomial Real

variable (K : Type*) [Field K] [NumberField K]

theorem rootIdealCorrection_sum_pos_of_absolute_convergence (Q : ℤ[X])
    (habs : Summable (fun n : ℕ => |rootIdealCorrection K Q n| / n))
    (htails : Summable (fun p : ℕ => if p.Prime then
      ∑' k : ℕ, |rootIdealCorrection K Q (p ^ (k + 1))| / (p : ℝ) ^ (k + 1) else 0)) :
    0 < ∑' n : ℕ, rootIdealCorrection K Q n / n := by
  let g := rootIdealCorrection K Q
  let f : ℕ → ℝ := fun n => g n / n
  have hg := rootIdealCorrection_isMultiplicative K Q
  have hf1 : f 1 = 1 := by simp [f, g, hg.1]
  have hf0 : f 0 = 0 := by simp [f]
  have hmul {m n : ℕ} (hcop : m.Coprime n) : f (m * n) = f m * f n := by
    dsimp [f]
    rw [hg.2 hcop, Nat.cast_mul, mul_div_mul_comm]
  have hnorm : Summable (fun n => ‖f n‖) := by
    simpa only [f, g, Real.norm_eq_abs, abs_div, Nat.abs_cast] using
      habs
  have hlocalnorm (p : Nat.Primes) : Summable (fun k : ℕ => ‖f (p.1 ^ k)‖) := by
    simpa only [f, g, Real.norm_eq_abs, abs_div, Nat.cast_pow, abs_pow, Nat.abs_cast] using
      rootIdealCorrection_local_abs_summable K Q p.2
  let t : Nat.Primes → ℝ := fun p => ∑' k : ℕ, f (p.1 ^ (k + 1))
  have htailabs : Summable (fun p : Nat.Primes => ∑' k : ℕ, ‖f (p.1 ^ (k + 1))‖) := by
    apply (summable_subtype_iff_indicator (s := {p : ℕ | p.Prime})
      (f := fun p : ℕ => ∑' k : ℕ, ‖f (p ^ (k + 1))‖)).mpr
    apply (htails).congr
    intro p
    rw [Set.indicator_apply]
    simp only [Set.mem_ofPred_eq, f, g, Real.norm_eq_abs, abs_div, Nat.cast_pow, abs_pow,
        Nat.abs_cast]
  have ht : Summable t := by
    apply htailabs.of_norm_bounded
    intro p
    exact norm_tsum_le_tsum_norm (((summable_nat_add_iff 1).mpr (hlocalnorm p)))
  have hfactor (p : Nat.Primes) : (∑' k : ℕ, f (p.1 ^ k)) = 1 + t p := by
    rw [(hlocalnorm p).of_norm.tsum_eq_zero_add, pow_zero, hf1]
  have hpos (p : Nat.Primes) : 0 < ∑' k : ℕ, f (p.1 ^ k) := by
    simpa only [f, g, Nat.cast_pow] using rootIdealCorrection_local_sum_pos K Q p.2
  have hlog : Summable (fun p : Nat.Primes => log (∑' k : ℕ, f (p.1 ^ k))) := by
    simpa only [hfactor] using Real.summable_log_one_add_of_summable ht
  have HP := EulerProduct.eulerProduct_hasProd hf1 (fun {_ _} h => hmul h) hnorm hf0
  have HL := Real.hasProd_of_hasSum_log hpos hlog.hasSum
  have HE := HP.unique HL
  change 0 < ∑' n : ℕ, f n
  rw [HE]
  exact exp_pos _

end NairTenenbaum
