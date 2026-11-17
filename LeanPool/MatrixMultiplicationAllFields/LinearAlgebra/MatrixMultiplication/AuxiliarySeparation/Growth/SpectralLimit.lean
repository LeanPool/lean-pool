/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Removing positive slack from the spectral inequality

The positive slack in the exponent can be sent to zero with the matrix size
fixed. A bound at all positive natural sizes then removes a fixed additive
error term.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.AuxiliarySeparation

open Filter Topology

/-- Continuity removes the positive slack in the spectral exponent. -/
theorem spectral_bound_of_positive_slack {ν k D : ℝ} {d n : ℕ}
    (hν : 0 < ν) (hn : 1 ≤ n)
    (hbound : ∀ δ : ℝ, 0 < δ →
      (d : ℝ) ^ ν * (n : ℝ) ^ (ν / (ν + δ)) ≤ (n : ℝ) * k + D) :
    (d : ℝ) ^ ν * (n : ℝ) ≤ (n : ℝ) * k + D := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    exact this.ne'
  have hδ : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hdenom : Tendsto (fun m : ℕ => ν + 1 / ((m : ℝ) + 1))
      atTop (𝓝 ν) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := ν)).add hδ
  have hexponent : Tendsto (fun m : ℕ => ν / (ν + 1 / ((m : ℝ) + 1)))
      atTop (𝓝 1) := by
    have h : Tendsto (fun m : ℕ => ν / (ν + 1 / ((m : ℝ) + 1)))
        atTop (𝓝 (ν / ν)) := by
      exact (tendsto_const_nhds (x := ν)).div hdenom hν.ne'
    rwa [div_self hν.ne'] at h
  have hpower : Tendsto
      (fun m : ℕ => (d : ℝ) ^ ν * (n : ℝ) ^ (ν / (ν + 1 / ((m : ℝ) + 1))))
      atTop (𝓝 ((d : ℝ) ^ ν * (n : ℝ))) := by
    simpa using tendsto_const_nhds.mul
      ((Real.continuousAt_const_rpow hn0).tendsto.comp hexponent)
  exact le_of_tendsto' hpower fun m => hbound _ (by positivity)

/-- A fixed additive error cannot enlarge a coefficient bounded at every
positive natural size. -/
theorem coefficient_le_of_nat_mul_bound {a k D : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → a * (n : ℝ) ≤ (n : ℝ) * k + D) :
    a ≤ k := by
  by_contra h
  have hgap : 0 < a - k := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨n, hn⟩ := exists_nat_gt (max (D / (a - k)) 0)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (le_max_right _ _) hn
  have hn1 : 1 ≤ n := by
    have : 0 < n := by exact_mod_cast hn0
    omega
  have hlarge : D < (n : ℝ) * (a - k) :=
    (div_lt_iff₀ hgap).mp (lt_of_le_of_lt (le_max_left _ _) hn)
  have hsmall := hbound n hn1
  nlinarith

/-- Uniform spectral inequalities for all positive sizes and all positive
slacks force the desired coefficient bound. -/
theorem spectral_coefficient_le_of_all_nat {ν k D : ℝ} {d : ℕ}
    (hν : 0 < ν)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∀ δ : ℝ, 0 < δ →
      (d : ℝ) ^ ν * (n : ℝ) ^ (ν / (ν + δ)) ≤ (n : ℝ) * k + D) :
    (d : ℝ) ^ ν ≤ k := by
  apply coefficient_le_of_nat_mul_bound (D := D)
  intro n hn
  exact spectral_bound_of_positive_slack hν hn (hbound n hn)

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
