/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryBrownianDyadicTents.lean.
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
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.SpecialFunctions.Sqrt
/-!
# Alternative Bakry Emery Brownian dyadic tents

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryBrownianDyadicLevel_norm_le`.
-/

@[expose] public section
open Set
namespace GinibrePoincare
noncomputable section

/-- The unscaled tent on the kth dyadic cell. -/
def bakryBrownianDyadicTent (n : ℕ) (k : Fin (2 ^ n)) : C(Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun t => max 0 (min ((2 : ℝ)^n*t-k.val) ((k.val+1 : ℕ)-(2 : ℝ)^n*t)), by fun_prop⟩

theorem bakryBrownianDyadicTent_nonneg (n : ℕ) (k : Fin (2 ^ n)) (t : Icc (0 : ℝ) 1) :
    0 ≤ bakryBrownianDyadicTent n k t := le_max_left _ _

theorem bakryBrownianDyadicTent_le_half (n : ℕ) (k : Fin (2 ^ n)) (t : Icc (0 : ℝ) 1) :
    bakryBrownianDyadicTent n k t ≤ 1/2 := by
  change max 0 (min _ _) ≤ _
  apply max_le (by norm_num)
  have h₁ := min_le_left ((2 : ℝ)^n*t-k.val) (((k.val+1 : ℕ) : ℝ)-(2 : ℝ)^n*t)
  have h₂ := min_le_right ((2 : ℝ)^n*t-k.val) (((k.val+1 : ℕ) : ℝ)-(2 : ℝ)^n*t)
  simp only [Nat.cast_add, Nat.cast_one] at h₁ h₂ ⊢
  linarith

/-- Distinct dyadic cells have disjoint open tent supports. -/
theorem bakryBrownianDyadicTent_disjoint (n : ℕ) (j k : Fin (2 ^ n)) (hjk : j ≠ k)
    (t : Icc (0 : ℝ) 1) :
    bakryBrownianDyadicTent n j t = 0 ∨ bakryBrownianDyadicTent n k t = 0 := by
  by_contra h
  push Not at h
  have hj : 0 < bakryBrownianDyadicTent n j t :=
    lt_of_le_of_ne (bakryBrownianDyadicTent_nonneg n j t) (Ne.symm h.1)
  have hk : 0 < bakryBrownianDyadicTent n k t :=
    lt_of_le_of_ne (bakryBrownianDyadicTent_nonneg n k t) (Ne.symm h.2)
  change 0 < max 0 (min _ _) at hj hk
  rw [lt_max_iff] at hj hk
  have hj' := lt_min_iff.mp (hj.resolve_left (lt_irrefl _))
  have hk' := lt_min_iff.mp (hk.resolve_left (lt_irrefl _))
  have hne : j.val ≠ k.val := fun he => hjk (Fin.ext he)
  rcases lt_or_gt_of_ne hne with hh | hh
  · have hh' : (j.val : ℝ)+1 ≤ k.val := by exact_mod_cast hh
    simp only [Nat.cast_add, Nat.cast_one] at hj' hk'
    linarith
  · have hh' : (k.val : ℝ)+1 ≤ j.val := by exact_mod_cast hh
    simp only [Nat.cast_add, Nat.cast_one] at hj' hk'
    linarith

/-- A level of the actual Faber–Schauder series; its amplitude is 2^(-n/2). -/
def bakryBrownianDyadicLevel (n : ℕ) (x : Fin (2 ^ n) → ℝ) : C(Icc (0 : ℝ) 1, ℝ) :=
  (1 / Real.sqrt 2)^n • ∑ k, x k • bakryBrownianDyadicTent n k

theorem bakryBrownianDyadicLevel_norm_le (n : ℕ) (x : Fin (2 ^ n) → ℝ)
    (A : ℝ) (hA : 0 ≤ A) (hx : ∀ k, |x k| ≤ A) :
    ‖bakryBrownianDyadicLevel n x‖ ≤ (1 / Real.sqrt 2)^n * A / 2 := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  simp only [bakryBrownianDyadicLevel, ContinuousMap.smul_apply,
    ContinuousMap.sum_apply, smul_eq_mul]
  change ‖(1 / Real.sqrt 2)^n * ∑ k, x k * bakryBrownianDyadicTent n k t‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hs : |∑ k, x k * bakryBrownianDyadicTent n k t| ≤ A/2 := by
    by_cases he : ∃ k, bakryBrownianDyadicTent n k t ≠ 0
    · obtain ⟨k, hk⟩ := he
      rw [Finset.sum_eq_single k]
      · rw [abs_mul, abs_of_nonneg (bakryBrownianDyadicTent_nonneg n k t)]
        calc
          |x k| * bakryBrownianDyadicTent n k t ≤ A * bakryBrownianDyadicTent n k t :=
            mul_le_mul_of_nonneg_right (hx k) (bakryBrownianDyadicTent_nonneg n k t)
          _ ≤ A*(1/2) := mul_le_mul_of_nonneg_left (bakryBrownianDyadicTent_le_half n k t) hA
          _ = A/2 := by ring
      · intro j _ hj
        rcases bakryBrownianDyadicTent_disjoint n j k hj t with hz | hz
        · simp [hz]
        · exact (hk hz).elim
      · simp
    · push Not at he
      simp only [he, mul_zero, Finset.sum_const_zero, abs_zero]
      positivity
  calc
    (1 / Real.sqrt 2)^n * ‖∑ k, x k * bakryBrownianDyadicTent n k t‖ ≤
        (1 / Real.sqrt 2)^n * (A/2) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end
end GinibrePoincare
