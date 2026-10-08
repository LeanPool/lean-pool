/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCadenceGate
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastOffsetDropBlock
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastDilation

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCadenceProfile

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The cadence profile descent: the scalar family iteration

The profile-head lemma simplifies further: the drop history's head at an anchor is EXACTLY
`ra^(n−m) · iterationDropSum ra F m` (`iterationDropSum_split`, the
semigroup property of the weighted history), so the induction carries the
anchors' drop sums as a second inductive component and the profile
convergence is one recurrence — no block decomposition.

The margin re-prices from `6A` to `24A`, with the shares exact:
`A·ra^(c_A+1) ≤ 1/24` makes the head's collapse share `(1/3)·D·θ^i ≤
(1/2)·D·θ^(i+1)` at `θ = 2A/(2A+1) ≥ 2/3` (equality of the share bound at
`A = 1`), and the error share closes from `ra^(c_A+1) ≤ θ/(16A)` (again
exact at the constants).  The result:

```
F n ≤ (delta + deltaRec) · θ^i          for every n ≥ ns + i·(c_A+1),
```

— per-stage factor `θ = 2A/(2A+1)`, law-free; stage length `c_A + 1`,
law-free; coefficient `delta + deltaRec`, Π-polynomial through the
trade only; availability `ns`, linear.  This is's linear-threshold
preview, delivered by proof, through the profile split, consuming
only the family shape and the row-349 dichotomy — no delayed form.
-/

namespace HCPolySupport.HighContrast.Quenched

open Finset

/-- The drop history is at most the total drop. -/
theorem iterationDropSum_le_total_drop {ra : ℝ} (hra0 : 0 ≤ ra)
    (hra1 : ra ≤ 1) {F : ℕ → ℝ}
    (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p) (m : ℕ) :
    iterationDropSum ra F m ≤ F 0 - F m := by
  rw [iterationDropSum]
  have hIcc : Finset.Icc 1 m = Finset.Ioc 0 m := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIcc]
  have hle : ∑ k ∈ Finset.Ioc 0 m, ra ^ (m - k) * (F (k - 1) - F k) ≤
      ∑ k ∈ Finset.Ioc 0 m, (F (k - 1) - F k) := by
    refine Finset.sum_le_sum fun k _ => ?_
    have hdrop : 0 ≤ F (k - 1) - F k := by
      have := hFmono (k - 1) k (by omega)
      linarith only [this]
    have hw : ra ^ (m - k) ≤ 1 := pow_le_one₀ hra0 hra1
    nlinarith only [hdrop, hw]
  have htel : ∑ k ∈ Finset.Ioc 0 m, (F (k - 1) - F k) = F 0 - F m :=
    telescope_Ioc 0 m (Nat.zero_le m)
  linarith only [hle, htel.le, htel.ge]

/-- **The split identity**: the weighted drop history factors exactly at any
anchor. -/
theorem iterationDropSum_split (ra : ℝ) (F : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    iterationDropSum ra F n = ra ^ (n - m) * iterationDropSum ra F m +
      ∑ k ∈ Finset.Ioc m n, ra ^ (n - k) * (F (k - 1) - F k) := by
  induction n, hmn using Nat.le_induction with
  | base =>
    rw [Nat.sub_self, pow_zero, one_mul, Finset.Ioc_self, Finset.sum_empty,
      add_zero]
  | succ n hmn ih =>
    have hsucc := iterationDropSum_succ ra F n
    have hIoc : ∑ k ∈ Finset.Ioc m (n + 1), ra ^ (n + 1 - k) * (F (k - 1) - F k) =
        ra * ∑ k ∈ Finset.Ioc m n, ra ^ (n - k) * (F (k - 1) - F k) +
          (F n - F (n + 1)) := by
      rw [Finset.sum_Ioc_succ_top hmn]
      have hlast : ra ^ (n + 1 - (n + 1)) * (F (n + 1 - 1) - F (n + 1)) =
          F n - F (n + 1) := by
        rw [Nat.sub_self, pow_zero, one_mul, Nat.add_sub_cancel]
      rw [hlast, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_Ioc] at hk
      have hexp : n + 1 - k = (n - k) + 1 := by omega
      rw [hexp, pow_succ]
      ring
    have hexp2 : n + 1 - m = (n - m) + 1 := by omega
    rw [hsucc, ih, hIoc, hexp2, pow_succ]
    ring

/-- **The anchored drop-history bound**: window telescope plus the exact
head. -/
theorem iterationDropSum_anchored {ra : ℝ} (hra0 : 0 ≤ ra) (hra1 : ra ≤ 1)
    {F : ℕ → ℝ} (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p) {m n : ℕ}
    (hmn : m ≤ n) :
    iterationDropSum ra F n ≤
      (F m - F n) + ra ^ (n - m) * iterationDropSum ra F m := by
  rw [iterationDropSum_split ra F hmn]
  have hioc : ∑ k ∈ Finset.Ioc m n, ra ^ (n - k) * (F (k - 1) - F k) ≤
      F m - F n := by
    have hle : ∑ k ∈ Finset.Ioc m n, ra ^ (n - k) * (F (k - 1) - F k) ≤
        ∑ k ∈ Finset.Ioc m n, (F (k - 1) - F k) := by
      refine Finset.sum_le_sum fun k _ => ?_
      have hdrop : 0 ≤ F (k - 1) - F k := by
        have := hFmono (k - 1) k (by omega)
        linarith only [this]
      have hw : ra ^ (n - k) ≤ 1 := pow_le_one₀ hra0 hra1
      nlinarith only [hdrop, hw]
    have htel : ∑ k ∈ Finset.Ioc m n, (F (k - 1) - F k) = F m - F n :=
      telescope_Ioc m n hmn
    linarith only [hle, htel.le, htel.ge]
  linarith only [hioc]

/-- The `24A` margin's attenuation: `A·ra^(c_A+1) ≤ 1/24`. -/
theorem cadence_head_margin24 {A alpha : ℝ} {cA : ℕ} (hA : 1 ≤ A)
    (halpha : 0 < alpha)
    (hcA : 24 * A ≤ (3 : ℝ) ^ (alpha * (cA : ℝ))) :
    A * ((3 : ℝ) ^ (-alpha)) ^ (cA + 1) ≤ 1 / 24 := by
  have hra0 : (0 : ℝ) < (3 : ℝ) ^ (-alpha) := Real.rpow_pos_of_pos (by norm_num) _
  have hra1 : (3 : ℝ) ^ (-alpha) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by linarith only [halpha])
  have hpow : ((3 : ℝ) ^ (-alpha)) ^ cA = (3 : ℝ) ^ (-(alpha * (cA : ℝ))) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-alpha)) cA,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (alpha * (cA : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hinv : (3 : ℝ) ^ (-(alpha * (cA : ℝ))) =
      ((3 : ℝ) ^ (alpha * (cA : ℝ)))⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  have h24A : (0 : ℝ) < 24 * A := by linarith only [hA]
  have hle : ((3 : ℝ) ^ (alpha * (cA : ℝ)))⁻¹ ≤ (24 * A)⁻¹ :=
    inv_anti₀ h24A hcA
  have hcAbound : A * ((3 : ℝ) ^ (-alpha)) ^ cA ≤ 1 / 24 := by
    rw [hpow, hinv]
    have hAinv : A * (24 * A)⁻¹ = 1 / 24 := by
      have hAne : A ≠ 0 := by linarith only [hA]
      field_simp
    calc A * ((3 : ℝ) ^ (alpha * (cA : ℝ)))⁻¹ ≤ A * (24 * A)⁻¹ :=
        mul_le_mul_of_nonneg_left hle (by linarith only [hA])
      _ = 1 / 24 := hAinv
  calc A * ((3 : ℝ) ^ (-alpha)) ^ (cA + 1)
      = (A * ((3 : ℝ) ^ (-alpha)) ^ cA) * ((3 : ℝ) ^ (-alpha)) := by ring
    _ ≤ (1 / 24) * 1 := by
        refine mul_le_mul hcAbound hra1 hra0.le (by norm_num)
    _ = 1 / 24 := mul_one _

end HCPolySupport.HighContrast.Quenched
