/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEchoWitness

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastAdaptiveDepthGate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The adaptive-depth gate: the family clause excludes the echo witness

The the stated witness is admissible for the FIXED-index construction.  The family
hypothesis at level-adapted lag supplies the recursion clause at every
within-octave pair `(n, m)`; on a plateau the drop history collapses
(the drop history is constant on a plateau), so once the memory has expired
(`A·ra^{n−b}·δ₀ ≤ λ/4`), the level is small (`A·λ ≤ 1/4`, automatic from
`A·δ₀ ≤ 1/2` by the echo-tower quarter bound), and the adapted-lag source is small
(`s ≤ λ/4`), the clause forces `λ ≤ (3/4)·λ` — false.  So the witness
VIOLATES the family clause at the middle generations of any sufficiently
long octave: the tower profile survives the fixed-index construction only, and
the condition's mechanism is not blocked by the corresponding clause.
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-- The drop-history recurrence: one step appends the newest drop. -/
theorem iterationDropSum_succ (ra : ℝ) (F : ℕ → ℝ) (n : ℕ) :
    iterationDropSum ra F (n + 1) =
      ra * iterationDropSum ra F n + (F n - F (n + 1)) := by
  rw [iterationDropSum, iterationDropSum,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  have h1 : ∀ k ∈ Finset.Icc 1 n,
      ra ^ (n + 1 - k) * (F (k - 1) - F k) =
        ra * (ra ^ (n - k) * (F (k - 1) - F k)) := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hexp : n + 1 - k = (n - k) + 1 := by omega
    rw [hexp, pow_succ]
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  simp

/-- The weighted drop history is at most the total drop. -/
theorem iterationDropSum_le_total {F : ℕ → ℝ}
    (hmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p) {ra : ℝ} (hra0 : 0 ≤ ra)
    (hra1 : ra ≤ 1) (b : ℕ) :
    iterationDropSum ra F b ≤ F 0 - F b := by
  have htel : ∀ m : ℕ, (∑ k ∈ Finset.Icc 1 m, (F (k - 1) - F k)) =
      F 0 - F m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]
        simp
  calc iterationDropSum ra F b ≤
      ∑ k ∈ Finset.Icc 1 b, (F (k - 1) - F k) := by
        refine Finset.sum_le_sum ?_
        intro k hk
        have hd : 0 ≤ F (k - 1) - F k := by
          have := hmono (k - 1) k (by omega)
          linarith only [this]
        have hw : ra ^ (b - k) ≤ 1 := pow_le_one₀ hra0 hra1
        nlinarith only [hd, hw, pow_nonneg hra0 (b - k)]
    _ = F 0 - F b := htel b

end

end HCPolySupport.HighContrast.Quenched
