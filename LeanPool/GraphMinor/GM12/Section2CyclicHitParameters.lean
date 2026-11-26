/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section11b

/-!
# Cyclic endpoint identities for the hit parameters

The trace subdivision in XII, page 243, lists its first vertex again
one period later at the end. Thus the end of a real interval is the
start of the cyclically next interval, except that the last end has
one period added. These identities make the corresponding vertex
paths and homotopies join around the circle.
-/

public section

namespace GraphMinor.GM12

open GM07

/-- Consecutive endpoints of a one-period subdivision match cyclically,
with one period added only at the last interval. -/
theorem cyclic_step_of_period_endpoints
    {n : ℕ} (hn : 0 < n) (t : Fin (n + 1) → ℝ)
    (hperiod : t (Fin.last n) = t 0 + 1) (i : Fin n) :
    t i.succ = t (finNext hn i).castSucc + if i.val + 1 = n then 1 else 0 := by
  by_cases hlast : i.val + 1 = n
  · have hnext : (finNext hn i).castSucc = (0 : Fin (n + 1)) := Fin.ext (by
      change (i.val + 1) % n = 0
      rw [hlast, Nat.mod_self])
    have hi : i.succ = Fin.last n := Fin.ext hlast
    rw [hi, hnext, hperiod]
    simp only [hlast, ↓reduceIte]
  · have hlt : i.val + 1 < n := lt_of_le_of_ne (Nat.succ_le_of_lt i.isLt) hlast
    have hi : (finNext hn i).castSucc = i.succ := Fin.ext (by
      change (i.val + 1) % n = i.val + 1
      exact Nat.mod_eq_of_lt hlt)
    rw [hi]
    simp only [hlast, ↓reduceIte, add_zero]

/-- A periodic curve takes the same value at the last endpoint of
one interval and the first endpoint of the cyclically next one. -/
theorem periodic_value_succ_eq_next
    {S : Type*} {f : ℝ → S} (hper : Function.Periodic f 1)
    {n : ℕ} (hn : 0 < n) (t : Fin (n + 1) → ℝ)
    (hperiod : t (Fin.last n) = t 0 + 1) (i : Fin n) :
    f (t i.succ) = f (t (finNext hn i).castSucc) := by
  rw [cyclic_step_of_period_endpoints hn t hperiod i]
  split_ifs
  · exact hper _
  · simp only [add_zero]

/-- The next index of a cyclic list with at least two entries is
never the current index. -/
theorem finNext_ne_of_two_le {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    finNext (by omega : 0 < n) i ≠ i := by
  intro heq
  have hval := congrArg Fin.val heq
  change (i.val + 1) % n = i.val at hval
  by_cases hlast : i.val + 1 = n
  · rw [hlast, Nat.mod_self] at hval
    omega
  · have hlt : i.val + 1 < n := lt_of_le_of_ne (Nat.succ_le_of_lt i.isLt) hlast
    rw [Nat.mod_eq_of_lt hlt] at hval
    omega

end GraphMinor.GM12
