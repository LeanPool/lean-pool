/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.FiniteRamsey.RamseyNumber
import LeanPool.FiniteRamsey.RamseyLowerBound
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

/-!
# The classical closed-form lower bound `2 ^ (k / 2) ≤ ramseyNumber ![k, k]`

`RamseyLowerBound.lean`'s `lt_ramseyNumber_of_choose_lt` is a general counting lemma needing a
numeric hypothesis, `n.choose k * 2 < 2 ^ (k.choose 2)`, supplied at the call site. This file
discharges that hypothesis at `n = 2 ^ (k / 2)`, recovering the textbook closed form: for `k ≥ 3`,
`ramseyNumber ![k, k] ≥ 2 ^ (k / 2)`.

The classical real-exponent argument bounds `n.choose k ≤ n ^ k / k!` and shows `n ^ k < k! *
2 ^ (k.choose 2 - 1)` at `n = 2 ^ (k / 2)`, which reduces, after cancelling the shared power of
two between `n ^ k` and `2 ^ (k.choose 2)`, to `2 ^ (k / 2 + 1) < k!`, true once `k` is large
enough for factorial growth to overtake exponential growth. Discretizing `k / 2` by `Nat`
truncation, rather than the real number `k / 2`, shifts exactly where "large enough" starts: for
even `k` this reduction is exact and the counting bound applies down to `k = 4`; for odd `k` the
reduction is stronger than needed (the shared power of two cancels completely, leaving `2 < k!`,
true for every `k ≥ 3`), but the hypothesis `k ≤ n` of `lt_ramseyNumber_of_choose_lt` itself fails
at `k = 3, 5` (`2 ^ (3 / 2) = 2 < 3` and `2 ^ (5 / 2) = 4 < 5`). Those two cases, and only those
two, are covered instead by the trivial bound `ramseyNumber ![k, k] ≥ k` (`le_ramseyNumber_self`),
which is itself at least as strong as `2 ^ (k / 2) ≤ k` whenever that holds.

## Main declarations

* `SimpleGraph.le_ramseyNumber_self`: the trivial bound `k ≤ ramseyNumber ![k, k]`, since with fewer
  than `k` vertices there is no `k`-subset of any colour to find.
* `SimpleGraph.two_pow_half_le_ramseyNumber`: the closed-form bound itself, `2 ^ (k / 2) ≤
  ramseyNumber ![k, k]` for `k ≥ 3`.

## Implementation notes

Both parities are handled at once: `k / 2 * k ≤ k.choose 2 + k / 2` (since `2 * (k / 2) ≤ k`) and
`2 ^ (k / 2 + 1) ≤ 2 ^ (k - 1) < k!` (`two_pow_pred_lt_factorial`, a direct induction from `k = 3`).

`two_mul_choose_two` (`2 * n.choose 2 = n * (n - 1)`, an equality, unlike the library's own
`Nat.choose_two_right : n.choose 2 = n * (n - 1) / 2`) is proved via
`Nat.descFactorial_eq_factorial_mul_choose` rather than by clearing the division in
`choose_two_right`, since it avoids having to separately establish `2 ∣ n * (n - 1)`: the
`descFactorial` route gives the doubled identity directly, without division ever entering the
picture.

## References

* P. Erdős, *Some remarks on the theory of graphs*, Bull. Amer. Math. Soc. 53 (1947), 292-294.

## Tags

ramsey theory, probabilistic method, asymptotics
-/

@[expose] public section

namespace SimpleGraph

/-! ### The trivial lower bound -/

/-- If there are fewer than `k` vertices, no colouring can have a `k`-clique of either colour. -/
theorem not_ramseyProperty_of_lt_left {n k : ℕ} (h : n < k) : ¬ RamseyProperty n k k := by
  intro hR
  rcases hR default with ⟨s, hs⟩ | ⟨s, hs⟩ <;>
  · have := hs.card_eq ▸ s.card_le_univ
    simp only [Fintype.card_fin] at this
    omega

/-- The trivial lower bound: the Ramsey number `R(k,k)` is at least `k`. -/
theorem le_ramseyNumber_self (k : ℕ) : k ≤ ramseyNumber ![k, k] :=
  not_lt.mp fun h => not_ramseyProperty_of_lt_left h (ramseyNumber_spec k k)

/-! ### Factorial growth -/

/-- `n!` outgrows `2 ^ (n - 1)` from `n = 3` on. -/
theorem two_pow_pred_lt_factorial {n : ℕ} (hn : 3 ≤ n) : 2 ^ (n - 1) < n.factorial := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    calc 2 ^ (n + 1 - 1) = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
      _ < (n + 1) * n.factorial := by nlinarith
      _ = (n + 1).factorial := (Nat.factorial_succ n).symm

/-! ### The numeric hypothesis at `n = 2 ^ (k / 2)` -/

/-- The doubled closed form for `n.choose 2`, as an equality rather than the library's own
division-based `Nat.choose_two_right`. -/
theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  change Nat.factorial 2 * n.choose 2 = n * (n - 1)
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  rcases n with _ | n
  · simp
  · simp [Nat.descFactorial]
    ring

/-- The numeric hypothesis `lt_ramseyNumber_of_choose_lt` needs, discharged at `n = 2 ^ (k / 2)`:
bound `k! * n.choose k ≤ n ^ k = 2 ^ (k / 2 * k)`, then use `k / 2 * k ≤ k.choose 2 + k / 2` and
`2 ^ (k / 2 + 1) < k!`. -/
theorem choose_pow_half_mul_two_lt {k : ℕ} (hk : 3 ≤ k) :
    (2 ^ (k / 2)).choose k * 2 < 2 ^ (k.choose 2) := by
  have hfact : k.factorial * (2 ^ (k / 2)).choose k ≤ 2 ^ (k / 2 * k) := by
    rw [pow_mul, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow _ k
  have hexp : k / 2 * k ≤ k.choose 2 + k / 2 := by
    have h1 := two_mul_choose_two k
    have h2 := Nat.div_mul_le_self k 2
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at h1
    nlinarith
  have hlt : 2 ^ (k / 2 + 1) < k.factorial :=
    (Nat.pow_le_pow_right two_pos (by omega)).trans_lt (two_pow_pred_lt_factorial hk)
  refine Nat.lt_of_mul_lt_mul_left (a := k.factorial) ?_
  calc k.factorial * ((2 ^ (k / 2)).choose k * 2) ≤ 2 ^ (k / 2 * k) * 2 := by
        rw [← mul_assoc]; gcongr
    _ ≤ 2 ^ (k.choose 2 + k / 2) * 2 := by gcongr
    _ = 2 ^ k.choose 2 * 2 ^ (k / 2 + 1) := by ring
    _ < 2 ^ k.choose 2 * k.factorial := by gcongr
    _ = k.factorial * 2 ^ k.choose 2 := mul_comm _ _

/-! ### The closed-form bound -/

/-- The classical closed-form lower bound. For `k ≥ 3`, `ramseyNumber ![k, k] ≥ 2 ^ (k / 2)`. If
`2 ^ (k / 2) ≤ k` (only `k = 3, 5` under `Nat` truncation), this is weaker than the trivial
`le_ramseyNumber_self`; otherwise it follows from `lt_ramseyNumber_of_choose_lt` via
`choose_pow_half_mul_two_lt`. -/
theorem two_pow_half_le_ramseyNumber {k : ℕ} (hk3 : 3 ≤ k) :
    2 ^ (k / 2) ≤ ramseyNumber ![k, k] := by
  by_cases h : 2 ^ (k / 2) ≤ k
  · exact h.trans (le_ramseyNumber_self k)
  · exact (lt_ramseyNumber_of_choose_lt (by omega) (choose_pow_half_mul_two_lt hk3)).le

/-- A worked instance: at `k = 6`, the closed form gives `ramseyNumber ![6, 6] ≥ 2 ^ 3 = 8`. The
exact value of `R(6, 6)` is a well-known open problem (see Radziszowski's dynamic survey *Small
Ramsey Numbers* for the current bounds); this bound is far below it, but it is proved
unconditionally, with no case-by-case combinatorial search. -/
example : (2 : ℕ) ^ (6 / 2) ≤ ramseyNumber ![6, 6] := two_pow_half_le_ramseyNumber (by norm_num)

end SimpleGraph
