/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Mathlib.Order.Filter.AtTopBot.Tendsto

import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The gap `n - e·v_p(n)` grows

Once `p > e + 1`, the `p`-adic valuation is a small fraction of its argument —
`(e + 2)·v_p(n) ≤ n` (`Nat.mul_padicValNat_le`) — so the gap `n - e·v_p(n)` is not only
nonnegative but tends to infinity (`Nat.tendsto_sub_mul_padicValNat_atTop`). These are the
integrality and the decay estimate behind convergence of the formal logarithm, and of the
antiderivative of an integral power series, on a residue disk of a local ring whose absolute
ramification index is at most `e`. The unramified case is `e = 1`. The strict form
`Nat.add_mul_padicValNat_lt` is what bounds the index of an antiderivative.
-/

@[expose] public section

open Filter

namespace Nat

/-- **The `p`-adic valuation is a small fraction of its argument** when `p > e + 1`: the
`(e + 2)`-form of Mathlib's `mul_padicValNat_le` (`p * v_p n ≤ n`), in the shape the
ramification estimates consume. -/
theorem mul_padicValNat_le {p e : ℕ} (hpe : e + 1 < p) (n : ℕ) :
    (e + 2) * padicValNat p n ≤ n :=
  (Nat.mul_le_mul_right _ (show e + 2 ≤ p by lia)).trans _root_.mul_padicValNat_le

/-- The gap `n - e·v_p(n)` is at least `B` as soon as `n ≥ (e + 2)·B`. -/
theorem add_mul_padicValNat_le {p e : ℕ} (hpe : e + 1 < p) {B n : ℕ} (hn : (e + 2) * B ≤ n) :
    B + e * padicValNat p n ≤ n := by
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < e + 2 by lia)
  calc (e + 2) * (B + e * padicValNat p n)
      = (e + 2) * B + e * ((e + 2) * padicValNat p n) := by ring
    _ ≤ n + e * n := Nat.add_le_add hn (Nat.mul_le_mul_left e (mul_padicValNat_le hpe n))
    _ ≤ (e + 2) * n := by lia

/-- Beyond index `m + 1` the gap is strict: `k + 1 > m + 1` and `p > m + e + 1` give
`(k + 1) - e·v_p(k + 1) > m + 1`, stated without natural subtraction. -/
theorem add_mul_padicValNat_lt {p e m k : ℕ} (hp : m + e + 1 < p) (hk : m + 1 < k + 1) :
    m + 1 + e * padicValNat p (k + 1) < k + 1 := by
  have h := mul_padicValNat_le (e := m + e) hp (k + 1)
  rcases eq_zero_or_pos (padicValNat p (k + 1)) with h0 | h1
  · lia
  lia [Nat.le_mul_of_pos_right m h1]

/-- `n - e·v_p(n) → ∞` when `p > e + 1`: the `p`-adic valuation is sublinear. -/
theorem tendsto_sub_mul_padicValNat_atTop {p e : ℕ} (hpe : e + 1 < p) :
    Tendsto (fun n ↦ n - e * padicValNat p n) atTop atTop :=
  tendsto_atTop.mpr fun B ↦ (eventually_ge_atTop ((e + 2) * B)).mono fun _ hn ↦
    Nat.le_sub_of_add_le (add_mul_padicValNat_le hpe hn)

end Nat

end
