/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Theorem7
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# An explicit sequence satisfying every growth fact

Śliwa takes `d₀ = 2`, `d₁ ≥ α⁴` and `dₙ₊₁ ≥ α^{(n dₙ)!}`. We take every `dⱼ` (`j ≥ 1`) to be a
power `8^{2s}`, so that `√dⱼ = 8ˢ` exactly and every growth fact becomes an inequality between
natural-number exponents. With `aₙ = 8^{2xₙ₋₁}` and `bₙ = 8^{2yₙ₋₁}` (`ReadL1.xs`, `ReadL1.ys`):

* `x₀ = 2`, so `a₁ = 8⁴ = α⁴`;
* `yᵢ ≥ (2xᵢ + 8^{xᵢ}) (1 + (2(i + 1) 8^{2xᵢ})!) + 8^{2xᵢ} + 4xᵢ + i + 5`, which carries
  Theorem 7's `α aₘ Aₘ Rₘ < bₘ`;
* `xᵢ₊₁ = 8^{2yᵢ} + 2yᵢ + i + 4`, which carries `aₘ₊₁ ≥ α^{2bₘ}`.

`ReadL1.theorem7Hyp_dRead` proves `Theorem7Hyp` for this sequence.
-/

@[expose] public section

namespace ReadL1

/- ### Natural-number inequalities -/

lemma sixteen_mul_add_lt_pow {x : ℕ} (hx : 2 ≤ x) : 16 * x + 4 < 8 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x _ ih => rw [pow_succ]; omega

lemma thirtytwo_sq_lt_pow {y : ℕ} (hy : 4 ≤ y) : 32 * y ^ 2 < 8 ^ y := by
  induction y, hy using Nat.le_induction with
  | base => norm_num
  | succ y hy ih =>
    have h1 : 4 * y ≤ y * y := Nat.mul_le_mul_right y hy
    rw [pow_succ 8 y]; nlinarith

lemma lt_eight_pow (n : ℕ) : n < 8 ^ n := Nat.lt_pow_self (by norm_num)

lemma le_eight_pow_two_mul (x : ℕ) : 8 ^ x ≤ 8 ^ (2 * x) :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

/- ### The sequence -/

/-- `yᵢ` as a function of `i` and `xᵢ`. -/
def yOf (i x : ℕ) : ℕ :=
  (2 * x + 8 ^ x) * (1 + (2 * (i + 1) * 8 ^ (2 * x)).factorial) + 8 ^ (2 * x) + 4 * x + i + 5

/-- `xᵢ`, with `aᵢ₊₁ = 8^{2xᵢ}`. -/
def xs : ℕ → ℕ
  | 0 => 2
  | i + 1 => 8 ^ (2 * yOf i (xs i)) + 2 * yOf i (xs i) + i + 4

/-- `yᵢ`, with `bᵢ₊₁ = 8^{2yᵢ}`. -/
def ys (i : ℕ) : ℕ := yOf i (xs i)

/-- **The explicit sequence**: `d₀ = 2`, `d₂ᵢ₊₁ = 8^{2xᵢ}`, `d₂ᵢ₊₂ = 8^{2yᵢ}`. -/
def dRead (j : ℕ) : ℕ :=
  if j = 0 then 2 else if j % 2 = 1 then 8 ^ (2 * xs (j / 2)) else 8 ^ (2 * ys (j / 2 - 1))

lemma seqA_dRead {n : ℕ} (hn : 1 ≤ n) : seqA dRead n = 8 ^ (2 * xs (n - 1)) := by
  unfold seqA dRead
  rw [ite_eq_right (by omega), ite_eq_left (by omega), show (2 * n - 1) / 2 = n - 1 by omega]

lemma seqB_dRead {n : ℕ} (hn : 1 ≤ n) : seqB dRead n = 8 ^ (2 * ys (n - 1)) := by
  unfold seqB dRead
  rw [ite_eq_right (by omega), ite_eq_right (by omega), show 2 * n / 2 - 1 = n - 1 by omega]

lemma seqA_dRead_zero : seqA dRead 0 = 2 := by simp [seqA, dRead]

lemma seqB_dRead_zero : seqB dRead 0 = 2 := by simp [seqB, dRead]

lemma two_le_xs (i : ℕ) : 2 ≤ xs i := by
  rcases i with _ | i
  · simp [xs]
  · simp only [xs]; have := lt_eight_pow (2 * yOf i (xs i)); omega

lemma ys_ge (i : ℕ) : 8 ^ (2 * xs i) + 4 * xs i + i + 5 ≤ ys i := by
  unfold ys yOf
  generalize (2 * xs i + 8 ^ xs i) * (1 + (2 * (i + 1) * 8 ^ (2 * xs i)).factorial) = P
  generalize 8 ^ (2 * xs i) = Q
  omega

lemma ys_ge_r (i : ℕ) :
    (2 * xs i + 8 ^ xs i) * (1 + (2 * (i + 1) * 8 ^ (2 * xs i)).factorial) + 1 ≤ ys i := by
  unfold ys yOf
  generalize (2 * xs i + 8 ^ xs i) * (1 + (2 * (i + 1) * 8 ^ (2 * xs i)).factorial) = P
  generalize 8 ^ (2 * xs i) = Q
  omega

lemma xs_succ (i : ℕ) : xs (i + 1) = 8 ^ (2 * ys i) + 2 * ys i + i + 4 := rfl

lemma xs_lt_ys (i : ℕ) : xs i < ys i := by
  have := ys_ge i; have := lt_eight_pow (2 * xs i); omega

lemma xs_lt_succ (i : ℕ) : xs i < xs (i + 1) := by
  have := xs_lt_ys i; have := lt_eight_pow (2 * ys i); rw [xs_succ]; omega

lemma xs_mono {i j : ℕ} (hij : i ≤ j) : xs i ≤ xs j :=
  (strictMono_nat_of_lt_succ xs_lt_succ).monotone hij

lemma eight_pow_le_ys (i : ℕ) : 8 ^ xs i ≤ ys i :=
  (le_eight_pow_two_mul _).trans (by have := ys_ge i; omega)

/- ### Real powers of `8` -/

lemma sqrt_eight_pow (x : ℕ) : Real.sqrt (((8 ^ (2 * x) : ℕ)) : ℝ) = (8 : ℝ) ^ x := by
  rw [Nat.cast_pow, Nat.cast_ofNat, mul_comm, pow_mul, Real.sqrt_sq (by positivity)]

lemma alpha_rpow_natCast (N : ℕ) : alpha ^ (N : ℝ) = (8 : ℝ) ^ N := by
  rw [alpha, Real.rpow_natCast]

lemma alpha_rpow_eight_pow (x : ℕ) : alpha ^ ((8 : ℝ) ^ x) = (8 : ℝ) ^ (8 ^ x) := by
  have : ((8 : ℝ) ^ x) = ((8 ^ x : ℕ) : ℝ) := by push_cast; rfl
  rw [this, alpha_rpow_natCast]

lemma eight_pow_lt_alpha_rpow {N : ℕ} {r : ℝ} (h : (N : ℝ) < r) : (8 : ℝ) ^ N < alpha ^ r := by
  rw [← alpha_rpow_natCast]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num [alpha]) h

lemma eight_pow_le_alpha_rpow {N : ℕ} {r : ℝ} (h : (N : ℝ) ≤ r) : (8 : ℝ) ^ N ≤ alpha ^ r := by
  rw [← alpha_rpow_natCast]
  exact alpha_rpow_le h

lemma capA_dRead {n : ℕ} (hn : 1 ≤ n) : capA dRead n = (8 : ℝ) ^ (8 ^ xs (n - 1)) := by
  rw [capA, seqA_dRead hn, sqrt_eight_pow, alpha_rpow_eight_pow]

lemma eight_pow_mono {M N : ℕ} (h : M ≤ N) : (8 : ℝ) ^ M ≤ (8 : ℝ) ^ N :=
  pow_le_pow_right₀ (by norm_num) h

lemma eight_pow_strictMono {M N : ℕ} (h : M < N) : (8 : ℝ) ^ M < (8 : ℝ) ^ N :=
  pow_lt_pow_right₀ (by norm_num) h

/- ### The growth facts -/

lemma dRead_a_small {n : ℕ} (hn : 1 ≤ n) : 8 * n * seqA dRead n < seqB dRead n := by
  rw [seqA_dRead hn, seqB_dRead hn]
  have hy := ys_ge (n - 1)
  have := lt_eight_pow (2 * xs (n - 1))
  have h1 : 8 * n < 8 ^ (n + 2) := by
    have := lt_eight_pow (n + 1); rw [pow_succ]; omega
  calc 8 * n * 8 ^ (2 * xs (n - 1)) < 8 ^ (n + 2) * 8 ^ (2 * xs (n - 1)) :=
        Nat.mul_lt_mul_of_pos_right h1 (by positivity)
    _ = 8 ^ (n + 2 + 2 * xs (n - 1)) := by rw [← pow_add]
    _ ≤ 8 ^ (2 * ys (n - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma dRead_b_small {n : ℕ} (hn : 1 ≤ n) : 8 * n * seqB dRead n < seqA dRead (n + 1) := by
  rw [seqB_dRead hn, seqA_dRead (by omega), Nat.add_sub_cancel]
  have hx : 8 ^ (2 * ys (n - 1)) + 2 * ys (n - 1) + (n - 1) + 4 ≤ xs n := by
    rw [show n = n - 1 + 1 by omega, xs_succ, Nat.add_sub_cancel]
  have := lt_eight_pow (2 * ys (n - 1))
  have h1 : 8 * n < 8 ^ (n + 2) := by
    have := lt_eight_pow (n + 1); rw [pow_succ]; omega
  calc 8 * n * 8 ^ (2 * ys (n - 1)) < 8 ^ (n + 2) * 8 ^ (2 * ys (n - 1)) :=
        Nat.mul_lt_mul_of_pos_right h1 (by positivity)
    _ = 8 ^ (n + 2 + 2 * ys (n - 1)) := by rw [← pow_add]
    _ ≤ 8 ^ (2 * xs n) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma dRead_one_le_a (n : ℕ) : 1 ≤ seqA dRead n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [seqA_dRead_zero]; norm_num
  · rw [seqA_dRead hn]; exact Nat.one_le_pow _ _ (by norm_num)

lemma dRead_a_big {n : ℕ} (hn : 1 ≤ n) : 4096 ≤ seqA dRead n := by
  rw [seqA_dRead hn]
  have := two_le_xs (n - 1)
  calc 4096 = 8 ^ 4 := by norm_num
    _ ≤ 8 ^ (2 * xs (n - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma dRead_seqA_mono {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : seqA dRead k ≤ seqA dRead n := by
  rw [seqA_dRead hk, seqA_dRead (by omega)]
  exact Nat.pow_le_pow_right (by norm_num) (by have := xs_mono (show k - 1 ≤ n - 1 by omega); omega)

lemma dRead_v_small (n k : ℕ) (hkn : k < n) : 8 * (seqV dRead k + 1) < seqA dRead n := by
  have ha := dRead_a_big (n := n) (by omega)
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have : seqV dRead k = 0 := by unfold seqV; rw [show k - 1 = 0 by omega, zero_mul]
    omega
  -- `vₖ ≤ 2(k - 1)bₖ` and `aₖ₊₁ ≥ bₖ 8^{2k+6}`.
  have hab : seqA dRead k ≤ seqB dRead k := by
    rw [seqA_dRead (by omega), seqB_dRead (by omega)]
    exact Nat.pow_le_pow_right (by norm_num) (by have := xs_lt_ys (k - 1); omega)
  have hv : seqV dRead k ≤ (k - 1) * (2 * seqB dRead k) := by
    unfold seqV; exact Nat.mul_le_mul_left _ (by omega)
  have hak : seqA dRead (k + 1) ≤ seqA dRead n := dRead_seqA_mono (by omega) (by omega)
  have hx : seqA dRead (k + 1) = 8 ^ (2 * xs k) := by rw [seqA_dRead (by omega), Nat.add_sub_cancel]
  have hxk : 8 ^ (2 * ys (k - 1)) + 2 * ys (k - 1) + (k - 1) + 4 ≤ xs k := by
    rw [show k = k - 1 + 1 by omega, xs_succ, Nat.add_sub_cancel]
  have hb : seqB dRead k = 8 ^ (2 * ys (k - 1)) := seqB_dRead (by omega)
  have hpow : 8 ^ (2 * ys (k - 1)) * 8 ^ (2 * k + 6) ≤ 8 ^ (2 * xs k) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hk8 : 16 * k + 8 < 8 ^ (2 * k + 6) := by
    have h1 := lt_eight_pow k
    have h2 : 8 ^ (k + 6) ≤ 8 ^ (2 * k + 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_add] at h2
    omega
  have hb1 : 1 ≤ seqB dRead k := by rw [hb]; exact Nat.one_le_pow _ _ (by norm_num)
  have : 8 * ((k - 1) * (2 * seqB dRead k) + 1) < seqB dRead k * 8 ^ (2 * k + 6) := by
    have h3 : 8 * ((k - 1) * (2 * seqB dRead k) + 1) ≤ (16 * k + 8) * seqB dRead k := by
      have : (k - 1) * (2 * seqB dRead k) ≤ k * (2 * seqB dRead k) :=
        Nat.mul_le_mul_right _ (by omega)
      nlinarith
    exact h3.trans_lt (by rw [mul_comm]; exact Nat.mul_lt_mul_of_pos_left hk8 (by omega))
  rw [hb] at this hv
  rw [hx] at hak
  omega

lemma dRead_a_double {m : ℕ} (hm : 1 ≤ m) : 2 * seqA dRead m ≤ seqA dRead (m + 1) := by
  rw [seqA_dRead hm, seqA_dRead (by omega), Nat.add_sub_cancel]
  have h1 := xs_lt_succ (m - 1)
  rw [show m - 1 + 1 = m by omega] at h1
  calc 2 * 8 ^ (2 * xs (m - 1)) ≤ 8 ^ 1 * 8 ^ (2 * xs (m - 1)) := by norm_num
    _ = 8 ^ (1 + 2 * xs (m - 1)) := by rw [← pow_add]
    _ ≤ 8 ^ (2 * xs m) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma dRead_two_le_b (m : ℕ) : 2 ≤ seqB dRead m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [seqB_dRead_zero]
  · rw [seqB_dRead hm]
    have := xs_lt_ys (m - 1)
    calc 2 ≤ 8 ^ 1 := by norm_num
      _ ≤ 8 ^ (2 * ys (m - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma dRead_a_sq {n : ℕ} (hn : 1 ≤ n) : n ^ 2 * seqA dRead n ^ 2 < seqB dRead n := by
  rw [seqA_dRead hn, seqB_dRead hn, ← pow_mul]
  have hy := ys_ge (n - 1)
  have := lt_eight_pow (2 * xs (n - 1))
  have h1 : n ^ 2 < 8 ^ (2 * n) := by
    rw [pow_mul']; exact Nat.pow_lt_pow_left (lt_eight_pow n) (by norm_num)
  calc n ^ 2 * 8 ^ (2 * xs (n - 1) * 2) < 8 ^ (2 * n) * 8 ^ (2 * xs (n - 1) * 2) :=
        Nat.mul_lt_mul_of_pos_right h1 (by positivity)
    _ = 8 ^ (2 * n + 2 * xs (n - 1) * 2) := by rw [← pow_add]
    _ ≤ 8 ^ (2 * ys (n - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma dRead_four_sq_b_lt_a {m : ℕ} (hm : 1 ≤ m) : 4 * seqB dRead m ^ 2 < seqA dRead (m + 1) := by
  rw [seqB_dRead hm, seqA_dRead (by omega), Nat.add_sub_cancel, ← pow_mul]
  have hx : 8 ^ (2 * ys (m - 1)) + 2 * ys (m - 1) + (m - 1) + 4 ≤ xs m := by
    rw [show m = m - 1 + 1 by omega, xs_succ, Nat.add_sub_cancel]
  have := lt_eight_pow (2 * ys (m - 1))
  calc 4 * 8 ^ (2 * ys (m - 1) * 2) < 8 ^ 1 * 8 ^ (2 * ys (m - 1) * 2) :=
        Nat.mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    _ = 8 ^ (1 + 2 * ys (m - 1) * 2) := by rw [← pow_add]
    _ ≤ 8 ^ (2 * xs m) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `α x² < α^{√x/4}` for `x = 8^{2s}`, `s ≥ 2`. -/
lemma rpow_of_eight_pow {s : ℕ} (hs : 2 ≤ s) :
    alpha * (((8 ^ (2 * s) : ℕ) : ℝ)) ^ 2 < alpha ^ (Real.sqrt ((8 ^ (2 * s) : ℕ) : ℝ) / 4) := by
  rw [sqrt_eight_pow]
  have h1 : alpha * (((8 ^ (2 * s) : ℕ) : ℝ)) ^ 2 = (8 : ℝ) ^ (4 * s + 1) := by
    rw [alpha]; push_cast; ring
  rw [h1]
  refine eight_pow_lt_alpha_rpow ?_
  have h2 := sixteen_mul_add_lt_pow hs
  have h3 : ((16 * s + 4 : ℕ) : ℝ) < ((8 ^ s : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at h3 ⊢
  linarith

lemma dRead_rpow_a {n : ℕ} (hn : 1 ≤ n) :
    alpha * (seqA dRead n : ℝ) ^ 2 < alpha ^ (Real.sqrt (seqA dRead n) / 4) := by
  rw [seqA_dRead hn]; exact rpow_of_eight_pow (two_le_xs _)

lemma dRead_rpow_b {n : ℕ} (hn : 1 ≤ n) :
    alpha * (seqB dRead n : ℝ) ^ 2 < alpha ^ (Real.sqrt (seqB dRead n) / 4) := by
  rw [seqB_dRead hn]
  exact rpow_of_eight_pow ((two_le_xs _).trans (xs_lt_ys _).le)

lemma dRead_pow_b {n : ℕ} (hn : 1 ≤ n) :
    (seqB dRead n : ℝ) ^ (4 * n) < alpha ^ (Real.sqrt (seqB dRead n) / 4) := by
  rw [seqB_dRead hn, sqrt_eight_pow]
  have hy := ys_ge (n - 1)
  have := lt_eight_pow (2 * xs (n - 1))
  set y := ys (n - 1)
  have hy4 : 4 ≤ y := by omega
  have hny : n ≤ y := by omega
  rw [show (((8 ^ (2 * y) : ℕ) : ℝ)) ^ (4 * n) = (8 : ℝ) ^ (2 * y * (4 * n)) by push_cast; ring]
  refine eight_pow_lt_alpha_rpow ?_
  have h1 := thirtytwo_sq_lt_pow hy4
  have h2 : 32 * (y * n) ≤ 32 * y ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hny)
  have h3 : ((2 * y * (4 * n) : ℕ) : ℝ) * 4 < ((8 ^ y : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * y * (4 * n) * 4 < 8 ^ y by nlinarith)
  push_cast at h3 ⊢
  linarith

lemma dRead_rpow_b_add_two_le {m : ℕ} (hm : 1 ≤ m) :
    alpha ^ Real.sqrt (seqB dRead m) + 2 ≤ alpha ^ Real.sqrt (seqA dRead (m + 1)) := by
  rw [seqB_dRead hm, seqA_dRead (by omega), Nat.add_sub_cancel, sqrt_eight_pow, sqrt_eight_pow,
    alpha_rpow_eight_pow, alpha_rpow_eight_pow]
  have h1 := xs_lt_ys (m - 1)
  have h2 : ys (m - 1) + 1 ≤ xs m := by
    have := xs_succ (m - 1); rw [show m - 1 + 1 = m by omega] at this
    have := lt_eight_pow (2 * ys (m - 1)); omega
  have h3 : 8 ^ ys (m - 1) + 1 ≤ 8 ^ xs m := by
    have : 8 ^ (ys (m - 1) + 1) ≤ 8 ^ xs m := Nat.pow_le_pow_right (by norm_num) h2
    rw [pow_succ] at this
    have := Nat.one_le_pow (ys (m - 1)) 8 (by norm_num)
    omega
  have h4 : (1 : ℝ) ≤ (8 : ℝ) ^ (8 ^ ys (m - 1)) := one_le_pow₀ (by norm_num)
  calc (8 : ℝ) ^ (8 ^ ys (m - 1)) + 2 ≤ (8 : ℝ) ^ (8 ^ ys (m - 1) + 1) := by
        rw [pow_succ]; linarith
    _ ≤ (8 : ℝ) ^ (8 ^ xs m) := eight_pow_mono h3

lemma dRead_three_pow_rpow_a_le {n : ℕ} (hn : 1 ≤ n) :
    3 * (seqB dRead n : ℝ) ^ n * alpha ^ Real.sqrt (seqA dRead n) ≤
      alpha ^ Real.sqrt (seqB dRead n) := by
  rw [seqB_dRead hn, seqA_dRead hn, sqrt_eight_pow, sqrt_eight_pow, alpha_rpow_eight_pow,
    alpha_rpow_eight_pow]
  have hy := ys_ge (n - 1)
  have h8x := eight_pow_le_ys (n - 1)
  have := lt_eight_pow (2 * xs (n - 1))
  set x := xs (n - 1)
  set y := ys (n - 1)
  have hy4 : 4 ≤ y := by omega
  have hny : n ≤ y := by omega
  have h1 := thirtytwo_sq_lt_pow hy4
  have hexp : 1 + 2 * y * n + 8 ^ x ≤ 8 ^ y := by
    have : 2 * y * n ≤ 2 * y ^ 2 := by
      rw [sq, mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hny)
    nlinarith
  calc 3 * (((8 ^ (2 * y) : ℕ) : ℝ)) ^ n * (8 : ℝ) ^ (8 ^ x)
      ≤ 8 * (((8 ^ (2 * y) : ℕ) : ℝ)) ^ n * (8 : ℝ) ^ (8 ^ x) := by gcongr; norm_num
    _ = (8 : ℝ) ^ (1 + 2 * y * n + 8 ^ x) := by push_cast; ring
    _ ≤ (8 : ℝ) ^ (8 ^ y) := eight_pow_mono hexp

lemma dRead_q_bound {m : ℕ} (hm : 2 ≤ m) :
    (seqA dRead m : ℝ) * alpha ^ Real.sqrt (seqB dRead (m - 1)) ≤
      alpha ^ (Real.sqrt (seqA dRead m) / 2) := by
  rw [seqA_dRead (by omega), seqB_dRead (by omega), sqrt_eight_pow, sqrt_eight_pow,
    alpha_rpow_eight_pow]
  have hx : 8 ^ (2 * ys (m - 1 - 1)) ≤ xs (m - 1) := by
    have := xs_succ (m - 1 - 1); rw [show m - 1 - 1 + 1 = m - 1 by omega] at this; omega
  have hy := le_eight_pow_two_mul (ys (m - 1 - 1))
  have h16 := sixteen_mul_add_lt_pow (two_le_xs (m - 1))
  set x := xs (m - 1)
  set y := ys (m - 1 - 1)
  rw [show (((8 ^ (2 * x) : ℕ) : ℝ)) * (8 : ℝ) ^ (8 ^ y) = (8 : ℝ) ^ (2 * x + 8 ^ y) by
    push_cast; ring]
  refine eight_pow_le_alpha_rpow ?_
  have h2 : ((2 * x + 8 ^ y : ℕ) : ℝ) * 2 ≤ ((8 ^ x : ℕ) : ℝ) := by
    exact_mod_cast (show (2 * x + 8 ^ y) * 2 ≤ 8 ^ x by omega)
  push_cast at h2 ⊢
  linarith

lemma dRead_alpha_pow_two_b_le {m : ℕ} (hm : 1 ≤ m) :
    alpha ^ (2 * seqB dRead m) ≤ seqA dRead (m + 1) := by
  rw [seqB_dRead hm, seqA_dRead (by omega), Nat.add_sub_cancel, alpha]
  have hx : 8 ^ (2 * ys (m - 1)) ≤ xs m := by
    have := xs_succ (m - 1); rw [show m - 1 + 1 = m by omega] at this; omega
  push_cast
  exact eight_pow_mono (by omega)

lemma dRead_rpow_a_le_b {n : ℕ} (hn : 1 ≤ n) : alpha ^ Real.sqrt (seqA dRead n) ≤ seqB dRead n := by
  rw [seqA_dRead hn, seqB_dRead hn, sqrt_eight_pow, alpha_rpow_eight_pow]
  have := eight_pow_le_ys (n - 1)
  push_cast
  exact eight_pow_mono (by omega)

lemma dRead_r_bound {m : ℕ} (hm : 3 ≤ m) :
    alpha * seqA dRead m * capA dRead m *
        (seqA dRead m * capA dRead m) ^ (2 * ((m - 2) * seqA dRead m)).factorial <
      seqB dRead m := by
  rw [capA_dRead (by omega), seqA_dRead (by omega), seqB_dRead (by omega), alpha]
  have hy := ys_ge_r (m - 1)
  set x := xs (m - 1)
  set y := ys (m - 1)
  set F := (2 * ((m - 2) * 8 ^ (2 * x))).factorial
  have hF : F ≤ (2 * (m - 1 + 1) * 8 ^ (2 * x)).factorial := by
    refine Nat.factorial_le ?_
    have : (m - 2) * 8 ^ (2 * x) ≤ (m - 1 + 1) * 8 ^ (2 * x) := Nat.mul_le_mul_right _ (by omega)
    calc 2 * ((m - 2) * 8 ^ (2 * x)) ≤ 2 * ((m - 1 + 1) * 8 ^ (2 * x)) := Nat.mul_le_mul_left _ this
      _ = 2 * (m - 1 + 1) * 8 ^ (2 * x) := by ring
  have hexp : 1 + 2 * x + 8 ^ x + (2 * x + 8 ^ x) * F < 2 * y := by
    have : (2 * x + 8 ^ x) * F ≤ (2 * x + 8 ^ x) * (2 * (m - 1 + 1) * 8 ^ (2 * x)).factorial :=
      Nat.mul_le_mul_left _ hF
    have hy1 : 1 ≤ y := le_trans (Nat.le_add_left 1 _) hy
    nlinarith
  calc (8 : ℝ) * (((8 ^ (2 * x) : ℕ) : ℝ)) * (8 : ℝ) ^ (8 ^ x) *
        ((((8 ^ (2 * x) : ℕ) : ℝ)) * (8 : ℝ) ^ (8 ^ x)) ^ F
      = (8 : ℝ) ^ (1 + 2 * x + 8 ^ x + (2 * x + 8 ^ x) * F) := by push_cast; ring
    _ < (8 : ℝ) ^ (2 * y) := eight_pow_strictMono hexp
    _ = (((8 ^ (2 * y) : ℕ) : ℝ)) := by push_cast; ring

/-- **The explicit sequence satisfies every growth fact.** -/
theorem theorem7Hyp_dRead : Theorem7Hyp dRead where
  one_le_a := dRead_one_le_a
  v_lt_a n k hkn := by have := dRead_v_small n k hkn; omega
  a_lt_b n := by
    rcases Nat.lt_or_ge n 1 with hn | hn
    · rw [show n = 0 by omega, seqB_dRead_zero]; simp
    · have h1 := dRead_a_small hn
      have : (n - 2) * seqA dRead n ≤ 8 * n * seqA dRead n := Nat.mul_le_mul_right _ (by omega)
      omega
  a_double _ hm := dRead_a_double hm
  two_le_b := dRead_two_le_b
  v_small := dRead_v_small
  a_small _ hn := dRead_a_small hn
  b_small _ hn := dRead_b_small hn
  a_sq _ hn := dRead_a_sq hn
  a_big _ hn := dRead_a_big hn
  rpow_a _ hn := dRead_rpow_a hn
  rpow_b _ hn := dRead_rpow_b hn
  pow_b _ hn := dRead_pow_b hn
  rpow_b_add_two_le _ hm := dRead_rpow_b_add_two_le hm
  three_pow_rpow_a_le _ hn := dRead_three_pow_rpow_a_le hn
  q_bound _ hm := dRead_q_bound hm
  four_sq_b_lt_a _ hm := dRead_four_sq_b_lt_a hm
  alpha_pow_two_b_le _ hm := dRead_alpha_pow_two_b_le hm
  rpow_a_le_b _ hn := dRead_rpow_a_le_b hn
  r_bound _ hm := dRead_r_bound hm

end ReadL1
