/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The dyadic descent of the matrix method

The matrix method of Daubechies–Lagarias proves Hölder continuity of a refinable function from a
recursion on the two halves of `[0, 1)`. This file contains the method in a scalar form, for
functions `A, B : ℝ → E` with values in a seminormed group, and the passage from oscillation
bounds on dyadic intervals to a Hölder estimate. The file
`FunctionSpaces.Wavelets.Examples.Daubechies.MatrixMethodD4` applies it to the scaling function
of D4.

The dyadic intervals of level `n` in `[0, 1)` are `I_{n,k} = [k/2^n, (k+1)/2^n)`, `0 ≤ k < 2^n`.
For `k < 2^(n+1)` and `d = ⌊k/2^n⌋ ∈ {0, 1}` the interval `I_{n+1,k}` lies in the half
`[d/2, (d+1)/2)`, and `x ↦ 2x - d` maps it onto `I_{n,r}` with `r = k mod 2^n`
(`Daubechies.mem_Ico_half_of_mem_dyadic`, `Daubechies.two_mul_sub_mem_dyadic`).

* **Halving recursion.** If `A` has oscillation at most `E_A` on `[0, 1)` and
  `‖A(x) - A(y)‖ ≤ ‖A(2x - d) - A(2y - d)‖/2` for `x, y` in the half `[d/2, (d+1)/2)`, then
  `‖A(x) - A(y)‖ ≤ E_A/2^n` for `x, y` in one interval `I_{n,k}`
  (`Daubechies.norm_sub_le_of_halving`).
* **Triangular recursion.** If moreover `B` has oscillation at most `E_B` on `[0, 1)`,
  `‖B(x) - B(y)‖ ≤ β ‖A(2x - d) - A(2y - d)‖ + ρ ‖B(2x - d) - B(2y - d)‖` on the halves with
  `β, ρ ≥ 0`, and `β E_A ≤ (ρ - 1/2) C`, then `‖B(x) - B(y)‖ ≤ ρ^n (E_B + C) - C/2^n` for `x, y`
  in one interval `I_{n,k}` (`Daubechies.norm_sub_le_of_triangular`). The pair of differences
  follows a lower triangular recursion with diagonal `(1/2, ρ)`, and for `ρ > 1/2` its rate is
  `ρ^n`.
* **Hölder estimate.** Let `f : ℝ → E` be continuous and bounded with
  `‖f(x + i) - f(y + i)‖ ≤ C ρ^n` for every integer `i` and all `x, y` in one interval `I_{n,k}`.
  By continuity the bound holds on the closed intervals `[k/2^n, (k+1)/2^n]`, `k ∈ ℤ`
  (`Daubechies.norm_sub_le_of_forall_Ico`, `Daubechies.norm_sub_le_of_unit_dyadic`); two points
  at distance at most `2^(-n)` lie in one closed interval or in two adjacent ones
  (`Daubechies.norm_sub_le_of_adjacent_dyadic`). For `0 ≤ ρ ≤ 2^(-a)` with `a ≥ 0`, the level `n`
  with `2^(-(n+1)) < |x - y| ≤ 2^(-n)` gives `‖f(x) - f(y)‖ ≤ K |x - y|^a`
  (`Daubechies.exists_holder_of_dyadic`, `Daubechies.exists_holder_of_unit_dyadic`).
-/

@[expose] public section

open Set

namespace Daubechies

/-! ### The dyadic descent -/

section DyadicDescent

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **The parent half of a dyadic interval**: for `n, k ∈ ℕ` put `d = ⌊k / 2^n⌋` (natural
division). Every point `x` of the dyadic interval `[k/2^(n+1), (k+1)/2^(n+1))` lies in the half
`[d/2, (d+1)/2)`. -/
theorem mem_Ico_half_of_mem_dyadic {n k : ℕ} {x : ℝ}
    (hx : x ∈ Ico ((k : ℝ) / 2 ^ (n + 1)) ((k + 1) / 2 ^ (n + 1))) :
    x ∈ Ico (((k / 2 ^ n : ℕ) : ℝ) / 2) ((((k / 2 ^ n : ℕ) : ℝ) + 1) / 2) := by
  have hk : (k : ℝ) = 2 ^ n * ((k / 2 ^ n : ℕ) : ℝ) + ((k % 2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod k (2 ^ n)).symm
  have hr : ((k % 2 ^ n : ℕ) : ℝ) + 1 ≤ 2 ^ n := by
    exact_mod_cast Nat.mod_lt k (by positivity)
  have hr0 : (0 : ℝ) ≤ ((k % 2 ^ n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [mem_Ico, pow_succ, div_le_iff₀ (by positivity), lt_div_iff₀ (by positivity)] at hx
  rw [mem_Ico, div_le_iff₀ two_pos, lt_div_iff₀ two_pos]
  constructor <;> nlinarith

/-- **The doubling map on a dyadic interval**: for `n, k ∈ ℕ` put `d = ⌊k / 2^n⌋` and
`r = k mod 2^n`, so that `k = 2^n d + r`. The map `x ↦ 2x - d` sends the dyadic interval
`[k/2^(n+1), (k+1)/2^(n+1))` of level `n + 1` onto the dyadic interval `[r/2^n, (r+1)/2^n)` of
level `n`. -/
theorem two_mul_sub_mem_dyadic {n k : ℕ} {x : ℝ}
    (hx : x ∈ Ico ((k : ℝ) / 2 ^ (n + 1)) ((k + 1) / 2 ^ (n + 1))) :
    2 * x - ((k / 2 ^ n : ℕ) : ℝ) ∈
      Ico (((k % 2 ^ n : ℕ) : ℝ) / 2 ^ n) ((((k % 2 ^ n : ℕ) : ℝ) + 1) / 2 ^ n) := by
  have hk : (k : ℝ) = 2 ^ n * ((k / 2 ^ n : ℕ) : ℝ) + ((k % 2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod k (2 ^ n)).symm
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [mem_Ico, pow_succ, div_le_iff₀ (by positivity), lt_div_iff₀ (by positivity)] at hx
  rw [mem_Ico, div_le_iff₀ h2, lt_div_iff₀ h2]
  constructor <;> nlinarith

/-- A dyadic interval `[k/2^n, (k+1)/2^n)` with `k < 2^n` lies in `[0, 1)`. -/
theorem mem_Ico_zero_one_of_mem_dyadic {n k : ℕ} (hk : k < 2 ^ n) {x : ℝ}
    (hx : x ∈ Ico ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n)) : x ∈ Ico (0 : ℝ) 1 := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hk' : (k : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast hk
  rw [mem_Ico, div_le_iff₀ h2, lt_div_iff₀ h2] at hx
  constructor <;> nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- The index of the parent half: for `k < 2^(n+1)`, `d = ⌊k / 2^n⌋` is `0` or `1`. -/
theorem div_two_pow_lt_two {n k : ℕ} (hk : k < 2 ^ (n + 1)) : k / 2 ^ n < 2 :=
  (Nat.div_lt_iff_lt_mul (by positivity)).2 (by rwa [pow_succ'] at hk)

/-- **Dyadic descent for a halving recursion.** Let `A : ℝ → E` have oscillation at most `E_A`
on `[0, 1)` and satisfy, on each half `[d/2, (d+1)/2)` (`d ∈ {0, 1}`),
`‖A(x) - A(y)‖ ≤ ‖A(2x - d) - A(2y - d)‖ / 2`. Then for all `x, y` in one dyadic interval
`[k/2^n, (k+1)/2^n)` of level `n` inside `[0, 1)` (that is, `k < 2^n`),
`‖A(x) - A(y)‖ ≤ E_A / 2^n`. By induction on `n`: the doubling map `x ↦ 2x - d` sends a dyadic
interval of level `n + 1` onto one of level `n` (`Daubechies.two_mul_sub_mem_dyadic`). -/
theorem norm_sub_le_of_halving {A : ℝ → E} {EA : ℝ}
    (hE : ∀ x ∈ Ico (0 : ℝ) 1, ∀ y ∈ Ico (0 : ℝ) 1, ‖A x - A y‖ ≤ EA)
    (hA : ∀ d : ℕ, d < 2 → ∀ x ∈ Ico ((d : ℝ) / 2) ((d + 1) / 2),
      ∀ y ∈ Ico ((d : ℝ) / 2) ((d + 1) / 2), ‖A x - A y‖ ≤ ‖A (2 * x - d) - A (2 * y - d)‖ / 2)
    (n : ℕ) {k : ℕ} (hk : k < 2 ^ n) {x y : ℝ} (hx : x ∈ Ico ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n))
    (hy : y ∈ Ico ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n)) : ‖A x - A y‖ ≤ EA / 2 ^ n := by
  induction n generalizing k x y with
  | zero =>
    obtain rfl : k = 0 := by simpa using hk
    simpa using hE x (by simpa using hx) y (by simpa using hy)
  | succ n ih =>
    have h := hA _ (div_two_pow_lt_two hk) x (mem_Ico_half_of_mem_dyadic hx) y
      (mem_Ico_half_of_mem_dyadic hy)
    have h' := ih (Nat.mod_lt k (by positivity)) (two_mul_sub_mem_dyadic hx)
      (two_mul_sub_mem_dyadic hy)
    calc ‖A x - A y‖ ≤ EA / 2 ^ n / 2 := h.trans (by gcongr)
      _ = EA / 2 ^ (n + 1) := by rw [pow_succ, div_div]

/-- **Dyadic descent for a triangular recursion.** Let `A, B : ℝ → E`, where `A` satisfies the
level bounds `‖A(x) - A(y)‖ ≤ E_A / 2^n` on the dyadic intervals of level `n` in `[0, 1)` (as
provided by `Daubechies.norm_sub_le_of_halving`), `B` has oscillation at most `E_B` on `[0, 1)`,
and on each half `[d/2, (d+1)/2)`
`‖B(x) - B(y)‖ ≤ β ‖A(2x - d) - A(2y - d)‖ + ρ ‖B(2x - d) - B(2y - d)‖`
with `β, ρ ≥ 0`. If `C` satisfies `β E_A ≤ (ρ - 1/2) C`, then on the dyadic intervals of level
`n` in `[0, 1)`
`‖B(x) - B(y)‖ ≤ ρ^n (E_B + C) - C / 2^n`.
This is the statement that a lower triangular `2 × 2` recursion with diagonal `1/2, ρ` produces
the rate `ρ^n` when `ρ > 1/2`; the term `- C / 2^n` makes the induction on `n` close. -/
theorem norm_sub_le_of_triangular {A B : ℝ → E} {EA EB β ρ C : ℝ} (hβ : 0 ≤ β) (hρ : 0 ≤ ρ)
    (hC : β * EA ≤ (ρ - 1 / 2) * C)
    (hA : ∀ (n k : ℕ), k < 2 ^ n → ∀ x ∈ Ico ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n),
      ∀ y ∈ Ico ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n), ‖A x - A y‖ ≤ EA / 2 ^ n)
    (hE : ∀ x ∈ Ico (0 : ℝ) 1, ∀ y ∈ Ico (0 : ℝ) 1, ‖B x - B y‖ ≤ EB)
    (hB : ∀ d : ℕ, d < 2 → ∀ x ∈ Ico ((d : ℝ) / 2) ((d + 1) / 2),
      ∀ y ∈ Ico ((d : ℝ) / 2) ((d + 1) / 2), ‖B x - B y‖ ≤
        β * ‖A (2 * x - d) - A (2 * y - d)‖ + ρ * ‖B (2 * x - d) - B (2 * y - d)‖)
    (n : ℕ) {k : ℕ} (hk : k < 2 ^ n) {x y : ℝ} (hx : x ∈ Ico ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n))
    (hy : y ∈ Ico ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n)) :
    ‖B x - B y‖ ≤ ρ ^ n * (EB + C) - C / 2 ^ n := by
  induction n generalizing k x y with
  | zero =>
    obtain rfl : k = 0 := by simpa using hk
    simpa using hE x (by simpa using hx) y (by simpa using hy)
  | succ n ih =>
    have hk' := Nat.mod_lt k (pow_pos two_pos n)
    have h := hB _ (div_two_pow_lt_two hk) x (mem_Ico_half_of_mem_dyadic hx) y
      (mem_Ico_half_of_mem_dyadic hy)
    have hA' := hA n _ hk' _ (two_mul_sub_mem_dyadic hx) _ (two_mul_sub_mem_dyadic hy)
    have hB' := ih hk' (two_mul_sub_mem_dyadic hx) (two_mul_sub_mem_dyadic hy)
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    calc ‖B x - B y‖ ≤ β * (EA / 2 ^ n) + ρ * (ρ ^ n * (EB + C) - C / 2 ^ n) :=
          h.trans (add_le_add (mul_le_mul_of_nonneg_left hA' hβ)
            (mul_le_mul_of_nonneg_left hB' hρ))
      _ = ρ ^ (n + 1) * (EB + C) - C / 2 ^ (n + 1) + (β * EA - (ρ - 1 / 2) * C) / 2 ^ n := by
          rw [pow_succ, pow_succ]
          field_simp
          ring
      _ ≤ ρ ^ (n + 1) * (EB + C) - C / 2 ^ (n + 1) := by
          have : (β * EA - (ρ - 1 / 2) * C) / 2 ^ n ≤ 0 :=
            div_nonpos_of_nonpos_of_nonneg (by linarith) h2.le
          linarith

end DyadicDescent

/-! ### From dyadic oscillation bounds to a Hölder estimate -/

section Holder

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **Oscillation bounds pass to the closed interval**: if `f : ℝ → E` is continuous, `a < b`,
and `‖f(x) - f(y)‖ ≤ C` for all `x, y ∈ [a, b)`, then the same holds for all `x, y ∈ [a, b]`.
The set of pairs `(x, y)` with `‖f(x) - f(y)‖ ≤ C` is closed and contains `[a, b) × [a, b)`,
hence its closure `[a, b] × [a, b]` (Mathlib's `closure_prod_eq`, `closure_Ico`). -/
theorem norm_sub_le_of_forall_Ico {f : ℝ → E} (hf : Continuous f) {a b C : ℝ} (hab : a < b)
    (h : ∀ x ∈ Ico a b, ∀ y ∈ Ico a b, ‖f x - f y‖ ≤ C) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖f x - f y‖ ≤ C := by
  have hS : IsClosed {p : ℝ × ℝ | ‖f p.1 - f p.2‖ ≤ C} :=
    isClosed_le (by fun_prop) continuous_const
  have hsub : closure (Ico a b ×ˢ Ico a b) ⊆ {p : ℝ × ℝ | ‖f p.1 - f p.2‖ ≤ C} :=
    closure_minimal (fun p hp => h p.1 hp.1 p.2 hp.2) hS
  rw [closure_prod_eq, closure_Ico hab.ne] at hsub
  exact fun x hx y hy => hsub (mk_mem_prod hx hy)

/-- **From the dyadic intervals of `[0, 1)` to those of `ℝ`**: let `f : ℝ → E` be continuous,
`n ∈ ℕ`, and suppose that `‖f(x + i) - f(y + i)‖ ≤ C` for every integer `i` and all `x, y` in
one dyadic interval `[k/2^n, (k+1)/2^n)` with `0 ≤ k < 2^n`. Then `‖f(x) - f(y)‖ ≤ C` for all
`x, y` in one closed dyadic interval `[k/2^n, (k+1)/2^n]`, `k ∈ ℤ`. Write `k = 2^n q + r` with
`0 ≤ r < 2^n` and apply `Daubechies.norm_sub_le_of_forall_Ico` to `t ↦ f(t + q)`. -/
theorem norm_sub_le_of_unit_dyadic {f : ℝ → E} (hf : Continuous f) {n : ℕ} {C : ℝ}
    (h : ∀ (i : ℤ) (k : ℕ), k < 2 ^ n → ∀ x ∈ Ico ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n),
      ∀ y ∈ Ico ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n), ‖f (x + i) - f (y + i)‖ ≤ C)
    (k : ℤ) : ∀ x ∈ Icc ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n),
      ∀ y ∈ Icc ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n), ‖f x - f y‖ ≤ C := by
  have hpos : (0 : ℤ) < 2 ^ n := by positivity
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = k % 2 ^ n :=
    ⟨(k % 2 ^ n).toNat, Int.toNat_of_nonneg (Int.emod_nonneg k hpos.ne')⟩
  have hrn : r < 2 ^ n := by
    have := Int.emod_lt_of_pos k hpos
    rw [← hr] at this
    exact_mod_cast this
  have hk : (k : ℝ) = 2 ^ n * ((k / 2 ^ n : ℤ) : ℝ) + r := by
    have := Int.mul_ediv_add_emod k (2 ^ n)
    rw [← hr] at this
    exact_mod_cast this.symm
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hg := norm_sub_le_of_forall_Ico (f := fun t => f (t + ((k / 2 ^ n : ℤ) : ℝ)))
    (hf.comp (continuous_id.add continuous_const)) (div_lt_div_of_pos_right (lt_add_one (r : ℝ)) h2)
    (h (k / 2 ^ n) r hrn)
  have hmem : ∀ x ∈ Icc ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n),
      x - ((k / 2 ^ n : ℤ) : ℝ) ∈ Icc ((r : ℝ) / 2 ^ n) ((r + 1) / 2 ^ n) := by
    intro x hx
    rw [mem_Icc, div_le_iff₀ h2, le_div_iff₀ h2] at hx ⊢
    constructor <;> nlinarith
  intro x hx y hy
  simpa using hg _ (hmem x hx) _ (hmem y hy)

/-- **Two adjacent dyadic intervals**: suppose `‖f(x) - f(y)‖ ≤ c` whenever `x, y` lie in one
closed dyadic interval `[k/2^n, (k+1)/2^n]`, `k ∈ ℤ`. Then `‖f(x) - f(y)‖ ≤ 2c` whenever
`x ≤ y ≤ x + 2^(-n)`: with `k = ⌊2^n x⌋`, either `y` lies in the interval `[k/2^n, (k+1)/2^n]`
of `x`, or the point `z = (k+1)/2^n` joins `x` to `y` through two adjacent intervals. -/
theorem norm_sub_le_of_adjacent_dyadic {f : ℝ → E} {n : ℕ} {c : ℝ}
    (h : ∀ k : ℤ, ∀ x ∈ Icc ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n),
      ∀ y ∈ Icc ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n), ‖f x - f y‖ ≤ c)
    {x y : ℝ} (hxy : x ≤ y) (hyx : y - x ≤ 1 / 2 ^ n) : ‖f x - f y‖ ≤ 2 * c := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hk1 : (⌊(2 : ℝ) ^ n * x⌋ : ℝ) ≤ 2 ^ n * x := Int.floor_le _
  have hk2 : 2 ^ n * x < ⌊(2 : ℝ) ^ n * x⌋ + 1 := Int.lt_floor_add_one _
  have hyx' : (y - x) * 2 ^ n ≤ 1 := by rwa [le_div_iff₀ h2] at hyx
  have hx : x ∈ Icc ((⌊(2 : ℝ) ^ n * x⌋ : ℝ) / 2 ^ n) ((⌊(2 : ℝ) ^ n * x⌋ + 1) / 2 ^ n) := by
    rw [mem_Icc, div_le_iff₀ h2, le_div_iff₀ h2]
    constructor <;> linarith
  have hc : 0 ≤ c := (norm_nonneg _).trans (h _ x hx x hx)
  by_cases hy : y ≤ (⌊(2 : ℝ) ^ n * x⌋ + 1) / 2 ^ n
  · have := h _ x hx y ⟨hx.1.trans hxy, hy⟩
    linarith
  · push Not at hy
    have hz : ((⌊(2 : ℝ) ^ n * x⌋ : ℝ) + 1) / 2 ^ n ∈
        Icc ((⌊(2 : ℝ) ^ n * x⌋ : ℝ) / 2 ^ n) ((⌊(2 : ℝ) ^ n * x⌋ + 1) / 2 ^ n) :=
      ⟨div_le_div_of_nonneg_right (by linarith) h2.le, le_rfl⟩
    have hz' : ((⌊(2 : ℝ) ^ n * x⌋ : ℝ) + 1) / 2 ^ n ∈
        Icc (((⌊(2 : ℝ) ^ n * x⌋ + 1 : ℤ) : ℝ) / 2 ^ n)
          ((((⌊(2 : ℝ) ^ n * x⌋ + 1 : ℤ) : ℝ) + 1) / 2 ^ n) := by
      push_cast
      exact ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) h2.le⟩
    have hy' : y ∈ Icc (((⌊(2 : ℝ) ^ n * x⌋ + 1 : ℤ) : ℝ) / 2 ^ n)
        ((((⌊(2 : ℝ) ^ n * x⌋ + 1 : ℤ) : ℝ) + 1) / 2 ^ n) := by
      push_cast
      refine ⟨hy.le, ?_⟩
      rw [le_div_iff₀ h2]
      linarith
    calc ‖f x - f y‖ = ‖(f x - f ((⌊(2 : ℝ) ^ n * x⌋ + 1) / 2 ^ n)) +
          (f ((⌊(2 : ℝ) ^ n * x⌋ + 1) / 2 ^ n) - f y)‖ := by abel_nf
      _ ≤ ‖f x - f ((⌊(2 : ℝ) ^ n * x⌋ + 1) / 2 ^ n)‖ +
          ‖f ((⌊(2 : ℝ) ^ n * x⌋ + 1) / 2 ^ n) - f y‖ := norm_add_le _ _
      _ ≤ c + c := add_le_add (h _ x hx _ hz) (h _ _ hz' y hy')
      _ = 2 * c := by ring

/-- **Choice of the dyadic level**: for `0 < t ≤ 1` there is `n ∈ ℕ` with
`2^(-(n+1)) < t ≤ 2^(-n)` (Mathlib's `exists_nat_pow_near_of_lt_one` with base `1/2`). -/
theorem exists_dyadic_level {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∃ n : ℕ, 1 / 2 ^ (n + 1) < t ∧ t ≤ 1 / 2 ^ n := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near_of_lt_one ht0 ht1 (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  exact ⟨n, by rwa [one_div_pow] at h1, by rwa [one_div_pow] at h2⟩

/-- **The rate `ρ^n` as a power of the scale**: if `0 ≤ ρ ≤ 2^(-a)` with `a ≥ 0` and
`2^(-(n+1)) < t`, then `ρ^n ≤ 2^a t^a`. Indeed `ρ^n ≤ (2^(-a))^n = (2^(-n))^a` and
`2^(-n) < 2t`. -/
theorem pow_le_two_rpow_mul_rpow {ρ a t : ℝ} {n : ℕ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 2 ^ (-a))
    (ha : 0 ≤ a) (ht : 1 / 2 ^ (n + 1) < t) : ρ ^ n ≤ 2 ^ a * t ^ a := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hpow : ((2 : ℝ) ^ (-a)) ^ n = (1 / 2 ^ n) ^ a := by
    rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num), Real.rpow_pow_comm
      (by norm_num), inv_pow, one_div]
  have hle : 1 / (2 : ℝ) ^ n ≤ 2 * t := by
    rw [pow_succ, ← div_div] at ht
    linarith
  calc ρ ^ n ≤ ((2 : ℝ) ^ (-a)) ^ n := pow_le_pow_left₀ hρ0 hρ n
    _ = (1 / 2 ^ n) ^ a := hpow
    _ ≤ (2 * t) ^ a := Real.rpow_le_rpow (by positivity) hle ha
    _ = 2 ^ a * t ^ a := Real.mul_rpow (by norm_num) (by linarith [ht, one_div_pos.2 h2])

/-- **Hölder continuity from dyadic oscillation bounds**: let `f : ℝ → E` be bounded,
`‖f(x)‖ ≤ M`, and suppose that `‖f(x) - f(y)‖ ≤ C ρ^n` whenever `x, y` lie in one closed dyadic
interval `[k/2^n, (k+1)/2^n]` (`n ∈ ℕ`, `k ∈ ℤ`), where `C ≥ 0`, `0 ≤ ρ ≤ 2^(-a)` and `a ≥ 0`.
Then `f` is Hölder continuous with exponent `a`: there is `K` with
`‖f(x) - f(y)‖ ≤ K |x - y|^a` for all `x, y ∈ ℝ`. For `0 < |x - y| ≤ 1` choose `n` with
`2^(-(n+1)) < |x - y| ≤ 2^(-n)` (`Daubechies.exists_dyadic_level`); then
`‖f(x) - f(y)‖ ≤ 2 C ρ^n ≤ 2 C 2^a |x - y|^a` (`Daubechies.norm_sub_le_of_adjacent_dyadic`,
`Daubechies.pow_le_two_rpow_mul_rpow`). For `|x - y| > 1`,
`‖f(x) - f(y)‖ ≤ 2M ≤ 2M |x - y|^a`. -/
theorem exists_holder_of_dyadic {f : ℝ → E} {M C ρ a : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (hC : 0 ≤ C)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 2 ^ (-a)) (ha : 0 ≤ a)
    (h : ∀ (n : ℕ) (k : ℤ), ∀ x ∈ Icc ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n),
      ∀ y ∈ Icc ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n), ‖f x - f y‖ ≤ C * ρ ^ n) :
    ∃ K, ∀ x y, ‖f x - f y‖ ≤ K * |x - y| ^ a := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hK1 : 0 ≤ 2 * C * 2 ^ a := by positivity
  refine ⟨2 * C * 2 ^ a + 2 * M, fun x y => ?_⟩
  wlog hxy : x ≤ y generalizing x y
  · rw [norm_sub_rev, abs_sub_comm]
    exact this y x (le_of_not_ge hxy)
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · simp only [sub_self, norm_zero, abs_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg le_rfl a)
  rw [abs_sub_comm, abs_of_pos (sub_pos.2 hlt)]
  have ht0 : 0 ≤ (y - x) ^ a := Real.rpow_nonneg (sub_pos.2 hlt).le a
  by_cases h1 : y - x ≤ 1
  · obtain ⟨n, hn1, hn2⟩ := exists_dyadic_level (sub_pos.2 hlt) h1
    have hρn := pow_le_two_rpow_mul_rpow hρ0 hρ ha hn1
    calc ‖f x - f y‖ ≤ 2 * (C * ρ ^ n) := norm_sub_le_of_adjacent_dyadic (h n) hxy hn2
      _ ≤ 2 * (C * (2 ^ a * (y - x) ^ a)) := by gcongr
      _ ≤ (2 * C * 2 ^ a + 2 * M) * (y - x) ^ a := by nlinarith [mul_nonneg hM0 ht0]
  · push Not at h1
    have ht : 1 ≤ (y - x) ^ a := Real.one_le_rpow h1.le ha
    calc ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith [hM x, hM y]
      _ ≤ (2 * C * 2 ^ a + 2 * M) * (y - x) ^ a := by
          nlinarith [mul_nonneg (add_nonneg hK1 (by linarith : (0 : ℝ) ≤ 2 * M))
            (sub_nonneg.2 ht)]

/-- **Hölder continuity from dyadic bounds on the unit interval**: let `f : ℝ → E` be continuous
and bounded, `‖f(x)‖ ≤ M`, let `C ≥ 0`, `0 ≤ ρ ≤ 2^(-a)` and `a ≥ 0`, and suppose that
`‖f(x + i) - f(y + i)‖ ≤ C ρ^n` for every `n ∈ ℕ`, every integer `i` and all `x, y` in one dyadic
interval `[k/2^n, (k+1)/2^n)` with `0 ≤ k < 2^n`. Then there is `K` with
`‖f(x) - f(y)‖ ≤ K |x - y|^a` for all `x, y ∈ ℝ` (`Daubechies.norm_sub_le_of_unit_dyadic`,
`Daubechies.exists_holder_of_dyadic`). -/
theorem exists_holder_of_unit_dyadic {f : ℝ → E} (hf : Continuous f) {M C ρ a : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M) (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 2 ^ (-a)) (ha : 0 ≤ a)
    (h : ∀ (n : ℕ) (i : ℤ) (k : ℕ), k < 2 ^ n → ∀ x ∈ Ico ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n),
      ∀ y ∈ Ico ((k : ℝ) / 2 ^ n) ((k + 1) / 2 ^ n), ‖f (x + i) - f (y + i)‖ ≤ C * ρ ^ n) :
    ∃ K, ∀ x y, ‖f x - f y‖ ≤ K * |x - y| ^ a :=
  exists_holder_of_dyadic hM hC hρ0 hρ ha fun n => norm_sub_le_of_unit_dyadic hf (h n)

end Holder

end Daubechies
