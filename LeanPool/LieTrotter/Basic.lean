/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.NoncommRing

/-!
# The Lie–Trotter product formula in a Banach algebra

For arbitrary elements `A, B` of a complete normed algebra over `ℝ` with `‖1‖ = 1`,

  `(exp (A/n) · exp (B/n))ⁿ → exp (A + B)`,

with the explicit rate `‖(exp (A/n) · exp (B/n))ⁿ − exp (A + B)‖ ≤ n⁻¹ · s²(3 + s)e^{2s}` for
every `n ≥ 1`, where `s = ‖A‖ + ‖B‖`.

The chain:

* `norm_exp_le_exp_norm`: `‖exp X‖ ≤ e^{‖X‖}`, by termwise domination of the series;
* `norm_exp_sub_one_sub_le`: the second-order remainder `‖exp X − 1 − X‖ ≤ ‖X‖² e^{‖X‖}`;
* `norm_exp_mul_exp_sub_exp_add_le`: the one-step defect
  `‖exp X · exp Y − exp (X + Y)‖ ≤ (‖X‖ + ‖Y‖)²(3 + ‖X‖ + ‖Y‖)e^{‖X‖+‖Y‖}`;
* `norm_pow_sub_pow_le_of_norm_le`: telescoping, `‖Sⁿ − Tⁿ‖ ≤ n Cⁿ ‖S − T‖` when
  `‖S‖, ‖T‖ ≤ C` and `1 ≤ C`;
* `norm_trotter_sub_le`: the explicit rate. At step `n` the one-step defect is `O(1/n²)` and
  the telescoping costs `n (e^{s/n})ⁿ = n e^s`, so the total is `O(1/n)`;
* `trotter_product`: the product formula.

This is the general form of the Lie product formula (after Sophus Lie, for matrices;
H. F. Trotter, 1959, for operator semigroups), in the bounded case: any real Banach algebra.

The file is extracted from csd-lean4 (`CsdLean4/Mathlib/Analysis/NormedSpace/TrotterGeneral.lean`,
https://github.com/zblore/csd-lean4), where it was added on 20 Aug 2026.
Adapted for Lean Pool: the series estimates use `HasSum.norm_le_of_bounded` directly,
avoiding repeated summability and `tsum` conversions and removing heartbeat overrides.
-/

@[expose] public section

open NormedSpace

namespace LieTrotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
variable [NormOneClass 𝔸]

/-- **The exponential norm bound**: `‖exp X‖ ≤ e^{‖X‖}` (termwise domination
of the exponential series). -/
theorem norm_exp_le_exp_norm (X : 𝔸) : ‖exp X‖ ≤ Real.exp ‖X‖ := by
  have hreal : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * ‖X‖ ^ n) (Real.exp ‖X‖) := by
    simpa only [smul_eq_mul, ← Real.exp_eq_exp_ℝ] using
      (exp_series_hasSum_exp' (𝕂 := ℝ) (‖X‖ : ℝ))
  refine (exp_series_hasSum_exp' (𝕂 := ℝ) X).norm_le_of_bounded hreal fun n => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rcases Nat.eq_zero_or_pos n with hzero | hpositive
  · subst hzero
    simp
  · exact mul_le_mul_of_nonneg_left (norm_pow_le' X hpositive) (by positivity)

omit [NormOneClass 𝔸] in
/-- **The quantitative second-order remainder**, Banach-algebra form:
`‖exp X − 1 − X‖ ≤ ‖X‖² · e^{‖X‖}`. -/
theorem norm_exp_sub_one_sub_le (X : 𝔸) :
    ‖exp X - 1 - X‖ ≤ ‖X‖ ^ 2 * Real.exp ‖X‖ := by
  let f : ℕ → 𝔸 := fun n => (n.factorial : ℝ)⁻¹ • X ^ n
  have hreal : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * ‖X‖ ^ n) (Real.exp ‖X‖) := by
    simpa only [smul_eq_mul, ← Real.exp_eq_exp_ℝ] using
      (exp_series_hasSum_exp' (𝕂 := ℝ) (‖X‖ : ℝ))
  have htail : HasSum (fun n => f (n + 2)) (exp X - 1 - X) := by
    convert (hasSum_nat_add_iff' 2).2 (exp_series_hasSum_exp' (𝕂 := ℝ) X) using 1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
      Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_one, Nat.factorial_one]
    abel
  refine htail.norm_le_of_bounded (hreal.mul_left (‖X‖ ^ 2)) fun n => ?_
  have hfactorial : ((n + 2).factorial : ℝ)⁻¹ ≤ (n.factorial : ℝ)⁻¹ := by
    gcongr
    omega
  calc ‖f (n + 2)‖ = ((n + 2).factorial : ℝ)⁻¹ * ‖X ^ (n + 2)‖ := by
        simp only [f, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ ((n + 2).factorial : ℝ)⁻¹ by positivity)]
    _ ≤ ((n + 2).factorial : ℝ)⁻¹ * ‖X‖ ^ (n + 2) :=
        mul_le_mul_of_nonneg_left (norm_pow_le' X (Nat.succ_pos _)) (by positivity)
    _ ≤ (n.factorial : ℝ)⁻¹ * ‖X‖ ^ (n + 2) :=
        mul_le_mul_of_nonneg_right hfactorial (by positivity)
    _ = ‖X‖ ^ 2 * ((n.factorial : ℝ)⁻¹ * ‖X‖ ^ n) := by ring

/-- **The one-step defect**, for any `X, Y`, with no commutativity assumption:
`‖exp X · exp Y − exp (X+Y)‖ ≤ (‖X‖+‖Y‖)²·(3+‖X‖+‖Y‖)·e^{‖X‖+‖Y‖}`. -/
theorem norm_exp_mul_exp_sub_exp_add_le (X Y : 𝔸) :
    ‖exp X * exp Y - exp (X + Y)‖
      ≤ (‖X‖ + ‖Y‖) ^ 2 * (3 + (‖X‖ + ‖Y‖)) * Real.exp (‖X‖ + ‖Y‖) := by
  set a := ‖X‖ with ha
  set b := ‖Y‖ with hb
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hdecomp : exp X * exp Y - exp (X + Y)
      = (exp X - 1 - X) * exp Y + (1 + X) * (exp Y - 1 - Y)
        + (X * Y - (exp (X + Y) - 1 - (X + Y))) := by
    noncomm_ring
  have h1 : ‖(exp X - 1 - X) * exp Y‖ ≤ a ^ 2 * Real.exp a * Real.exp b := by
    calc ‖(exp X - 1 - X) * exp Y‖
        ≤ ‖exp X - 1 - X‖ * ‖exp Y‖ := norm_mul_le _ _
      _ ≤ (a ^ 2 * Real.exp a) * Real.exp b := by
          refine mul_le_mul (norm_exp_sub_one_sub_le X)
            (norm_exp_le_exp_norm Y) (norm_nonneg _) (by positivity)
  have h2 : ‖(1 + X) * (exp Y - 1 - Y)‖ ≤ (1 + a) * (b ^ 2 * Real.exp b) := by
    calc ‖(1 + X) * (exp Y - 1 - Y)‖
        ≤ ‖(1 : 𝔸) + X‖ * ‖exp Y - 1 - Y‖ := norm_mul_le _ _
      _ ≤ (1 + a) * (b ^ 2 * Real.exp b) := by
          have hone : ‖(1 : 𝔸) + X‖ ≤ 1 + a := by
            calc ‖(1 : 𝔸) + X‖ ≤ ‖(1 : 𝔸)‖ + ‖X‖ := norm_add_le _ _
              _ = 1 + a := by rw [norm_one]
          exact mul_le_mul hone (norm_exp_sub_one_sub_le Y)
            (norm_nonneg _) (by positivity)
  have h3 : ‖X * Y - (exp (X + Y) - 1 - (X + Y))‖
      ≤ a * b + (a + b) ^ 2 * Real.exp (a + b) := by
    calc ‖X * Y - (exp (X + Y) - 1 - (X + Y))‖
        ≤ ‖X * Y‖ + ‖exp (X + Y) - 1 - (X + Y)‖ := norm_sub_le _ _
      _ ≤ a * b + (a + b) ^ 2 * Real.exp (a + b) := by
          refine add_le_add (norm_mul_le _ _) ?_
          calc ‖exp (X + Y) - 1 - (X + Y)‖
              ≤ ‖X + Y‖ ^ 2 * Real.exp ‖X + Y‖ := norm_exp_sub_one_sub_le _
            _ ≤ (a + b) ^ 2 * Real.exp (a + b) := by
                have hab : ‖X + Y‖ ≤ a + b := norm_add_le _ _
                gcongr
  have heab : Real.exp a * Real.exp b = Real.exp (a + b) :=
    (Real.exp_add a b).symm
  have heb : Real.exp b ≤ Real.exp (a + b) :=
    Real.exp_le_exp.mpr (by linarith)
  have he1 : (1 : ℝ) ≤ Real.exp (a + b) :=
    Real.one_le_exp (by linarith)
  have hepos : (0 : ℝ) < Real.exp (a + b) := Real.exp_pos _
  -- The difference is `a² + 3ab + b² + a³ + 3a²b + 2ab² + b³ ≥ 0`.
  have hpoly : a ^ 2 + (1 + a) * b ^ 2 + (a * b + (a + b) ^ 2)
      ≤ (a + b) ^ 2 * (3 + (a + b)) := by
    nlinarith [mul_nonneg ha0 hb0, mul_nonneg (mul_nonneg ha0 ha0) hb0,
      mul_nonneg (mul_nonneg ha0 hb0) hb0, sq_nonneg a, sq_nonneg b]
  calc ‖exp X * exp Y - exp (X + Y)‖
      ≤ ‖(exp X - 1 - X) * exp Y‖ + ‖(1 + X) * (exp Y - 1 - Y)‖
        + ‖X * Y - (exp (X + Y) - 1 - (X + Y))‖ := by
        rw [hdecomp]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ a ^ 2 * Real.exp a * Real.exp b + (1 + a) * (b ^ 2 * Real.exp b)
        + (a * b + (a + b) ^ 2 * Real.exp (a + b)) :=
        add_le_add (add_le_add h1 h2) h3
    _ ≤ a ^ 2 * Real.exp (a + b) + (1 + a) * (b ^ 2 * Real.exp (a + b))
        + (a * b * Real.exp (a + b) + (a + b) ^ 2 * Real.exp (a + b)) := by
        refine add_le_add (add_le_add ?_ ?_) (add_le_add ?_ le_rfl)
        · rw [mul_assoc, heab]
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left heb (by positivity)) (by linarith)
        · calc a * b = a * b * 1 := by ring
            _ ≤ a * b * Real.exp (a + b) :=
              mul_le_mul_of_nonneg_left he1 (mul_nonneg ha0 hb0)
    _ = (a ^ 2 + (1 + a) * b ^ 2 + (a * b + (a + b) ^ 2))
        * Real.exp (a + b) := by ring
    _ ≤ (a + b) ^ 2 * (3 + (a + b)) * Real.exp (a + b) :=
        mul_le_mul_of_nonneg_right hpoly hepos.le

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] in
/-- **Telescoping**: for `‖S‖, ‖T‖ ≤ C`, `‖Sⁿ⁺¹ − Tⁿ⁺¹‖ ≤ (n + 1) Cⁿ ‖S − T‖`. -/
theorem norm_pow_succ_sub_pow_succ_le {S T : 𝔸} {C : ℝ} (hS : ‖S‖ ≤ C) (hT : ‖T‖ ≤ C)
    (n : ℕ) : ‖S ^ (n + 1) - T ^ (n + 1)‖ ≤ (n + 1) * C ^ n * ‖S - T‖ := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hS
  induction n with
  | zero => simp
  | succ n ih =>
    have hdecomp : S ^ (n + 1 + 1) - T ^ (n + 1 + 1)
        = (S ^ (n + 1) - T ^ (n + 1)) * S + T ^ (n + 1) * (S - T) := by
      rw [pow_succ S (n + 1), pow_succ T (n + 1), sub_mul, mul_sub]
      abel
    have hTn : ‖T ^ (n + 1)‖ ≤ C ^ (n + 1) :=
      (norm_pow_le' T (Nat.succ_pos n)).trans (pow_le_pow_left₀ (norm_nonneg _) hT _)
    calc ‖S ^ (n + 1 + 1) - T ^ (n + 1 + 1)‖
        ≤ ‖S ^ (n + 1) - T ^ (n + 1)‖ * ‖S‖ + ‖T ^ (n + 1)‖ * ‖S - T‖ := by
          rw [hdecomp]
          exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ((n + 1) * C ^ n * ‖S - T‖) * C + C ^ (n + 1) * ‖S - T‖ := by
          gcongr
      _ = ((n + 1 : ℕ) + 1) * C ^ (n + 1) * ‖S - T‖ := by push_cast; ring

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] in
/-- **Growth-controlled telescoping**: for `‖S‖, ‖T‖ ≤ C` with `1 ≤ C`,
`‖Sⁿ − Tⁿ‖ ≤ n · Cⁿ · ‖S − T‖`. -/
theorem norm_pow_sub_pow_le_of_norm_le {S T : 𝔸} {C : ℝ} (hC : 1 ≤ C)
    (hS : ‖S‖ ≤ C) (hT : ‖T‖ ≤ C) (n : ℕ) :
    ‖S ^ n - T ^ n‖ ≤ n * C ^ n * ‖S - T‖ := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  cases n with
  | zero => simp
  | succ n =>
    have hpower : C ^ n ≤ C ^ (n + 1) := by
      calc C ^ n = C ^ n * 1 := (mul_one _).symm
        _ ≤ C ^ n * C := mul_le_mul_of_nonneg_left hC (pow_nonneg hC0 n)
        _ = C ^ (n + 1) := (pow_succ C n).symm
    push_cast
    exact (norm_pow_succ_sub_pow_succ_le hS hT n).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpower (show (0 : ℝ) ≤ n + 1 by positivity))
        (norm_nonneg _))

omit [NormOneClass 𝔸] in
/-- `exp x ^ n = exp (n • x)`, by induction from `exp_add_of_commute`. (Mathlib's `exp_nsmul`
needs a `ℚ`-algebra instance, which instance search does not find for a general real Banach
algebra; it could be supplied by restricting scalars from `ℝ` to `ℚ`.) -/
theorem exp_pow_eq_exp_nsmul (x : 𝔸) (n : ℕ) : exp x ^ n = exp (n • x) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih,
      ← exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
        ((Commute.refl x).smul_left (k : ℕ))
        ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
        ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _),
      ← succ_nsmul]


/-- **The explicit rate.** For `n ≥ 1`,
`‖(exp (A/n) · exp (B/n))ⁿ − exp (A + B)‖ ≤ n⁻¹ · s²(3 + s)e^{2s}` with `s = ‖A‖ + ‖B‖`.
The one-step defect is `O(1/n²)`, and the telescoping costs `n · (e^{s/n})ⁿ = n e^s`. -/
theorem norm_trotter_sub_le (A B : 𝔸) (n : ℕ) (hn : 1 ≤ n) :
    ‖(exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n - exp (A + B)‖
      ≤ (n : ℝ)⁻¹ * ((‖A‖ + ‖B‖) ^ 2 * (3 + (‖A‖ + ‖B‖)) * Real.exp (2 * (‖A‖ + ‖B‖))) := by
  set s := ‖A‖ + ‖B‖ with hs
  have hs0 : 0 ≤ s := by positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have hexpAB : exp (A + B) = exp ((n : ℝ)⁻¹ • (A + B)) ^ n := by
    rw [exp_pow_eq_exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      mul_inv_cancel₀ (ne_of_gt hnpos), one_smul]
  have hnormA : ‖(n : ℝ)⁻¹ • A‖ = (n : ℝ)⁻¹ * ‖A‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hninv]
  have hnormB : ‖(n : ℝ)⁻¹ • B‖ = (n : ℝ)⁻¹ * ‖B‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hninv]
  have hsn : ‖(n : ℝ)⁻¹ • A‖ + ‖(n : ℝ)⁻¹ • B‖ = (n : ℝ)⁻¹ * s := by
    rw [hnormA, hnormB, hs]; ring
  -- the uniform norm ceiling e^{s/n} on all three step factors
  set C := Real.exp ((n : ℝ)⁻¹ * s) with hC
  have hC1 : 1 ≤ C := Real.one_le_exp (mul_nonneg hninv hs0)
  have hfac : ‖exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)‖ ≤ C := by
    calc ‖exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)‖
        ≤ ‖exp ((n : ℝ)⁻¹ • A)‖ * ‖exp ((n : ℝ)⁻¹ • B)‖ := norm_mul_le _ _
      _ ≤ Real.exp ‖(n : ℝ)⁻¹ • A‖ * Real.exp ‖(n : ℝ)⁻¹ • B‖ :=
          mul_le_mul (norm_exp_le_exp_norm _) (norm_exp_le_exp_norm _)
            (norm_nonneg _) (Real.exp_pos _).le
      _ = C := by rw [← Real.exp_add, hsn]
  have hfacAB : ‖exp ((n : ℝ)⁻¹ • (A + B))‖ ≤ C := by
    calc ‖exp ((n : ℝ)⁻¹ • (A + B))‖
        ≤ Real.exp ‖(n : ℝ)⁻¹ • (A + B)‖ := norm_exp_le_exp_norm _
      _ ≤ C := by
          rw [hC]
          refine Real.exp_le_exp.mpr ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hninv]
          have : ‖A + B‖ ≤ s := norm_add_le _ _
          exact mul_le_mul_of_nonneg_left this hninv
  have hCn : C ^ n ≤ Real.exp s := by
    rw [hC, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    rw [show (n : ℝ) * ((n : ℝ)⁻¹ * s) = ((n : ℝ) * (n : ℝ)⁻¹) * s from by
      ring, mul_inv_cancel₀ (ne_of_gt hnpos), one_mul]
  have hstep := norm_exp_mul_exp_sub_exp_add_le
    ((n : ℝ)⁻¹ • A) ((n : ℝ)⁻¹ • B)
  rw [hsn, ← smul_add] at hstep
  have htel := norm_pow_sub_pow_le_of_norm_le hC1 hfac hfacAB n
  have hsle : (n : ℝ)⁻¹ * s ≤ s := by
    calc (n : ℝ)⁻¹ * s ≤ 1 * s := by
          gcongr
          rw [inv_le_one_iff₀]
          right; exact_mod_cast hn
      _ = s := one_mul s
  have hstep' : ‖exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)
        - exp ((n : ℝ)⁻¹ • (A + B))‖
      ≤ ((n : ℝ)⁻¹ * s) ^ 2 * (3 + s) * Real.exp s := by
    refine le_trans hstep ?_
    have h3le : 3 + (n : ℝ)⁻¹ * s ≤ 3 + s := by linarith
    have hele : Real.exp ((n : ℝ)⁻¹ * s) ≤ Real.exp s :=
      Real.exp_le_exp.mpr hsle
    have hsq : (0 : ℝ) ≤ ((n : ℝ)⁻¹ * s) ^ 2 := sq_nonneg _
    calc ((n : ℝ)⁻¹ * s) ^ 2 * (3 + (n : ℝ)⁻¹ * s)
          * Real.exp ((n : ℝ)⁻¹ * s)
        ≤ ((n : ℝ)⁻¹ * s) ^ 2 * (3 + s) * Real.exp ((n : ℝ)⁻¹ * s) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h3le hsq) (Real.exp_pos _).le
      _ ≤ ((n : ℝ)⁻¹ * s) ^ 2 * (3 + s) * Real.exp s := by
          refine mul_le_mul_of_nonneg_left hele ?_
          have : (0 : ℝ) ≤ 3 + s := by linarith
          positivity
  calc ‖(exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n - exp (A + B)‖
      = ‖(exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n
          - exp ((n : ℝ)⁻¹ • (A + B)) ^ n‖ := by rw [hexpAB]
    _ ≤ n * C ^ n * ‖exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)
          - exp ((n : ℝ)⁻¹ • (A + B))‖ := htel
    _ ≤ n * Real.exp s * (((n : ℝ)⁻¹ * s) ^ 2 * (3 + s) * Real.exp s) := by
        have hcoef : (n : ℝ) * C ^ n ≤ n * Real.exp s :=
          mul_le_mul_of_nonneg_left hCn hnpos.le
        refine mul_le_mul hcoef hstep' (norm_nonneg _) ?_
        positivity
    _ = ((n : ℝ) * (n : ℝ)⁻¹)
          * ((n : ℝ)⁻¹ * (s ^ 2 * (3 + s) * (Real.exp s * Real.exp s))) := by
        ring
    _ = (n : ℝ)⁻¹ * (s ^ 2 * (3 + s) * Real.exp (2 * s)) := by
        rw [mul_inv_cancel₀ (ne_of_gt hnpos), one_mul, ← Real.exp_add,
          ← two_mul]

/-- **The Lie–Trotter product formula in a Banach algebra**: for any `A, B`,
`(exp (A/n) · exp (B/n))ⁿ → exp (A + B)`. -/
theorem trotter_product (A B : 𝔸) :
    Filter.Tendsto
      (fun n : ℕ => (exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n)
      Filter.atTop (nhds (exp (A + B))) := by
  set s := ‖A‖ + ‖B‖ with hs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * (s ^ 2 * (3 + s) * Real.exp (2 * s)))
      Filter.atTop (nhds 0) := by
    have := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
      (s ^ 2 * (3 + s) * Real.exp (2 * s))
    simpa using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact norm_trotter_sub_le A B n hn

end LieTrotter
