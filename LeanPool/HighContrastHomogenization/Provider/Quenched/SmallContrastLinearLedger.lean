/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAdaptiveDescent
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastDescentStageArithmetic

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastLinearLedger

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The linear level schedule at the corrected source model

-(3), first half.  At the corrected source model of
the strengthened free-threshold estimate — the Π-carrying channel with ABSOLUTE decay at
the anchor scale (`S1·3^{−bA·m}`), a lag-only channel (`S0·3^{−b0·lag}`,
law-free at the instantiation), and an absolute channel at the line scale
(`S2·3^{−b2·n}`) — the squaring level schedule `linLam := echoTower (128A²) d0` is
VALID with explicitly defined lags, memories, window counts, and pads:

* the `S1`/`S2` burn-ins are paid ONCE, in the start `linR 0`, and
  propagate through the pad (`linR_abs_cond`) — no per-round `log₃ S1`
  (contrast the lag floor of the lag-only model);
* the lag floor carries only `log₃ S0` and the level part;
* `linear_ledger_descent` instantiates the proved
  `the descent induction theorem` (the corresponding clause): `F n ≤ linLam j` from `linR j` on.

The geometric conversion to `hdecay` shape is the companion module.
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-- The squaring level schedule. -/
@[expose]
def linLam (A d0 : ℝ) : ℕ → ℝ := echoTower (128 * A ^ 2) d0

/-- The window count of round `j`. -/
@[expose]
def linII (A lamj : ℝ) : ℕ :=
  ⌈Real.logb 3 (1 / (16 * A ^ 2 * lamj)) /
    Real.logb 3 ((2 * A + 1) / (2 * A))⌉₊

/-- The memory margin of round `j`. -/
@[expose]
def linT (alpha d0 lamj : ℝ) : ℕ :=
  ⌈Real.logb 3 (d0 / (2 * lamj ^ 2)) / alpha⌉₊

/-- The round lag: only the lag-only channel's logarithm and the level. -/
@[expose]
def linL (A b0 S0 lamj : ℝ) : ℕ :=
  ⌈Real.logb 3 (S0 / (2 * A * lamj ^ 2)) / b0⌉₊

/-- The absolute-channel pad: keeps the one-time burn-ins propagating. -/
@[expose]
def linPad (A bA b2 lamj : ℝ) : ℕ :=
  ⌈2 * Real.logb 3 (1 / (128 * A ^ 2 * lamj)) / bA⌉₊ +
    ⌈2 * Real.logb 3 (1 / (128 * A ^ 2 * lamj)) / b2⌉₊

/-- The round starts: the absolute burn-ins are paid once, at the start. -/
@[expose]
def linR (ns cA : ℕ) (A alpha b0 bA b2 S0 S1 S2 d0 : ℝ) : ℕ → ℕ
  | 0 => ns + ⌈Real.logb 3 (S1 / (A * d0 ^ 2)) / bA⌉₊ +
      ⌈Real.logb 3 (S2 / (A * d0 ^ 2)) / b2⌉₊
  | j + 1 => linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j +
      (max (linL A b0 S0 (linLam A d0 j)) (linT alpha d0 (linLam A d0 j)) +
        linII A (linLam A d0 j) * (cA + 1) +
        linPad A bA b2 (linLam A d0 j) + 1)

/-! ## Level facts -/

theorem linLam_pos {A d0 : ℝ} (hA : 1 ≤ A) (hd0 : 0 < d0) (j : ℕ) :
    0 < linLam A d0 j :=
  echoTower_pos (by nlinarith only [hA]) hd0 j

theorem linLam_le_floor {A d0 : ℝ} (hA : 1 ≤ A) (hd0 : 0 < d0)
    (hgs : 128 * A ^ 2 * d0 ≤ 1) (j : ℕ) : linLam A d0 j ≤ d0 :=
  echoTower_le_floor (by nlinarith only [hA]) hd0 hgs j

theorem linLam_succ (A d0 : ℝ) (j : ℕ) :
    linLam A d0 (j + 1) = 128 * A ^ 2 * linLam A d0 j ^ 2 := rfl

theorem linR_zero (ns cA : ℕ) (A alpha b0 bA b2 S0 S1 S2 d0 : ℝ) :
    linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 =
      ns + ⌈Real.logb 3 (S1 / (A * d0 ^ 2)) / bA⌉₊ +
        ⌈Real.logb 3 (S2 / (A * d0 ^ 2)) / b2⌉₊ := rfl

theorem linR_succ (ns cA : ℕ) (A alpha b0 bA b2 S0 S1 S2 d0 : ℝ) (j : ℕ) :
    linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 (j + 1) =
      linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j +
        (max (linL A b0 S0 (linLam A d0 j)) (linT alpha d0 (linLam A d0 j)) +
          linII A (linLam A d0 j) * (cA + 1) +
          linPad A bA b2 (linLam A d0 j) + 1) := rfl

theorem ns_le_linR (ns cA : ℕ) (A alpha b0 bA b2 S0 S1 S2 d0 : ℝ) :
    ∀ j, ns ≤ linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j := by
  intro j
  induction j with
  | zero => rw [linR_zero]; omega
  | succ j ihj => rw [linR_succ]; omega

/-! ## The per-round conditions -/

/-- The window count does its job. -/
theorem linII_spec {A lamj : ℝ} (hA : 1 ≤ A) (hlam : 0 < lamj) :
    (2 * A / (2 * A + 1)) ^ linII A lamj ≤ 16 * A ^ 2 * lamj := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
  have hrate : 0 < Real.logb 3 ((2 * A + 1) / (2 * A)) := by
    have h1 : (1 : ℝ) < (2 * A + 1) / (2 * A) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith only []
    exact Real.logb_pos (by norm_num) h1
  have htarget : (0 : ℝ) < 16 * A ^ 2 * lamj := by positivity
  have hkey := geometric_le_of_logb (C := 1)
    (target := 16 * A ^ 2 * lamj)
    (rate := Real.logb 3 ((2 * A + 1) / (2 * A))) one_pos htarget hrate
    (L := (linII A lamj : ℝ))
    (by
      have h2 : Real.logb 3 (1 / (16 * A ^ 2 * lamj)) /
          Real.logb 3 ((2 * A + 1) / (2 * A)) ≤ (linII A lamj : ℝ) := by
        rw [linII]
        exact Nat.le_ceil _
      have h3 : Real.logb 3 (1 / (16 * A ^ 2 * lamj)) =
          Real.logb 3 (1 / (16 * A ^ 2 * lamj)) := rfl
      exact h2)
  have hfrac : (0 : ℝ) < (2 * A + 1) / (2 * A) := by positivity
  have hpow : (2 * A / (2 * A + 1)) ^ linII A lamj =
      (3 : ℝ) ^ (-(Real.logb 3 ((2 * A + 1) / (2 * A)) *
        (linII A lamj : ℝ))) := by
    have hinv : 2 * A / (2 * A + 1) =
        (3 : ℝ) ^ (-Real.logb 3 ((2 * A + 1) / (2 * A))) := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
        Real.rpow_logb (by norm_num) (by norm_num) hfrac]
      rw [inv_div]
    rw [hinv, ← Real.rpow_natCast
      ((3 : ℝ) ^ (-Real.logb 3 ((2 * A + 1) / (2 * A)))) (linII A lamj),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  calc (2 * A / (2 * A + 1)) ^ linII A lamj =
      (3 : ℝ) ^ (-(Real.logb 3 ((2 * A + 1) / (2 * A)) *
        (linII A lamj : ℝ))) := hpow
    _ = 1 * (3 : ℝ) ^ (-(Real.logb 3 ((2 * A + 1) / (2 * A)) *
        (linII A lamj : ℝ))) := (one_mul _).symm
    _ ≤ 16 * A ^ 2 * lamj := hkey

/-- The memory margin does its job. -/
theorem linT_spec {A alpha d0 lamj : ℝ} (halpha : 0 < alpha)
    (hd0 : 0 < d0) (hlam : 0 < lamj) (hA : 1 ≤ A) :
    8 * A ^ 2 * ((3 : ℝ) ^ (-alpha)) ^ linT alpha d0 lamj * d0 ≤
      16 * A ^ 2 * lamj ^ 2 := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
  have htarget : (0 : ℝ) < 2 * lamj ^ 2 := by positivity
  have hkey := geometric_le_of_logb (C := d0) (target := 2 * lamj ^ 2)
    (rate := alpha) hd0 htarget halpha (L := (linT alpha d0 lamj : ℝ))
    (by rw [linT]; exact Nat.le_ceil _)
  have hpow : ((3 : ℝ) ^ (-alpha)) ^ linT alpha d0 lamj =
      (3 : ℝ) ^ (-(alpha * (linT alpha d0 lamj : ℝ))) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-alpha)) (linT alpha d0 lamj),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have h1 : d0 * ((3 : ℝ) ^ (-alpha)) ^ linT alpha d0 lamj ≤
      2 * lamj ^ 2 := by
    rw [hpow]
    exact hkey
  have h2 := mul_le_mul_of_nonneg_left h1
    (by positivity : (0 : ℝ) ≤ 8 * A ^ 2)
  nlinarith only [h2]

/-- The lag does its job on the lag-only channel. -/
theorem linL_spec {A b0 S0 lamj : ℝ} (hb0 : 0 < b0) (hS0 : 0 < S0)
    (hlam : 0 < lamj) (hA : 1 ≤ A) :
    S0 * (3 : ℝ) ^ (-(b0 * (linL A b0 S0 lamj : ℝ))) ≤
      2 * A * lamj ^ 2 := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
  have htarget : (0 : ℝ) < 2 * A * lamj ^ 2 := by positivity
  exact geometric_le_of_logb hS0 htarget hb0
    (by rw [linL]; exact Nat.le_ceil _)

/-- The pad's rpow value dominates the level-ratio square. -/
theorem linPad_rpow_le {A bA b2 lamj b : ℝ} (hA : 1 ≤ A) (hlam : 0 < lamj)
    (hb : 0 < b)
    (hpadb : 2 * Real.logb 3 (1 / (128 * A ^ 2 * lamj)) / b ≤
      (linPad A bA b2 lamj : ℝ)) :
    (3 : ℝ) ^ (-(b * (linPad A bA b2 lamj : ℝ))) ≤
      (128 * A ^ 2 * lamj) ^ 2 := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
  have hy : (0 : ℝ) < (128 * A ^ 2 * lamj) ^ 2 := by positivity
  have hlog : Real.logb 3 ((1 / (128 * A ^ 2 * lamj)) ^ 2) ≤
      b * (linPad A bA b2 lamj : ℝ) := by
    rw [Real.logb_pow]
    push_cast
    have h1 := mul_le_mul_of_nonneg_left hpadb hb.le
    calc (2 : ℝ) * Real.logb 3 (1 / (128 * A ^ 2 * lamj)) =
        b * (2 * Real.logb 3 (1 / (128 * A ^ 2 * lamj)) / b) := by
          field_simp
      _ ≤ b * (linPad A bA b2 lamj : ℝ) := h1
  have hstep1 : (3 : ℝ) ^ (-(b * (linPad A bA b2 lamj : ℝ))) ≤
      (3 : ℝ) ^ (-(Real.logb 3 ((1 / (128 * A ^ 2 * lamj)) ^ 2))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by linarith only [hlog])
  have hstep2 : (3 : ℝ) ^
      (-(Real.logb 3 ((1 / (128 * A ^ 2 * lamj)) ^ 2))) =
      (128 * A ^ 2 * lamj) ^ 2 := by
    rw [show (1 / (128 * A ^ 2 * lamj)) ^ 2 =
      ((128 * A ^ 2 * lamj) ^ 2)⁻¹ by field_simp]
    rw [Real.logb_inv, neg_neg]
    exact Real.rpow_logb (by norm_num) (by norm_num) hy
  rw [hstep2] at hstep1
  exact hstep1

/-! ## The absolute-channel conditions: paid once, propagated by the pad -/

theorem linR_abs_cond {ns cA : ℕ} {A alpha b0 bA b2 S0 S1 S2 d0 : ℝ}
    (hA : 1 ≤ A) (hd0 : 0 < d0)
    (hS1 : 1 ≤ S1) (hS2 : 1 ≤ S2) (hbA : 0 < bA) (hb2 : 0 < b2) :
    ∀ j, S1 * (3 : ℝ) ^ (-(bA *
        (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))) ≤
        A * linLam A d0 j ^ 2 ∧
      S2 * (3 : ℝ) ^ (-(b2 *
        (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))) ≤
        A * linLam A d0 j ^ 2 := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
  intro j
  induction j with
  | zero =>
      have hlam0 : linLam A d0 0 = d0 := rfl
      constructor
      · have htarget : (0 : ℝ) < A * d0 ^ 2 := by positivity
        have hstart : Real.logb 3 (S1 / (A * d0 ^ 2)) / bA ≤
            (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℝ) := by
          rw [linR_zero]
          push_cast
          have h1 := Nat.le_ceil (Real.logb 3 (S1 / (A * d0 ^ 2)) / bA)
          have h2 : (0 : ℝ) ≤ (ns : ℝ) := Nat.cast_nonneg ns
          have h3 : (0 : ℝ) ≤
              ((⌈Real.logb 3 (S2 / (A * d0 ^ 2)) / b2⌉₊ : ℕ) : ℝ) :=
            Nat.cast_nonneg _
          linarith only [h1, h2, h3]
        have := geometric_le_of_logb (by linarith only [hS1]) htarget hbA
          hstart
        rw [hlam0]
        exact this
      · have htarget : (0 : ℝ) < A * d0 ^ 2 := by positivity
        have hstart : Real.logb 3 (S2 / (A * d0 ^ 2)) / b2 ≤
            (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℝ) := by
          rw [linR_zero]
          push_cast
          have h1 := Nat.le_ceil (Real.logb 3 (S2 / (A * d0 ^ 2)) / b2)
          have h2 : (0 : ℝ) ≤ (ns : ℝ) := Nat.cast_nonneg ns
          have h3 : (0 : ℝ) ≤
              ((⌈Real.logb 3 (S1 / (A * d0 ^ 2)) / bA⌉₊ : ℕ) : ℝ) :=
            Nat.cast_nonneg _
          linarith only [h1, h2, h3]
        have := geometric_le_of_logb (by linarith only [hS2]) htarget hb2
          hstart
        rw [hlam0]
        exact this
  | succ j ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hlamj := linLam_pos hA hd0 j
      have hpadA : 2 * Real.logb 3 (1 / (128 * A ^ 2 * linLam A d0 j)) / bA ≤
          (linPad A bA b2 (linLam A d0 j) : ℝ) := by
        rw [linPad]
        push_cast
        have h1 := Nat.le_ceil
          (2 * Real.logb 3 (1 / (128 * A ^ 2 * linLam A d0 j)) / bA)
        have h2 : (0 : ℝ) ≤ ((⌈2 * Real.logb 3
            (1 / (128 * A ^ 2 * linLam A d0 j)) / b2⌉₊ : ℕ) : ℝ) :=
          Nat.cast_nonneg _
        linarith only [h1, h2]
      have hpadB : 2 * Real.logb 3 (1 / (128 * A ^ 2 * linLam A d0 j)) / b2 ≤
          (linPad A bA b2 (linLam A d0 j) : ℝ) := by
        rw [linPad]
        push_cast
        have h1 := Nat.le_ceil
          (2 * Real.logb 3 (1 / (128 * A ^ 2 * linLam A d0 j)) / b2)
        have h2 : (0 : ℝ) ≤ ((⌈2 * Real.logb 3
            (1 / (128 * A ^ 2 * linLam A d0 j)) / bA⌉₊ : ℕ) : ℝ) :=
          Nat.cast_nonneg _
        linarith only [h1, h2]
      have hstep : (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ) +
          (linPad A bA b2 (linLam A d0 j) : ℝ) ≤
          (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 (j + 1) : ℝ) := by
        rw [linR_succ]
        push_cast
        have h1 : (0 : ℝ) ≤ ((max (linL A b0 S0 (linLam A d0 j))
            (linT alpha d0 (linLam A d0 j)) : ℕ) : ℝ) := Nat.cast_nonneg _
        have h2 : (0 : ℝ) ≤
            ((linII A (linLam A d0 j) * (cA + 1) : ℕ) : ℝ) :=
          Nat.cast_nonneg _
        push_cast at h1 h2
        linarith only [h1, h2]
      have hcommon : ∀ b : ℝ, 0 < b →
          2 * Real.logb 3 (1 / (128 * A ^ 2 * linLam A d0 j)) / b ≤
            (linPad A bA b2 (linLam A d0 j) : ℝ) →
          ∀ S : ℝ, 1 ≤ S →
          S * (3 : ℝ) ^ (-(b *
            (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))) ≤
            A * linLam A d0 j ^ 2 →
          S * (3 : ℝ) ^ (-(b *
            (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 (j + 1) : ℝ))) ≤
            A * linLam A d0 (j + 1) ^ 2 := by
        intro b hb hpadb S hS ihS
        have hdecomp : S * (3 : ℝ) ^ (-(b *
            (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 (j + 1) : ℝ))) ≤
            S * (3 : ℝ) ^ (-(b *
              (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))) *
              (3 : ℝ) ^ (-(b * (linPad A bA b2 (linLam A d0 j) : ℝ))) := by
          rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
          refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hS])
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have h4 := mul_le_mul_of_nonneg_left hstep hb.le
          nlinarith only [h4, hb]
        have hpadval := linPad_rpow_le (b2 := b2) (bA := bA) hA hlamj hb hpadb
        have hprod : S * (3 : ℝ) ^ (-(b *
            (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))) *
            (3 : ℝ) ^ (-(b * (linPad A bA b2 (linLam A d0 j) : ℝ))) ≤
            A * linLam A d0 j ^ 2 * (128 * A ^ 2 * linLam A d0 j) ^ 2 :=
          mul_le_mul ihS hpadval
            (Real.rpow_pos_of_pos (by norm_num) _).le (by positivity)
        calc S * (3 : ℝ) ^ (-(b *
            (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 (j + 1) : ℝ))) ≤
            S * (3 : ℝ) ^ (-(b *
              (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))) *
              (3 : ℝ) ^ (-(b * (linPad A bA b2 (linLam A d0 j) : ℝ))) :=
              hdecomp
          _ ≤ A * linLam A d0 j ^ 2 * (128 * A ^ 2 * linLam A d0 j) ^ 2 :=
              hprod
          _ = A * (128 * A ^ 2 * linLam A d0 j ^ 2) ^ 2 := by ring
          _ = A * linLam A d0 (j + 1) ^ 2 := by rw [linLam_succ]
      exact ⟨hcommon bA hbA hpadA S1 hS1 ih1, hcommon b2 hb2 hpadB S2 hS2 ih2⟩

/-- **The linear level schedule is valid**: the descent holds at it. -/
theorem linear_ledger_descent {A alpha d0 S0 S1 S2 b0 bA b2 : ℝ}
    {F : ℕ → ℝ} {src : ℕ → ℕ → ℝ} {ns cA : ℕ}
    (hA : 1 ≤ A) (halpha : 0 < alpha)
    (hcA : 24 * A ≤ (3 : ℝ) ^ (alpha * (cA : ℝ)))
    (hd0 : 0 < d0) (hgs : 128 * A ^ 2 * d0 ≤ 1)
    (hd0small : 9 * A * d0 ≤ 1)
    (hS0 : 1 ≤ S0) (hS1 : 1 ≤ S1) (hS2 : 1 ≤ S2)
    (hb0 : 0 < b0) (hbA : 0 < bA) (hb2 : 0 < b2)
    (hFnn : ∀ n, 0 ≤ F n)
    (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p)
    (hFd0 : ∀ n, F n ≤ d0)
    (hfam : ∀ n m : ℕ, ns ≤ m → m ≤ n →
      F n ≤ A * iterationDropSum ((3 : ℝ) ^ (-alpha)) F n +
        A * F m ^ 2 + src n m)
    (hsrc : ∀ n m : ℕ, ns ≤ m → m ≤ n →
      src n m ≤ S1 * (3 : ℝ) ^ (-(bA * (m : ℝ))) +
        S0 * (3 : ℝ) ^ (-(b0 * ((n - m : ℕ) : ℝ))) +
        S2 * (3 : ℝ) ^ (-(b2 * (n : ℝ)))) :
    ∀ j, ∀ n : ℕ, linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j ≤ n →
      F n ≤ linLam A d0 j := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
  have habs := linR_abs_cond (ns := ns) (cA := cA) (alpha := alpha)
    (b0 := b0) (S0 := S0) hA hd0 hS1 hS2 hbA hb2
  have hrns := ns_le_linR ns cA A alpha b0 bA b2 S0 S1 S2 d0
  refine adaptive_descent_ledger (src := src) (lam := linLam A d0)
    (sE := fun j =>
      S1 * (3 : ℝ) ^ (-(bA *
        (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))) +
      S0 * (3 : ℝ) ^ (-(b0 * (linL A b0 S0 (linLam A d0 j) : ℝ))) +
      S2 * (3 : ℝ) ^ (-(b2 *
        (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))))
    (r := linR ns cA A alpha b0 bA b2 S0 S1 S2 d0)
    (L := fun j => linL A b0 S0 (linLam A d0 j))
    (T := fun j => linT alpha d0 (linLam A d0 j))
    (ii := fun j => linII A (linLam A d0 j))
    hA halpha hd0.le hcA hFnn hFmono hFd0 hfam
    (fun j => (linLam_pos hA hd0 j).le)
    (fun j => by
      have h1 := linLam_le_floor hA hd0 hgs j
      nlinarith only [h1, hd0small, hA0, linLam_pos hA hd0 j])
    (le_refl d0)
    (hrns 0)
    ?_ ?_ ?_ ?_
  · -- hsrcL
    intro j k hk
    have hrj := hrns j
    have h1 := hsrc
      (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j + k)
      (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j + k -
        linL A b0 S0 (linLam A d0 j))
      (by omega) (by omega)
    have hlag : ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j + k) -
        (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j + k -
          linL A b0 S0 (linLam A d0 j)) : ℕ) =
        linL A b0 S0 (linLam A d0 j) := by omega
    rw [hlag] at h1
    have hanchor : ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℕ) : ℝ) ≤
        ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j + k -
          linL A b0 S0 (linLam A d0 j) : ℕ) : ℝ) := by
      have h2 : linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j ≤
          linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j + k -
            linL A b0 S0 (linLam A d0 j) := by omega
      exact_mod_cast h2
    have hline : ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℕ) : ℝ) ≤
        ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j + k : ℕ) : ℝ) := by
      have h2 : linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j ≤
          linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j + k := by omega
      exact_mod_cast h2
    have hm1 : S1 * (3 : ℝ) ^ (-(bA *
        ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j + k -
          linL A b0 S0 (linLam A d0 j) : ℕ) : ℝ))) ≤
        S1 * (3 : ℝ) ^ (-(bA *
          (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hS1])
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      nlinarith only [hanchor, hbA]
    have hm2 : S2 * (3 : ℝ) ^ (-(b2 *
        ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j + k : ℕ) : ℝ))) ≤
        S2 * (3 : ℝ) ^ (-(b2 *
          (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hS2])
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      nlinarith only [hline, hb2]
    linarith only [h1, hm1, hm2]
  · -- hsE0
    intro j
    have h1 : (0 : ℝ) ≤ S1 * (3 : ℝ) ^ (-(bA *
        (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))) := by
      have hS1' : (0 : ℝ) ≤ S1 := by linarith only [hS1]
      positivity
    have h2 : (0 : ℝ) ≤ S0 * (3 : ℝ) ^
        (-(b0 * (linL A b0 S0 (linLam A d0 j) : ℝ))) := by
      have hS0' : (0 : ℝ) ≤ S0 := by linarith only [hS0]
      positivity
    have h3 : (0 : ℝ) ≤ S2 * (3 : ℝ) ^ (-(b2 *
        (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))) := by
      have hS2' : (0 : ℝ) ≤ S2 := by linarith only [hS2]
      positivity
    linarith only [h1, h2, h3]
  · -- hstep
    intro j
    have hlamj := linLam_pos hA hd0 j
    have hii := linII_spec hA hlamj
    have hT := linT_spec (A := A) halpha hd0 hlamj hA
    have hL := linL_spec (A := A) hb0 (by linarith only [hS0]) hlamj hA
    obtain ⟨hs1, hs2⟩ := habs j
    have hpiece1 : linLam A d0 j *
        (2 * A / (2 * A + 1)) ^ linII A (linLam A d0 j) ≤
        16 * A ^ 2 * linLam A d0 j ^ 2 := by
      have h4 := mul_le_mul_of_nonneg_left hii hlamj.le
      nlinarith only [h4, hlamj]
    have hpiece3 : 8 * A * (S0 * (3 : ℝ) ^
        (-(b0 * (linL A b0 S0 (linLam A d0 j) : ℝ)))) ≤
        16 * A ^ 2 * linLam A d0 j ^ 2 := by
      nlinarith only [hL, hA0]
    have hpiece4 : 8 * A * (S1 * (3 : ℝ) ^ (-(bA *
        (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ)))) ≤
        8 * A ^ 2 * linLam A d0 j ^ 2 := by
      nlinarith only [hs1, hA0]
    have hpiece5 : 8 * A * (S2 * (3 : ℝ) ^ (-(b2 *
        (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ)))) ≤
        8 * A ^ 2 * linLam A d0 j ^ 2 := by
      nlinarith only [hs2, hA0]
    have hpiece2 : 8 * A * (A *
        ((3 : ℝ) ^ (-alpha)) ^ linT alpha d0 (linLam A d0 j) * d0) ≤
        16 * A ^ 2 * linLam A d0 j ^ 2 := by
      have h4 : 8 * A * (A *
          ((3 : ℝ) ^ (-alpha)) ^ linT alpha d0 (linLam A d0 j) * d0) =
          8 * A ^ 2 *
            ((3 : ℝ) ^ (-alpha)) ^ linT alpha d0 (linLam A d0 j) * d0 := by
        ring
      rw [h4]
      exact hT
    have hdist : 8 * A * (A *
        ((3 : ℝ) ^ (-alpha)) ^ linT alpha d0 (linLam A d0 j) * d0 +
        A * linLam A d0 j ^ 2 +
        (S1 * (3 : ℝ) ^ (-(bA *
          (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))) +
          S0 * (3 : ℝ) ^ (-(b0 * (linL A b0 S0 (linLam A d0 j) : ℝ))) +
          S2 * (3 : ℝ) ^ (-(b2 *
            (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))))) =
        8 * A * (A *
          ((3 : ℝ) ^ (-alpha)) ^ linT alpha d0 (linLam A d0 j) * d0) +
        8 * A ^ 2 * linLam A d0 j ^ 2 +
        8 * A * (S1 * (3 : ℝ) ^ (-(bA *
          (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ)))) +
        8 * A * (S0 * (3 : ℝ) ^
          (-(b0 * (linL A b0 S0 (linLam A d0 j) : ℝ)))) +
        8 * A * (S2 * (3 : ℝ) ^ (-(b2 *
          (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ)))) := by
      ring
    have hgoal : linLam A d0 j *
        (2 * A / (2 * A + 1)) ^ linII A (linLam A d0 j) +
        8 * A * (A *
          ((3 : ℝ) ^ (-alpha)) ^ linT alpha d0 (linLam A d0 j) * d0 +
          A * linLam A d0 j ^ 2 +
          (S1 * (3 : ℝ) ^ (-(bA *
            (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))) +
            S0 * (3 : ℝ) ^ (-(b0 * (linL A b0 S0 (linLam A d0 j) : ℝ))) +
            S2 * (3 : ℝ) ^ (-(b2 *
              (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))))) ≤
        128 * A ^ 2 * linLam A d0 j ^ 2 := by
      rw [hdist]
      have hX : (0 : ℝ) ≤ A ^ 2 * linLam A d0 j ^ 2 := by positivity
      linarith only [hpiece1, hpiece2, hpiece3, hpiece4, hpiece5, hX]
    calc linLam A d0 j *
        (2 * A / (2 * A + 1)) ^ linII A (linLam A d0 j) +
        8 * A * (A *
          ((3 : ℝ) ^ (-alpha)) ^ linT alpha d0 (linLam A d0 j) * d0 +
          A * linLam A d0 j ^ 2 +
          (S1 * (3 : ℝ) ^ (-(bA *
            (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))) +
            S0 * (3 : ℝ) ^ (-(b0 * (linL A b0 S0 (linLam A d0 j) : ℝ))) +
            S2 * (3 : ℝ) ^ (-(b2 *
              (linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 j : ℝ))))) ≤
        128 * A ^ 2 * linLam A d0 j ^ 2 := hgoal
      _ = linLam A d0 (j + 1) := (linLam_succ A d0 j).symm
  · -- hspace
    intro j
    rw [linR_succ]
    omega

end

end HCPolySupport.HighContrast.Quenched
