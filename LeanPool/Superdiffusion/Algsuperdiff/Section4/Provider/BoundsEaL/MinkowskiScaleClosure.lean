/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.ScaleSumOrdering

/-!
# MinkowskiScaleClosure

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Minkowski-ordered scale sum: the three per-scale shapes, closed

Everything below is abstract-real arithmetic: no model, no measure, no carrier occurs.

## What is here

`MinkowskiTransport.lean` leaves the anchor's right-hand side as the single
scalar

```
𝔠_{2s} ∑_{l ≥ 0} 3^{-sl} G_l ,
```

`G_l` the per-cube `L^{p/2}` moment at the descendant scale `n − l`.  The
proved per-cube moment layer produces `G_l` in exactly three shapes:

* a uniform part `K p γ s^{-2}` (Step 3's first and third summands: their
  majorants do not see the descendant scale -- this is why the manuscript calls
  them straightforward);
* a linear-times-exponential part `K p γ (m−j) 3^{2γ(m−j)}` (Step 3's second
  summand at the value slot, `m − j = (m−n)+l`); and
* a flat exponential part `K p γ 3^{2γ(m−j)}` (the additive `1` in the value
  bullet, and the deterministic `σ` ratio leg).

This module evaluates all three against the geometric weight, in the `ℓ¹`
ordering:

```
𝔠_{2s} ∑_l 3^{-sl} · γ A                     ≤ 2 γ A                (uniform)
𝔠_{2s} ∑_l 3^{-sl} · γ(D+l) 3^{2γ(D+l)}      ≤ γ(36 D + 144/s)      (ScaleSumOrdering)
𝔠_{2s} ∑_l 3^{-sl} · γ 3^{2γ(D+l)}           ≤ 36 γ/s               (flat)
```

## References

* ABK26, `l.bounds.mathcal.E.aL`, Step 5.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

noncomputable section

/-! ## 1. The geometric ratio and the termwise domination -/

/-- `∑_{l ≥ 0} 3^{-sl} = (1 - 3^{-s})^{-1}`. -/
theorem tsum_rpow_three_neg_mul_nat {s : ℝ} (hs : 0 < s) :
    ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) = (1 - (3 : ℝ) ^ (-s))⁻¹ := by
  have h30 : (0 : ℝ) < 3 := by norm_num
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-s) := Real.rpow_pos_of_pos h30 _
  have hr1 : (3 : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])
  have hrpow : ∀ l : ℕ, ((3 : ℝ) ^ (-s)) ^ l = (3 : ℝ) ^ (-(s * (l : ℝ))) := by
    intro l
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-s)) l, ← Real.rpow_mul h30.le]
    congr 1
    ring
  rw [← tsum_congr hrpow]
  exact tsum_geometric_of_lt_one hr0.le hr1

/-- **The uniform shape.**  `𝔠_{2s} ∑_l 3^{-sl} ≤ 2`, the exact cancellation
`𝔠_{2s}/𝔠_s = 1 + 3^{-s} ≤ 2`. -/
theorem geometricTwo_mul_tsum_le_two {s : ℝ} (hs : 0 < s) :
    (1 - (3 : ℝ) ^ (-(2 * s))) * ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) ≤ 2 := by
  have h30 : (0 : ℝ) < 3 := by norm_num
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-s) := Real.rpow_pos_of_pos h30 _
  have hr1 : (3 : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])
  have hw : (0 : ℝ) < 1 - (3 : ℝ) ^ (-s) := by linarith only [hr1]
  have hsq : (3 : ℝ) ^ (-(2 * s)) = (3 : ℝ) ^ (-s) * (3 : ℝ) ^ (-s) := by
    rw [← Real.rpow_add h30]
    congr 1
    ring
  rw [tsum_rpow_three_neg_mul_nat hs, hsq]
  have hfac : 1 - (3 : ℝ) ^ (-s) * (3 : ℝ) ^ (-s) =
      (1 + (3 : ℝ) ^ (-s)) * (1 - (3 : ℝ) ^ (-s)) := by ring
  rw [hfac, mul_assoc, mul_inv_cancel₀ (ne_of_gt hw), mul_one]
  linarith only [hr1]

/-- The termwise domination shared by the linear and the flat shape:
`3^{-sl} 3^{2γ(D+l)} ≤ 9 · 3^{-(s/2)l}` under `4γ ≤ s` and `γD ≤ 1`. -/
private theorem termDomination {s gam D : ℝ} (hs : 0 < s)
    (h4gam : 4 * gam ≤ s) (hgamD : gam * D ≤ 1) (l : ℕ) :
    (3 : ℝ) ^ (-(s * (l : ℝ))) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) ≤
      9 * (3 : ℝ) ^ (-(s / 2) * (l : ℝ)) := by
  have h30 : (0 : ℝ) < 3 := by norm_num
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
  have hexp : -(s * (l : ℝ)) + 2 * gam * (D + (l : ℝ)) ≤ 2 + -(s / 2) * (l : ℝ) := by
    have hDpart : 2 * (gam * D) ≤ 2 := by linarith only [hgamD]
    have hlpart : 2 * gam * (l : ℝ) ≤ s / 2 * (l : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith only [h4gam]) hl0
    have hexpand : 2 * gam * (D + (l : ℝ)) = 2 * (gam * D) + 2 * gam * (l : ℝ) := by ring
    have hsl : (0 : ℝ) ≤ s * (l : ℝ) := mul_nonneg hs.le hl0
    linarith only [hDpart, hlpart, hexpand, hsl]
  have hcombine : (3 : ℝ) ^ (-(s * (l : ℝ))) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) =
      (3 : ℝ) ^ (-(s * (l : ℝ)) + 2 * gam * (D + (l : ℝ))) := (Real.rpow_add h30 _ _).symm
  have hsplit : (3 : ℝ) ^ (2 + -(s / 2) * (l : ℝ)) = 9 * (3 : ℝ) ^ (-(s / 2) * (l : ℝ)) := by
    rw [Real.rpow_add h30]
    norm_num
  rw [hcombine, ← hsplit]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-! ## 2. The three shapes -/

/-- Summability of the flat shape. -/
theorem summable_flatScaleTerm {s gam D : ℝ} (hs : 0 < s) (hgam : 0 ≤ gam)
    (h4gam : 4 * gam ≤ s) (hgamD : gam * D ≤ 1) :
    Summable fun l : ℕ =>
      (3 : ℝ) ^ (-(s * (l : ℝ))) * (gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) := by
  have h30 : (0 : ℝ) < 3 := by norm_num
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-(s / 2)) := Real.rpow_pos_of_pos h30 _
  have hr1 : (3 : ℝ) ^ (-(s / 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])
  have hrpow : ∀ l : ℕ, ((3 : ℝ) ^ (-(s / 2))) ^ l = (3 : ℝ) ^ (-(s / 2) * (l : ℝ)) := by
    intro l
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(s / 2))) l, ← Real.rpow_mul h30.le]
  have hgeo : Summable fun l : ℕ => (3 : ℝ) ^ (-(s / 2) * (l : ℝ)) :=
    (summable_geometric_of_lt_one hr0.le hr1).congr hrpow
  refine Summable.of_nonneg_of_le (fun l => ?_) (fun l => ?_) (hgeo.mul_left (9 * gam))
  · exact mul_nonneg (Real.rpow_nonneg h30.le _)
      (mul_nonneg hgam (Real.rpow_nonneg h30.le _))
  · have h := termDomination hs h4gam hgamD l
    have hmul := mul_le_mul_of_nonneg_left h hgam
    have hid1 : (3 : ℝ) ^ (-(s * (l : ℝ))) * (gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) =
        gam * ((3 : ℝ) ^ (-(s * (l : ℝ))) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) := by ring
    have hid2 : gam * (9 * (3 : ℝ) ^ (-(s / 2) * (l : ℝ))) =
        9 * gam * (3 : ℝ) ^ (-(s / 2) * (l : ℝ)) := by ring
    linarith only [hmul, hid1, hid2]

/-- **The flat shape.**  `𝔠_{2s} ∑_l 3^{-sl} γ 3^{2γ(D+l)} ≤ 36 γ/s`. -/
theorem flatScaleSum_le {s gam D : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hgam : 0 ≤ gam)
    (h4gam : 4 * gam ≤ s) (hgamD : gam * D ≤ 1) :
    (1 - (3 : ℝ) ^ (-(2 * s))) *
        ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
          (gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) ≤ gam * (36 / s) := by
  have h30 : (0 : ℝ) < 3 := by norm_num
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-(s / 2)) := Real.rpow_pos_of_pos h30 _
  have hr1 : (3 : ℝ) ^ (-(s / 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])
  have hw : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(s / 2)) := by linarith only [hr1]
  have hrpow : ∀ l : ℕ, ((3 : ℝ) ^ (-(s / 2))) ^ l = (3 : ℝ) ^ (-(s / 2) * (l : ℝ)) := by
    intro l
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(s / 2))) l, ← Real.rpow_mul h30.le]
  have hgeo : Summable fun l : ℕ => (3 : ℝ) ^ (-(s / 2) * (l : ℝ)) :=
    (summable_geometric_of_lt_one hr0.le hr1).congr hrpow
  have hgeoval : ∑' l : ℕ, (3 : ℝ) ^ (-(s / 2) * (l : ℝ)) =
      (1 - (3 : ℝ) ^ (-(s / 2)))⁻¹ := by
    rw [← tsum_congr hrpow]
    exact tsum_geometric_of_lt_one hr0.le hr1
  have hsum := summable_flatScaleTerm hs hgam h4gam hgamD
  have hterm : ∀ l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
      (gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) ≤
        9 * gam * (3 : ℝ) ^ (-(s / 2) * (l : ℝ)) := by
    intro l
    have h := termDomination hs h4gam hgamD l
    have hmul := mul_le_mul_of_nonneg_left h hgam
    have hid1 : (3 : ℝ) ^ (-(s * (l : ℝ))) * (gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) =
        gam * ((3 : ℝ) ^ (-(s * (l : ℝ))) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) := by ring
    have hid2 : gam * (9 * (3 : ℝ) ^ (-(s / 2) * (l : ℝ))) =
        9 * gam * (3 : ℝ) ^ (-(s / 2) * (l : ℝ)) := by ring
    linarith only [hmul, hid1, hid2]
  have hle : ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
      (gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) ≤
        9 * gam * (1 - (3 : ℝ) ^ (-(s / 2)))⁻¹ := by
    refine le_trans (Summable.tsum_le_tsum hterm hsum (hgeo.mul_left (9 * gam))) ?_
    rw [tsum_mul_left, hgeoval]
  have hnn : (0 : ℝ) ≤ ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
      (gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) :=
    tsum_nonneg fun l => mul_nonneg (Real.rpow_nonneg h30.le _)
      (mul_nonneg hgam (Real.rpow_nonneg h30.le _))
  have hcss1 : (1 : ℝ) - (3 : ℝ) ^ (-(2 * s)) ≤ 1 := by
    have : (0 : ℝ) < (3 : ℝ) ^ (-(2 * s)) := Real.rpow_pos_of_pos h30 _
    linarith only [this]
  have hcss0 : (0 : ℝ) ≤ 1 - (3 : ℝ) ^ (-(2 * s)) := by
    have h1 : (3 : ℝ) ^ (-(2 * s)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith only [hs])
    linarith only [h1]
  have hwlb : s / 4 ≤ 1 - (3 : ℝ) ^ (-(s / 2)) := by
    have h := half_le_one_sub_rpow_three_neg (u := s / 2) (by linarith only [hs])
      (by linarith only [hs1])
    linarith only [h]
  have hinvw : (1 - (3 : ℝ) ^ (-(s / 2)))⁻¹ ≤ 4 / s := by
    rw [le_div_iff₀ hs, inv_mul_eq_div, div_le_iff₀ hw]
    linarith only [hwlb]
  have hstep : (1 - (3 : ℝ) ^ (-(2 * s))) *
      ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
        (gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) ≤
      1 * (9 * gam * (1 - (3 : ℝ) ^ (-(s / 2)))⁻¹) :=
    mul_le_mul hcss1 hle hnn (by norm_num)
  have hlast : 9 * gam * (1 - (3 : ℝ) ^ (-(s / 2)))⁻¹ ≤ gam * (36 / s) := by
    have hmono : 9 * gam * (1 - (3 : ℝ) ^ (-(s / 2)))⁻¹ ≤ 9 * gam * (4 / s) :=
      mul_le_mul_of_nonneg_left hinvw (by linarith only [hgam])
    have hid : 9 * gam * (4 / s) = gam * (36 / s) := by
      field_simp
      ring
    linarith only [hmono, hid]
  linarith only [hstep, hlast]

/-- Summability of the linear-times-exponential shape (the shape
`ScaleSumOrdering.minkowskiOrder_scaleSum_le` evaluates).  A local
re-derivation of that proof's internal `hsumLHS`. -/
theorem summable_linearScaleTerm {s gam D : ℝ} (hs : 0 < s) (hgam : 0 ≤ gam)
    (h4gam : 4 * gam ≤ s) (hD : 0 ≤ D) (hgamD : gam * D ≤ 1) :
    Summable fun l : ℕ => (3 : ℝ) ^ (-(s * (l : ℝ))) *
      (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) := by
  have h30 : (0 : ℝ) < 3 := by norm_num
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-(s / 2)) := Real.rpow_pos_of_pos h30 _
  have hr1 : (3 : ℝ) ^ (-(s / 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])
  have hnorm : ‖(3 : ℝ) ^ (-(s / 2))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have hrpow : ∀ l : ℕ, ((3 : ℝ) ^ (-(s / 2))) ^ l = (3 : ℝ) ^ (-(s / 2) * (l : ℝ)) := by
    intro l
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(s / 2))) l, ← Real.rpow_mul h30.le]
  have hgeo : Summable fun l : ℕ => (3 : ℝ) ^ (-(s / 2) * (l : ℝ)) :=
    (summable_geometric_of_lt_one hr0.le hr1).congr hrpow
  have hlin : Summable fun l : ℕ => (l : ℝ) * (3 : ℝ) ^ (-(s / 2) * (l : ℝ)) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    refine (h.congr fun l => ?_)
    rw [pow_one, hrpow l]
  have hmaj : Summable fun l : ℕ =>
      9 * gam * D * (3 : ℝ) ^ (-(s / 2) * (l : ℝ)) +
        9 * gam * ((l : ℝ) * (3 : ℝ) ^ (-(s / 2) * (l : ℝ))) :=
    (hgeo.mul_left (9 * gam * D)).add (hlin.mul_left (9 * gam))
  refine Summable.of_nonneg_of_le (fun l => ?_) (fun l => ?_) hmaj
  · have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    exact mul_nonneg (Real.rpow_nonneg h30.le _)
      (mul_nonneg (mul_nonneg hgam (by linarith only [hD, hl0])) (Real.rpow_nonneg h30.le _))
  · have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    have hcoef : (0 : ℝ) ≤ gam * (D + (l : ℝ)) :=
      mul_nonneg hgam (by linarith only [hD, hl0])
    have h := termDomination hs h4gam hgamD l
    have hmul := mul_le_mul_of_nonneg_left h hcoef
    have hid1 : (3 : ℝ) ^ (-(s * (l : ℝ))) *
        (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) =
        gam * (D + (l : ℝ)) *
          ((3 : ℝ) ^ (-(s * (l : ℝ))) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) := by ring
    have hid2 : gam * (D + (l : ℝ)) * (9 * (3 : ℝ) ^ (-(s / 2) * (l : ℝ))) =
        9 * gam * D * (3 : ℝ) ^ (-(s / 2) * (l : ℝ)) +
          9 * gam * ((l : ℝ) * (3 : ℝ) ^ (-(s / 2) * (l : ℝ))) := by ring
    linarith only [hmul, hid1, hid2]

/-- Summability of the uniform shape. -/
theorem summable_constScaleTerm {s c : ℝ} (hs : 0 < s) :
    Summable fun l : ℕ => (3 : ℝ) ^ (-(s * (l : ℝ))) * c := by
  have h30 : (0 : ℝ) < 3 := by norm_num
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-s) := Real.rpow_pos_of_pos h30 _
  have hr1 : (3 : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])
  have hrpow : ∀ l : ℕ, ((3 : ℝ) ^ (-s)) ^ l = (3 : ℝ) ^ (-(s * (l : ℝ))) := by
    intro l
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-s)) l, ← Real.rpow_mul h30.le]
    congr 1
    ring
  have hgeo : Summable fun l : ℕ => (3 : ℝ) ^ (-(s * (l : ℝ))) :=
    (summable_geometric_of_lt_one hr0.le hr1).congr hrpow
  exact hgeo.mul_right c

/-! ## 3. The three shapes, summed -/

/-- **The Minkowski-ordered scale sum, closed.**

For `0 < s ≤ 1`, `4γ ≤ s`, `0 ≤ D` with `γD ≤ 1` (the anchor's own binder
`m ≤ n + γ^{-1}`) and `0 ≤ A`,

```
𝔠_{2s} ∑_{l ≥ 0} 3^{-sl} · ( γA + γ(D+l)3^{2γ(D+l)} + γ 3^{2γ(D+l)} )
    ≤ γ (2A + 36D + 180/s) .
```

The three summands are exactly the three shapes the proved per-cube moment
layer produces. -/
theorem minkowskiScaleSum_total_le {s gam D A : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hgam : 0 ≤ gam) (h4gam : 4 * gam ≤ s) (hD : 0 ≤ D) (hgamD : gam * D ≤ 1)
    (hA : 0 ≤ A) :
    (1 - (3 : ℝ) ^ (-(2 * s))) *
        ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
          (gam * A + (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) +
            gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))))) ≤
      gam * (2 * A + 36 * D + 180 / s) := by
  have h30 : (0 : ℝ) < 3 := by norm_num
  have hs1const := summable_constScaleTerm (s := s) (c := gam * A) hs
  have hs2 := summable_linearScaleTerm hs hgam h4gam hD hgamD
  have hs3 := summable_flatScaleTerm hs hgam h4gam hgamD
  have hsplit : ∀ l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
      (gam * A + (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) +
        gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))))) =
      (3 : ℝ) ^ (-(s * (l : ℝ))) * (gam * A) +
        ((3 : ℝ) ^ (-(s * (l : ℝ))) *
            (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) +
          (3 : ℝ) ^ (-(s * (l : ℝ))) *
            (gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))))) := by
    intro l
    ring
  have htsum : ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
      (gam * A + (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) +
        gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))))) =
      (∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) * (gam * A)) +
        ((∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
            (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))))) +
          ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
            (gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))))) := by
    rw [tsum_congr hsplit, Summable.tsum_add hs1const (hs2.add hs3),
      Summable.tsum_add hs2 hs3]
  have hcss0 : (0 : ℝ) ≤ 1 - (3 : ℝ) ^ (-(2 * s)) := by
    have h1 : (3 : ℝ) ^ (-(2 * s)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith only [hs])
    linarith only [h1]
  -- the uniform piece
  have huni : (1 - (3 : ℝ) ^ (-(2 * s))) *
      ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) * (gam * A) ≤ 2 * (gam * A) := by
    have hpull : ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) * (gam * A) =
        (∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ)))) * (gam * A) := tsum_mul_right
    rw [hpull, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (geometricTwo_mul_tsum_le_two hs)
      (mul_nonneg hgam hA)
  -- the linear piece
  have hlin := minkowskiOrder_scaleSum_le hs hs1 hgam h4gam hD hgamD
  -- the flat piece
  have hflat := flatScaleSum_le hs hs1 hgam h4gam hgamD
  have hexpand : (1 - (3 : ℝ) ^ (-(2 * s))) *
      ((∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) * (gam * A)) +
        ((∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
            (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))))) +
          ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
            (gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))))) =
      (1 - (3 : ℝ) ^ (-(2 * s))) * (∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) * (gam * A)) +
        ((1 - (3 : ℝ) ^ (-(2 * s))) *
            ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
              (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) +
          (1 - (3 : ℝ) ^ (-(2 * s))) *
            ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
              (gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))))) := by ring
  have htarget : 2 * (gam * A) + (gam * (36 * D + 144 / s) + gam * (36 / s)) =
      gam * (2 * A + 36 * D + 180 / s) := by
    field_simp
    ring
  rw [htsum, hexpand]
  linarith only [huni, hlin, hflat, htarget]

/-! ## 4. The square root, against the anchor's own scalar -/

/-- Subadditivity of `Real.sqrt`.  A local re-derivation of the `have hsub`
step inside `ScaleSumOrdering.sqrt_minkowskiOrder_bound_le`. -/
private theorem sqrtAdd {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hy2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hcross : (0 : ℝ) ≤ 2 * (Real.sqrt x * Real.sqrt y) := by positivity
  have hexpand : (Real.sqrt x + Real.sqrt y) ^ 2 =
      Real.sqrt x ^ 2 + Real.sqrt y ^ 2 + 2 * (Real.sqrt x * Real.sqrt y) := by ring
  have hle : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    linarith only [hx2, hy2, hcross, hexpand]
  exact le_trans (Real.sqrt_le_sqrt hle) (le_of_eq (Real.sqrt_sq (by positivity)))

/-- **The square root, at the anchor's own scalar.**

With the uniform slot at `A = s^{-2}`,

```
√( γ (2 s^{-2} + 36 D + 180/s) )  ≤  16 √γ ( s^{-1} + √D ) ,
``` -/
theorem sqrt_minkowskiScaleSum_le {s gam D : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hgam : 0 ≤ gam) (hD : 0 ≤ D) :
    Real.sqrt (gam * (2 * (s⁻¹ * s⁻¹) + 36 * D + 180 / s)) ≤
      16 * Real.sqrt gam * (s⁻¹ + Real.sqrt D) := by
  have hsinv : (0 : ℝ) < s⁻¹ := inv_pos.mpr hs
  have hsge : (1 : ℝ) ≤ s⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hs]
    linarith only [hs1]
  have hsplit : gam * (2 * (s⁻¹ * s⁻¹) + 36 * D + 180 / s) =
      2 * (gam * (s⁻¹ * s⁻¹)) + (36 * (gam * D) + 180 * (gam * s⁻¹)) := by
    field_simp
    ring
  have hn1 : (0 : ℝ) ≤ 2 * (gam * (s⁻¹ * s⁻¹)) := by positivity
  have hn2 : (0 : ℝ) ≤ 36 * (gam * D) := by positivity
  have hn3 : (0 : ℝ) ≤ 180 * (gam * s⁻¹) := by positivity
  have hA1 : Real.sqrt (2 * (gam * (s⁻¹ * s⁻¹))) ≤ 2 * (Real.sqrt gam * s⁻¹) := by
    have hid : Real.sqrt (2 * (gam * (s⁻¹ * s⁻¹))) =
        Real.sqrt 2 * (Real.sqrt gam * s⁻¹) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul hgam,
        Real.sqrt_mul_self hsinv.le]
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    have hmono : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    have h2 : Real.sqrt 2 ≤ 2 := by linarith only [hmono, h4]
    have hnn : (0 : ℝ) ≤ Real.sqrt gam * s⁻¹ := mul_nonneg (Real.sqrt_nonneg _) hsinv.le
    have hmul := mul_le_mul_of_nonneg_right h2 hnn
    linarith only [hid, hmul]
  have hA2 : Real.sqrt (36 * (gam * D)) = 6 * (Real.sqrt gam * Real.sqrt D) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul hgam,
      show (36 : ℝ) = 6 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
  have hA3 : Real.sqrt (180 * (gam * s⁻¹)) ≤ 14 * (Real.sqrt gam * s⁻¹) := by
    have hid : Real.sqrt (180 * (gam * s⁻¹)) =
        Real.sqrt 180 * (Real.sqrt gam * Real.sqrt s⁻¹) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul hgam]
    have h196 : Real.sqrt 196 = 14 := by
      rw [show (196 : ℝ) = 14 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    have hmono180 : Real.sqrt 180 ≤ Real.sqrt 196 := Real.sqrt_le_sqrt (by norm_num)
    have h180 : Real.sqrt 180 ≤ 14 := by linarith only [hmono180, h196]
    have hsq : Real.sqrt s⁻¹ ≤ s⁻¹ := by
      have hself : Real.sqrt (s⁻¹ * s⁻¹) = s⁻¹ := Real.sqrt_mul_self hsinv.le
      have hle : s⁻¹ ≤ s⁻¹ * s⁻¹ := by
        have hstep := mul_le_mul_of_nonneg_left hsge hsinv.le
        rw [mul_one] at hstep
        exact hstep
      have hmono := Real.sqrt_le_sqrt hle
      linarith only [hmono, hself]
    have hchain : Real.sqrt gam * Real.sqrt s⁻¹ ≤ Real.sqrt gam * s⁻¹ :=
      mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
    have hnn : (0 : ℝ) ≤ Real.sqrt gam * Real.sqrt s⁻¹ :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hstep : Real.sqrt 180 * (Real.sqrt gam * Real.sqrt s⁻¹) ≤
        14 * (Real.sqrt gam * s⁻¹) :=
      mul_le_mul h180 hchain hnn (by norm_num)
    linarith only [hid, hstep]
  have hsub1 := sqrtAdd hn1 (add_nonneg hn2 hn3)
  have hsub2 := sqrtAdd hn2 hn3
  have hgam0 : (0 : ℝ) ≤ Real.sqrt gam := Real.sqrt_nonneg gam
  have hexpand : 16 * Real.sqrt gam * (s⁻¹ + Real.sqrt D) =
      16 * (Real.sqrt gam * s⁻¹) + 16 * (Real.sqrt gam * Real.sqrt D) := by ring
  have hmid : 6 * (Real.sqrt gam * Real.sqrt D) ≤ 16 * (Real.sqrt gam * Real.sqrt D) := by
    have hnn : (0 : ℝ) ≤ Real.sqrt gam * Real.sqrt D :=
      mul_nonneg hgam0 (Real.sqrt_nonneg _)
    linarith only [hnn]
  rw [hsplit]
  linarith only [hsub1, hsub2, hA1, hA2, hA3, hexpand, hmid]

end

end Algsuperdiff.Section4.Provider.BoundsEaL
