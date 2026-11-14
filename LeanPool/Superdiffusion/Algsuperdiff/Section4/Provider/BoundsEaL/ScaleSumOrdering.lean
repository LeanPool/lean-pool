/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# ScaleSumOrdering

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 5's scale sum: the two orderings of the same per-scale data

Nothing here imports that file, and nothing here claims the anchor.  Everything
below is abstract-real arithmetic: no model, no measure, no carrier occurs.

## What is here

The manuscript's Step 5 combines the per-scale data

```
G_l  =  B · min{1, (γ(D+l))^{1/2}} · 3^{γ(D+l)} ,   D = m − n ,  l = n − j ≥ 0 ,
```

(`B` carries the `Γ₂`-moment constant `(K p)^{1/2}`, `D = m − n`) against the
geometric scale weight `3^{−s l}`.  There are two possible orderings, and they
are NOT equivalent:

* the **`ℓ^p` (Jensen) ordering** `( c_s ∑_l 3^{−s l} G_l^p )^{1/p}`, which is
  what the printed display literally writes -- the weight sits INSIDE the `p`-th
  power, so after the `p`-th root it acts at the rate `s/p`; and
* the **`ℓ¹` (Minkowski) ordering** `( c_{2s} ∑_l 3^{−s l} G_l^2 )^{1/2}`, which
  is what `d.mathcal.E`'s `q = 2` branch offers directly (the scale sum is
  already outside the `p`-th power there, so the `p/2`-th moments may be
  combined by the triangle inequality in `L^{p/2}` instead of by Jensen).

This module proves the exact arithmetic of both.

1. `minkowskiOrder_scaleSum_le` / `sqrt_minkowskiOrder_bound_le`: in the `ℓ¹`
   ordering the sum is at most `γ(36 D + 144/s)`, i.e. its square root is at most
   `12 √γ (√D + s^{−1/2})` -- exactly the value the manuscript's Step 5 asserts
   for its display, with an explicit absolute constant.
2. `anchorScalar_rpow_lt_jensenOrder_weighted_term` (with
   `jensenOrder_term_le_printed_summand` for faithfulness to the printed
   summand): in the `ℓ^p` ordering ONE term of the same sum already exceeds the
   `p`-th power of the anchor's own scalar `C √γ s^{−1}` at `D = 0` and at the
   top `p = C^{-1} γ^{-1} s` of the anchor's `p`-range, for `C > 72`.  Since
   the anchor's statement at a constant `C₀` implies it at every `C ≥ C₀` (all
   three parameter ranges shrink and the right-hand side grows with `C`), this
   settles the `ℓ^p` ordering for every constant.

The two together locate the discrepancy exactly: it is the placement of the
`p`-th root relative to the scale sum, and nothing else.  The maximising scale
in 2 is `l ≈ p/s`, where `3^{−s l/p} ≈ 1/3` while `(γ l)^{1/2} ≈ (γ p/s)^{1/2}`;
the `ℓ¹` ordering instead sees the geometric weight at full strength and is
maximised at `l ≈ 1/s`, which is the source of the printed `s^{−1/2}`.

## References

* ABK26, `l.bounds.mathcal.E.aL`, Step 5; `d.mathcal.E`;
  `e.mathcalE.infty.to.q`.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

/-! ## 1. Two elementary transcendental estimates -/

/-- `1 ≤ log 3`, from `exp 1 < 2.72 < 3`. -/
private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
  exact le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))

/-- **The geometric discount is at least `u/2`** on `0 < u ≤ 1`:
`u/2 ≤ 1 − 3^{−u}`.  This is the only place a logarithm enters the `ℓ¹`
ordering. -/
theorem half_le_one_sub_rpow_three_neg {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    u / 2 ≤ 1 - (3 : ℝ) ^ (-u) := by
  have hL : (1 : ℝ) ≤ Real.log 3 := one_le_log_three
  have hL0 : (0 : ℝ) < Real.log 3 := lt_of_lt_of_le zero_lt_one hL
  have hXlb : 1 + u * Real.log 3 ≤ (3 : ℝ) ^ u := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    have hE := Real.add_one_le_exp (Real.log 3 * u)
    have hcomm : Real.log 3 * u = u * Real.log 3 := mul_comm _ _
    linarith only [hE, hcomm]
  have hden : (0 : ℝ) < 1 + u * Real.log 3 := by positivity
  have hX0 : (0 : ℝ) < (3 : ℝ) ^ u := Real.rpow_pos_of_pos (by norm_num) u
  have hinv : ((3 : ℝ) ^ u)⁻¹ ≤ (1 + u * Real.log 3)⁻¹ := by
    exact inv_anti₀ hden hXlb
  have hprod : (1 : ℝ) ≤ Real.log 3 * (2 - u) :=
    le_trans hL (le_mul_of_one_le_right hL0.le (by linarith only [hu1]))
  have hid : (1 - u / 2) * (1 + u * Real.log 3) - 1 =
      u / 2 * (Real.log 3 * (2 - u) - 1) := by ring
  have hnn : 0 ≤ u / 2 * (Real.log 3 * (2 - u) - 1) :=
    mul_nonneg (by linarith only [hu]) (by linarith only [hprod])
  have hle : (1 + u * Real.log 3)⁻¹ ≤ 1 - u / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    linarith only [hid, hnn]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) u]
  linarith only [hinv, hle]

/-! ## 2. The `ℓ¹` (Minkowski) ordering: the manuscript's own value -/

/-- **The scale sum in the `ℓ¹` ordering.**

For `0 < s ≤ 1`, `4γ ≤ s`, `D ≥ 0` and `γ D ≤ 1` (the anchor's own binder
`m ≤ n + γ^{-1}`),

```
(1 − 3^{−2s}) · ∑_{l ≥ 0} 3^{−s l} · γ(D+l) · 3^{2γ(D+l)}  ≤  γ (36 D + 144/s) .
```

The summand is the square of the second summand's per-scale majorant
`min{1,(γ(D+l))^{1/2}} 3^{γ(D+l)}` with the `min` discarded (`min ≤` its second
argument), and the prefactor is the `q = 2` geometric discount `𝔠_{2s}`. -/
theorem minkowskiOrder_scaleSum_le {s gam D : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hgam : 0 ≤ gam) (h4gam : 4 * gam ≤ s) (hD : 0 ≤ D) (hgamD : gam * D ≤ 1) :
    (1 - (3 : ℝ) ^ (-(2 * s))) *
        ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
          (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) ≤
      gam * (36 * D + 144 / s) := by
  have h30 : (0 : ℝ) < 3 := by norm_num
  set r : ℝ := (3 : ℝ) ^ (-(s / 2)) with hrdef
  have hr0 : 0 < r := Real.rpow_pos_of_pos h30 _
  have hr1 : r < 1 := by
    rw [hrdef]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])
  have hw0 : (0 : ℝ) < 1 - r := by linarith only [hr1]
  have hrpow : ∀ l : ℕ, r ^ l = (3 : ℝ) ^ (-(s / 2) * (l : ℝ)) := by
    intro l
    rw [hrdef, ← Real.rpow_natCast ((3 : ℝ) ^ (-(s / 2))) l,
      ← Real.rpow_mul h30.le]
  -- the termwise bound
  have hterm : ∀ l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
      (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) ≤
        9 * gam * (r ^ l * (D + (l : ℝ))) := by
    intro l
    have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    have hcoef : 0 ≤ gam * (D + (l : ℝ)) := mul_nonneg hgam (by linarith only [hD, hl0])
    have hexp : -(s * (l : ℝ)) + 2 * gam * (D + (l : ℝ)) ≤ 2 + -(s / 2) * (l : ℝ) := by
      have hDpart : 2 * (gam * D) ≤ 2 := by linarith only [hgamD]
      have hlpart : 2 * gam * (l : ℝ) ≤ s / 2 * (l : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith only [h4gam]) hl0
      have hexpand : 2 * gam * (D + (l : ℝ)) = 2 * (gam * D) + 2 * gam * (l : ℝ) := by
        ring
      have hsl : 0 ≤ s * (l : ℝ) := mul_nonneg hs.le hl0
      linarith only [hDpart, hlpart, hexpand, hsl]
    have hpow : (3 : ℝ) ^ (-(s * (l : ℝ))) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) ≤
        9 * r ^ l := by
      rw [← Real.rpow_add h30]
      calc (3 : ℝ) ^ (-(s * (l : ℝ)) + 2 * gam * (D + (l : ℝ)))
          ≤ (3 : ℝ) ^ (2 + -(s / 2) * (l : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ = 9 * r ^ l := by
            rw [Real.rpow_add h30, hrpow l]
            norm_num
    calc (3 : ℝ) ^ (-(s * (l : ℝ))) *
          (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))))
        = gam * (D + (l : ℝ)) *
            ((3 : ℝ) ^ (-(s * (l : ℝ))) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) := by ring
      _ ≤ gam * (D + (l : ℝ)) * (9 * r ^ l) := mul_le_mul_of_nonneg_left hpow hcoef
      _ = 9 * gam * (r ^ l * (D + (l : ℝ))) := by ring
  -- summability
  have hsumG : Summable fun l : ℕ => r ^ l := summable_geometric_of_lt_one hr0.le hr1
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have hsumL : Summable fun l : ℕ => (l : ℝ) * r ^ l := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    exact h.congr fun l => by rw [pow_one]
  have hsumR : Summable fun l : ℕ => 9 * gam * (r ^ l * (D + (l : ℝ))) := by
    refine ((hsumG.mul_left (9 * gam * D)).add (hsumL.mul_left (9 * gam))).congr ?_
    intro l
    ring
  have hsumLHS : Summable fun l : ℕ => (3 : ℝ) ^ (-(s * (l : ℝ))) *
      (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) := by
    refine hsumR.of_nonneg_of_le (fun l => ?_) hterm
    have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    have hcoef : 0 ≤ gam * (D + (l : ℝ)) := mul_nonneg hgam (by linarith only [hD, hl0])
    have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s * (l : ℝ))) := Real.rpow_nonneg h30.le _
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) := Real.rpow_nonneg h30.le _
    exact mul_nonneg h1 (mul_nonneg hcoef h2)
  -- the two geometric evaluations
  have hgeo : ∑' l : ℕ, r ^ l = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0.le hr1
  have hlin : ∑' l : ℕ, (l : ℝ) * r ^ l = r / (1 - r) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  have hsplit : ∑' l : ℕ, 9 * gam * (r ^ l * (D + (l : ℝ))) =
      9 * gam * D * (1 - r)⁻¹ + 9 * gam * (r / (1 - r) ^ 2) := by
    have hcongr : ∀ l : ℕ, 9 * gam * (r ^ l * (D + (l : ℝ))) =
        9 * gam * D * r ^ l + 9 * gam * ((l : ℝ) * r ^ l) := by
      intro l
      ring
    rw [tsum_congr hcongr, Summable.tsum_add (hsumG.mul_left (9 * gam * D))
      (hsumL.mul_left (9 * gam)), tsum_mul_left, tsum_mul_left, hgeo, hlin]
  -- the arithmetic of the two geometric constants
  have hr4 : (3 : ℝ) ^ (-(2 * s)) = r ^ 4 := by
    rw [hrpow 4, show -(s / 2) * ((4 : ℕ) : ℝ) = -(2 * s) from by push_cast; ring]
  have hcss : 1 - (3 : ℝ) ^ (-(2 * s)) ≤ 4 * (1 - r) := by
    have h2 : r ^ 2 ≤ 1 := pow_le_one₀ hr0.le hr1.le
    have h3 : r ^ 3 ≤ 1 := pow_le_one₀ hr0.le hr1.le
    have hpoly : 1 - r ^ 4 = (1 - r) * (1 + r + r ^ 2 + r ^ 3) := by ring
    have hchain : (1 - r) * (1 + r + r ^ 2 + r ^ 3) ≤ (1 - r) * 4 :=
      mul_le_mul_of_nonneg_left (by linarith only [hr1, h2, h3]) hw0.le
    rw [hr4]
    linarith only [hpoly, hchain]
  have hwlb : s / 4 ≤ 1 - r := by
    have h := half_le_one_sub_rpow_three_neg (u := s / 2) (by linarith only [hs])
      (by linarith only [hs1])
    rw [hrdef]
    linarith only [h]
  have hinvw : (1 - r)⁻¹ ≤ 4 / s := by
    rw [le_div_iff₀ hs, inv_mul_eq_div, div_le_iff₀ hw0]
    linarith only [hwlb]
  -- assembly
  have hTle : ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
      (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) ≤
        9 * gam * ((1 - r)⁻¹ * (D + (1 - r)⁻¹)) := by
    refine le_trans (Summable.tsum_le_tsum hterm hsumLHS hsumR) ?_
    rw [hsplit]
    have hsq : r / (1 - r) ^ 2 ≤ (1 - r)⁻¹ * (1 - r)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      have hid : (1 - r)⁻¹ * (1 - r)⁻¹ * (1 - r) ^ 2 = 1 := by
        field_simp
      linarith only [hid, hr1.le]
    have hfac : 9 * gam * (r / (1 - r) ^ 2) ≤ 9 * gam * ((1 - r)⁻¹ * (1 - r)⁻¹) :=
      mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ 9 * gam by linarith only [hgam])
    have hexpand : 9 * gam * ((1 - r)⁻¹ * (D + (1 - r)⁻¹)) =
        9 * gam * D * (1 - r)⁻¹ + 9 * gam * ((1 - r)⁻¹ * (1 - r)⁻¹) := by ring
    linarith only [hfac, hexpand]
  have hTnn : (0 : ℝ) ≤ ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
      (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) := by
    refine tsum_nonneg fun l => ?_
    have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    have hcoef : 0 ≤ gam * (D + (l : ℝ)) := mul_nonneg hgam (by linarith only [hD, hl0])
    have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s * (l : ℝ))) := Real.rpow_nonneg h30.le _
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) := Real.rpow_nonneg h30.le _
    exact mul_nonneg h1 (mul_nonneg hcoef h2)
  have hcss0 : (0 : ℝ) ≤ 1 - (3 : ℝ) ^ (-(2 * s)) := by
    rw [hr4]
    have h4 : r ^ 4 ≤ 1 := pow_le_one₀ hr0.le hr1.le
    linarith only [h4]
  have hstep1 : (1 - (3 : ℝ) ^ (-(2 * s))) *
      ∑' l : ℕ, (3 : ℝ) ^ (-(s * (l : ℝ))) *
        (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))) ≤
      (4 * (1 - r)) * (9 * gam * ((1 - r)⁻¹ * (D + (1 - r)⁻¹))) := by
    refine mul_le_mul hcss hTle hTnn ?_
    positivity
  have hcancel : (4 * (1 - r)) * (9 * gam * ((1 - r)⁻¹ * (D + (1 - r)⁻¹))) =
      36 * gam * (D + (1 - r)⁻¹) := by
    field_simp
    ring
  have hfinal : 36 * gam * (D + (1 - r)⁻¹) ≤ gam * (36 * D + 144 / s) := by
    have hmono : (0 : ℝ) ≤ 36 * gam := by linarith only [hgam]
    have hstep : 36 * gam * (D + (1 - r)⁻¹) ≤ 36 * gam * (D + 4 / s) :=
      mul_le_mul_of_nonneg_left (by linarith only [hinvw]) hmono
    have hid : 36 * gam * (D + 4 / s) = gam * (36 * D + 144 / s) := by
      field_simp
      ring
    linarith only [hstep, hid]
  linarith only [hstep1, hcancel, hfinal]

/-! ## 3. The `ℓ^p` (Jensen) ordering: one term already overshoots -/

end Algsuperdiff.Section4.Provider.BoundsEaL
