/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Ambient.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# HolderGagliardoRadial

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The radial kernel integral `∫_{B(x,R)} |x-y|^{-β} dy`

Nothing here imports that file, nothing here claims the anchor, and nothing
here is a frozen statement.

## The target

This file proves the sharp-in-`R` bound, with the explicit constant, in the
ambient supremum metric of `Vec d`:

```text
  ∫_{B(x,R)} |x-y|^{-β} dy  ≤  ( 2^d 3^β / (1 - 3^{β-d}) ) · R^{d-β}
        for  0 < β < d .
```

Everything is `ℝ≥0∞`-valued, so no integrability side condition is needed.

## The mechanism

The ball is covered by the point `x` (where the integrand is the junk value
`0^{-β} = 0`) together with the triadic annuli `A_i = { R·3^{-i-1} ≤ |x-y| <
R·3^{-i} }`.  On `A_i` the integrand is at most `(R·3^{-i-1})^{-β}` and `|A_i|
≤ (2·R·3^{-i})^d`, so the `i`-th contribution is `T_i = (^{-i-1})^{-β}
(2^{-i})^d`, a geometric sequence of ratio `3^{β}/3^{d} < 1`.

## References

* ABK26, `t.regularity` Step 4, (the two seminorm comparisons stated without
  proof).
* ABK26, (the fractional Sobolev seminorm) (the Hölder seminorm and the `p = ∞`
  convention).
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory Metric
open HCPolySupport
open scoped ENNReal

variable {d : ℕ}

/-! ## 1. The triadic annuli around a point -/

/-- The radius `R · 3^{-i}` of the `i`-th triadic shell. -/
noncomputable def annulusRadius (R : ℝ) (i : ℕ) : ℝ := R * (3 : ℝ) ^ (-(i : ℝ))

theorem annulusRadius_zero (R : ℝ) : annulusRadius R 0 = R := by
  rw [annulusRadius]
  norm_num

theorem annulusRadius_pos {R : ℝ} (hR : 0 < R) (i : ℕ) : 0 < annulusRadius R i := by
  rw [annulusRadius]
  positivity

theorem annulusRadius_succ (R : ℝ) (i : ℕ) :
    annulusRadius R (i + 1) = annulusRadius R i / 3 := by
  have hexp : (-((i + 1 : ℕ) : ℝ)) = -(i : ℝ) + (-1 : ℝ) := by push_cast; ring
  rw [annulusRadius, annulusRadius, hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    Real.rpow_neg_one]
  ring

theorem annulusRadius_eq_pow (R : ℝ) (i : ℕ) : annulusRadius R i = R * (1 / 3 : ℝ) ^ i := by
  rw [annulusRadius, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast, one_div,
    inv_pow]

/-- **The `i`-th triadic annulus** `{ R·3^{-i-1} ≤ |x-y| < R·3^{-i} }` around `x`. -/
def triadicAnnulus (x : Vec d) (R : ℝ) (i : ℕ) : Set (Vec d) :=
  {y | annulusRadius R (i + 1) ≤ dist x y ∧ dist x y < annulusRadius R i}

theorem measurableSet_triadicAnnulus (x : Vec d) (R : ℝ) (i : ℕ) :
    MeasurableSet (triadicAnnulus x R i) := by
  have hcont : Continuous fun y : Vec d => dist x y := continuous_const.dist continuous_id
  exact (measurableSet_le measurable_const hcont.measurable).inter
    (measurableSet_lt hcont.measurable measurable_const)

theorem triadicAnnulus_subset_ball (x : Vec d) (R : ℝ) (i : ℕ) :
    triadicAnnulus x R i ⊆ Metric.ball x (annulusRadius R i) := by
  intro y hy
  rw [Metric.mem_ball, dist_comm]
  exact hy.2

/-- **The annuli cover the punctured ball.**  The centre is separated out
because the integrand takes the junk value `0^{-β} = 0` there. -/
theorem ball_subset_singleton_union_triadicAnnulus (x : Vec d) {R : ℝ} (hR : 0 < R) :
    Metric.ball x R ⊆ ({x} : Set (Vec d)) ∪ ⋃ i : ℕ, triadicAnnulus x R i := by
  classical
  intro y hy
  rcases eq_or_ne y x with rfl | hyx
  · exact Or.inl rfl
  refine Or.inr ?_
  have hdpos : 0 < dist x y := dist_pos.mpr (Ne.symm hyx)
  have hlt : dist x y < R := by
    rw [dist_comm]
    exact Metric.mem_ball.mp hy
  have hex : ∃ n : ℕ, annulusRadius R (n + 1) ≤ dist x y := by
    obtain ⟨n, hn⟩ :=
      exists_pow_lt_of_lt_one (div_pos hdpos hR) (by norm_num : (1 : ℝ) / 3 < 1)
    refine ⟨n, ?_⟩
    have hnR : R * (1 / 3 : ℝ) ^ n < dist x y := by
      have := (lt_div_iff₀ hR).mp hn
      linarith only [this]
    have hpn : (0 : ℝ) ≤ (1 / 3 : ℝ) ^ n := by positivity
    have hmono : (1 / 3 : ℝ) ^ (n + 1) ≤ (1 / 3 : ℝ) ^ n := by
      rw [pow_succ]
      linarith only [hpn]
    have hscale : R * (1 / 3 : ℝ) ^ (n + 1) ≤ R * (1 / 3 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left hmono hR.le
    rw [annulusRadius_eq_pow R (n + 1)]
    linarith only [hnR, hscale]
  have key : ∀ i : ℕ, (∀ k, k < i → ¬ annulusRadius R (k + 1) ≤ dist x y) →
      dist x y < annulusRadius R i := by
    intro i hmin
    match i with
    | 0 => rw [annulusRadius_zero]; exact hlt
    | (k + 1) =>
      have hk := hmin k (by omega)
      push Not at hk
      exact hk
  exact Set.mem_iUnion.mpr
    ⟨Nat.find hex, Nat.find_spec hex, key _ fun k hk => Nat.find_min hex hk⟩

/-! ## 2. The geometric sequence of shell contributions -/

/-- `T_i = (R·3^{-i-1})^{-β} · (2·R·3^{-i})^d`, the `i`-th shell contribution. -/
noncomputable def annulusTerm (d : ℕ) (R beta : ℝ) (i : ℕ) : ℝ :=
  annulusRadius R (i + 1) ^ (-beta) * (2 * annulusRadius R i) ^ d

/-- The common ratio `3^β / 3^d` of the shell contributions. -/
noncomputable def annulusRatio (d : ℕ) (beta : ℝ) : ℝ := (3 : ℝ) ^ beta / (3 : ℝ) ^ d

theorem annulusRatio_pos (d : ℕ) (beta : ℝ) : 0 < annulusRatio d beta := by
  rw [annulusRatio]
  positivity

theorem annulusRatio_lt_one {beta : ℝ} (hbd : beta < (d : ℝ)) : annulusRatio d beta < 1 := by
  have hnum : (3 : ℝ) ^ beta < (3 : ℝ) ^ ((d : ℕ) : ℝ) :=
    Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 3) |>.mpr hbd
  rw [Real.rpow_natCast] at hnum
  have hden : (0 : ℝ) < (3 : ℝ) ^ d := by positivity
  rw [annulusRatio, div_lt_one hden]
  exact hnum

theorem annulusTerm_pos {R : ℝ} (hR : 0 < R) (beta : ℝ) (i : ℕ) :
    0 < annulusTerm d R beta i := by
  have h1 : (0 : ℝ) < annulusRadius R (i + 1) ^ (-beta) :=
    Real.rpow_pos_of_pos (annulusRadius_pos hR (i + 1)) _
  have h2 : (0 : ℝ) < (2 * annulusRadius R i) ^ d := by
    have := annulusRadius_pos hR i
    positivity
  rw [annulusTerm]
  exact mul_pos h1 h2

theorem annulusTerm_succ {R : ℝ} (hR : 0 < R) (beta : ℝ) (i : ℕ) :
    annulusTerm d R beta (i + 1) = annulusRatio d beta * annulusTerm d R beta i := by
  have ha : (0 : ℝ) < annulusRadius R (i + 1) := annulusRadius_pos hR (i + 1)
  have hb : (0 : ℝ) < annulusRadius R i := annulusRadius_pos hR i
  have hfirst : annulusRadius R (i + 1 + 1) ^ (-beta) =
      (3 : ℝ) ^ beta * annulusRadius R (i + 1) ^ (-beta) := by
    rw [annulusRadius_succ, Real.div_rpow ha.le (by norm_num : (0 : ℝ) ≤ 3),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    field_simp
  have hsecond : (2 * annulusRadius R (i + 1)) ^ d =
      (2 * annulusRadius R i) ^ d / (3 : ℝ) ^ d := by
    rw [annulusRadius_succ, show 2 * (annulusRadius R i / 3) = 2 * annulusRadius R i / 3 by ring,
      div_pow]
  rw [annulusTerm, annulusTerm, annulusRatio, hfirst, hsecond]
  ring

theorem annulusTerm_eq_geometric {R : ℝ} (hR : 0 < R) (beta : ℝ) :
    ∀ i : ℕ, annulusTerm d R beta i = annulusTerm d R beta 0 * annulusRatio d beta ^ i
  | 0 => by rw [pow_zero, mul_one]
  | (i + 1) => by
    rw [annulusTerm_succ hR beta i, annulusTerm_eq_geometric hR beta i, pow_succ]
    ring

/-! ## 3. The shell estimate -/

theorem volume_triadicAnnulus_le {x : Vec d} {R : ℝ} (hR : 0 < R) (i : ℕ) :
    volume (triadicAnnulus x R i) ≤ ENNReal.ofReal ((2 * annulusRadius R i) ^ d) := by
  refine (measure_mono (triadicAnnulus_subset_ball x R i)).trans ?_
  rw [Real.volume_pi_ball x (annulusRadius_pos hR i), Fintype.card_fin]

theorem lintegral_triadicAnnulus_le {x : Vec d} {R beta : ℝ} (hR : 0 < R) (hbeta : 0 ≤ beta)
    (i : ℕ) :
    ∫⁻ y in triadicAnnulus x R i, ENNReal.ofReal (dist x y ^ (-beta)) ∂volume ≤
      ENNReal.ofReal (annulusTerm d R beta i) := by
  have hpt : ∀ y ∈ triadicAnnulus x R i,
      ENNReal.ofReal (dist x y ^ (-beta)) ≤
        ENNReal.ofReal (annulusRadius R (i + 1) ^ (-beta)) := by
    intro y hy
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos (annulusRadius_pos hR (i + 1)) hy.1 (neg_nonpos.mpr hbeta))
  calc ∫⁻ y in triadicAnnulus x R i, ENNReal.ofReal (dist x y ^ (-beta)) ∂volume
      ≤ ∫⁻ _ in triadicAnnulus x R i,
          ENNReal.ofReal (annulusRadius R (i + 1) ^ (-beta)) ∂volume :=
        setLIntegral_mono' (measurableSet_triadicAnnulus x R i) hpt
    _ = ENNReal.ofReal (annulusRadius R (i + 1) ^ (-beta)) * volume (triadicAnnulus x R i) :=
        setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (annulusRadius R (i + 1) ^ (-beta)) *
          ENNReal.ofReal ((2 * annulusRadius R i) ^ d) :=
        mul_le_mul' le_rfl (volume_triadicAnnulus_le hR i)
    _ = ENNReal.ofReal (annulusTerm d R beta i) := by
        rw [annulusTerm, ← ENNReal.ofReal_mul
          (Real.rpow_nonneg (annulusRadius_pos hR (i + 1)).le _)]

/-! ## 4. The ball estimate -/

/-- `C_rad(d,β) = 2^d · 3^β · (1 - 3^{β-d})^{-1}`, in the closed form the shell
sum produces: `(R/3)^{-β}(2R)^d` divided by `1 - 3^β/3^d`, at `R = 1`. -/
noncomputable def radialKernelConst (d : ℕ) (beta : ℝ) : ℝ :=
  ((1 : ℝ) / 3) ^ (-beta) * (2 : ℝ) ^ d / (1 - annulusRatio d beta)

theorem one_sub_annulusRatio_pos {beta : ℝ} (hbd : beta < (d : ℝ)) :
    0 < 1 - annulusRatio d beta := by
  have := annulusRatio_lt_one hbd
  linarith only [this]

theorem radialKernelConst_pos {beta : ℝ} (hbd : beta < (d : ℝ)) :
    0 < radialKernelConst d beta := by
  have hden := one_sub_annulusRatio_pos hbd
  have hnum : (0 : ℝ) < ((1 : ℝ) / 3) ^ (-beta) * (2 : ℝ) ^ d := by
    have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < (1 : ℝ) / 3) (-beta)
    positivity
  rw [radialKernelConst]
  exact div_pos hnum hden

/-- `T_0 = (R/3)^{-β} (2R)^d = C_rad(d,β)·(1 - ratio)·R^{d}·R^{-β}`, in the
factored form used by the sum. -/
theorem annulusTerm_zero {R : ℝ} (hR : 0 < R) (beta : ℝ) :
    annulusTerm d R beta 0 = R ^ (-beta) * ((1 : ℝ) / 3) ^ (-beta) * ((2 : ℝ) ^ d * R ^ d) := by
  have hrad : annulusRadius R (0 + 1) = R * ((1 : ℝ) / 3) := by
    rw [annulusRadius_succ, annulusRadius_zero]
    ring
  rw [annulusTerm, hrad, annulusRadius_zero,
    Real.mul_rpow hR.le (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3), mul_pow]

/-- **The radial kernel integral on a ball.**

For `0 < β < d`, in the ambient supremum metric,
`∫_{B(x,R)} |x-y|^{-β} dy ≤ C_rad(d,β) · R^{d} · R^{-β}`. -/
theorem lintegral_ball_dist_rpow_neg_le {x : Vec d} {R beta : ℝ} (hR : 0 < R)
    (hbeta : 0 < beta) (hbd : beta < (d : ℝ)) :
    ∫⁻ y in Metric.ball x R, ENNReal.ofReal (dist x y ^ (-beta)) ∂volume ≤
      ENNReal.ofReal (radialKernelConst d beta * (R ^ d * R ^ (-beta))) := by
  have hcentre : ∫⁻ y in ({x} : Set (Vec d)),
      ENNReal.ofReal (dist x y ^ (-beta)) ∂volume = 0 := by
    have hpt : ∀ y ∈ ({x} : Set (Vec d)),
        ENNReal.ofReal (dist x y ^ (-beta)) ≤ (0 : ℝ≥0∞) := by
      intro y hy
      rw [show y = x from hy, dist_self, Real.zero_rpow (by linarith only [hbeta] : -beta ≠ 0),
        ENNReal.ofReal_zero]
    refine le_antisymm ?_ zero_le
    calc ∫⁻ y in ({x} : Set (Vec d)), ENNReal.ofReal (dist x y ^ (-beta)) ∂volume
        ≤ ∫⁻ _ in ({x} : Set (Vec d)), (0 : ℝ≥0∞) ∂volume :=
          setLIntegral_mono' (measurableSet_singleton x) hpt
      _ = 0 := lintegral_zero
  have hgeom : ∑' i : ℕ, ENNReal.ofReal (annulusTerm d R beta i) =
      ENNReal.ofReal (annulusTerm d R beta 0) * (1 - ENNReal.ofReal (annulusRatio d beta))⁻¹ := by
    have hterm : ∀ i : ℕ, ENNReal.ofReal (annulusTerm d R beta i) =
        ENNReal.ofReal (annulusTerm d R beta 0) * ENNReal.ofReal (annulusRatio d beta) ^ i := by
      intro i
      rw [annulusTerm_eq_geometric hR beta i,
        ENNReal.ofReal_mul (annulusTerm_pos hR beta 0).le,
        ENNReal.ofReal_pow (annulusRatio_pos d beta).le]
    rw [tsum_congr hterm, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hsum : ∫⁻ y in Metric.ball x R, ENNReal.ofReal (dist x y ^ (-beta)) ∂volume ≤
      ∑' i : ℕ, ENNReal.ofReal (annulusTerm d R beta i) := by
    calc ∫⁻ y in Metric.ball x R, ENNReal.ofReal (dist x y ^ (-beta)) ∂volume
        ≤ ∫⁻ y in ({x} : Set (Vec d)) ∪ ⋃ i : ℕ, triadicAnnulus x R i,
            ENNReal.ofReal (dist x y ^ (-beta)) ∂volume :=
          lintegral_mono_set (ball_subset_singleton_union_triadicAnnulus x hR)
      _ ≤ (∫⁻ y in ({x} : Set (Vec d)), ENNReal.ofReal (dist x y ^ (-beta)) ∂volume) +
            ∫⁻ y in ⋃ i : ℕ, triadicAnnulus x R i,
              ENNReal.ofReal (dist x y ^ (-beta)) ∂volume :=
          lintegral_union_le _ _ _
      _ = ∫⁻ y in ⋃ i : ℕ, triadicAnnulus x R i,
            ENNReal.ofReal (dist x y ^ (-beta)) ∂volume := by rw [hcentre, zero_add]
      _ ≤ ∑' i : ℕ, ∫⁻ y in triadicAnnulus x R i,
            ENNReal.ofReal (dist x y ^ (-beta)) ∂volume :=
          lintegral_iUnion_le _ _
      _ ≤ ∑' i : ℕ, ENNReal.ofReal (annulusTerm d R beta i) :=
          ENNReal.tsum_le_tsum fun i => lintegral_triadicAnnulus_le hR hbeta.le i
  refine hsum.trans ?_
  rw [hgeom]
  have hone : (1 : ℝ≥0∞) - ENNReal.ofReal (annulusRatio d beta) =
      ENNReal.ofReal (1 - annulusRatio d beta) := by
    rw [ENNReal.ofReal_sub _ (annulusRatio_pos d beta).le, ENNReal.ofReal_one]
  rw [hone, ← ENNReal.ofReal_inv_of_pos (one_sub_annulusRatio_pos hbd),
    ← ENNReal.ofReal_mul (annulusTerm_pos hR beta 0).le]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [annulusTerm_zero hR beta, radialKernelConst]
  field_simp

/-! ## 5. The `ℝ≥0∞`-native form -/

/-- Points are null in `Vec d` once `d ≥ 1` (`{x}` is the closed ball of radius
`0`, of volume `(2·0)^d`). -/
theorem volume_singleton_eq_zero (hd : 1 ≤ d) (x : Vec d) :
    volume ({x} : Set (Vec d)) = 0 := by
  rw [← Metric.closedBall_zero, Real.volume_pi_closedBall x le_rfl, Fintype.card_fin, mul_zero,
    zero_pow (by omega : d ≠ 0), ENNReal.ofReal_zero]

/-- **The radial kernel integral, with the `ℝ≥0∞`-native kernel `‖x-y‖ₑ^{-β}`.**

The two kernels differ only on the diagonal — where the real junk value is
`0^{-β} = 0` and the `ℝ≥0∞` value is `⊤` — which is null because `0 < β < d`
forces `1 ≤ d`. -/
theorem lintegral_enorm_sub_rpow_neg_le_of_subset_ball {x : Vec d} {R beta : ℝ}
    {A : Set (Vec d)} (hA : A ⊆ Metric.ball x R) (hR : 0 < R) (hbeta : 0 < beta)
    (hbd : beta < (d : ℝ)) :
    ∫⁻ y in A, ‖x - y‖ₑ ^ (-beta) ∂volume ≤
      ENNReal.ofReal (radialKernelConst d beta * (R ^ d * R ^ (-beta))) := by
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · exfalso
      rw [h0] at hbd
      norm_num at hbd
      linarith only [hbeta, hbd]
    · exact hpos
  have hcentre : ∫⁻ y in ({x} : Set (Vec d)), ‖x - y‖ₑ ^ (-beta) ∂volume = 0 :=
    setLIntegral_measure_zero _ _ (volume_singleton_eq_zero hd x)
  have hmeasdiff : MeasurableSet (Metric.ball x R \ ({x} : Set (Vec d))) :=
    (Metric.isOpen_ball.measurableSet).diff (measurableSet_singleton x)
  have hpt : ∀ y ∈ Metric.ball x R \ ({x} : Set (Vec d)),
      ‖x - y‖ₑ ^ (-beta) ≤ ENNReal.ofReal (dist x y ^ (-beta)) := by
    intro y hy
    have hne : y ≠ x := hy.2
    have hpos : 0 < dist x y := dist_pos.mpr (Ne.symm hne)
    have henorm : ‖x - y‖ₑ = ENNReal.ofReal (dist x y) := by
      rw [dist_eq_norm, ← ofReal_norm]
    rw [henorm, ENNReal.ofReal_rpow_of_pos hpos]
  have hcover : Metric.ball x R ⊆
      (Metric.ball x R \ ({x} : Set (Vec d))) ∪ ({x} : Set (Vec d)) := by
    intro y hy
    by_cases h : y = x
    · exact Or.inr h
    · exact Or.inl ⟨hy, h⟩
  calc ∫⁻ y in A, ‖x - y‖ₑ ^ (-beta) ∂volume
      ≤ ∫⁻ y in Metric.ball x R, ‖x - y‖ₑ ^ (-beta) ∂volume := lintegral_mono_set hA
    _ ≤ ∫⁻ y in (Metric.ball x R \ ({x} : Set (Vec d))) ∪ ({x} : Set (Vec d)),
          ‖x - y‖ₑ ^ (-beta) ∂volume := lintegral_mono_set hcover
    _ ≤ (∫⁻ y in Metric.ball x R \ ({x} : Set (Vec d)), ‖x - y‖ₑ ^ (-beta) ∂volume) +
          ∫⁻ y in ({x} : Set (Vec d)), ‖x - y‖ₑ ^ (-beta) ∂volume := lintegral_union_le _ _ _
    _ = ∫⁻ y in Metric.ball x R \ ({x} : Set (Vec d)), ‖x - y‖ₑ ^ (-beta) ∂volume := by
        rw [hcentre, add_zero]
    _ ≤ ∫⁻ y in Metric.ball x R \ ({x} : Set (Vec d)),
          ENNReal.ofReal (dist x y ^ (-beta)) ∂volume := setLIntegral_mono' hmeasdiff hpt
    _ ≤ ∫⁻ y in Metric.ball x R, ENNReal.ofReal (dist x y ^ (-beta)) ∂volume :=
        lintegral_mono_set Set.sdiff_subset
    _ ≤ ENNReal.ofReal (radialKernelConst d beta * (R ^ d * R ^ (-beta))) :=
        lintegral_ball_dist_rpow_neg_le hR hbeta hbd

end Algsuperdiff.Section4.Provider.Regularity
