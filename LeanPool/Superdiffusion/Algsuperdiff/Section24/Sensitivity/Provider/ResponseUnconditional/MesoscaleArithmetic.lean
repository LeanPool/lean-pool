/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale.LoadNormalization

/-!
# MesoscaleArithmetic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The real arithmetic of the unconditional response aggregation

Source: ABK26.

This module contains the **gauge-free real arithmetic** of the aggregation half
of `l.J.sensitivity.no.conditions`: the mesoscale exponent bookkeeping, the
damping identities of the mesoscopic depth, and the single arithmetic fold that
turns the four aggregated families into the four terms of the frozen conclusion
`Algsuperdiff.Frozen.Section24.responseJ_sensitivity_unconditional`.

Nothing here mentions a coefficient field, a cube, a gauge or a multiscale
quantity: every statement is about plain real numbers.  It is split off from
`Provider.ResponseUnconditional.Aggregation` purely so that each declaration
elaborates inside the default heartbeat budget.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional

open Algsuperdiff.Section24.Sensitivity.Provider.Mesoscale

noncomputable section

/-- CoarseGraining writes multiscale weights with explicit `Real.rpow`. -/
private theorem rpow_eq_pow (x y : ℝ) : Real.rpow x y = x ^ y := rfl

/-! ## Removing the mesoscale constant from the frozen `rpow` base

The mesoscopic depth is attached to `u = 1 + C₀ X`, while the frozen conclusion
carries the bare base `1 + X`.  For `C₀ ≥ 1` and an exponent in `[0,1]` the two
differ by the harmless factor `C₀`. -/

/-- `(1 +)^θ ≤ C (1 + X)^θ` for `1 ≤ C`, `0 ≤ X` and `0 ≤ θ ≤ 1`. -/
theorem rpow_one_add_const_mul_le {C X θ : ℝ} (hC : 1 ≤ C) (hX : 0 ≤ X)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.rpow (1 + C * X) θ ≤ C * Real.rpow (1 + X) θ := by
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hbase : (0 : ℝ) ≤ 1 + X := by linarith only [hX]
  have hCX : (0 : ℝ) ≤ C * X := mul_nonneg hCpos.le hX
  have hstep : 1 + C * X ≤ C * (1 + X) := by linarith only [hC]
  have h1 : Real.rpow (1 + C * X) θ ≤ Real.rpow (C * (1 + X)) θ := by
    simp only [rpow_eq_pow]
    refine Real.rpow_le_rpow ?_ hstep hθ0
    linarith only [hCX]
  refine h1.trans ?_
  simp only [rpow_eq_pow]
  rw [Real.mul_rpow hCpos.le hbase]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hbase _)
  calc C ^ θ ≤ C ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hC hθ1
    _ = C := Real.rpow_one C

/-- The frozen exponents `2t/(1-2s)` lie in `[0,1]` on the frozen range
`0 < s ≤ 1/4`, `0 ≤ t ≤ 1/4`. -/
theorem frozen_exponent_mem {s t : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4) (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 4) :
    0 ≤ 2 * t / (1 - 2 * s) ∧ 2 * t / (1 - 2 * s) ≤ 1 := by
  have hβ : (0 : ℝ) < 1 - 2 * s := by linarith
  refine ⟨div_nonneg (by linarith) hβ.le, ?_⟩
  rw [div_le_one hβ]
  linarith

/-! ## The mesoscale rescaling factor against the frozen base -/

/-- **The mesoscale factor against the frozen `rpow` base.**  At the mesoscopic
depth `H = mesoscaleDepth s (1 + C₀ X)`, the descendant rescaling factor
`3^{2 t H}` is bounded by `3 C₀ (1 + X)^{2t/(1-2s)}` — the frozen base carries no
constant. -/
theorem three_rpow_two_mul_depth_le_const_mul_rpow {s t X C₀ : ℝ} (hs0 : 0 < s)
    (hs : s ≤ 1 / 4) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) (hX : 0 ≤ X) (hC₀ : 1 ≤ C₀) :
    Real.rpow (3 : ℝ) (2 * t * (mesoscaleDepth s (1 + C₀ * X) : ℝ)) ≤
      3 * C₀ * Real.rpow (1 + X) (2 * t / (1 - 2 * s)) := by
  have hC₀pos : (0 : ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hu : (1 : ℝ) ≤ 1 + C₀ * X := by
    linarith only [mul_nonneg hC₀pos.le hX]
  obtain ⟨hθ0, hθ1⟩ := frozen_exponent_mem hs0 hs ht0 ht
  have h1 := three_rpow_two_mul_mesoscaleDepth_le (s := s) (u := 1 + C₀ * X) (t := t)
    hs0 hs hu ht0 ht
  have h2 := rpow_one_add_const_mul_le (C := C₀) (X := X)
    (θ := 2 * t / (1 - 2 * s)) hC₀ hX hθ0 hθ1
  calc Real.rpow (3 : ℝ) (2 * t * (mesoscaleDepth s (1 + C₀ * X) : ℝ))
      ≤ 3 * Real.rpow (1 + C₀ * X) (2 * t / (1 - 2 * s)) := h1
    _ ≤ 3 * (C₀ * Real.rpow (1 + X) (2 * t / (1 - 2 * s))) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = 3 * C₀ * Real.rpow (1 + X) (2 * t / (1 - 2 * s)) := by ring

/-! ## The damping identities of the mesoscopic depth -/

/-- The mesoscopic damping factor `3^{-2(1-2s)H}` is at most one. -/
theorem three_rpow_neg_two_one_sub_two_mul_le_one {s : ℝ} (hs : s ≤ 1 / 4) (H : ℕ) :
    Real.rpow (3 : ℝ) (-(2 * ((1 - 2 * s) * (H : ℝ)))) ≤ 1 := by
  simp only [rpow_eq_pow]
  refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
  have hH : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  have hβ : (0 : ℝ) ≤ 1 - 2 * s := by linarith only [hs]
  linarith only [mul_nonneg hβ hH]

/-- `3^{-2H} · 3^{2sH} = 3^{-2(1-s)H} ≤ 3^{-2(1-2s)H}`. -/
theorem three_rpow_neg_two_mul_rpow_le {s : ℝ} (hs0 : 0 ≤ s) (H : ℕ) :
    Real.rpow (3 : ℝ) (-(2 * (H : ℝ))) * Real.rpow (3 : ℝ) (2 * s * (H : ℝ)) ≤
      Real.rpow (3 : ℝ) (-(2 * ((1 - 2 * s) * (H : ℝ)))) := by
  have heq : Real.rpow (3 : ℝ) (-(2 * (H : ℝ))) *
      Real.rpow (3 : ℝ) (2 * s * (H : ℝ)) =
      Real.rpow (3 : ℝ) (-(2 * (1 - s) * (H : ℝ))) := by
    simp only [rpow_eq_pow]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [heq]
  refine (three_rpow_neg_two_mul_one_sub_le hs0 H).trans (le_of_eq ?_)
  congr 1
  ring

/-- `3^{-2H} · (3^{2sH})² = 3^{-2(1-2s)H}`. -/
theorem three_rpow_neg_two_mul_rpow_sq_eq {s : ℝ} (H : ℕ) :
    Real.rpow (3 : ℝ) (-(2 * (H : ℝ))) * Real.rpow (3 : ℝ) (2 * s * (H : ℝ)) ^ 2 =
      Real.rpow (3 : ℝ) (-(2 * ((1 - 2 * s) * (H : ℝ)))) := by
  simp only [rpow_eq_pow]
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (2 * s * (H : ℝ))) 2, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  push_cast
  ring

/-- **The `min` bookkeeping of the fourth frozen term.**  At the mesoscopic depth
attached to `1 + C₀ X` the damped square `X² 3^{-2(1-2s)H}` is bounded by a
constant multiple of `min {1, X}²`. -/
theorem sq_mul_damping_le_min {s X C₀ : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4)
    (hX : 0 ≤ X) (hC₀ : 1 ≤ C₀) :
    X ^ 2 * Real.rpow (3 : ℝ)
        (-(2 * ((1 - 2 * s) * (mesoscaleDepth s (1 + C₀ * X) : ℕ) : ℝ))) ≤
      (C₀ ^ 2)⁻¹ * (max 1 (C₀ ^ 2) * min 1 X ^ 2) := by
  have hC₀pos : (0 : ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hu : (1 : ℝ) ≤ 1 + C₀ * X := by
    linarith only [mul_nonneg hC₀pos.le hX]
  have hmain := sub_one_sq_mul_three_rpow_neg_two_mesoscaleDepth_le_min
    (s := s) (u := 1 + C₀ * X) hs0 hs hu
  have hrw : (1 + C₀ * X) - 1 = C₀ * X := by ring
  rw [hrw] at hmain
  have hstep : (C₀ * X) ^ 2 *
      Real.rpow (3 : ℝ)
        (-(2 * ((1 - 2 * s) * (mesoscaleDepth s (1 + C₀ * X) : ℕ) : ℝ))) ≤
      max 1 (C₀ ^ 2) * min 1 X ^ 2 := hmain.trans (min_one_sq_mul_le C₀ X)
  have hCsq : (0 : ℝ) < C₀ ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hstep (le_of_lt (inv_pos.mpr hCsq))
  refine le_trans (le_of_eq ?_) hscaled
  field_simp

/-! ## The aggregation constant -/

/-- The constant produced by the aggregation, in terms of the constant `C₀` of
the mesoscopic depth and the constant `K` of the per-cube estimate. -/
def aggConst (C₀ K : ℝ) : ℝ :=
  18 * C₀ + 3 * K * C₀ + K + 2 * K * max 1 (C₀ ^ 2) * (C₀ ^ 2)⁻¹

theorem one_le_max_one_sq (C₀ : ℝ) : (1 : ℝ) ≤ max 1 (C₀ ^ 2) := le_max_left _ _

theorem aggConst_pos {C₀ K : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 ≤ K) : 0 < aggConst C₀ K := by
  have hC₀pos : (0 : ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hm : (0 : ℝ) ≤ max 1 (C₀ ^ 2) := le_trans zero_le_one (one_le_max_one_sq C₀)
  have h1 : (0 : ℝ) ≤ 3 * K * C₀ := by positivity
  have h2 : (0 : ℝ) ≤ 2 * K * max 1 (C₀ ^ 2) * (C₀ ^ 2)⁻¹ := by positivity
  have h3 : (0 : ℝ) < 18 * C₀ := by positivity
  unfold aggConst
  linarith only [h1, h2, h3, hK]

theorem eighteen_mul_le_aggConst {C₀ K : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 ≤ K) :
    18 * C₀ ≤ aggConst C₀ K := by
  have hC₀pos : (0 : ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hm : (0 : ℝ) ≤ max 1 (C₀ ^ 2) := le_trans zero_le_one (one_le_max_one_sq C₀)
  have h1 : (0 : ℝ) ≤ 3 * K * C₀ := by positivity
  have h2 : (0 : ℝ) ≤ 2 * K * max 1 (C₀ ^ 2) * (C₀ ^ 2)⁻¹ := by positivity
  unfold aggConst
  linarith only [h1, h2, hK]

theorem three_mul_le_aggConst {C₀ K : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 ≤ K) :
    3 * K * C₀ ≤ aggConst C₀ K := by
  have hC₀pos : (0 : ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hm : (0 : ℝ) ≤ max 1 (C₀ ^ 2) := le_trans zero_le_one (one_le_max_one_sq C₀)
  have h1 : (0 : ℝ) ≤ 18 * C₀ := by positivity
  have h2 : (0 : ℝ) ≤ 2 * K * max 1 (C₀ ^ 2) * (C₀ ^ 2)⁻¹ := by positivity
  unfold aggConst
  linarith only [h1, h2, hK]

theorem le_aggConst {C₀ K : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 ≤ K) : K ≤ aggConst C₀ K := by
  have hC₀pos : (0 : ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hm : (0 : ℝ) ≤ max 1 (C₀ ^ 2) := le_trans zero_le_one (one_le_max_one_sq C₀)
  have h1 : (0 : ℝ) ≤ 18 * C₀ := by positivity
  have h2 : (0 : ℝ) ≤ 3 * K * C₀ := by positivity
  have h3 : (0 : ℝ) ≤ 2 * K * max 1 (C₀ ^ 2) * (C₀ ^ 2)⁻¹ := by positivity
  unfold aggConst
  linarith only [h1, h2, h3]

theorem two_mul_min_coeff_le_aggConst {C₀ K : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 ≤ K) :
    2 * (K * ((C₀ ^ 2)⁻¹ * max 1 (C₀ ^ 2))) ≤ aggConst C₀ K := by
  have hC₀pos : (0 : ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hm : (0 : ℝ) ≤ max 1 (C₀ ^ 2) := le_trans zero_le_one (one_le_max_one_sq C₀)
  have hi : (0 : ℝ) ≤ (C₀ ^ 2)⁻¹ := by positivity
  have h1 : (0 : ℝ) ≤ 18 * C₀ := by positivity
  have h2 : (0 : ℝ) ≤ 3 * K * C₀ := by positivity
  have heq : 2 * (K * ((C₀ ^ 2)⁻¹ * max 1 (C₀ ^ 2))) =
      2 * K * max 1 (C₀ ^ 2) * (C₀ ^ 2)⁻¹ := by ring
  rw [heq]
  unfold aggConst
  linarith only [h1, h2, hK]

theorem min_coeff_le_aggConst {C₀ K : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 ≤ K) :
    K * ((C₀ ^ 2)⁻¹ * max 1 (C₀ ^ 2)) ≤ aggConst C₀ K := by
  have hC₀pos : (0 : ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hm : (0 : ℝ) ≤ max 1 (C₀ ^ 2) := le_trans zero_le_one (one_le_max_one_sq C₀)
  have hi : (0 : ℝ) ≤ (C₀ ^ 2)⁻¹ := by positivity
  have hprod : (0 : ℝ) ≤ K * ((C₀ ^ 2)⁻¹ * max 1 (C₀ ^ 2)) := by positivity
  linarith only [hprod, two_mul_min_coeff_le_aggConst hC₀ hK]

/-! ## The arithmetic fold into the four frozen terms -/

/-- **The main term.**  `6 μ⁻¹ 3^{2tH} E²` is one of the frozen first terms. -/
theorem main_term_le {μ C₀ K Wt Yt E : ℝ} (hμ : 0 < μ) (hC₀ : 1 ≤ C₀) (hK : 0 ≤ K)
    (hYt0 : 0 ≤ Yt) (hWt : Wt ≤ 3 * C₀ * Yt) :
    6 * μ⁻¹ * (Wt * E ^ 2) ≤ aggConst C₀ K * μ⁻¹ * Yt * E ^ 2 := by
  have hμinv : (0 : ℝ) < μ⁻¹ := inv_pos.mpr hμ
  have hE : (0 : ℝ) ≤ E ^ 2 := sq_nonneg E
  have hstep : 6 * Wt ≤ aggConst C₀ K * Yt := by
    have h1 : 6 * Wt ≤ 6 * (3 * C₀ * Yt) := by linarith only [hWt]
    have h2 : 6 * (3 * C₀ * Yt) ≤ aggConst C₀ K * Yt := by
      linarith only
        [mul_le_mul_of_nonneg_right (eighteen_mul_le_aggConst hC₀ hK) hYt0]
    linarith only [h1, h2]
  calc 6 * μ⁻¹ * (Wt * E ^ 2) = (6 * Wt) * (μ⁻¹ * E ^ 2) := by ring
    _ ≤ (aggConst C₀ K * Yt) * (μ⁻¹ * E ^ 2) :=
        mul_le_mul_of_nonneg_right hstep (by positivity)
    _ = aggConst C₀ K * μ⁻¹ * Yt * E ^ 2 := by ring

/-- **The value term.**  `K μ⁻¹ σ0⁻¹ 3^{2sH} λ⁻¹ ‖h‖²_{L²}` is part of the second
frozen term. -/
theorem value_term_le {μ σ0 C₀ K W Ys L val : ℝ} (hμ : 0 < μ) (hσ0 : 0 < σ0)
    (hC₀ : 1 ≤ C₀) (hK : 0 ≤ K) (hL : 0 ≤ L) (hYs0 : 0 ≤ Ys)
    (hW : W ≤ 3 * C₀ * Ys) :
    K * μ⁻¹ * σ0⁻¹ * (W * L) * val ^ 2 ≤
      aggConst C₀ K * μ⁻¹ * σ0 * L * Ys * (σ0⁻¹ ^ 2 * val ^ 2) := by
  have hμinv : (0 : ℝ) < μ⁻¹ := inv_pos.mpr hμ
  have hσinv : (0 : ℝ) < σ0⁻¹ := inv_pos.mpr hσ0
  have hval : (0 : ℝ) ≤ val ^ 2 := sq_nonneg val
  have hσ : σ0 * σ0⁻¹ ^ 2 = σ0⁻¹ := by field_simp
  have hstep : K * W ≤ aggConst C₀ K * Ys := by
    have h1 : K * W ≤ K * (3 * C₀ * Ys) := mul_le_mul_of_nonneg_left hW hK
    have h2 : K * (3 * C₀ * Ys) ≤ aggConst C₀ K * Ys := by
      linarith only
        [mul_le_mul_of_nonneg_right (three_mul_le_aggConst hC₀ hK) hYs0]
    linarith only [h1, h2]
  calc K * μ⁻¹ * σ0⁻¹ * (W * L) * val ^ 2
      = (K * W) * (μ⁻¹ * σ0⁻¹ * L * val ^ 2) := by ring
    _ ≤ (aggConst C₀ K * Ys) * (μ⁻¹ * σ0⁻¹ * L * val ^ 2) :=
        mul_le_mul_of_nonneg_right hstep (by positivity)
    _ = aggConst C₀ K * μ⁻¹ * (σ0 * σ0⁻¹ ^ 2) * L * Ys * val ^ 2 := by rw [hσ]; ring
    _ = aggConst C₀ K * μ⁻¹ * σ0 * L * Ys * (σ0⁻¹ ^ 2 * val ^ 2) := by ring

/-- **The shaking term.**  `K μ⁻¹ (μ-1)² σ0 3^{2sH} λ⁻¹` is the other part of the
second frozen term. -/
theorem shaking_term_le {μ σ0 C₀ K W Ys L : ℝ} (hμ : 0 < μ) (hσ0 : 0 < σ0)
    (hC₀ : 1 ≤ C₀) (hK : 0 ≤ K) (hL : 0 ≤ L) (hYs0 : 0 ≤ Ys)
    (hW : W ≤ 3 * C₀ * Ys) :
    K * μ⁻¹ * (μ - 1) ^ 2 * σ0 * (W * L) ≤
      aggConst C₀ K * μ⁻¹ * σ0 * L * Ys * (μ - 1) ^ 2 := by
  have hμinv : (0 : ℝ) < μ⁻¹ := inv_pos.mpr hμ
  have hstep : K * W ≤ aggConst C₀ K * Ys := by
    have h1 : K * W ≤ K * (3 * C₀ * Ys) := mul_le_mul_of_nonneg_left hW hK
    have h2 : K * (3 * C₀ * Ys) ≤ aggConst C₀ K * Ys := by
      linarith only
        [mul_le_mul_of_nonneg_right (three_mul_le_aggConst hC₀ hK) hYs0]
    linarith only [h1, h2]
  calc K * μ⁻¹ * (μ - 1) ^ 2 * σ0 * (W * L)
      = (K * W) * (μ⁻¹ * (μ - 1) ^ 2 * σ0 * L) := by ring
    _ ≤ (aggConst C₀ K * Ys) * (μ⁻¹ * (μ - 1) ^ 2 * σ0 * L) :=
        mul_le_mul_of_nonneg_right hstep (by positivity)
    _ = aggConst C₀ K * μ⁻¹ * σ0 * L * Ys * (μ - 1) ^ 2 := by ring

/-- **The Young split of the mixed gradient term.**  The source's step in ABK26:
`μ⁻¹σ0⁻¹ λ⁻¹ ≤ ½(μ⁻²σ0⁻² + λ⁻²)`, after which the `3^{-2(1-s)H}` damping sends
the first half to the third frozen term and the second half to the fourth. -/
theorem young_gradient_term_le {μ σ0 C₀ K W D2 Dm L gr : ℝ} (hμ : 0 < μ)
    (hσ0 : 0 < σ0) (hC₀ : 1 ≤ C₀) (hK : 0 ≤ K)
    (hW0 : 0 ≤ W) (hD20 : 0 ≤ D2) (hDm1 : Dm ≤ 1) (hD2W : D2 * W ≤ Dm)
    (hmin : (gr * L) ^ 2 * Dm ≤ (C₀ ^ 2)⁻¹ * (max 1 (C₀ ^ 2) * min 1 (gr * L) ^ 2)) :
    K * μ⁻¹ * σ0⁻¹ * (W * L) * (D2 * gr ^ 2) ≤
      aggConst C₀ K * μ⁻¹ ^ 2 * σ0⁻¹ ^ 2 * gr ^ 2 +
        2⁻¹ * aggConst C₀ K * min 1 (gr * L) ^ 2 := by
  have hμinv : (0 : ℝ) < μ⁻¹ := inv_pos.mpr hμ
  have hσinv : (0 : ℝ) < σ0⁻¹ := inv_pos.mpr hσ0
  have hgr2 : (0 : ℝ) ≤ gr ^ 2 := sq_nonneg gr
  have hD2W0 : (0 : ℝ) ≤ D2 * W := mul_nonneg hD20 hW0
  have hAM : μ⁻¹ * σ0⁻¹ * L ≤ 2⁻¹ * ((μ⁻¹ * σ0⁻¹) ^ 2 + L ^ 2) := by
    linarith only [sq_nonneg (μ⁻¹ * σ0⁻¹ - L)]
  have hbase : K * μ⁻¹ * σ0⁻¹ * (W * L) * (D2 * gr ^ 2) ≤
      2⁻¹ * K * ((μ⁻¹ * σ0⁻¹) ^ 2 * gr ^ 2) * (D2 * W) +
        2⁻¹ * K * ((gr * L) ^ 2 * (D2 * W)) := by
    have hco : (0 : ℝ) ≤ K * gr ^ 2 * (D2 * W) := by positivity
    have hstep := mul_le_mul_of_nonneg_right hAM hco
    calc K * μ⁻¹ * σ0⁻¹ * (W * L) * (D2 * gr ^ 2)
        = (μ⁻¹ * σ0⁻¹ * L) * (K * gr ^ 2 * (D2 * W)) := by ring
      _ ≤ (2⁻¹ * ((μ⁻¹ * σ0⁻¹) ^ 2 + L ^ 2)) * (K * gr ^ 2 * (D2 * W)) := hstep
      _ = 2⁻¹ * K * ((μ⁻¹ * σ0⁻¹) ^ 2 * gr ^ 2) * (D2 * W) +
            2⁻¹ * K * ((gr * L) ^ 2 * (D2 * W)) := by ring
  refine hbase.trans ?_
  have hpart1 : 2⁻¹ * K * ((μ⁻¹ * σ0⁻¹) ^ 2 * gr ^ 2) * (D2 * W) ≤
      aggConst C₀ K * μ⁻¹ ^ 2 * σ0⁻¹ ^ 2 * gr ^ 2 := by
    have hle1 : D2 * W ≤ 1 := hD2W.trans hDm1
    have hnn : (0 : ℝ) ≤ (μ⁻¹ * σ0⁻¹) ^ 2 * gr ^ 2 := by positivity
    have hco : (0 : ℝ) ≤ 2⁻¹ * K * ((μ⁻¹ * σ0⁻¹) ^ 2 * gr ^ 2) := by positivity
    have hstep : 2⁻¹ * K * ((μ⁻¹ * σ0⁻¹) ^ 2 * gr ^ 2) * (D2 * W) ≤
        2⁻¹ * K * ((μ⁻¹ * σ0⁻¹) ^ 2 * gr ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hle1 hco
    refine hstep.trans ?_
    have hKA : 2⁻¹ * K ≤ aggConst C₀ K := by
      linarith only [le_aggConst hC₀ hK, hK]
    linarith only [mul_le_mul_of_nonneg_right hKA hnn]
  have hpart2 : 2⁻¹ * K * ((gr * L) ^ 2 * (D2 * W)) ≤
      2⁻¹ * aggConst C₀ K * min 1 (gr * L) ^ 2 := by
    have hX2 : (0 : ℝ) ≤ (gr * L) ^ 2 := sq_nonneg _
    have hstep1 : (gr * L) ^ 2 * (D2 * W) ≤ (gr * L) ^ 2 * Dm :=
      mul_le_mul_of_nonneg_left hD2W hX2
    have hmnn : (0 : ℝ) ≤ min 1 (gr * L) ^ 2 := sq_nonneg _
    have hco : (0 : ℝ) ≤ 2⁻¹ * K := by positivity
    have hcoef : 2⁻¹ * K * ((C₀ ^ 2)⁻¹ * max 1 (C₀ ^ 2)) ≤ 2⁻¹ * aggConst C₀ K := by
      have hbig := min_coeff_le_aggConst hC₀ hK
      linarith only [hbig]
    calc 2⁻¹ * K * ((gr * L) ^ 2 * (D2 * W))
        ≤ 2⁻¹ * K * ((C₀ ^ 2)⁻¹ * (max 1 (C₀ ^ 2) * min 1 (gr * L) ^ 2)) :=
          mul_le_mul_of_nonneg_left (hstep1.trans hmin) hco
      _ = (2⁻¹ * K * ((C₀ ^ 2)⁻¹ * max 1 (C₀ ^ 2))) * min 1 (gr * L) ^ 2 := by ring
      _ ≤ 2⁻¹ * aggConst C₀ K * min 1 (gr * L) ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef hmnn
  linarith only [hpart1, hpart2]

/-- **The pure gradient term.**  `K 3^{-2H} (3^{2sH} λ⁻¹)² ‖∇h‖²` is the fourth
frozen term. -/
theorem pure_gradient_term_le {C₀ K W D2 Dm L gr : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 ≤ K)
    (hD2W2 : D2 * W ^ 2 = Dm)
    (hmin : (gr * L) ^ 2 * Dm ≤ (C₀ ^ 2)⁻¹ * (max 1 (C₀ ^ 2) * min 1 (gr * L) ^ 2)) :
    K * D2 * (W * L) ^ 2 * gr ^ 2 ≤ 2⁻¹ * aggConst C₀ K * min 1 (gr * L) ^ 2 := by
  have heq : K * D2 * (W * L) ^ 2 * gr ^ 2 = K * ((gr * L) ^ 2 * (D2 * W ^ 2)) := by
    ring
  rw [heq, hD2W2]
  have hmnn : (0 : ℝ) ≤ min 1 (gr * L) ^ 2 := sq_nonneg _
  calc K * ((gr * L) ^ 2 * Dm)
      ≤ K * ((C₀ ^ 2)⁻¹ * (max 1 (C₀ ^ 2) * min 1 (gr * L) ^ 2)) :=
        mul_le_mul_of_nonneg_left hmin hK
    _ = (K * ((C₀ ^ 2)⁻¹ * max 1 (C₀ ^ 2))) * min 1 (gr * L) ^ 2 := by ring
    _ ≤ 2⁻¹ * aggConst C₀ K * min 1 (gr * L) ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ hmnn
        linarith only [two_mul_min_coeff_le_aggConst hC₀ hK]

/-- **The arithmetic fold of the aggregation.**  The four aggregated families
are bounded by the four terms of the frozen conclusion. -/
theorem mesoscale_fold {μ σ0 C₀ K L gr val E Wt W D2 Dm Yt Ys : ℝ} (hμ : 0 < μ)
    (hσ0 : 0 < σ0) (hC₀ : 1 ≤ C₀) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hW0 : 0 ≤ W) (hD20 : 0 ≤ D2) (hYt0 : 0 ≤ Yt) (hYs0 : 0 ≤ Ys)
    (hWt : Wt ≤ 3 * C₀ * Yt) (hW : W ≤ 3 * C₀ * Ys) (hDm1 : Dm ≤ 1)
    (hD2W : D2 * W ≤ Dm) (hD2W2 : D2 * W ^ 2 = Dm)
    (hmin : (gr * L) ^ 2 * Dm ≤ (C₀ ^ 2)⁻¹ * (max 1 (C₀ ^ 2) * min 1 (gr * L) ^ 2)) :
    6 * μ⁻¹ * (Wt * E ^ 2) + K * μ⁻¹ * σ0⁻¹ * (W * L) * val ^ 2 +
        (K * μ⁻¹ * (μ - 1) ^ 2 * σ0 * (W * L) +
          K * μ⁻¹ * σ0⁻¹ * (W * L) * (D2 * gr ^ 2) +
          K * D2 * (W * L) ^ 2 * gr ^ 2) ≤
      aggConst C₀ K * μ⁻¹ * Yt * E ^ 2 +
        aggConst C₀ K * μ⁻¹ * σ0 * L * Ys * (σ0⁻¹ ^ 2 * val ^ 2 + (μ - 1) ^ 2) +
        aggConst C₀ K * μ⁻¹ ^ 2 * σ0⁻¹ ^ 2 * gr ^ 2 +
        aggConst C₀ K * min 1 (gr * L) ^ 2 := by
  have h1 := main_term_le (μ := μ) (C₀ := C₀) (K := K) (Wt := Wt) (Yt := Yt) (E := E)
    hμ hC₀ hK hYt0 hWt
  have h2 := value_term_le (μ := μ) (σ0 := σ0) (C₀ := C₀) (K := K) (W := W)
    (Ys := Ys) (L := L) (val := val) hμ hσ0 hC₀ hK hL hYs0 hW
  have h3 := shaking_term_le (μ := μ) (σ0 := σ0) (C₀ := C₀) (K := K) (W := W)
    (Ys := Ys) (L := L) hμ hσ0 hC₀ hK hL hYs0 hW
  have h4 := young_gradient_term_le (μ := μ) (σ0 := σ0) (C₀ := C₀) (K := K) (W := W)
    (D2 := D2) (Dm := Dm) (L := L) (gr := gr) hμ hσ0 hC₀ hK hW0 hD20 hDm1
    hD2W hmin
  have h5 := pure_gradient_term_le (C₀ := C₀) (K := K) (W := W) (D2 := D2) (Dm := Dm)
    (L := L) (gr := gr) hC₀ hK hD2W2 hmin
  have hsplit : aggConst C₀ K * μ⁻¹ * σ0 * L * Ys *
      (σ0⁻¹ ^ 2 * val ^ 2 + (μ - 1) ^ 2) =
      aggConst C₀ K * μ⁻¹ * σ0 * L * Ys * (σ0⁻¹ ^ 2 * val ^ 2) +
        aggConst C₀ K * μ⁻¹ * σ0 * L * Ys * (μ - 1) ^ 2 := by ring
  rw [hsplit]
  linarith only [h1, h2, h3, h4, h5]

end

end Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional
