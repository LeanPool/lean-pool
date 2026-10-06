/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.NormComparison
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# High-contrast homogenization: Analytic.SingularKernel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Gagliardo kernel is uniformly integrable on balls

The fractional seminorm of `e.physical.fractional.norm` is a double
integral whose inner integrand is

`|ψ(x) - ψ(y)|² / |x - y|^{d + 2s}`.

For a Lipschitz field the numerator is `O(‖x - y‖²)`, so the integrand is
dominated by the Riesz-type kernel `‖x - y‖^{2 - (d + 2s)}` with exponent
`e = 2 - (d + 2s) > -d` exactly when `s < 1`.  This module supplies the two
ingredients of that reduction:

* a bound on `∫ ‖x - y‖^e dy` over the ball of radius `D` centred at `x` that is
  **independent of the centre** and finite for every `e > -d`;
* the pointwise domination of the Gagliardo integrand by that kernel.

The integral bound is proved by a dyadic decomposition into the shells
`2^{-k-1} ≤ ‖x - y‖ < 2^{-k}`, on each of which the integrand is bounded by its
value on the inner sphere and the shell is contained in a ball of known volume.
The resulting series is geometric with ratio `2^{-(e + d)} < 1`.  No
polar-coordinate machinery is used, and every bound is centre-independent
because the ambient balls all have the same volume.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The singular kernel is uniformly integrable on balls -/

theorem exists_bound_lintegral_ball_rpow (d : ℕ) {D e : ℝ} (hD : 0 < D)
    (he : -(d : ℝ) < e) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ x : Vec d,
      (∫⁻ y in Metric.ball x D, ENNReal.ofReal (‖x - y‖ ^ e) ∂volume) ≤ B := by
  classical
  rcases le_or_gt 0 e with he0 | he0
  · -- Nonnegative exponent: the integrand is bounded on the ball.
    refine ⟨ENNReal.ofReal (D ^ e) * ENNReal.ofReal ((2 * D) ^ d),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, fun x => ?_⟩
    calc (∫⁻ y in Metric.ball x D, ENNReal.ofReal (‖x - y‖ ^ e) ∂volume)
        ≤ ∫⁻ _ in Metric.ball x D, ENNReal.ofReal (D ^ e) ∂volume := by
          refine lintegral_mono_ae ?_
          filter_upwards [self_mem_ae_restrict (measurableSet_ball (x := x) (ε := D))] with y hy
          refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) ?_ he0)
          have h := Metric.mem_ball'.mp hy
          rw [dist_eq_norm] at h
          exact h.le
      _ = ENNReal.ofReal (D ^ e) * volume (Metric.ball x D) := setLIntegral_const _ _
      _ = ENNReal.ofReal (D ^ e) * ENNReal.ofReal ((2 * D) ^ d) := by
          rw [volume_ball_eq x hD]
  · -- Negative exponent: dyadic shells near the centre, boundedness far away.
    have hene : e ≠ 0 := ne_of_lt he0
    set q : ℝ := 1 / 2 with hqdef
    have hq0 : (0 : ℝ) < q := by rw [hqdef]; norm_num
    have hq1 : q < 1 := by rw [hqdef]; norm_num
    set ρ : ℝ := q ^ e * q ^ d with hρdef
    set Cgeo : ℝ := q ^ e * 2 ^ d with hCdef
    have hqe0 : (0 : ℝ) < q ^ e := Real.rpow_pos_of_pos hq0 e
    have hρ0 : (0 : ℝ) < ρ := by
      rw [hρdef]; exact mul_pos hqe0 (pow_pos hq0 d)
    have hC0 : (0 : ℝ) ≤ Cgeo := by
      rw [hCdef]; positivity
    have hρ1 : ρ < 1 := by
      have hcast : q ^ d = q ^ ((d : ℕ) : ℝ) := (Real.rpow_natCast q d).symm
      have hsum : ρ = q ^ (e + (d : ℝ)) := by
        rw [hρdef, Real.rpow_add hq0, hcast]
      rw [hsum]
      exact Real.rpow_lt_one hq0.le hq1 (by linarith only [he])
    -- The dyadic profile and its geometric law.
    set T : ℕ → ℝ := fun k => (q ^ (k + 1)) ^ e * ((2 * q ^ k) ^ d) with hTdef
    have hTrec : ∀ k : ℕ, T (k + 1) = ρ * T k := by
      intro k
      have h1 : (q ^ (k + 1 + 1)) ^ e = q ^ e * (q ^ (k + 1)) ^ e := by
        have : q ^ (k + 1 + 1) = q * q ^ (k + 1) := by ring
        rw [this, Real.mul_rpow hq0.le (pow_nonneg hq0.le _)]
      have h2 : (2 * q ^ (k + 1)) ^ d = q ^ d * (2 * q ^ k) ^ d := by
        have : (2 : ℝ) * q ^ (k + 1) = q * (2 * q ^ k) := by ring
        rw [this, mul_pow]
      rw [hTdef]
      simp only []
      rw [h1, h2, hρdef]
      ring
    have hTpow : ∀ k : ℕ, T k = Cgeo * ρ ^ k := by
      intro k
      induction k with
      | zero => rw [hTdef, hCdef]; norm_num
      | succ n ih => rw [hTrec n, ih, pow_succ]; ring
    have hT0 : ∀ k : ℕ, 0 ≤ T k := by
      intro k
      rw [hTdef]
      have : (0 : ℝ) ≤ (q ^ (k + 1)) ^ e := Real.rpow_nonneg (pow_nonneg hq0.le _) e
      positivity
    refine ⟨ENNReal.ofReal Cgeo * (1 - ENNReal.ofReal ρ)⁻¹ + ENNReal.ofReal ((2 * D) ^ d), ?_, ?_⟩
    · refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_,
        ENNReal.ofReal_ne_top⟩
      have : ENNReal.ofReal ρ < 1 := ENNReal.ofReal_lt_one.mpr hρ1
      exact ne_of_lt (by rw [ENNReal.inv_lt_top]; exact tsub_pos_iff_lt.mpr this)
    · intro x
      -- Split the ball into the unit ball around `x` and the remainder.
      have hcover :
          Metric.ball x D ⊆ Metric.ball x 1 ∪ (Metric.ball x D \ Metric.ball x 1) := by
        intro y hy
        by_cases h : y ∈ Metric.ball x 1
        · exact Or.inl h
        · exact Or.inr ⟨hy, h⟩
      -- Far part.
      have hfar : (∫⁻ y in Metric.ball x D \ Metric.ball x 1,
          ENNReal.ofReal (‖x - y‖ ^ e) ∂volume) ≤ ENNReal.ofReal ((2 * D) ^ d) := by
        have hmeas : MeasurableSet (Metric.ball x D \ Metric.ball x 1) :=
          measurableSet_ball.diff measurableSet_ball
        calc (∫⁻ y in Metric.ball x D \ Metric.ball x 1,
              ENNReal.ofReal (‖x - y‖ ^ e) ∂volume)
            ≤ ∫⁻ _ in Metric.ball x D \ Metric.ball x 1, (1 : ℝ≥0∞) ∂volume := by
              refine lintegral_mono_ae ?_
              filter_upwards [self_mem_ae_restrict hmeas] with y hy
              have h1 : (1 : ℝ) ≤ ‖x - y‖ := by
                have h := hy.2
                rw [Metric.mem_ball'] at h
                push Not at h
                rwa [dist_eq_norm] at h
              calc ENNReal.ofReal (‖x - y‖ ^ e)
                  ≤ ENNReal.ofReal 1 :=
                    ENNReal.ofReal_le_ofReal
                      (Real.rpow_le_one_of_one_le_of_nonpos h1 he0.le)
                _ = 1 := ENNReal.ofReal_one
          _ = 1 * volume (Metric.ball x D \ Metric.ball x 1) := setLIntegral_const _ _
          _ ≤ 1 * volume (Metric.ball x D) :=
              mul_le_mul' (le_refl _) (measure_mono Set.sdiff_subset)
          _ = ENNReal.ofReal ((2 * D) ^ d) := by rw [volume_ball_eq x hD, one_mul]
      -- Near part: dyadic shells.
      have hshell : ∀ k : ℕ,
          (∫⁻ y in Metric.ball x (q ^ k) \ Metric.ball x (q ^ (k + 1)),
            ENNReal.ofReal (‖x - y‖ ^ e) ∂volume) ≤ ENNReal.ofReal (T k) := by
        intro k
        have hr1 : (0 : ℝ) < q ^ (k + 1) := pow_pos hq0 _
        have hr0 : (0 : ℝ) < q ^ k := pow_pos hq0 _
        have hmeas : MeasurableSet (Metric.ball x (q ^ k) \ Metric.ball x (q ^ (k + 1))) :=
          measurableSet_ball.diff measurableSet_ball
        calc (∫⁻ y in Metric.ball x (q ^ k) \ Metric.ball x (q ^ (k + 1)),
              ENNReal.ofReal (‖x - y‖ ^ e) ∂volume)
            ≤ ∫⁻ _ in Metric.ball x (q ^ k) \ Metric.ball x (q ^ (k + 1)),
                ENNReal.ofReal ((q ^ (k + 1)) ^ e) ∂volume := by
              refine lintegral_mono_ae ?_
              filter_upwards [self_mem_ae_restrict hmeas] with y hy
              have h2 : q ^ (k + 1) ≤ ‖x - y‖ := by
                have h := hy.2
                rw [Metric.mem_ball'] at h
                push Not at h
                rwa [dist_eq_norm] at h
              exact ENNReal.ofReal_le_ofReal
                (Real.rpow_le_rpow_of_nonpos hr1 h2 he0.le)
          _ = ENNReal.ofReal ((q ^ (k + 1)) ^ e) *
                volume (Metric.ball x (q ^ k) \ Metric.ball x (q ^ (k + 1))) :=
              setLIntegral_const _ _
          _ ≤ ENNReal.ofReal ((q ^ (k + 1)) ^ e) * volume (Metric.ball x (q ^ k)) :=
              mul_le_mul' (le_refl _) (measure_mono Set.sdiff_subset)
          _ = ENNReal.ofReal ((q ^ (k + 1)) ^ e) * ENNReal.ofReal ((2 * q ^ k) ^ d) := by
              rw [volume_ball_eq x hr0]
          _ = ENNReal.ofReal (T k) := by
              have hTk : T k = (q ^ (k + 1)) ^ e * ((2 * q ^ k) ^ d) := rfl
              rw [hTk, ENNReal.ofReal_mul (Real.rpow_nonneg hr1.le e)]
      have hcov2 : Metric.ball x 1 ⊆ ({x} : Set (Vec d)) ∪
          ⋃ k : ℕ, (Metric.ball x (q ^ k) \ Metric.ball x (q ^ (k + 1))) := by
        intro y hy
        by_cases hxy : y = x
        · exact Or.inl (by simp [hxy])
        · right
          have hdpos : 0 < dist y x := dist_pos.mpr hxy
          have hex : ∃ n : ℕ, q ^ (n + 1) ≤ dist y x := by
            obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hdpos hq1
            refine ⟨n, ?_⟩
            have hmono : q ^ (n + 1) ≤ q ^ n := by
              rw [pow_succ]
              have hp := pow_pos hq0 n
              have : q ^ n * q ≤ q ^ n * 1 := by
                exact mul_le_mul_of_nonneg_left hq1.le hp.le
              linarith only [this]
            linarith only [hmono, hn]
          have hk1 : q ^ (Nat.find hex + 1) ≤ dist y x := Nat.find_spec hex
          have hk0 : dist y x < q ^ (Nat.find hex) := by
            rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
            · rw [h0, pow_zero]
              exact Metric.mem_ball.mp hy
            · have hlt : Nat.find hex - 1 < Nat.find hex := by omega
              have hmin := Nat.find_min hex hlt
              push Not at hmin
              have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := by omega
              rwa [hsucc] at hmin
          refine Set.mem_iUnion.mpr ⟨Nat.find hex, Metric.mem_ball.mpr hk0, ?_⟩
          simp only [Metric.mem_ball, not_lt]
          exact hk1
      have hsing : (∫⁻ y in ({x} : Set (Vec d)),
          ENNReal.ofReal (‖x - y‖ ^ e) ∂volume) = 0 := by
        have heqon : Set.EqOn (fun y : Vec d => ENNReal.ofReal (‖x - y‖ ^ e))
            (fun _ : Vec d => (0 : ℝ≥0∞)) ({x} : Set (Vec d)) := by
          intro z hz
          have hz' : z = x := hz
          subst hz'
          simp [Real.zero_rpow hene]
        rw [setLIntegral_congr_fun (measurableSet_singleton x) heqon, lintegral_zero]
      have hnear : (∫⁻ y in Metric.ball x 1, ENNReal.ofReal (‖x - y‖ ^ e) ∂volume)
          ≤ ENNReal.ofReal Cgeo * (1 - ENNReal.ofReal ρ)⁻¹ := by
        calc (∫⁻ y in Metric.ball x 1, ENNReal.ofReal (‖x - y‖ ^ e) ∂volume)
            ≤ ∫⁻ y in ({x} : Set (Vec d)) ∪
                ⋃ k : ℕ, (Metric.ball x (q ^ k) \ Metric.ball x (q ^ (k + 1))),
                ENNReal.ofReal (‖x - y‖ ^ e) ∂volume := lintegral_mono_set hcov2
          _ ≤ (∫⁻ y in ({x} : Set (Vec d)), ENNReal.ofReal (‖x - y‖ ^ e) ∂volume) +
                ∫⁻ y in ⋃ k : ℕ, (Metric.ball x (q ^ k) \ Metric.ball x (q ^ (k + 1))),
                  ENNReal.ofReal (‖x - y‖ ^ e) ∂volume := lintegral_union_le _ _ _
          _ = ∫⁻ y in ⋃ k : ℕ, (Metric.ball x (q ^ k) \ Metric.ball x (q ^ (k + 1))),
                  ENNReal.ofReal (‖x - y‖ ^ e) ∂volume := by rw [hsing, zero_add]
          _ ≤ ∑' k : ℕ, ∫⁻ y in (Metric.ball x (q ^ k) \ Metric.ball x (q ^ (k + 1))),
                  ENNReal.ofReal (‖x - y‖ ^ e) ∂volume := lintegral_iUnion_le _ _
          _ ≤ ∑' k : ℕ, ENNReal.ofReal (T k) := ENNReal.tsum_le_tsum hshell
          _ = ∑' k : ℕ, ENNReal.ofReal Cgeo * (ENNReal.ofReal ρ) ^ k := by
              refine tsum_congr fun k => ?_
              rw [hTpow k, ENNReal.ofReal_mul hC0, ENNReal.ofReal_pow hρ0.le]
          _ = ENNReal.ofReal Cgeo * ∑' k : ℕ, (ENNReal.ofReal ρ) ^ k :=
              ENNReal.tsum_mul_left
          _ = ENNReal.ofReal Cgeo * (1 - ENNReal.ofReal ρ)⁻¹ := by
              rw [ENNReal.tsum_geometric]
      calc (∫⁻ y in Metric.ball x D, ENNReal.ofReal (‖x - y‖ ^ e) ∂volume)
          ≤ ∫⁻ y in Metric.ball x 1 ∪ (Metric.ball x D \ Metric.ball x 1),
              ENNReal.ofReal (‖x - y‖ ^ e) ∂volume := lintegral_mono_set hcover
        _ ≤ (∫⁻ y in Metric.ball x 1, ENNReal.ofReal (‖x - y‖ ^ e) ∂volume) +
              ∫⁻ y in Metric.ball x D \ Metric.ball x 1,
                ENNReal.ofReal (‖x - y‖ ^ e) ∂volume := lintegral_union_le _ _ _
        _ ≤ ENNReal.ofReal Cgeo * (1 - ENNReal.ofReal ρ)⁻¹ + ENNReal.ofReal ((2 * D) ^ d) :=
            add_le_add hnear hfar

/-! ## The pointwise bound on the Gagliardo kernel -/

theorem gagliardo_kernel_le {ψ : Vec d → Vec d} {L : ℝ}
    (hlip : ∀ x y, ‖ψ x - ψ y‖ ≤ L * ‖x - y‖) {p : ℝ} (hp : 0 ≤ p) (x y : Vec d) :
    vecNormSq (ψ x - ψ y) / Real.sqrt (vecNormSq (x - y)) ^ p
      ≤ ((d : ℝ) * L ^ 2) * ‖x - y‖ ^ (2 - p) := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have ht0 : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
  have hnum : vecNormSq (ψ x - ψ y) ≤ ((d : ℝ) * L ^ 2) * ‖x - y‖ ^ 2 := by
    have h1 : vecNormSq (ψ x - ψ y) ≤ (d : ℝ) * ‖ψ x - ψ y‖ ^ 2 :=
      vecNormSq_le_dim_mul_norm_sq _
    have h2 : ‖ψ x - ψ y‖ ≤ L * ‖x - y‖ := hlip x y
    have hn : (0 : ℝ) ≤ ‖ψ x - ψ y‖ := norm_nonneg _
    have h3 : ‖ψ x - ψ y‖ ^ 2 ≤ (L * ‖x - y‖) ^ 2 := by
      calc ‖ψ x - ψ y‖ ^ 2 = ‖ψ x - ψ y‖ * ‖ψ x - ψ y‖ := pow_two _
        _ ≤ (L * ‖x - y‖) * (L * ‖x - y‖) := mul_self_le_mul_self hn h2
        _ = (L * ‖x - y‖) ^ 2 := (pow_two _).symm
    calc vecNormSq (ψ x - ψ y) ≤ (d : ℝ) * ‖ψ x - ψ y‖ ^ 2 := h1
      _ ≤ (d : ℝ) * (L * ‖x - y‖) ^ 2 := mul_le_mul_of_nonneg_left h3 hd0
      _ = ((d : ℝ) * L ^ 2) * ‖x - y‖ ^ 2 := by ring
  have hRHS0 : (0 : ℝ) ≤ ((d : ℝ) * L ^ 2) * ‖x - y‖ ^ (2 - p) := by
    have : (0 : ℝ) ≤ ‖x - y‖ ^ (2 - p) := Real.rpow_nonneg ht0 _
    have hdL : (0 : ℝ) ≤ (d : ℝ) * L ^ 2 := by positivity
    exact mul_nonneg hdL this
  rcases eq_or_lt_of_le ht0 with ht | ht
  · -- `x = y`: both sides degenerate, and the left-hand side vanishes.
    have hxy : x - y = 0 := norm_eq_zero.mp ht.symm
    have hψ0 : ψ x - ψ y = 0 := by
      have h := hlip x y
      rw [hxy, norm_zero, mul_zero] at h
      exact norm_le_zero_iff.mp h
    rw [hψ0, show vecNormSq (0 : Vec d) = 0 from vecNormSq_eq_zero_iff.mpr rfl, zero_div]
    exact hRHS0
  · have hden1 : ‖x - y‖ ^ p ≤ Real.sqrt (vecNormSq (x - y)) ^ p :=
      Real.rpow_le_rpow ht0 (norm_le_sqrt_vecNormSq (x - y)) hp
    have htp : (0 : ℝ) < ‖x - y‖ ^ p := Real.rpow_pos_of_pos ht p
    have hnum0 : (0 : ℝ) ≤ ((d : ℝ) * L ^ 2) * ‖x - y‖ ^ 2 := by positivity
    have hstep : vecNormSq (ψ x - ψ y) / Real.sqrt (vecNormSq (x - y)) ^ p
        ≤ (((d : ℝ) * L ^ 2) * ‖x - y‖ ^ 2) / (‖x - y‖ ^ p) :=
      div_le_div₀ hnum0 hnum htp hden1
    have hcalc : (((d : ℝ) * L ^ 2) * ‖x - y‖ ^ 2) / (‖x - y‖ ^ p)
        = ((d : ℝ) * L ^ 2) * ‖x - y‖ ^ (2 - p) := by
      have h2 : ‖x - y‖ ^ (2 : ℝ) = ‖x - y‖ ^ (2 : ℕ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [Real.rpow_sub ht, ← h2]
      ring
    exact hstep.trans_eq hcalc

end

end HighContrast
end HCPolySupport
