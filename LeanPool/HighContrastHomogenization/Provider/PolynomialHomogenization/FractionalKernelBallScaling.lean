/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.SingularKernel

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.FractionalKernelBallScaling

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Radius-sharp integrability of the interior fractional kernel

The shrinking-shell proof retains the radius in every shell, giving the
homogeneous factor `r^(e+d)`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A negative Riesz power above the dimensional threshold has its sharp
homogeneous integral bound on every ball. -/
theorem exists_bound_lintegral_ball_rpow_scaled (d : ℕ) {e : ℝ}
    (hed : -(d : ℝ) < e) (he0 : e < 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (x : Vec d) {r : ℝ}, 0 < r →
      (∫⁻ y in Metric.ball x r,
        ENNReal.ofReal (‖x - y‖ ^ e) ∂volume) ≤
          C * ENNReal.ofReal (r ^ (e + (d : ℝ))) := by
  classical
  let q : ℝ := 1 / 2
  let ratio : ℝ := q ^ (e + (d : ℝ))
  let Cbase : ℝ := q ^ e * 2 ^ d
  have hq0 : 0 < q := by dsimp only [q]; norm_num
  have hq1 : q < 1 := by dsimp only [q]; norm_num
  have hratio0 : 0 < ratio := by
    dsimp only [ratio]
    exact Real.rpow_pos_of_pos hq0 _
  have hratio1 : ratio < 1 := by
    dsimp only [ratio]
    exact Real.rpow_lt_one hq0.le hq1 (by linarith only [hed])
  have hCbase0 : 0 ≤ Cbase := by
    dsimp only [Cbase]
    positivity
  let C : ℝ≥0∞ :=
    ENNReal.ofReal Cbase * (1 - ENNReal.ofReal ratio)⁻¹
  refine ⟨C, ?_, ?_⟩
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
      have hratio : ENNReal.ofReal ratio < 1 :=
        ENNReal.ofReal_lt_one.mpr hratio1
      rw [ENNReal.inv_ne_top]
      exact ne_of_gt ((tsub_pos_iff_lt).2 hratio))
  · intro x r hr
    let shell : ℕ → Set (Vec d) := fun k =>
      Metric.ball x (r * q ^ k) \ Metric.ball x (r * q ^ (k + 1))
    let T : ℕ → ℝ := fun k =>
      (r * q ^ (k + 1)) ^ e * (2 * (r * q ^ k)) ^ d
    have hTrec : ∀ k : ℕ, T (k + 1) = ratio * T k := by
      intro k
      have hrq0 : 0 ≤ r * q ^ (k + 1) := by positivity
      have h1 : (r * q ^ (k + 1 + 1)) ^ e =
          q ^ e * (r * q ^ (k + 1)) ^ e := by
        have heq : r * q ^ (k + 1 + 1) = q * (r * q ^ (k + 1)) := by
          ring
        rw [heq, Real.mul_rpow hq0.le hrq0]
      have h2 : (2 * (r * q ^ (k + 1))) ^ d =
          q ^ d * (2 * (r * q ^ k)) ^ d := by
        have heq : 2 * (r * q ^ (k + 1)) = q * (2 * (r * q ^ k)) := by
          ring
        rw [heq, mul_pow]
      have hqd : q ^ d = q ^ ((d : ℕ) : ℝ) :=
        (Real.rpow_natCast q d).symm
      have hcoef : q ^ e * q ^ d = ratio := by
        rw [hqd, ← Real.rpow_add hq0]
      dsimp only [T]
      rw [h1, h2]
      calc
        q ^ e * (r * q ^ (k + 1)) ^ e *
            (q ^ d * (2 * (r * q ^ k)) ^ d) =
            (q ^ e * q ^ d) *
              ((r * q ^ (k + 1)) ^ e *
                (2 * (r * q ^ k)) ^ d) := by ring
        _ = ratio * ((r * q ^ (k + 1)) ^ e *
              (2 * (r * q ^ k)) ^ d) := by rw [hcoef]
    have hTbase : T 0 = Cbase * r ^ (e + (d : ℝ)) := by
      have hrd : r ^ d = r ^ ((d : ℕ) : ℝ) :=
        (Real.rpow_natCast r d).symm
      dsimp only [T, Cbase]
      norm_num
      rw [mul_pow, hrd]
      calc
        (r * q) ^ e * (2 ^ d * r ^ (d : ℝ)) =
            (q ^ e * 2 ^ d) * (r ^ e * r ^ (d : ℝ)) := by
          rw [Real.mul_rpow hr.le hq0.le]
          ring
        _ = (q ^ e * 2 ^ d) * r ^ (e + (d : ℝ)) := by
          rw [Real.rpow_add hr]
    have hTpow : ∀ k : ℕ,
        T k = (Cbase * r ^ (e + (d : ℝ))) * ratio ^ k := by
      intro k
      induction k with
      | zero => simpa only [pow_zero, mul_one] using hTbase
      | succ k ih => rw [hTrec k, ih, pow_succ]; ring
    have hT0 : ∀ k : ℕ, 0 ≤ T k := by
      intro k
      dsimp only [T]
      positivity
    have hshell : ∀ k : ℕ,
        (∫⁻ y in shell k,
          ENNReal.ofReal (‖x - y‖ ^ e) ∂volume) ≤ ENNReal.ofReal (T k) := by
      intro k
      have hinner : 0 < r * q ^ (k + 1) := mul_pos hr (pow_pos hq0 _)
      have houter : 0 < r * q ^ k := mul_pos hr (pow_pos hq0 _)
      have hmeas : MeasurableSet (shell k) :=
        measurableSet_ball.diff measurableSet_ball
      calc
        (∫⁻ y in shell k,
            ENNReal.ofReal (‖x - y‖ ^ e) ∂volume) ≤
            ∫⁻ _y in shell k,
              ENNReal.ofReal ((r * q ^ (k + 1)) ^ e) ∂volume := by
          refine lintegral_mono_ae ?_
          filter_upwards [self_mem_ae_restrict hmeas] with y hy
          have hdist : r * q ^ (k + 1) ≤ ‖x - y‖ := by
            have h := hy.2
            rw [Metric.mem_ball'] at h
            push Not at h
            rwa [dist_eq_norm] at h
          exact ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow_of_nonpos hinner hdist he0.le)
        _ = ENNReal.ofReal ((r * q ^ (k + 1)) ^ e) *
            volume (shell k) := setLIntegral_const _ _
        _ ≤ ENNReal.ofReal ((r * q ^ (k + 1)) ^ e) *
            volume (Metric.ball x (r * q ^ k)) :=
          mul_le_mul' le_rfl (measure_mono sdiff_subset)
        _ = ENNReal.ofReal ((r * q ^ (k + 1)) ^ e) *
            ENNReal.ofReal ((2 * (r * q ^ k)) ^ d) := by
          rw [volume_ball_eq x houter]
        _ = ENNReal.ofReal (T k) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hinner.le e)]
    have hcover : Metric.ball x r ⊆ ({x} : Set (Vec d)) ∪ ⋃ k, shell k := by
      intro y hy
      by_cases hxy : y = x
      · exact Or.inl (by simp [hxy])
      · right
        have hdist0 : 0 < dist y x := dist_pos.mpr hxy
        have hex : ∃ n : ℕ, r * q ^ (n + 1) ≤ dist y x := by
          obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hdist0 hr) hq1
          refine ⟨n, ?_⟩
          have hqn : q ^ (n + 1) ≤ q ^ n := by
            rw [pow_succ]
            exact mul_le_of_le_one_right (pow_nonneg hq0.le _) hq1.le
          have hscaled : r * q ^ n < dist y x := by
            simpa only [mul_comm] using (lt_div_iff₀ hr).mp hn
          exact (mul_le_mul_of_nonneg_left hqn hr.le).trans hscaled.le
        let n := Nat.find hex
        have hninner : r * q ^ (n + 1) ≤ dist y x := Nat.find_spec hex
        have hnouter : dist y x < r * q ^ n := by
          rcases Nat.eq_zero_or_pos n with hn | hn
          · simpa only [hn, pow_zero, mul_one] using Metric.mem_ball.mp hy
          · have hmin := Nat.find_min hex (Nat.pred_lt hn.ne')
            push Not at hmin
            have hnid : n.pred + 1 = n := Nat.succ_pred_eq_of_pos hn
            rwa [hnid] at hmin
        refine Set.mem_iUnion.mpr ⟨n, Metric.mem_ball.mpr hnouter, ?_⟩
        simpa only [Metric.mem_ball, not_lt] using hninner
    have hsing : (∫⁻ y in ({x} : Set (Vec d)),
        ENNReal.ofReal (‖x - y‖ ^ e) ∂volume) = 0 := by
      have heqon : Set.EqOn (fun y : Vec d => ENNReal.ofReal (‖x - y‖ ^ e))
          (fun _ => (0 : ℝ≥0∞)) ({x} : Set (Vec d)) := by
        intro z hz
        subst z
        simp [Real.zero_rpow (ne_of_lt he0)]
      rw [setLIntegral_congr_fun (measurableSet_singleton x) heqon,
        lintegral_zero]
    calc
      (∫⁻ y in Metric.ball x r,
          ENNReal.ofReal (‖x - y‖ ^ e) ∂volume) ≤
          ∫⁻ y in ({x} : Set (Vec d)) ∪ ⋃ k, shell k,
            ENNReal.ofReal (‖x - y‖ ^ e) ∂volume := lintegral_mono_set hcover
      _ ≤ (∫⁻ y in ({x} : Set (Vec d)),
            ENNReal.ofReal (‖x - y‖ ^ e) ∂volume) +
          ∫⁻ y in ⋃ k, shell k,
            ENNReal.ofReal (‖x - y‖ ^ e) ∂volume := lintegral_union_le _ _ _
      _ = ∫⁻ y in ⋃ k, shell k,
            ENNReal.ofReal (‖x - y‖ ^ e) ∂volume := by rw [hsing, zero_add]
      _ ≤ ∑' k, ∫⁻ y in shell k,
            ENNReal.ofReal (‖x - y‖ ^ e) ∂volume := lintegral_iUnion_le _ _
      _ ≤ ∑' k, ENNReal.ofReal (T k) := ENNReal.tsum_le_tsum hshell
      _ = ∑' k, (ENNReal.ofReal Cbase *
            ENNReal.ofReal (r ^ (e + (d : ℝ)))) *
          (ENNReal.ofReal ratio) ^ k := by
        refine tsum_congr fun k => ?_
        rw [hTpow k, ENNReal.ofReal_mul
          (mul_nonneg hCbase0 (Real.rpow_nonneg hr.le _)),
          ENNReal.ofReal_mul hCbase0, ENNReal.ofReal_pow hratio0.le]
      _ = (ENNReal.ofReal Cbase *
            ENNReal.ofReal (r ^ (e + (d : ℝ)))) *
          ∑' k, (ENNReal.ofReal ratio) ^ k := ENNReal.tsum_mul_left
      _ = C * ENNReal.ofReal (r ^ (e + (d : ℝ))) := by
        rw [ENNReal.tsum_geometric]
        dsimp only [C]
        ac_rfl

end

end HighContrast
end HCPolySupport
