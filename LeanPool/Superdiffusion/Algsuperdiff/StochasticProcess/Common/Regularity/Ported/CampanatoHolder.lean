/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.CampanatoTelescope

/-!
# CampanatoHolder

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Campanato-to-Hölder conversion on `[1/2,1)`

The exponent restriction bounds the order-`alpha⁻¹` Campanato constant by a
numerical constant.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport Filter Topology
open Algsuperdiff.Section4.Support
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-- The common constant in the local small-contrast Hölder estimate. -/
def smallContrastLocalHolderConstant (d : ℕ) : ℝ :=
  16 * ballVolumePrice 2 d * smallContrastCampanatoConstant d +
    12 * ballVolumePrice 3 d * smallContrastCampanatoConstant d

theorem smallContrastLocalHolderConstant_nonneg (d : ℕ) :
    0 ≤ smallContrastLocalHolderConstant d := by
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (ballVolumePrice_nonneg 2 d))
      (smallContrastCampanatoConstant_nonneg d))
    (mul_nonneg (mul_nonneg (by norm_num) (ballVolumePrice_nonneg 3 d))
      (smallContrastCampanatoConstant_nonneg d))

private theorem metricBall_triple_dyadic_subset_unit [NeZero d]
    {x : Vec d} (hx : x ∈ smallContrastBall d (1 / 2)) (n : ℕ) :
    Metric.ball x (3 * smallContrastDyadicRadius (smallContrastCampanatoRadius d) n) ⊆
      smallContrastUnitBall d := by
  have hR := smallContrastCampanatoRadius_pos (d := d)
  let r := smallContrastDyadicRadius (smallContrastCampanatoRadius d) n
  have hr : 0 < r := smallContrastDyadicRadius_pos hR n
  have hrle : r ≤ smallContrastCampanatoRadius d := smallContrastDyadicRadius_le hR.le n
  have hdr : (d : ℝ) * (3 * r) < 1 / 2 := by
    have hdpos : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    have hthree := three_mul_dimension_mul_campanatoRadius (d := d)
    have hle : 3 * (d : ℝ) * r ≤
        3 * (d : ℝ) * smallContrastCampanatoRadius d :=
      mul_le_mul_of_nonneg_left hrle (mul_nonneg (by norm_num) hdpos.le)
    linarith only [hle, hthree]
  exact subset_trans (metricBall_subset_euclideanBall_dimension x (3 * r))
    (subset_trans (euclideanBall_subset_euclideanBall
      (mul_nonneg (Nat.cast_nonneg d) (by positivity : 0 ≤ 3 * r)) hdr)
      (euclideanBall_half_subset_unit_of_mem_half hx))

private theorem abs_dyadicAverage_sub_tripleAverage_le [NeZero d]
    {alpha K : ℝ} {u : H1Function (smallContrastUnitBall d)}
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1) (hK : 0 ≤ K)
    (hcamp : HasSmallContrastBallCampanatoBound alpha K u)
    {x y : Vec d} (hx : x ∈ smallContrastBall d (1 / 2))
    (n : ℕ)
    (hsub : Metric.ball y
        (smallContrastDyadicRadius (smallContrastCampanatoRadius d) n) ⊆
      Metric.ball x
        (3 * smallContrastDyadicRadius (smallContrastCampanatoRadius d) n)) :
    |smallContrastCampanatoAverage (d := d) u.toFun y n -
        volumeAverage (Metric.ball x
          (3 * smallContrastDyadicRadius (smallContrastCampanatoRadius d) n)) u.toFun| ≤
      3 * ballVolumePrice 3 d * smallContrastCampanatoConstant d * K *
        smallContrastDyadicRadius (smallContrastCampanatoRadius d) n ^ alpha := by
  let r := smallContrastDyadicRadius (smallContrastCampanatoRadius d) n
  let W := Metric.ball x (3 * r)
  let V := Metric.ball y r
  have hR := smallContrastCampanatoRadius_pos (d := d)
  have hr : 0 < r := smallContrastDyadicRadius_pos hR n
  have h3r : 0 < 3 * r := by positivity
  have hWunit := metricBall_triple_dyadic_subset_unit hx n
  have huW : MemLp u.toFun 2 (volume.restrict W) :=
    u.memL2.mono_measure (Measure.restrict_mono hWunit le_rfl)
  have huV : MemLp u.toFun 2 (volume.restrict V) :=
    huW.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hWtop : volume W ≠ ⊤ := by
    dsimp only [W]
    rw [Real.volume_pi_ball x h3r]
    exact ENNReal.ofReal_ne_top
  have hVtop : volume V ≠ ⊤ := by
    dsimp only [V]
    rw [Real.volume_pi_ball y hr]
    exact ENNReal.ofReal_ne_top
  let : IsFiniteMeasure (volume.restrict W) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hWtop⟩
  let : IsFiniteMeasure (volume.restrict V) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hVtop⟩
  have hdiffW : MemLp (fun z => u.toFun z - volumeAverage W u.toFun) 2
      (volume.restrict W) := huW.sub (memLp_const _)
  have hdiffV : MemLp (fun z => u.toFun z - volumeAverage W u.toFun) 2
      (volume.restrict V) := huV.sub (memLp_const _)
  have hmean := abs_volumeAverage_sub_windowAverage_le
    (measurableSet_ball : MeasurableSet V) hsub
    (volume_metricBall_toReal_pos x h3r) (volume_metricBall_toReal_pos y hr)
    hVtop (huV.integrable one_le_two) hdiffV.integrable_sq hdiffW.integrable_sq
  rw [sqrt_volume_metricBall_ratio (d := d) x y
    (R := 3 * r) (r := r) (k := 3) hr (by norm_num) (by ring)] at hmean
  have hosc := hcamp x hx (3 * r) h3r
    (by
      have := smallContrastDyadicRadius_le hR.le n
      exact mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 3) :
        3 * r ≤ 3 * smallContrastCampanatoRadius d)
  have hraw := hmean.trans (mul_le_mul_of_nonneg_left hosc
    (ballVolumePrice_nonneg 3 d))
  have hthreepow : (3 * r) ^ alpha ≤ 3 * r ^ alpha := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hr.le]
    have h3alpha : (3 : ℝ) ^ alpha ≤ 3 := by
      exact Real.rpow_le_self_of_one_le (by norm_num) halpha.2.le
    exact mul_le_mul_of_nonneg_right h3alpha (Real.rpow_nonneg hr.le _)
  have hcoef : 0 ≤ ballVolumePrice 3 d * smallContrastCampanatoConstant d * K :=
    mul_nonneg
      (mul_nonneg (ballVolumePrice_nonneg 3 d)
        (smallContrastCampanatoConstant_nonneg d)) hK
  refine hraw.trans ?_
  dsimp only [smallContrastCampanatoAverage, W, V, r] at hraw ⊢
  calc
    ballVolumePrice 3 d *
          (smallContrastCampanatoConstant d * K * (3 * r) ^ alpha) ≤
        ballVolumePrice 3 d * smallContrastCampanatoConstant d * K *
          (3 * r ^ alpha) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hthreepow hcoef
    _ = 3 * ballVolumePrice 3 d * smallContrastCampanatoConstant d * K *
        r ^ alpha := by ring

private theorem metricBall_y_subset_triple_x
    {x y : Vec d} {r : ℝ} (hr : 0 < r) (hxy : ‖x - y‖ ≤ r) :
    Metric.ball y r ⊆ Metric.ball x (3 * r) := by
  apply Metric.ball_subset_ball'
  rw [dist_eq_norm, norm_sub_rev]
  linarith only [hxy, hr]

/-- The representative is Hölder for separations at most the fixed telescope
radius. -/
theorem local_holder_smallContrastCampanatoRepresentative [NeZero d]
    {alpha K : ℝ} {u : H1Function (smallContrastUnitBall d)}
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1) (hK : 0 ≤ K)
    (hcamp : HasSmallContrastBallCampanatoBound alpha K u)
    {x y : Vec d} (hx : x ∈ smallContrastBall d (1 / 2))
    (hy : y ∈ smallContrastBall d (1 / 2))
    (hxy : ‖x - y‖ ≤ smallContrastCampanatoRadius d) :
    |smallContrastCampanatoRepresentative (d := d) u.toFun x -
        smallContrastCampanatoRepresentative (d := d) u.toFun y| ≤
      smallContrastLocalHolderConstant d * K * ‖x - y‖ ^ alpha := by
  by_cases hzero : ‖x - y‖ = 0
  · have hxeq : x = y := sub_eq_zero.mp (norm_eq_zero.mp hzero)
    subst y
    simp only [sub_self, abs_zero, norm_zero,
      Real.zero_rpow (ne_of_gt (lt_of_lt_of_le (by norm_num) halpha.1)), mul_zero]
    exact le_rfl
  have hrho : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
  obtain ⟨n, hnlo, hnhi⟩ := exists_smallContrastDyadicRadius_bracket
    (smallContrastCampanatoRadius_pos (d := d)) hrho hxy
  let r := smallContrastDyadicRadius (smallContrastCampanatoRadius d) n
  have hr : 0 < r := smallContrastDyadicRadius_pos
    (smallContrastCampanatoRadius_pos (d := d)) n
  have htailx := dist_average_representative_le halpha hK hcamp hx n
  have htaily := dist_average_representative_le halpha hK hcamp hy n
  have hsubx : Metric.ball x r ⊆ Metric.ball x (3 * r) :=
    Metric.ball_subset_ball (by linarith only [hr])
  have hsuby : Metric.ball y r ⊆ Metric.ball x (3 * r) :=
    metricBall_y_subset_triple_x hr hnhi
  have hmeanx := abs_dyadicAverage_sub_tripleAverage_le
    halpha hK hcamp hx n hsubx
  have hmeany := abs_dyadicAverage_sub_tripleAverage_le
    halpha hK hcamp hx n hsuby
  have htri : |smallContrastCampanatoRepresentative (d := d) u.toFun x -
        smallContrastCampanatoRepresentative (d := d) u.toFun y| ≤
      dist (smallContrastCampanatoAverage (d := d) u.toFun x n)
          (smallContrastCampanatoRepresentative (d := d) u.toFun x) +
        |smallContrastCampanatoAverage (d := d) u.toFun x n -
          volumeAverage (Metric.ball x (3 * r)) u.toFun| +
        |smallContrastCampanatoAverage (d := d) u.toFun y n -
          volumeAverage (Metric.ball x (3 * r)) u.toFun| +
        dist (smallContrastCampanatoAverage (d := d) u.toFun y n)
          (smallContrastCampanatoRepresentative (d := d) u.toFun y) := by
    rw [Real.dist_eq, Real.dist_eq]
    let a := -(smallContrastCampanatoAverage (d := d) u.toFun x n -
      smallContrastCampanatoRepresentative (d := d) u.toFun x)
    let b := smallContrastCampanatoAverage (d := d) u.toFun x n -
      volumeAverage (Metric.ball x (3 * r)) u.toFun
    let c := -(smallContrastCampanatoAverage (d := d) u.toFun y n -
      volumeAverage (Metric.ball x (3 * r)) u.toFun)
    let e := smallContrastCampanatoAverage (d := d) u.toFun y n -
      smallContrastCampanatoRepresentative (d := d) u.toFun y
    have hid : smallContrastCampanatoRepresentative (d := d) u.toFun x -
        smallContrastCampanatoRepresentative (d := d) u.toFun y = a + b + c + e := by
      dsimp only [a, b, c, e]
      ring
    rw [hid]
    calc
      |a + b + c + e| ≤ |a + b + c| + |e| := abs_add_le _ _
      _ ≤ (|a| + |b| + |c|) + |e| :=
        add_le_add (abs_add_three a b c) le_rfl
      _ = _ := by dsimp only [a, b, c, e]; rw [abs_neg, abs_neg]
  have hcollect : |smallContrastCampanatoRepresentative (d := d) u.toFun x -
        smallContrastCampanatoRepresentative (d := d) u.toFun y| ≤
      (8 * ballVolumePrice 2 d * smallContrastCampanatoConstant d +
        6 * ballVolumePrice 3 d * smallContrastCampanatoConstant d) * K *
          r ^ alpha := by
    dsimp only [r] at hmeanx hmeany htailx htaily ⊢
    linarith only [htri, htailx, htaily, hmeanx, hmeany]
  have hrle : r ≤ 2 * ‖x - y‖ := by
    rw [smallContrastDyadicRadius_succ] at hnlo
    linarith only [hnlo]
  have hrpow : r ^ alpha ≤ 2 * ‖x - y‖ ^ alpha := by
    have hmono := Real.rpow_le_rpow hr.le hrle
      (le_trans (by norm_num) halpha.1)
    have htwo : (2 * ‖x - y‖) ^ alpha ≤ 2 * ‖x - y‖ ^ alpha := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _)]
      have := Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 2) halpha.2.le
      exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (norm_nonneg _) _)
    exact hmono.trans htwo
  have hcoef : 0 ≤
      (8 * ballVolumePrice 2 d * smallContrastCampanatoConstant d +
        6 * ballVolumePrice 3 d * smallContrastCampanatoConstant d) * K := by
    exact mul_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (ballVolumePrice_nonneg 2 d))
        (smallContrastCampanatoConstant_nonneg d))
      (mul_nonneg (mul_nonneg (by norm_num) (ballVolumePrice_nonneg 3 d))
        (smallContrastCampanatoConstant_nonneg d))) hK
  refine hcollect.trans ?_
  calc
    (8 * ballVolumePrice 2 d * smallContrastCampanatoConstant d +
          6 * ballVolumePrice 3 d * smallContrastCampanatoConstant d) * K * r ^ alpha ≤
      ((8 * ballVolumePrice 2 d * smallContrastCampanatoConstant d +
          6 * ballVolumePrice 3 d * smallContrastCampanatoConstant d) * K) *
        (2 * ‖x - y‖ ^ alpha) := mul_le_mul_of_nonneg_left hrpow hcoef
    _ = smallContrastLocalHolderConstant d * K * ‖x - y‖ ^ alpha := by
      rw [smallContrastLocalHolderConstant]
      ring

/-! ## Finite convex chaining -/

/-- The number of links used to compare points in the small-contrast Hölder estimate. -/
def smallContrastHolderChainLength (d : ℕ) : ℕ := 12 * d + 1

theorem smallContrastHolderChainLength_pos (d : ℕ) :
    0 < smallContrastHolderChainLength d := by
  unfold smallContrastHolderChainLength
  omega

private theorem smallContrast_segment_point_mem
    {W : Set (Vec d)} (hW : Convex ℝ W) {x y : Vec d}
    (hx : x ∈ W) (hy : y ∈ W) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    x + t • (y - x) ∈ W := by
  have hid : x + t • (y - x) = (1 - t) • x + t • y := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [hid]
  exact hW hx hy (by linarith only [ht1]) ht0 (by ring)

private theorem smallContrast_segment_step_norm
    (x y : Vec d) (N k : ℕ) :
    ‖(x + ((k : ℝ) / N) • (y - x)) -
        (x + (((k : ℕ) + 1 : ℝ) / N) • (y - x))‖ =
      (1 / (N : ℝ)) * ‖x - y‖ := by
  have hid : (x + ((k : ℝ) / N) • (y - x)) -
        (x + (((k : ℕ) + 1 : ℝ) / N) • (y - x)) =
      ((k : ℝ) / N - ((k : ℝ) + 1) / N) • (y - x) := by
    rw [sub_smul]
    abel
  rw [hid, norm_smul]
  have hcoef : (k : ℝ) / N - ((k : ℝ) + 1) / N = -(1 / (N : ℝ)) := by ring
  rw [hcoef, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ)), norm_sub_rev]

/-- A local scalar Hölder estimate on `B_{1/2}` globalizes with the fixed
dimension-only chain length `12d+1`. -/
theorem holder_on_halfBall_of_local [NeZero d]
    {alpha L : ℝ} {G : Vec d → ℝ}
    (halpha0 : 0 ≤ alpha) (hL : 0 ≤ L)
    (hloc : ∀ x ∈ smallContrastBall d (1 / 2),
      ∀ y ∈ smallContrastBall d (1 / 2),
        ‖x - y‖ ≤ smallContrastCampanatoRadius d →
        |G x - G y| ≤ L * ‖x - y‖ ^ alpha) :
    ∀ x ∈ smallContrastBall d (1 / 2),
      ∀ y ∈ smallContrastBall d (1 / 2),
        |G x - G y| ≤
          (smallContrastHolderChainLength d : ℝ) * L * ‖x - y‖ ^ alpha := by
  intro x hx y hy
  let N := smallContrastHolderChainLength d
  have hNpos : 0 < N := smallContrastHolderChainLength_pos d
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNreal
  let p : ℕ → Vec d := fun k => x + ((k : ℝ) / N) • (y - x)
  have hmem : ∀ k : ℕ, k ≤ N → p k ∈ smallContrastBall d (1 / 2) := by
    intro k hk
    apply smallContrast_segment_point_mem (convex_euclideanBall 0 (1 / 2)) hx hy
    · positivity
    · rw [div_le_one hNreal]
      exact_mod_cast hk
  have hxylt : ‖x - y‖ < 1 := by
    have hxE := (mem_euclideanBall_toEuc_iff x 0
      (by norm_num : (0 : ℝ) < 1 / 2)).2 hx
    have hyE := (mem_euclideanBall_toEuc_iff y 0
      (by norm_num : (0 : ℝ) < 1 / 2)).2 hy
    rw [Metric.mem_ball, dist_eq_norm, map_zero, sub_zero] at hxE hyE
    have hE : euclideanNorm (x - y) < 1 := by
      have heq : euclideanNorm (x - y) = ‖toEuc x - toEuc y‖ := by
        unfold euclideanNorm
        change Real.sqrt (euclideanSqDist x y) = ‖toEuc x - toEuc y‖
        rw [← norm_sq_toEuc_sub x y, Real.sqrt_sq (norm_nonneg _)]
      rw [heq]
      exact lt_of_le_of_lt (norm_sub_le _ _) (by linarith only [hxE, hyE])
    exact lt_of_le_of_lt (norm_le_euclideanNorm _) hE
  have hstepR : (1 / (N : ℝ)) * ‖x - y‖ ≤ smallContrastCampanatoRadius d := by
    have hdpos : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    have hNlower : 12 * (d : ℝ) < (N : ℝ) := by
      dsimp only [N, smallContrastHolderChainLength]
      push_cast
      norm_num
    have hstep : (1 / (N : ℝ)) * ‖x - y‖ < (12 * (d : ℝ))⁻¹ := by
      rw [one_div]
      have h12d : 0 < 12 * (d : ℝ) := mul_pos (by norm_num) hdpos
      have hInv : (N : ℝ)⁻¹ < (12 * (d : ℝ))⁻¹ :=
        (inv_lt_inv₀ hNreal h12d).2 hNlower
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left (le_of_lt hxylt) (inv_nonneg.mpr hNreal.le))
        (by simpa only [mul_one] using hInv)
    simpa only [smallContrastCampanatoRadius] using hstep.le
  have hstep : ∀ k : ℕ, k + 1 ≤ N →
      |G (p k) - G (p (k + 1))| ≤
        L * ((1 / (N : ℝ)) * ‖x - y‖) ^ alpha := by
    intro k hk
    have hk0 : k ≤ N := Nat.le_of_succ_le hk
    have hnorm := smallContrast_segment_step_norm x y N k
    have hnorm' : ‖p k - p (k + 1)‖ =
        (1 / (N : ℝ)) * ‖x - y‖ := by
      simpa only [p, Nat.cast_add, Nat.cast_one] using hnorm
    have h := hloc (p k) (hmem k hk0) (p (k + 1)) (hmem (k + 1) hk)
      (by rw [hnorm']; exact hstepR)
    rwa [hnorm'] at h
  have hind : ∀ k : ℕ, k ≤ N →
      |G x - G (p k)| ≤
        (k : ℝ) * (L * ((1 / (N : ℝ)) * ‖x - y‖) ^ alpha) := by
    intro k
    induction k with
    | zero =>
        intro _
        simp only [p, Nat.cast_zero, zero_div, zero_smul, add_zero, sub_self,
          abs_zero, zero_mul]
        exact le_rfl
    | succ k ih =>
        intro hk
        have hk0 : k ≤ N := Nat.le_of_succ_le hk
        have htri : |G x - G (p (k + 1))| ≤
            |G x - G (p k)| + |G (p k) - G (p (k + 1))| := by
          have hid : G x - G (p (k + 1)) =
              (G x - G (p k)) + (G (p k) - G (p (k + 1))) := by ring
          rw [hid]
          exact abs_add_le _ _
        calc
          |G x - G (p (k + 1))| ≤
              |G x - G (p k)| + |G (p k) - G (p (k + 1))| := htri
          _ ≤ (k : ℝ) * (L * ((1 / (N : ℝ)) * ‖x - y‖) ^ alpha) +
              L * ((1 / (N : ℝ)) * ‖x - y‖) ^ alpha :=
            add_le_add (ih hk0) (hstep k hk)
          _ = ((k + 1 : ℕ) : ℝ) *
              (L * ((1 / (N : ℝ)) * ‖x - y‖) ^ alpha) := by
            push_cast
            ring
  have hpN : p N = y := by
    simp only [p, div_self hNne, one_smul]
    abel
  have hfin := hind N le_rfl
  rw [hpN] at hfin
  have hbase : (1 / (N : ℝ)) * ‖x - y‖ ≤ ‖x - y‖ := by
    have hNOne : 1 ≤ (N : ℝ) := by exact_mod_cast hNpos
    have hinv : (1 / (N : ℝ)) ≤ 1 := by
      rw [div_eq_mul_inv, one_mul]
      exact (inv_le_one₀ hNreal).2 hNOne
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hinv (norm_nonneg (x - y)))
  have hrpow := Real.rpow_le_rpow (by positivity : 0 ≤ (1 / (N : ℝ)) * ‖x - y‖)
    hbase halpha0
  calc
    |G x - G y| ≤ (N : ℝ) *
        (L * ((1 / (N : ℝ)) * ‖x - y‖) ^ alpha) := hfin
    _ ≤ (N : ℝ) * (L * ‖x - y‖ ^ alpha) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrpow hL)
        (Nat.cast_nonneg N)
    _ = (smallContrastHolderChainLength d : ℝ) * L * ‖x - y‖ ^ alpha := by
      dsimp only [N]
      ring

/-- Global sup-metric Hölder bound of the Campanato representative. -/
theorem holder_smallContrastCampanatoRepresentative [NeZero d]
    {alpha K : ℝ} {u : H1Function (smallContrastUnitBall d)}
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1) (hK : 0 ≤ K)
    (hcamp : HasSmallContrastBallCampanatoBound alpha K u) :
    ∀ x ∈ smallContrastBall d (1 / 2),
      ∀ y ∈ smallContrastBall d (1 / 2),
      |smallContrastCampanatoRepresentative (d := d) u.toFun x -
          smallContrastCampanatoRepresentative (d := d) u.toFun y| ≤
        (smallContrastHolderChainLength d : ℝ) *
          smallContrastLocalHolderConstant d * K * ‖x - y‖ ^ alpha := by
  have h := holder_on_halfBall_of_local (d := d) (alpha := alpha)
    (L := smallContrastLocalHolderConstant d * K)
    (G := smallContrastCampanatoRepresentative (d := d) u.toFun)
    (le_trans (by norm_num) halpha.1)
    (mul_nonneg (smallContrastLocalHolderConstant_nonneg d) hK)
    (fun x hx y hy hxy =>
      local_holder_smallContrastCampanatoRepresentative halpha hK hcamp hx hy hxy)
  simpa only [mul_assoc] using h

/-- A positive sup-metric Hölder modulus gives continuity on its window.  On
the range `alpha >= 1/2`, a squared epsilon radius is a uniform
modulus, so no exponent-dependent constant is introduced. -/
theorem continuousOn_of_supHolderBoundOn_Ico_half
    {W : Set (Vec d)} {alpha L : ℝ} {G : Vec d → ℝ}
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1) (hL : 0 ≤ L)
    (hholder : ∀ x ∈ W, ∀ y ∈ W,
      |G x - G y| ≤ L * ‖x - y‖ ^ alpha) :
    ContinuousOn G W := by
  rw [Metric.continuousOn_iff]
  intro p hp ε hε
  let t := min 1 (ε / (L + 1))
  have hL1 : 0 < L + 1 := add_pos_of_nonneg_of_pos hL (by norm_num)
  have ht : 0 < t := lt_min (by norm_num) (div_pos hε hL1)
  refine ⟨t ^ 2, sq_pos_of_pos ht, ?_⟩
  intro q hq hd
  have hnorm : ‖q - p‖ < t ^ 2 := by rwa [← dist_eq_norm]
  have htOne : t ≤ 1 := min_le_left _ _
  have htSqOne : t ^ 2 ≤ 1 := by
    have hm := pow_le_pow_left₀ (le_of_lt ht) htOne 2
    simpa only [one_pow] using hm
  have hnormOne : ‖q - p‖ ≤ 1 :=
    (le_of_lt hnorm).trans htSqOne
  have hpowExp : ‖q - p‖ ^ alpha ≤ ‖q - p‖ ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hnormOne (by norm_num) halpha.1
  have hpowBase : ‖q - p‖ ^ (1 / 2 : ℝ) ≤ (t ^ 2) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (norm_nonneg _) (le_of_lt hnorm) (by norm_num)
  have hcollapse : (t ^ 2) ^ (1 / 2 : ℝ) = t := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht.le]
    norm_num
  have hpow : ‖q - p‖ ^ alpha ≤ t := by
    rw [hcollapse] at hpowBase
    exact hpowExp.trans hpowBase
  have hmain : |G q - G p| ≤ L * t :=
    (hholder q hq p hp).trans (mul_le_mul_of_nonneg_left hpow hL)
  have htQuot : t ≤ ε / (L + 1) := min_le_right _ _
  have hlt : L * t < ε := by
    calc
      L * t ≤ L * (ε / (L + 1)) := mul_le_mul_of_nonneg_left htQuot hL
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ hL1]
        nlinarith only [hL, hε]
  rw [Real.dist_eq]
  exact hmain.trans_lt hlt

/-- Continuity of the canonical Campanato representative on the interior
half-ball. -/
theorem continuousOn_smallContrastCampanatoRepresentative [NeZero d]
    {alpha K : ℝ} {u : H1Function (smallContrastUnitBall d)}
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1) (hK : 0 ≤ K)
    (hcamp : HasSmallContrastBallCampanatoBound alpha K u) :
    ContinuousOn (smallContrastCampanatoRepresentative (d := d) u.toFun)
      (smallContrastBall d (1 / 2)) := by
  apply continuousOn_of_supHolderBoundOn_Ico_half halpha
    (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (smallContrastLocalHolderConstant_nonneg d)) hK)
  exact holder_smallContrastCampanatoRepresentative halpha hK hcamp

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
