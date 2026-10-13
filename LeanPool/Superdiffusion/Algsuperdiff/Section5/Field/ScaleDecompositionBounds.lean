/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.Holder
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.ScaleDecompositionSmooth
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.ScalesConcentration.Weights

/-!
# ScaleDecompositionBounds

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Logarithmic local bounds for the stream-field scale decomposition

The sharp carrier is read on the first triadic origin cube containing the
Euclidean ball.  Its crossover weight is linear in that cube scale, hence of
order `1 + log R`.  Summation of the negative value rates and nonnegative
gradient rates gives the two local constants of that decomposition.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section4.Probability.ScalesConcentration
open HCPolySupport
open HCPolySupport.Book.Ch02
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- The first triadic scale whose side is at least `4 R`. -/
def streamObservationScale (R : ℝ) : ℕ :=
  Nat.ceil (Real.logb 3 (4 * R))

/-- The logarithmic radial weight used by both halves of the field. -/
def streamLogWeight (R : ℝ) : ℝ := 1 + Real.log R

theorem streamLogWeight_pos {R : ℝ} (hR : 1 ≤ R) : 0 < streamLogWeight R := by
  unfold streamLogWeight
  have hlog := Real.log_nonneg hR
  linarith only [hlog]

private theorem norm_le_sqrt_vecNormSq_scale (x : Vec d) :
    ‖x‖ ≤ Real.sqrt (vecNormSq x) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (HCPolySupport.sq_apply_le_vecNormSq x i)

private theorem streamObservationScale_cast_lt {R : ℝ} (hR : 1 ≤ R) :
    (streamObservationScale R : ℝ) < 4 + Real.log R := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hfourR : (1 : ℝ) ≤ 4 * R := by
    nlinarith only [hR]
  have hlogb0 : 0 ≤ Real.logb 3 (4 * R) :=
    Real.logb_nonneg (by norm_num) hfourR
  have hceil := Nat.ceil_lt_add_one hlogb0
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := log_three_gt_one.le
  have hlogFourR0 : 0 ≤ Real.log (4 * R) := Real.log_nonneg hfourR
  have hdiv : Real.logb 3 (4 * R) ≤ Real.log (4 * R) := by
    unfold Real.logb
    exact div_le_self hlogFourR0 hlog3
  have hlogmul : Real.log (4 * R) = Real.log 4 + Real.log R :=
    Real.log_mul (by norm_num) (ne_of_gt hRpos)
  have hlogFour : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at this ⊢
    exact this
  unfold streamObservationScale
  rw [hlogmul] at hdiv
  linarith only [hceil, hdiv, hlogFour]

private theorem streamObservationScale_add_three_le_logWeight {R : ℝ}
    (hR : 1 ≤ R) :
    (streamObservationScale R : ℝ) + 3 ≤ 7 * streamLogWeight R := by
  have hscale := (streamObservationScale_cast_lt hR).le
  have hlog := Real.log_nonneg hR
  unfold streamLogWeight
  linarith only [hscale, hlog]

private theorem streamObservationScale_add_two_le_logWeight {R : ℝ}
    (hR : 1 ≤ R) :
    (streamObservationScale R : ℝ) + 2 ≤ 6 * streamLogWeight R := by
  have hscale := (streamObservationScale_cast_lt hR).le
  have hlog := Real.log_nonneg hR
  unfold streamLogWeight
  linarith only [hscale, hlog]

theorem mem_openOriginCube_streamObservationScale {R : ℝ} (hR : 1 ≤ R)
    {x : Vec d} (hx : Real.sqrt (vecNormSq x) ≤ R) :
    x ∈ openCubeSet (originCube d (streamObservationScale R : ℤ)) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hpow : 4 * R ≤ (3 : ℝ) ^ streamObservationScale R := by
    calc
      4 * R = Real.rpow 3 (Real.logb 3 (4 * R)) :=
        (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
      _ ≤ Real.rpow 3 (streamObservationScale R : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (Nat.le_ceil (Real.logb 3 (4 * R)))
      _ = (3 : ℝ) ^ streamObservationScale R := Real.rpow_natCast 3 _
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hcoord : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  have hxi : |x i| ≤ R := hcoord.trans ((norm_le_sqrt_vecNormSq_scale x).trans hx)
  have hhalf : R < (1 / 2 : ℝ) * (3 : ℝ) ^ streamObservationScale R := by
    nlinarith only [hpow, hRpos]
  have hpowInt : (3 : ℝ) ^ ((streamObservationScale R : ℕ) : ℤ) =
      (3 : ℝ) ^ streamObservationScale R := by simp
  rw [hpowInt]
  constructor
  · linarith only [hxi, hhalf, neg_abs_le (x i)]
  · linarith only [hxi, hhalf, le_abs_self (x i)]

def streamSmallRatio (M : ABKModel d) : ℝ := Real.rpow 3 (-M.gamma)

def streamLargeRatio (M : ABKModel d) : ℝ := Real.rpow 3 (M.gamma - 1)

def streamSmallSeries (M : ABKModel d) : ℝ :=
  ∑' r : ℕ, ((r : ℝ) + 1) * streamSmallRatio M ^ r

def streamLargeSeries (M : ABKModel d) : ℝ :=
  ∑' r : ℕ, ((r : ℝ) + 1) * streamLargeRatio M ^ r

private theorem streamSmallRatio_pos (M : ABKModel d) : 0 < streamSmallRatio M :=
  Real.rpow_pos_of_pos (by norm_num) _

private theorem streamSmallRatio_lt_one (M : ABKModel d) : streamSmallRatio M < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (neg_neg_of_pos M.shellPrefix.gamma_pos)

private theorem streamLargeRatio_pos (M : ABKModel d) : 0 < streamLargeRatio M :=
  Real.rpow_pos_of_pos (by norm_num) _

private theorem streamLargeRatio_lt_one (M : ABKModel d) : streamLargeRatio M < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (by linarith only [M.shellPrefix.gamma_le_quarter])

private theorem summable_streamSmallSeries (M : ABKModel d) :
    Summable fun r : ℕ => ((r : ℝ) + 1) * streamSmallRatio M ^ r :=
  Section4.Provider.Annular.summable_poly1_geom
    (streamSmallRatio_pos M).le (streamSmallRatio_lt_one M)

private theorem summable_streamLargeSeries (M : ABKModel d) :
    Summable fun r : ℕ => ((r : ℝ) + 1) * streamLargeRatio M ^ r :=
  Section4.Provider.Annular.summable_poly1_geom
    (streamLargeRatio_pos M).le (streamLargeRatio_lt_one M)

private theorem streamSmallSeries_nonneg (M : ABKModel d) : 0 ≤ streamSmallSeries M :=
  tsum_nonneg fun _ => mul_nonneg (by positivity)
    (pow_nonneg (streamSmallRatio_pos M).le _)

private theorem streamLargeSeries_nonneg (M : ABKModel d) : 0 ≤ streamLargeSeries M :=
  tsum_nonneg fun _ => mul_nonneg (by positivity)
    (pow_nonneg (streamLargeRatio_pos M).le _)

private theorem smallScaleFactor (M : ABKModel d) (r : ℕ) :
    Real.rpow 3 (M.gamma * ((-1 - (r : ℤ) : ℤ) : ℝ)) =
      Real.rpow 3 (-M.gamma) * streamSmallRatio M ^ r := by
  rw [show M.gamma * ((-1 - (r : ℤ) : ℤ) : ℝ) =
      -M.gamma + (-M.gamma) * (r : ℝ) by push_cast; ring,
    Section4.Provider.BoundsEaL.rpow3_add]
  congr 1
  exact Section4.Provider.BoundsEaL.rpow3_mul_natCast (-M.gamma) r

private theorem largeScaleFactor (M : ABKModel d) (r : ℕ) :
    Real.rpow 3 ((M.gamma - 1) * ((r : ℤ) : ℝ)) = streamLargeRatio M ^ r := by
  exact Section4.Provider.BoundsEaL.rpow3_mul_natCast (M.gamma - 1) r

private theorem smallWeight_le (ell r : ℕ) :
    sharpTailWeight (-1 - (r : ℤ)) (ell : ℤ) ≤
      ((ell : ℝ) + 3) * ((r : ℝ) + 1) := by
  have habs : (-1 - (r : ℤ)).natAbs ≤ 1 + r := by
    have := Int.natAbs_sub_le (-1 : ℤ) (r : ℤ)
    simpa only [Int.natAbs_neg, Int.natAbs_one, Int.natAbs_natCast] using this
  unfold sharpTailWeight
  simp only [Int.natAbs_natCast]
  have habsR : ((-1 - (r : ℤ)).natAbs : ℝ) ≤ 1 + (r : ℝ) := by exact_mod_cast habs
  have hell0 : (0 : ℝ) ≤ (ell : ℝ) := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith only [habsR, hell0, hr0]

private theorem largeWeight_le (ell r : ℕ) :
    sharpTailWeight (r : ℤ) (ell : ℤ) ≤
      ((ell : ℝ) + 2) * ((r : ℝ) + 1) := by
  unfold sharpTailWeight
  simp only [Int.natAbs_natCast]
  have hell0 : (0 : ℝ) ≤ (ell : ℝ) := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith only [hell0, hr0]

private theorem matrixOperatorNorm_le_sum_abs_entries_scale (A : Mat d) :
    matrixOperatorNorm A ≤ ∑ i, ∑ k, |A i k| := by
  have h := matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries A (0 : Mat d)
  simpa only [matrixOperatorNorm_zero, Matrix.zero_apply, sub_zero, zero_add] using h

/-- A concrete sample constant for the logarithmic bound on the rough part. -/
def streamFieldSmallBallConst (M : ABKModel d) (omega : FullSample d M.gamma) : ℝ :=
  14 * (d : ℝ) ^ 2 * (streamSharpConst M omega : ℝ) *
    Real.rpow 3 (-M.gamma) * streamSmallSeries M

/-- A concrete sample constant for the logarithmic gradient bound on the
smooth part. -/
def streamFieldLargeGradientConst (M : ABKModel d)
    (omega : FullSample d M.gamma) : ℝ :=
  6 * (d : ℝ) * (streamSharpConst M omega : ℝ) * streamLargeSeries M

theorem streamFieldSmallBallConst_nonneg (M : ABKModel d)
    (omega : FullSample d M.gamma) : 0 ≤ streamFieldSmallBallConst M omega := by
  unfold streamFieldSmallBallConst
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg (d : ℝ))) (Nat.cast_nonneg _))
      (Real.rpow_pos_of_pos (by norm_num) _).le)
    (streamSmallSeries_nonneg M)

theorem streamFieldLargeGradientConst_nonneg (M : ABKModel d)
    (omega : FullSample d M.gamma) : 0 ≤ streamFieldLargeGradientConst M omega := by
  unfold streamFieldLargeGradientConst
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) (Nat.cast_nonneg _))
    (streamLargeSeries_nonneg M)

/-- On a Euclidean ball, the rough negative-shell part is bounded by a
constant times `1 + log R`. -/
theorem matrixOperatorNorm_streamFieldSmall_le (M : ABKModel d)
    (omega : FullSample d M.gamma) {R : ℝ} (hR : 1 ≤ R) {x : Vec d}
    (hx : Real.sqrt (vecNormSq x) ≤ R) :
    matrixOperatorNorm (streamFieldSmall omega x) ≤
      streamFieldSmallBallConst M omega * streamLogWeight R := by
  let ell := streamObservationScale R
  have hxCube : x ∈ openCubeSet (originCube d (ell : ℤ)) :=
    mem_openOriginCube_streamObservationScale hR hx
  have hzero := zero_mem_openOriginCube d (ell : ℤ)
  have hC := streamSharpConst_spec M omega
  have hentry : ∀ i k : Fin d,
      |streamFieldSmall omega x i k| ≤
        2 * (streamSharpConst M omega : ℝ) * ((ell : ℝ) + 3) *
          Real.rpow 3 (-M.gamma) * streamSmallSeries M := by
    intro i k
    have hs := summable_streamIncrement_descending omega.1 (-1) x i k
    have hmajSummable : Summable fun r : ℕ =>
        2 * (streamSharpConst M omega : ℝ) * ((ell : ℝ) + 3) *
          Real.rpow 3 (-M.gamma) *
            (((r : ℝ) + 1) * streamSmallRatio M ^ r) := by
      refine ((summable_streamSmallSeries M).mul_left
        (2 * (streamSharpConst M omega : ℝ) * ((ell : ℝ) + 3) *
          Real.rpow 3 (-M.gamma))).congr ?_
      intro r
      ring
    have hmaj : ∀ r : ℕ,
        |omega.1.1 (-1 - (r : ℤ)) x i k -
          omega.1.1 (-1 - (r : ℤ)) 0 i k| ≤
        2 * (streamSharpConst M omega : ℝ) * ((ell : ℝ) + 3) *
          Real.rpow 3 (-M.gamma) *
            (((r : ℝ) + 1) * streamSmallRatio M ^ r) := by
      intro r
      have hxv := abs_entry_le_localCubeControl (ell : ℤ)
        (omega.1.1 (-1 - (r : ℤ))) hxCube i k
      have h0v := abs_entry_le_localCubeControl (ell : ℤ)
        (omega.1.1 (-1 - (r : ℤ))) hzero i k
      have hsharp := (hC (-1 - (r : ℤ)) (ell : ℤ)).1
      have hw := smallWeight_le ell r
      calc
        |omega.1.1 (-1 - (r : ℤ)) x i k -
            omega.1.1 (-1 - (r : ℤ)) 0 i k| ≤
            2 * localCubeControl (ell : ℤ) (omega.1.1 (-1 - (r : ℤ))) := by
          have := abs_sub (omega.1.1 (-1 - (r : ℤ)) x i k)
            (omega.1.1 (-1 - (r : ℤ)) 0 i k)
          linarith only [this, hxv, h0v]
        _ ≤ 2 * ((streamSharpConst M omega : ℝ) *
            Real.rpow 3 (M.gamma * ((-1 - (r : ℤ) : ℤ) : ℝ)) *
              sharpTailWeight (-1 - (r : ℤ)) (ell : ℤ)) :=
          mul_le_mul_of_nonneg_left hsharp (by norm_num)
        _ = 2 * ((streamSharpConst M omega : ℝ) *
            (Real.rpow 3 (-M.gamma) * streamSmallRatio M ^ r) *
              sharpTailWeight (-1 - (r : ℤ)) (ell : ℤ)) := by
          rw [smallScaleFactor]
        _ ≤ 2 * ((streamSharpConst M omega : ℝ) *
            (Real.rpow 3 (-M.gamma) * streamSmallRatio M ^ r) *
              (((ell : ℝ) + 3) * ((r : ℝ) + 1))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_left hw
          exact mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le
              (pow_nonneg (streamSmallRatio_pos M).le _))
        _ = 2 * (streamSharpConst M omega : ℝ) * ((ell : ℝ) + 3) *
            Real.rpow 3 (-M.gamma) *
              (((r : ℝ) + 1) * streamSmallRatio M ^ r) := by ring
    rw [streamFieldSmall_apply_entry]
    have hsNorm : Summable fun r : ℕ =>
        ‖omega.1.1 (-1 - (r : ℤ)) x i k -
          omega.1.1 (-1 - (r : ℤ)) 0 i k‖ := hs.norm
    calc
      |∑' r : ℕ, (omega.1.1 (-1 - (r : ℤ)) x i k -
          omega.1.1 (-1 - (r : ℤ)) 0 i k)| ≤
          ∑' r : ℕ, |omega.1.1 (-1 - (r : ℤ)) x i k -
            omega.1.1 (-1 - (r : ℤ)) 0 i k| := by
        rw [← Real.norm_eq_abs]
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsNorm
      _ ≤ ∑' r : ℕ, 2 * (streamSharpConst M omega : ℝ) * ((ell : ℝ) + 3) *
          Real.rpow 3 (-M.gamma) *
            (((r : ℝ) + 1) * streamSmallRatio M ^ r) :=
        hs.abs.tsum_le_tsum hmaj hmajSummable
      _ = 2 * (streamSharpConst M omega : ℝ) * ((ell : ℝ) + 3) *
          Real.rpow 3 (-M.gamma) * streamSmallSeries M := by
        unfold streamSmallSeries
        rw [← tsum_mul_left]
  have hmatrix := (matrixOperatorNorm_le_sum_abs_entries_scale
    (streamFieldSmall omega x)).trans (show
      (∑ i, ∑ k, |streamFieldSmall omega x i k|) ≤
        (d : ℝ) ^ 2 * (2 * (streamSharpConst M omega : ℝ) * ((ell : ℝ) + 3) *
          Real.rpow 3 (-M.gamma) * streamSmallSeries M) by
      calc
        (∑ i, ∑ k, |streamFieldSmall omega x i k|) ≤
            ∑ _i : Fin d, ∑ _k : Fin d,
              2 * (streamSharpConst M omega : ℝ) * ((ell : ℝ) + 3) *
                Real.rpow 3 (-M.gamma) * streamSmallSeries M := by
          gcongr with i _ k _
          exact hentry i k
        _ = _ := by simp [pow_two]; ring)
  have hscale := streamObservationScale_add_three_le_logWeight hR
  unfold streamFieldSmallBallConst
  have hcoef : 0 ≤ 2 * (d : ℝ) ^ 2 * (streamSharpConst M omega : ℝ) *
      Real.rpow 3 (-M.gamma) * streamSmallSeries M := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg (d : ℝ)))
          (Nat.cast_nonneg _)) (Real.rpow_pos_of_pos (by norm_num) _).le)
      (streamSmallSeries_nonneg M)
  exact hmatrix.trans (by
    have := mul_le_mul_of_nonneg_left hscale hcoef
    convert this using 1 <;> ring)

/-- On a Euclidean ball, the gradient of the nonnegative-shell part is
bounded by a constant times `1 + log R`. -/
theorem norm_streamFieldLargeDeriv_le (M : ABKModel d)
    (omega : FullSample d M.gamma) {R : ℝ} (hR : 1 ≤ R) {x : Vec d}
    (hx : Real.sqrt (vecNormSq x) ≤ R) :
    ‖streamFieldLargeDeriv omega x‖ ≤
      streamFieldLargeGradientConst M omega * streamLogWeight R := by
  let ell := streamObservationScale R
  have hxCube : x ∈ openCubeSet (originCube d (ell : ℤ)) :=
    mem_openOriginCube_streamObservationScale hR hx
  have hC := streamSharpConst_spec M omega
  have hmaj : ∀ r : ℕ, ‖ShellField.deriv (omega.1.1 (r : ℤ)) x‖ ≤
      (d : ℝ) * (streamSharpConst M omega : ℝ) * ((ell : ℝ) + 2) *
        (((r : ℝ) + 1) * streamLargeRatio M ^ r) := by
    intro r
    have hlocal := matrixDerivativeNorm_deriv_le_localCubeDerivNorm
      (ell : ℤ) (omega.1.1 (r : ℤ)) hxCube
    have hgauge : localCubeDerivNorm (ell : ℤ) (omega.1.1 (r : ℤ)) ≤
        sharpGradientGauge (ell : ℤ) (r : ℤ) omega.1 := by
      rw [sharpGradientGauge_eq]
      exact le_add_of_nonneg_right
        (mul_nonneg (zpow_pos (by norm_num) _).le
          (localCubeSecondDerivNorm_nonneg _ _))
    have hsharp := (hC (r : ℤ) (ell : ℤ)).2
    have hw := largeWeight_le ell r
    calc
      ‖ShellField.deriv (omega.1.1 (r : ℤ)) x‖ ≤
          (d : ℝ) * ShellField.matrixDerivativeNorm
            (ShellField.deriv (omega.1.1 (r : ℤ)) x) :=
        Section5.Support.norm_le_dim_mul_matrixDerivativeNorm _
      _ ≤ (d : ℝ) * localCubeDerivNorm (ell : ℤ) (omega.1.1 (r : ℤ)) := by
        gcongr
      _ ≤ (d : ℝ) * sharpGradientGauge (ell : ℤ) (r : ℤ) omega.1 := by gcongr
      _ ≤ (d : ℝ) * ((streamSharpConst M omega : ℝ) *
          Real.rpow 3 ((M.gamma - 1) * ((r : ℤ) : ℝ)) *
            sharpTailWeight (r : ℤ) (ell : ℤ)) := by gcongr
      _ = (d : ℝ) * ((streamSharpConst M omega : ℝ) *
          streamLargeRatio M ^ r * sharpTailWeight (r : ℤ) (ell : ℤ)) := by
        rw [largeScaleFactor]
      _ ≤ (d : ℝ) * ((streamSharpConst M omega : ℝ) *
          streamLargeRatio M ^ r * (((ell : ℝ) + 2) * ((r : ℝ) + 1))) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
        apply mul_le_mul_of_nonneg_left hw
        exact mul_nonneg (Nat.cast_nonneg _)
          (pow_nonneg (streamLargeRatio_pos M).le _)
      _ = (d : ℝ) * (streamSharpConst M omega : ℝ) * ((ell : ℝ) + 2) *
          (((r : ℝ) + 1) * streamLargeRatio M ^ r) := by ring
  have hmajSummable : Summable fun r : ℕ =>
      (d : ℝ) * (streamSharpConst M omega : ℝ) * ((ell : ℝ) + 2) *
        (((r : ℝ) + 1) * streamLargeRatio M ^ r) := by
    refine ((summable_streamLargeSeries M).mul_left
      ((d : ℝ) * (streamSharpConst M omega : ℝ) * ((ell : ℝ) + 2))).congr ?_
    intro r
    ring
  have hsumNorm : Summable fun r : ℕ =>
      ‖ShellField.deriv (omega.1.1 (r : ℤ)) x‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hmaj hmajSummable
  unfold streamFieldLargeDeriv
  calc
    ‖∑' r : ℕ, ShellField.deriv (omega.1.1 (r : ℤ)) x‖ ≤
        ∑' r : ℕ, ‖ShellField.deriv (omega.1.1 (r : ℤ)) x‖ :=
      norm_tsum_le_tsum_norm hsumNorm
    _ ≤ ∑' r : ℕ, (d : ℝ) * (streamSharpConst M omega : ℝ) *
        ((ell : ℝ) + 2) * (((r : ℝ) + 1) * streamLargeRatio M ^ r) :=
      hsumNorm.tsum_le_tsum hmaj hmajSummable
    _ = (d : ℝ) * (streamSharpConst M omega : ℝ) * ((ell : ℝ) + 2) *
        streamLargeSeries M := by
      unfold streamLargeSeries
      rw [← tsum_mul_left]
    _ ≤ streamFieldLargeGradientConst M omega * streamLogWeight R := by
      have hscale := streamObservationScale_add_two_le_logWeight hR
      have hcoef : 0 ≤ (d : ℝ) * (streamSharpConst M omega : ℝ) *
          streamLargeSeries M := by
        exact mul_nonneg
          (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg _))
          (streamLargeSeries_nonneg M)
      unfold streamFieldLargeGradientConst
      have := mul_le_mul_of_nonneg_left hscale hcoef
      convert this using 1
      all_goals first | rfl | ring

end

end Algsuperdiff.Section5.Field
