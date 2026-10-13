/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import LeanPool.MarkovProcess.MarkovProcess.Analysis.PaleyZygmund
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.ExitTimeExponentialMoment

/-!
# ExitTimeSurvival

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Survival of the exit time above a fraction of its mean

A uniform bound `E_y tau_U ≤ M` on the expected exit time from an open set `U`, valid from every
starting point, controls every moment of the exit time.  The multiplier `K = 4` and the rate
`lam = log (4 / 3) / (4 M)` meet the rate condition of
`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_two_of_lintegral_le` with equality,
so `E_x exp (lam * tau_U) ≤ 2`, and the elementary bound `t ^ p ≤ (p / (lam * e)) ^ p * exp (lam t)`
turns that into `E_x tau_U ^ p ≤ 2 * (p / (lam * e)) ^ p`
(`IsConservative.lintegral_exitTime_pow_le_of_lintegral_le`).  At `p = 2` this is the explicit
second-moment bound `E_x tau_U ^ 2 ≤ 288 * M ^ 2`
(`IsConservative.lintegral_exitTime_sq_le_of_lintegral_le`).

Fed into the Paley--Zygmund inequality, the second moment turns a *lower* bound `mLow ≤ E_x tau_U`
into a lower bound on the probability of surviving a fraction of `mLow`,

  `(1 - rho) ^ 2 * mLow ^ 2 ≤ 288 * M ^ 2 * Q_x {rho * mLow ≤ tau_U}`

(`IsConservative.sq_le_mul_measure_le_exitTime_of_lintegral_le`), which at `rho = 1 / 2` reads
`mLow ^ 2 ≤ 1152 * M ^ 2 * Q_x {mLow / 2 ≤ tau_U}`
(`IsConservative.sq_le_mul_measure_half_le_exitTime_of_lintegral_le`).  The upper bound `M` is
required from every starting point, as the exponential moment needs it; the lower bound `mLow` is
required only at the starting point whose survival probability is bounded, so the conclusion is
uniform over any set of starting points on which the lower bound holds.

The constant `288` is not optimal.  It records the two crude estimates `1 / 4 ≤ log (4 / 3)` and
`8 / 3 ≤ e` that keep the arithmetic elementary; the exponential-moment theorem itself is stated
with a free multiplier and a free rate, so a consumer wanting a smaller constant can supply its
own pair.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

open MarkovProcess

namespace Algsuperdiff.Process

namespace SubMarkovKernelSemigroup

open MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- **Every polynomial moment from an expected-exit bound.**  A uniform bound `M` on the expected
exit time from `U`, together with a multiplier `K > 1` and a positive rate `lam` meeting the
normalization condition `exp (lam * K * M) * (K + 2) ≤ 2 * K`, bounds every polynomial moment of
the exit time by `2 * (p / (lam * e)) ^ p`. -/
theorem IsConservative.lintegral_exitTime_pow_le_of_lintegral_le
    (hFeller : P.IsFellerKernelSemigroup) (hKol : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (M : ℝ≥0)
    (hM : ∀ y, ∫⁻ omega, ContinuousPath.exitTime U omega
      ∂(IsConservative.continuousProcess P hP y) ≤ (M : ℝ≥0∞))
    (K : ℝ≥0) (hK1 : 1 < K) (lam : ℝ) (hlam : 0 < lam)
    (hrate : Real.exp (lam * ((K : ℝ) * (M : ℝ))) * ((K : ℝ) + 2) ≤ 2 * (K : ℝ))
    (p : ℕ) (x : alpha) :
    ∫⁻ omega, ContinuousPath.exitTime U omega ^ p
        ∂(IsConservative.continuousProcess P hP x)
      ≤ 2 * ENNReal.ofReal (((p : ℝ) / (lam * Real.exp 1)) ^ p) := by
  have hexp := hP.lintegral_exponentialStoppingWeight_exitTime_le_two_of_lintegral_le P hFeller
    hKol U hU M hM K hK1 lam hlam.le hrate x
  calc
    ∫⁻ omega, ContinuousPath.exitTime U omega ^ p
        ∂(IsConservative.continuousProcess P hP x)
        ≤ ENNReal.ofReal (((p : ℝ) / (lam * Real.exp 1)) ^ p) *
          ∫⁻ omega, ContinuousPath.exponentialStoppingWeight lam
            (ContinuousPath.exitTime U) omega
            ∂(IsConservative.continuousProcess P hP x) :=
      hP.lintegral_exitTime_pow_le P U lam hlam p x
    _ ≤ ENNReal.ofReal (((p : ℝ) / (lam * Real.exp 1)) ^ p) * 2 := mul_le_mul_right hexp _
    _ = 2 * ENNReal.ofReal (((p : ℝ) / (lam * Real.exp 1)) ^ p) := mul_comm _ _

/-- The crude lower bound `1 / 4 ≤ log (4 / 3)`, from `log t ≤ t - 1` at `t = 3 / 4`. -/
private theorem one_quarter_le_log_four_thirds : (1 : ℝ) / 4 ≤ Real.log (4 / 3) := by
  have h : Real.log (3 / 4) ≤ 3 / 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hinv : Real.log (4 / 3) = -Real.log (3 / 4) := by
    rw [← Real.log_inv]
    norm_num
  rw [hinv]
  linarith only [h]

/-- The crude lower bound `8 / 3 ≤ e`. -/
private theorem eight_thirds_le_exp_one : (8 : ℝ) / 3 ≤ Real.exp 1 := by
  have h : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  linarith only [h]

/-- **An explicit second moment from an expected-exit bound.**  A uniform bound `M` on the
expected exit time from `U`, valid from every starting point, gives the second-moment bound
`E_x tau_U ^ 2 ≤ 288 * M ^ 2` from every starting point. -/
theorem IsConservative.lintegral_exitTime_sq_le_of_lintegral_le
    (hFeller : P.IsFellerKernelSemigroup) (hKol : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (M : ℝ≥0)
    (hM : ∀ y, ∫⁻ omega, ContinuousPath.exitTime U omega
      ∂(IsConservative.continuousProcess P hP y) ≤ (M : ℝ≥0∞))
    (x : alpha) :
    ∫⁻ omega, ContinuousPath.exitTime U omega ^ 2
        ∂(IsConservative.continuousProcess P hP x) ≤ 288 * (M : ℝ≥0∞) ^ 2 := by
  have hExit : Measurable fun omega : ContinuousPath alpha ↦ ContinuousPath.exitTime U omega :=
    ContinuousPath.measurable_exitTime U hU
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ M) with hM0 | hM0
  · have hzero : ∫⁻ omega, ContinuousPath.exitTime U omega
        ∂(IsConservative.continuousProcess P hP x) = 0 := by
      refine le_antisymm ?_ zero_le
      simpa only [← hM0, ENNReal.coe_zero] using! hM x
    have hae := (lintegral_eq_zero_iff hExit).mp hzero
    have hsq : ∫⁻ omega, ContinuousPath.exitTime U omega ^ 2
        ∂(IsConservative.continuousProcess P hP x) = 0 := by
      rw [lintegral_eq_zero_iff (hExit.pow_const 2)]
      filter_upwards [hae] with omega homega
      simp only [Pi.zero_apply] at homega ⊢
      rw [homega, zero_pow (by norm_num)]
    rw [hsq]
    exact zero_le
  · have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
    set lam : ℝ := Real.log (4 / 3) / (4 * (M : ℝ)) with hlamdef
    have hlogpos : (0 : ℝ) < Real.log (4 / 3) :=
      lt_of_lt_of_le (by norm_num) one_quarter_le_log_four_thirds
    have hlam : (0 : ℝ) < lam := div_pos hlogpos (by positivity)
    have hprod : lam * (((4 : ℝ≥0) : ℝ) * (M : ℝ)) = Real.log (4 / 3) := by
      rw [hlamdef]
      push_cast
      field_simp
    have hrate : Real.exp (lam * (((4 : ℝ≥0) : ℝ) * (M : ℝ))) * (((4 : ℝ≥0) : ℝ) + 2) ≤
        2 * ((4 : ℝ≥0) : ℝ) := by
      rw [hprod, Real.exp_log (by norm_num)]
      norm_num
    have hmain := IsConservative.lintegral_exitTime_pow_le_of_lintegral_le P hP hFeller hKol U hU
      M hM
      4 (by norm_num) lam hlam hrate 2 x
    have hlow : (1 : ℝ) / (16 * (M : ℝ)) ≤ lam := by
      rw [hlamdef, le_div_iff₀ (by positivity)]
      have hid : (1 : ℝ) / (16 * (M : ℝ)) * (4 * (M : ℝ)) = 1 / 4 := by
        field_simp
        ring
      rw [hid]
      exact one_quarter_le_log_four_thirds
    have hlame : (1 : ℝ) / (6 * (M : ℝ)) ≤ lam * Real.exp 1 := by
      have hmul : (1 : ℝ) / (16 * (M : ℝ)) * (8 / 3) ≤ lam * Real.exp 1 :=
        mul_le_mul hlow eight_thirds_le_exp_one (by norm_num) hlam.le
      have hid : (1 : ℝ) / (16 * (M : ℝ)) * (8 / 3) = 1 / (6 * (M : ℝ)) := by
        field_simp
        ring
      linarith only [hmul, hid.ge, hid.le]
    have hlamepos : (0 : ℝ) < lam * Real.exp 1 := by positivity
    have hquot : (2 : ℝ) / (lam * Real.exp 1) ≤ 12 * (M : ℝ) := by
      rw [div_le_iff₀ hlamepos]
      have hstep : (12 : ℝ) * (M : ℝ) * (1 / (6 * (M : ℝ))) ≤ 12 * (M : ℝ) * (lam * Real.exp 1) :=
        mul_le_mul_of_nonneg_left hlame (by positivity)
      have hid : (12 : ℝ) * (M : ℝ) * (1 / (6 * (M : ℝ))) = 2 := by
        field_simp
        ring
      linarith only [hstep, hid.ge, hid.le]
    have hreal : (2 : ℝ) * (((2 : ℕ) : ℝ) / (lam * Real.exp 1)) ^ 2 ≤ 288 * (M : ℝ) ^ 2 := by
      have hcast : (((2 : ℕ) : ℝ) / (lam * Real.exp 1)) = 2 / (lam * Real.exp 1) := by norm_num
      rw [hcast]
      have hsq : ((2 : ℝ) / (lam * Real.exp 1)) ^ 2 ≤ (12 * (M : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hquot 2
      nlinarith only [hsq]
    refine hmain.trans ?_
    have hcoe : (288 : ℝ≥0∞) * (M : ℝ≥0∞) ^ 2 = ENNReal.ofReal (288 * (M : ℝ) ^ 2) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow M.coe_nonneg,
        ENNReal.ofReal_coe_nnreal]
      norm_num
    rw [hcoe, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hreal

/-- **Paley--Zygmund for the exit time.**  A uniform bound `M` on the expected exit time from `U`,
valid from every starting point, together with a lower bound `mLow` on the expected exit time from
the single starting point `x`, bounds the probability of surviving the level `rho * mLow`:
`(1 - rho) ^ 2 * mLow ^ 2 ≤ 288 * M ^ 2 * Q_x {rho * mLow ≤ tau_U}`.  The subtraction is the
truncated one of `ℝ≥0∞`, so a level `rho ≥ 1` leaves the trivial bound. -/
theorem IsConservative.sq_le_mul_measure_le_exitTime_of_lintegral_le
    (hFeller : P.IsFellerKernelSemigroup) (hKol : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (M : ℝ≥0)
    (hM : ∀ y, ∫⁻ omega, ContinuousPath.exitTime U omega
      ∂(IsConservative.continuousProcess P hP y) ≤ (M : ℝ≥0∞))
    (mLow rho : ℝ≥0) (x : alpha)
    (hlow : (mLow : ℝ≥0∞) ≤ ∫⁻ omega, ContinuousPath.exitTime U omega
      ∂(IsConservative.continuousProcess P hP x)) :
    ((1 : ℝ≥0∞) - rho) ^ 2 * (mLow : ℝ≥0∞) ^ 2 ≤
      288 * (M : ℝ≥0∞) ^ 2 *
        IsConservative.continuousProcess P hP x
          {omega | (rho : ℝ≥0∞) * (mLow : ℝ≥0∞) ≤ ContinuousPath.exitTime U omega} := by
  have hfin : ∫⁻ omega, ContinuousPath.exitTime U omega
      ∂(IsConservative.continuousProcess P hP x) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (hM x)
  have hPZ := lintegral_sq_mul_measure_ge_le (IsConservative.continuousProcess P hP x)
    (ContinuousPath.measurable_exitTime U hU) hfin rho
  have hsubset :
      {omega | (rho : ℝ≥0∞) * ∫⁻ eta, ContinuousPath.exitTime U eta
          ∂(IsConservative.continuousProcess P hP x) ≤ ContinuousPath.exitTime U omega} ⊆
        {omega | (rho : ℝ≥0∞) * (mLow : ℝ≥0∞) ≤ ContinuousPath.exitTime U omega} := by
    intro omega homega
    exact le_trans (mul_le_mul_right hlow _) homega
  calc
    ((1 : ℝ≥0∞) - rho) ^ 2 * (mLow : ℝ≥0∞) ^ 2
        ≤ ((1 : ℝ≥0∞) - rho) ^ 2 * (∫⁻ omega, ContinuousPath.exitTime U omega
            ∂(IsConservative.continuousProcess P hP x)) ^ 2 := by gcongr
    _ ≤ (∫⁻ omega, ContinuousPath.exitTime U omega ^ 2
            ∂(IsConservative.continuousProcess P hP x)) *
          IsConservative.continuousProcess P hP x
            {omega | (rho : ℝ≥0∞) * ∫⁻ eta, ContinuousPath.exitTime U eta
              ∂(IsConservative.continuousProcess P hP x) ≤ ContinuousPath.exitTime U omega} :=
      hPZ
    _ ≤ 288 * (M : ℝ≥0∞) ^ 2 *
          IsConservative.continuousProcess P hP x
            {omega | (rho : ℝ≥0∞) * (mLow : ℝ≥0∞) ≤ ContinuousPath.exitTime U omega} :=
      mul_le_mul' (IsConservative.lintegral_exitTime_sq_le_of_lintegral_le P hP hFeller hKol U hU
        M hM x)
        (measure_mono hsubset)

/-- **Survival above half the guaranteed mean.**  The level `rho = 1 / 2` of
`IsConservative.sq_le_mul_measure_le_exitTime_of_lintegral_le`:
`mLow ^ 2 ≤ 1152 * M ^ 2 * Q_x {mLow / 2 ≤ tau_U}`. -/
theorem IsConservative.sq_le_mul_measure_half_le_exitTime_of_lintegral_le
    (hFeller : P.IsFellerKernelSemigroup) (hKol : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (M : ℝ≥0)
    (hM : ∀ y, ∫⁻ omega, ContinuousPath.exitTime U omega
      ∂(IsConservative.continuousProcess P hP y) ≤ (M : ℝ≥0∞))
    (mLow : ℝ≥0) (x : alpha)
    (hlow : (mLow : ℝ≥0∞) ≤ ∫⁻ omega, ContinuousPath.exitTime U omega
      ∂(IsConservative.continuousProcess P hP x)) :
    (mLow : ℝ≥0∞) ^ 2 ≤
      1152 * (M : ℝ≥0∞) ^ 2 *
        IsConservative.continuousProcess P hP x
          {omega | (mLow : ℝ≥0∞) / 2 ≤ ContinuousPath.exitTime U omega} := by
  have hhalf := IsConservative.sq_le_mul_measure_le_exitTime_of_lintegral_le P hP hFeller hKol U
    hU M hM
    mLow (1 / 2) x hlow
  have hcoe : (((1 : ℝ≥0) / 2 : ℝ≥0) : ℝ≥0∞) = 2⁻¹ := by
    rw [ENNReal.coe_div (by norm_num)]
    norm_num
  have hone : (1 : ℝ≥0∞) - (((1 : ℝ≥0) / 2 : ℝ≥0) : ℝ≥0∞) = 2⁻¹ := by
    rw [hcoe]
    exact ENNReal.sub_eq_of_eq_add (by simp) (ENNReal.inv_two_add_inv_two).symm
  have hset : {omega | ((((1 : ℝ≥0) / 2 : ℝ≥0)) : ℝ≥0∞) * (mLow : ℝ≥0∞) ≤
        ContinuousPath.exitTime U omega} =
      {omega | (mLow : ℝ≥0∞) / 2 ≤ ContinuousPath.exitTime U omega} := by
    ext omega
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hcoe, ENNReal.div_eq_inv_mul]
  rw [hone, hset] at hhalf
  have hfour : (4 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 2) = 1 := by
    rw [← ENNReal.inv_pow]
    norm_num
    rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  calc
    (mLow : ℝ≥0∞) ^ 2 = 4 * ((2 : ℝ≥0∞)⁻¹ ^ 2) * (mLow : ℝ≥0∞) ^ 2 := by
      rw [hfour, one_mul]
    _ = 4 * (((2 : ℝ≥0∞)⁻¹ ^ 2) * (mLow : ℝ≥0∞) ^ 2) := by rw [mul_assoc]
    _ ≤ 4 * (288 * (M : ℝ≥0∞) ^ 2 *
          IsConservative.continuousProcess P hP x
            {omega | (mLow : ℝ≥0∞) / 2 ≤ ContinuousPath.exitTime U omega}) :=
      mul_le_mul_right hhalf 4
    _ = 1152 * (M : ℝ≥0∞) ^ 2 *
          IsConservative.continuousProcess P hP x
            {omega | (mLow : ℝ≥0∞) / 2 ≤ ContinuousPath.exitTime U omega} := by
      rw [← mul_assoc, ← mul_assoc]
      norm_num

end

end SubMarkovKernelSemigroup

end Algsuperdiff.Process
