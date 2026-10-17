/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.ExitTimeHomogenizationJointMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Trace.SurvivalProbability
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Trace.HitExitBridge
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.ExitTimeLaplace

/-!
# OneStepLaplace

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# One-step Laplace contraction on a good cube

The Paley--Zygmund survival probability on the inner cube is converted into a
strict contraction for the negative exponential of the exit time from the
enlarged cube.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open Algsuperdiff.Section5.Trace
open DivergenceFormProcess.StoppedDirichlet
open HCPolySupport MarkovProcess MarkovProcess.SubMarkovKernelSemigroup MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

/-- The one-step contraction obtained from survival at half the lower exit-time
scale and discount rate `(Cup * T)⁻¹`. -/
def oneStepLaplaceContraction (Cup clow : ℝ≥0) : ℝ≥0∞ :=
  1 - (survivalProbabilityConstant Cup clow : ℝ≥0∞) *
    (1 - ENNReal.ofReal (Real.exp (-(clow : ℝ) / (2 * Cup))))

private theorem ennreal_exp_neg_le_one {a : ℝ} (ha : 0 ≤ a) :
    ENNReal.ofReal (Real.exp (-a)) ≤ 1 := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha))

private theorem contraction_algebra {p q e : ℝ≥0∞}
    (hpq : p ≤ q) (hq : q ≤ 1) (he : e ≤ 1) :
    e * q + (1 - q) ≤ 1 - p * (1 - e) := by
  have hp : p ≤ 1 := hpq.trans hq
  have hpTop : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp
  have hqTop : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq
  have heTop : e ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top he
  have hleftTop : e * q + (1 - q) ≠ ⊤ := by
    apply ENNReal.add_ne_top.2
    exact ⟨ENNReal.mul_ne_top heTop hqTop,
      ENNReal.sub_ne_top ENNReal.one_ne_top⟩
  have hrightTop : 1 - p * (1 - e) ≠ ⊤ :=
    ENNReal.sub_ne_top ENNReal.one_ne_top
  have hprod : p * (1 - e) ≤ 1 := by
    calc
      p * (1 - e) ≤ 1 * (1 - e) :=
        mul_le_mul_of_nonneg_right hp zero_le
      _ ≤ 1 := by simpa only [one_mul] using (tsub_le_self : 1 - e ≤ 1)
  apply (ENNReal.toReal_le_toReal hleftTop hrightTop).mp
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top heTop hqTop)
      (ENNReal.sub_ne_top ENNReal.one_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hq ENNReal.one_ne_top,
    ENNReal.toReal_one,
    ENNReal.toReal_sub_of_le hprod ENNReal.one_ne_top, ENNReal.toReal_one,
    ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le he ENNReal.one_ne_top, ENNReal.toReal_one]
  have hpqReal : p.toReal ≤ q.toReal := ENNReal.toReal_mono hqTop hpq
  have hmul := mul_le_mul_of_nonneg_left hpqReal
    (sub_nonneg.mpr (ENNReal.toReal_mono ENNReal.one_ne_top he))
  calc
    e.toReal * q.toReal + (1 - q.toReal) =
        1 - (1 - e.toReal) * q.toReal := by ring
    _ ≤ 1 - (1 - e.toReal) * p.toReal := sub_le_sub_left hmul 1
    _ = 1 - p.toReal * (1 - e.toReal) := by ring

section Generic

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

omit [LocallyCompactSpace alpha] in
/-- A uniform lower survival probability gives the one-step Laplace
contraction at rate `(Cup * T)⁻¹`. -/
theorem lintegral_discountedExitTime_le_oneStepLaplaceContraction
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    {U : Set alpha} (hU : IsOpen U) (T Cup clow : ℝ≥0)
    (hT : 0 < T) (hCup : 0 < Cup) (x : alpha)
    (hsurv : ((survivalProbabilityConstant Cup clow : ℝ≥0) : ℝ≥0∞) ≤
      hP.continuousProcess P x
        {eta | ((clow * T / 2 : ℝ≥0) : ℝ≥0∞) ≤ ContinuousPath.exitTime U eta}) :
    ∫⁻ eta, Algsuperdiff.Process.ContinuousPath.discountedStoppingWeight
        ((Cup : ℝ) * (T : ℝ))⁻¹ (ContinuousPath.exitTime U) eta
      ∂(hP.continuousProcess P x) ≤ oneStepLaplaceContraction Cup clow := by
  let Q : Measure (ContinuousPath alpha) := hP.continuousProcess P x
  let a : ℝ≥0 := clow * T / 2
  let A : Set (ContinuousPath alpha) := {eta | (a : ℝ≥0∞) ≤ ContinuousPath.exitTime U eta}
  let lam : ℝ := ((Cup : ℝ) * (T : ℝ))⁻¹
  let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(clow : ℝ) / (2 * Cup)))
  let p : ℝ≥0∞ := survivalProbabilityConstant Cup clow
  have hlam : 0 < lam := by unfold lam; positivity
  have haMeas : MeasurableSet A := by
    exact measurableSet_le measurable_const (ContinuousPath.measurable_exitTime U hU)
  have he : e ≤ 1 := by
    unfold e
    simpa only [neg_div] using ennreal_exp_neg_le_one
      (div_nonneg (NNReal.coe_nonneg clow) (by positivity : (0 : ℝ) ≤ 2 * Cup))
  have hpoint : Algsuperdiff.Process.ContinuousPath.discountedStoppingWeight lam
      (ContinuousPath.exitTime U) ≤
      fun eta ↦ A.indicator (fun _ ↦ e) eta + Aᶜ.indicator (fun _ ↦ 1) eta := by
    intro eta
    change Algsuperdiff.Process.ContinuousPath.discountedStoppingWeight lam
      (ContinuousPath.exitTime U) eta ≤
        A.indicator (fun _ ↦ e) eta + Aᶜ.indicator (fun _ ↦ 1) eta
    by_cases hetaA : eta ∈ A
    · rw [Set.indicator_of_mem hetaA, Set.indicator_of_notMem
        (show eta ∉ Aᶜ by simpa only [Set.mem_compl_iff, not_not])]
      simp only [add_zero]
      by_cases hfinite : ContinuousPath.exitTime U eta < ⊤
      · rw [Algsuperdiff.Process.ContinuousPath.discountedStoppingWeight, Set.indicator_of_mem
          (show eta ∈ {omega | ContinuousPath.exitTime U omega < ⊤} by exact hfinite)]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have htau : (a : ℝ) ≤ (ContinuousPath.exitTime U eta).toReal := by
          simpa only [ENNReal.coe_toReal] using
            (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hfinite.ne).mpr hetaA
        have hscale : lam * (a : ℝ) = (clow : ℝ) / (2 * Cup) := by
          unfold lam a
          push_cast
          field_simp [hCup.ne', hT.ne']
        have hmul := neg_le_neg (mul_le_mul_of_nonneg_left htau hlam.le)
        calc
          -lam * (ContinuousPath.exitTime U eta).toReal =
              -(lam * (ContinuousPath.exitTime U eta).toReal) := by ring
          _ ≤ -(lam * (a : ℝ)) := hmul
          _ = -(clow : ℝ) / (2 * Cup) := by rw [hscale]; ring
      · rw [Algsuperdiff.Process.ContinuousPath.discountedStoppingWeight, Set.indicator_of_notMem
          (show eta ∉ {omega | ContinuousPath.exitTime U omega < ⊤} by exact hfinite)]
        exact zero_le
    · rw [Set.indicator_of_notMem hetaA, Set.indicator_of_mem
        (show eta ∈ Aᶜ by simpa only [Set.mem_compl_iff])]
      simp only [zero_add]
      rw [Algsuperdiff.Process.ContinuousPath.discountedStoppingWeight]
      by_cases hfinite : ContinuousPath.exitTime U eta < ⊤
      · rw [Set.indicator_of_mem
          (show eta ∈ {omega | ContinuousPath.exitTime U omega < ⊤} by exact hfinite)]
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam.le) ENNReal.toReal_nonneg))
      · rw [Set.indicator_of_notMem
          (show eta ∉ {omega | ContinuousPath.exitTime U omega < ⊤} by exact hfinite)]
        exact zero_le
  have hq : Q A ≤ 1 := by
    calc
      Q A ≤ Q Set.univ := measure_mono (Set.subset_univ A)
      _ = 1 := measure_univ
  have hpq : p ≤ Q A := by
    simpa only [p, Q, A, a] using hsurv
  calc
    ∫⁻ eta, Algsuperdiff.Process.ContinuousPath.discountedStoppingWeight
        ((Cup : ℝ) * (T : ℝ))⁻¹ (ContinuousPath.exitTime U) eta ∂Q =
        ∫⁻ eta, Algsuperdiff.Process.ContinuousPath.discountedStoppingWeight lam
          (ContinuousPath.exitTime U) eta ∂Q := by rfl
    _ ≤ ∫⁻ eta, (A.indicator (fun _ ↦ e) eta +
          Aᶜ.indicator (fun _ ↦ 1) eta) ∂Q := lintegral_mono hpoint
    _ = e * Q A + Q Aᶜ := by
      rw [lintegral_add_left (measurable_const.indicator haMeas),
        lintegral_indicator_const haMeas,
        lintegral_indicator_const haMeas.compl]
      simp only [one_mul]
    _ = e * Q A + (1 - Q A) := by rw [prob_compl_eq_one_sub haMeas]
    _ ≤ 1 - p * (1 - e) := contraction_algebra hpq hq he
    _ = oneStepLaplaceContraction Cup clow := rfl

end Generic

end


end Algsuperdiff.Section5.Provider
