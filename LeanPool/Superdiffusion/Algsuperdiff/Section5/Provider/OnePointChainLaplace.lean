/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.ExitTimeJointCarrier
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.OnePointChainTrace

/-!
# OnePointChainLaplace

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The survival probability and the padded family, on a general carrier

The one-step Laplace contraction rests on the Paley--Zygmund survival probability of the exit
time, and the chaining estimate consumes the resulting per-cell bounds as one padded family.
Both are stated here on an arbitrary carrier, the cube being read inside it by a map `emb` and
the cell by an open set carrying no other starting point.  Neither argument uses anything about
the state space: the survival probability is the Paley--Zygmund inequality at the level one half,
and the reindexing contributes no starting point at a padded index.

## Main results

* `survivalProbabilityConstant_le_measure_le_exitTime_on` — the survival probability on a carrier.
* `one_step_laplace_hone_of_partition_cubes_image` — the padded-family form of a scale-by-scale
  cube estimate on a carrier.

## References

* ABK26, the one-step Laplace estimate of Section 5.3.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support Algsuperdiff.Section5.Trace
open DivergenceFormProcess.StoppedDirichlet
open HCPolySupport MarkovProcess MarkovProcess.SubMarkovKernelSemigroup MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

/-! ## 1. The survival probability on a carrier -/

section Survival

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

/-- **Survival at half the guaranteed expected exit time, on a general carrier.**  This is the
Paley--Zygmund estimate, whose proof uses
no property of the state space: an upper bound `Cup * T` on the expected exit time from the open
set `U`, valid from every starting point, and a lower bound `clow * T` at the starting point `x`,
give `clow ^ 2 / (1152 * Cup ^ 2) ≤ Q_x {clow * T / 2 ≤ tau_U}`. -/
theorem survivalProbabilityConstant_le_measure_le_exitTime_on
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hKol : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (T Cup clow : ℝ≥0) (hT : 0 < T)
    (hupper : ∀ y, ∫⁻ eta, ContinuousPath.exitTime U eta
      ∂(hP.continuousProcess P y) ≤ ((Cup * T : ℝ≥0) : ℝ≥0∞))
    (x : alpha)
    (hlower : ((clow * T : ℝ≥0) : ℝ≥0∞) ≤
      ∫⁻ eta, ContinuousPath.exitTime U eta ∂(hP.continuousProcess P x)) :
    ((survivalProbabilityConstant Cup clow : ℝ≥0) : ℝ≥0∞) ≤
      hP.continuousProcess P x
        {eta | ((clow * T / 2 : ℝ≥0) : ℝ≥0∞) ≤ ContinuousPath.exitTime U eta} := by
  have hhalf : (((clow * T / 2 : ℝ≥0)) : ℝ≥0∞) = ((clow * T : ℝ≥0) : ℝ≥0∞) / 2 := by
    rw [ENNReal.coe_div (by norm_num)]
    norm_num
  have hmain :=
    Algsuperdiff.Process.SubMarkovKernelSemigroup.IsConservative.sq_le_mul_measure_half_le_exitTime_of_lintegral_le
      P hP hFeller hKol U hU
    (Cup * T) hupper (clow * T) x hlower
  rw [← hhalf] at hmain
  set mu : ℝ≥0∞ := hP.continuousProcess P x
    {eta | ((clow * T / 2 : ℝ≥0) : ℝ≥0∞) ≤ ContinuousPath.exitTime U eta} with hmu
  have hTsq : ((T : ℝ≥0∞)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hT.ne')
  have hTtop : ((T : ℝ≥0∞)) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hcancel : (T : ℝ≥0∞) ^ 2 * (clow : ℝ≥0∞) ^ 2 ≤
      (T : ℝ≥0∞) ^ 2 * (1152 * (Cup : ℝ≥0∞) ^ 2 * mu) := by
    calc
      (T : ℝ≥0∞) ^ 2 * (clow : ℝ≥0∞) ^ 2 = ((clow * T : ℝ≥0) : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.coe_mul, mul_pow]
        ring
      _ ≤ 1152 * ((Cup * T : ℝ≥0) : ℝ≥0∞) ^ 2 * mu := hmain
      _ = (T : ℝ≥0∞) ^ 2 * (1152 * (Cup : ℝ≥0∞) ^ 2 * mu) := by
        rw [ENNReal.coe_mul, mul_pow]
        ring
  have hstep : (clow : ℝ≥0∞) ^ 2 ≤ 1152 * (Cup : ℝ≥0∞) ^ 2 * mu :=
    (ENNReal.mul_le_mul_iff_right hTsq hTtop).mp hcancel
  rcases eq_or_ne Cup 0 with hCup | hCup
  · have hzero : survivalProbabilityConstant Cup clow = 0 := by
      rw [survivalProbabilityConstant, hCup]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, div_zero]
    rw [hzero, ENNReal.coe_zero]
    exact zero_le
  · have hden : (1152 * Cup ^ 2 : ℝ≥0) ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 hCup)
    rw [survivalProbabilityConstant, ENNReal.coe_div hden]
    refine ENNReal.div_le_of_le_mul ?_
    rw [ENNReal.coe_mul, ENNReal.coe_pow]
    calc
      ((clow : ℝ≥0∞)) ^ 2 = ((clow : ℝ≥0) : ℝ≥0∞) ^ 2 := rfl
      _ ≤ 1152 * (Cup : ℝ≥0∞) ^ 2 * mu := hstep
      _ = mu * (((1152 : ℝ≥0) : ℝ≥0∞) * (Cup : ℝ≥0∞) ^ 2) := by
        push_cast
        ring

end Survival

/-! ## 3. The padded family of the chaining estimate -/

/-- Reindex a scale-by-scale cube estimate on a carrier into the literal `hone` family of the
chaining estimate.  The padded indices contribute no starting points. -/
theorem one_step_laplace_hone_of_partition_cubes_image {d r : ℕ} {alpha : Type*}
    [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
    [SecondCountableTopology alpha] [Nonempty alpha]
    (emb : C(Vec d, alpha)) (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (n : ℤ) (sites : Fin r ↪ Section5.Percolation.Site d) (lam : ℝ) (rho : ℝ≥0∞)
    (hstep : ∀ j : Fin r, ∀ z ∈ closure (cubeSetAt (rescaleSite n (sites j)) n),
      ∫⁻ eta, Algsuperdiff.Process.ContinuousPath.discountedStoppingWeight lam
          (ContinuousPath.exitTime
            (emb '' cubeSetAt (rescaleSite n (sites j)) (n + 1))) eta
        ∂(hP.continuousProcess P (emb z)) ≤ rho) :
    ∀ i, ∀ z ∈ emb '' enumeratedClosedCubeFamily n sites i,
      ∫⁻ eta, Algsuperdiff.Process.ContinuousPath.discountedStoppingWeight lam
          (ContinuousPath.exitTime
            (emb '' enumeratedOpenEnlargementFamily n sites i)) eta
        ∂(hP.continuousProcess P z) ≤ rho := by
  rintro i _ ⟨z, hz, rfl⟩
  unfold enumeratedClosedCubeFamily at hz
  unfold enumeratedOpenEnlargementFamily
  split
  next hi =>
    rw [dite_eq_left hi] at hz
    have hz' : z ∈ closure (cubeSetAt (rescaleSite n (sites ⟨i, hi⟩)) n) := by
      simpa only [closedPartitionCube, closure_cubeSetAt] using hz
    have hopen : openEnlargedPartitionCube n (sites ⟨i, hi⟩) =
        cubeSetAt (rescaleSite n (sites ⟨i, hi⟩)) (n + 1) := by
      rw [openEnlargedPartitionCube, cubeSetAt_eq_ball]
      congr 1
      rw [zpow_add_one₀ (by positivity : (3 : ℝ) ≠ 0)]
      ring
    rw [hopen]
    exact hstep ⟨i, hi⟩ z hz'
  next hi =>
    rw [dite_eq_right hi] at hz
    exact False.elim hz

end

end Algsuperdiff.Section5.Provider
