/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.BaseCaseAllScaleError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.BaseCaseMStarError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.InductionStart

/-!
# BaseCaseAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Final assembly of the Section 3 base case

This module combines the three proved base-error regimes with the annealed
plateau estimates and constructs the induction state at `m**`.  A single
positive constant depending only on `d` is chosen before the model and every
scale parameter.  It is the sum of the constants used by the `m**` and `m*`
error regimes, so each of the three error conclusions follows by monotonicity
of its tail scale.

The terminal endpoint in the induction-state error window is proved directly.
For `s` in `[8 gamma, 1]`, the open-interval base estimate is applied at
`min s (1/2)`, transported to `s` by antitonicity of the cutoff error, and
bounded using `sqrt (baseLoss d u) <= K u^-1`.  The factor two from
`(min s (1/2))^-1 <= 2 s^-1` is absorbed into the chosen start constant.
-/

namespace Algsuperdiff.Section3.Provider.Base

open HCPolySupport MeasureTheory
open HCPolySupport.IndependentSums
open Algsuperdiff.Section3.Provider.Scales

noncomputable section

variable {d : ℕ}

/-- The common dimension-only error constant for all three base regimes. -/
noncomputable def baseCaseErrorConst (d : ℕ) : ℝ :=
  baseCaseMStarStarErrorConst d + cutoffMassSqrtConst d

/-- The common base-error constant is strictly positive. -/
theorem baseCaseErrorConst_pos (d : ℕ) : 0 < baseCaseErrorConst d := by
  exact add_pos (baseCaseMStarStarErrorConst_pos d) (cutoffMassSqrtConst_pos d)

private theorem baseCaseMStarStarErrorConst_le (d : ℕ) :
    baseCaseMStarStarErrorConst d ≤ baseCaseErrorConst d := by
  exact le_add_of_nonneg_right (cutoffMassSqrtConst_pos d).le

private theorem cutoffMassSqrtConst_le_baseCaseErrorConst (d : ℕ) :
    cutoffMassSqrtConst d ≤ baseCaseErrorConst d := by
  exact le_add_of_nonneg_left (baseCaseMStarStarErrorConst_pos d).le

private theorem isOneSidedOrlicz_mono_scale
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {Psi : ℝ → ℝ} {X : Omega → ℝ} {A B : ℝ}
    (h : Probability.IsOneSidedOrlicz mu Psi X A) (hAB : A ≤ B) :
    Probability.IsOneSidedOrlicz mu Psi X B := by
  exact ⟨h.1, lt_of_lt_of_le h.2.1 hAB, h.2.2.1, h.2.2.2.mono_scale hAB⟩

private theorem isDeterministicShiftOneSidedOrlicz_mono_scale
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {Psi : ℝ → ℝ} {X : Omega → ℝ} {b A B : ℝ}
    (h : Probability.IsDeterministicShiftOneSidedOrlicz mu Psi X b A)
    (hAB : A ≤ B) :
    Probability.IsDeterministicShiftOneSidedOrlicz mu Psi X b B := by
  exact ⟨h.1, lt_of_lt_of_le h.2.1 hAB, h.2.2.1, h.2.2.2.mono_scale hAB⟩

private theorem isTwoTermBigOWith_mono_scales
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {Psi1 Psi2 : ℝ → ℝ} {X : Omega → ℝ} {A1 A2 B1 B2 : ℝ}
    (h : Probability.IsTwoTermBigOWith mu Psi1 Psi2 X A1 A2)
    (hA1 : A1 ≤ B1) (hA2 : A2 ≤ B2) :
    Probability.IsTwoTermBigOWith mu Psi1 Psi2 X B1 B2 := by
  obtain ⟨Y, Z, hPsi1, hPsi2, hA1pos, hA2pos, hXmeas, hYmeas, hZmeas,
    hdom, hYtail, hZtail⟩ := h
  exact ⟨Y, Z, hPsi1, hPsi2, lt_of_lt_of_le hA1pos hA1,
    lt_of_lt_of_le hA2pos hA2, hXmeas, hYmeas, hZmeas, hdom,
    hYtail.mono_scale hA1, hZtail.mono_scale hA2⟩

private theorem cutoffHomogenizationError_isTwoTermBigOWith_common
    (M : ABKModel d) (m : ℤ) (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2) (gammaSigma 4)
      (Observable.cutoffHomogenizationError M m
        ⟨(s : ℝ), (Set.mem_Ioo.mp s.2).1⟩)
      (baseCaseErrorConst d * M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
        (3 : ℝ) ^ (M.gamma * (m : ℝ)) * Real.sqrt (baseLoss d s))
      (baseCaseErrorConst d * (Real.sqrt M.nu)⁻¹ *
        (Real.sqrt (Real.sqrt M.gamma))⁻¹ *
          (3 : ℝ) ^ (M.gamma * (m : ℝ) / 2) *
            Real.sqrt (Real.sqrt (baseLoss d s))) := by
  have h := cutoffHomogenizationError_isTwoTermBigOWith_allScale M m s
  apply isTwoTermBigOWith_mono_scales h
  · have hcore : 0 ≤ M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
        (3 : ℝ) ^ (M.gamma * (m : ℝ)) * Real.sqrt (baseLoss d s) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (inv_nonneg.mpr M.nu_pos.le)
            (inv_nonneg.mpr (Real.sqrt_nonneg _)))
          (Real.rpow_nonneg (by norm_num) _))
        (Real.sqrt_nonneg _)
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (baseCaseMStarStarErrorConst_le d) hcore
  · have hcore : 0 ≤ (Real.sqrt M.nu)⁻¹ *
        (Real.sqrt (Real.sqrt M.gamma))⁻¹ *
          (3 : ℝ) ^ (M.gamma * (m : ℝ) / 2) *
            Real.sqrt (Real.sqrt (baseLoss d s)) := by
      positivity
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (baseCaseMStarStarErrorConst_le d) hcore

private theorem cutoffHomogenizationError_isOneSidedOrlicz_common
    (M : ABKModel d) (m : ℤ) (hm : m ≤ mStarStar M)
    (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    Probability.IsOneSidedOrlicz
      (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (Observable.cutoffHomogenizationError M m
        ⟨(s : ℝ), (Set.mem_Ioo.mp s.2).1⟩)
      (baseCaseErrorConst d * (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
        Real.sqrt M.gamma * Real.sqrt (baseLoss d s)) := by
  have h := cutoffHomogenizationError_isOneSidedOrlicz_le_mStarStar M m hm s
  apply isOneSidedOrlicz_mono_scale h
  have hcore : 0 ≤ (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
      Real.sqrt M.gamma * Real.sqrt (baseLoss d s) := by
    positivity
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (baseCaseMStarStarErrorConst_le d) hcore

private theorem cutoffHomogenizationError_isDeterministicShiftOneSidedOrlicz_common
    (M : ABKModel d) (m : ℤ) (hm : m ≤ mStar M)
    (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    Probability.IsDeterministicShiftOneSidedOrlicz
      (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (Observable.cutoffHomogenizationError M m
        ⟨(s : ℝ), (Set.mem_Ioo.mp s.2).1⟩)
      2
      (baseCaseErrorConst d * (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
        Real.sqrt (baseLoss d s)) := by
  have h := cutoffHomogenizationError_isDeterministicShiftOneSidedOrlicz_le_mStar M m hm s
  apply isDeterministicShiftOneSidedOrlicz_mono_scale h
  have hcore : 0 ≤ (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
      Real.sqrt (baseLoss d s) := by
    positivity
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (cutoffMassSqrtConst_le_baseCaseErrorConst d) hcore

/-- A proved local corrected base-case assembly, with one common dimension-only
error constant and a directly assembled induction start. -/
theorem base_case
    (d : ℕ) :
    ∃ C0 Cstart : ℝ, 0 < C0 ∧ 0 < Cstart ∧
      ∀ M : ABKModel d,
        (∀ m : ℤ,
          M.nu ≤ (Annealed.sigmaBar M m : ℝ) ∧
          (Annealed.sigmaBar M m : ℝ) ≤
            M.nu *
              (1 + Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ *
                M.gamma⁻¹ * (1 + 4 * M.gamma) *
                  (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ∧
          ∀ s : {s : ℝ // s ∈ Set.Ioo 0 1},
            Probability.IsTwoTermBigOWith
              (Cutoff.cutoffSampleLaw M).toMeasure
              (HCPolySupport.IndependentSums.gammaSigma 2)
              (HCPolySupport.IndependentSums.gammaSigma 4)
              (Observable.cutoffHomogenizationError M m
                ⟨(s : ℝ), s.property.1⟩)
              (C0 * M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
                (3 : ℝ) ^ (M.gamma * (m : ℝ)) *
                  Real.sqrt (baseLoss d s))
              (C0 * (Real.sqrt M.nu)⁻¹ *
                (Real.sqrt (Real.sqrt M.gamma))⁻¹ *
                  (3 : ℝ) ^ (M.gamma * (m : ℝ) / 2) *
                    Real.sqrt (Real.sqrt (baseLoss d s)))) ∧
        (∀ m : ℤ, m ≤ mStarStar M →
          M.nu ≤ (Annealed.sigmaBar M m : ℝ) ∧
          (Annealed.sigmaBar M m : ℝ) ≤ (1 + M.gamma ^ 2) * M.nu ∧
          ∀ s : {s : ℝ // s ∈ Set.Ioo 0 1},
            Probability.IsOneSidedOrlicz
              (Cutoff.cutoffSampleLaw M).toMeasure
              (HCPolySupport.IndependentSums.gammaSigma 2)
              (Observable.cutoffHomogenizationError M m
                ⟨(s : ℝ), s.property.1⟩)
              (C0 * (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
                Real.sqrt M.gamma * Real.sqrt (baseLoss d s))) ∧
        (∀ m : ℤ, m ≤ mStar M →
          M.nu ≤ (Annealed.sigmaBar M m : ℝ) ∧
          (Annealed.sigmaBar M m : ℝ) ≤ 2 * M.nu ∧
          ∀ s : {s : ℝ // s ∈ Set.Ioo 0 1},
            Probability.IsDeterministicShiftOneSidedOrlicz
              (Cutoff.cutoffSampleLaw M).toMeasure
              (HCPolySupport.IndependentSums.gammaSigma 2)
              (Observable.cutoffHomogenizationError M m
                ⟨(s : ℝ), s.property.1⟩)
              2
              (C0 * (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
                Real.sqrt (baseLoss d s))) ∧
        ∃ Estart : {E : ℝ // 1 ≤ E},
          (Estart : ℝ) = Cstart * (Real.sqrt (Disorder.cstar M))⁻¹ ∧
          Algsuperdiff.Frozen.Section3.inductionState
            M (mStarStar M) Estart := by
  let K : ℝ := Real.sqrt (1 + 6 * (d : ℝ) * Real.log 3)
  let Cstart : ℝ := max 2 (2 * baseCaseErrorConst d * K)
  have hKpos : 0 < K := by
    dsimp only [K]
    refine Real.sqrt_pos.mpr ?_
    have h : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.log 3 :=
      mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
    linarith
  have hbase : ∀ u : {s : ℝ // s ∈ Set.Ioo 0 1},
      Real.sqrt (baseLoss d u) ≤ K * (u : ℝ)⁻¹ := by
    exact Scales.sqrt_baseLoss_le d
  have hCstart : 0 < Cstart := by
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨baseCaseErrorConst d, Cstart, baseCaseErrorConst_pos d, hCstart, ?_⟩
  intro M
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    obtain ⟨hlow, hup⟩ := annealedPlateau M m
    exact ⟨hlow, hup, fun s ↦
      cutoffHomogenizationError_isTwoTermBigOWith_common M m s⟩
  · intro m hm
    obtain ⟨hlow, hup⟩ := annealedPlateau_le_mStarStar M m hm
    exact ⟨hlow, hup, fun s ↦
      cutoffHomogenizationError_isOneSidedOrlicz_common M m hm s⟩
  · intro m hm
    obtain ⟨hlow, hup⟩ := annealedPlateau_le_mStar M m hm
    exact ⟨hlow, hup, fun s ↦
      cutoffHomogenizationError_isDeterministicShiftOneSidedOrlicz_common M m hm s⟩
  · have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
    have hcs : (0 : ℝ) < Disorder.cstar M :=
      (Disorder.cstar_characterization M).1
    have hsq : (0 : ℝ) < Real.sqrt (Disorder.cstar M) := Real.sqrt_pos.mpr hcs
    have hsqle : Real.sqrt (Disorder.cstar M) ≤ 2 := by
      have h := Real.sqrt_le_sqrt
        (show Disorder.cstar M ≤ 2 ^ 2 by
          linarith [Provider.Disorder.cstar_le_three_halves M])
      rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
    have hEge : (1 : ℝ) ≤ Cstart * (Real.sqrt (Disorder.cstar M))⁻¹ := by
      have hinv : (2 : ℝ)⁻¹ ≤ (Real.sqrt (Disorder.cstar M))⁻¹ := by
        rw [inv_le_inv₀ (by norm_num : (0 : ℝ) < 2) hsq]
        exact hsqle
      calc
        (1 : ℝ) = 2 * (2 : ℝ)⁻¹ := by norm_num
        _ ≤ Cstart * (Real.sqrt (Disorder.cstar M))⁻¹ :=
          mul_le_mul (show (2 : ℝ) ≤ Cstart by
            exact le_max_left _ _) hinv (by norm_num) (by positivity)
    refine ⟨⟨Cstart * (Real.sqrt (Disorder.cstar M))⁻¹, hEge⟩, rfl,
      inductionState_diffusivity M, ?_⟩
    intro m hm s hsWindow
    have hs0 : (0 : ℝ) < s :=
      (mul_pos (by norm_num : (0 : ℝ) < 8) hg).trans_le hsWindow.1
    have hu0 : (0 : ℝ) < min s (1 / 2) := lt_min hs0 (by norm_num)
    have hu1 : min s (1 / 2) < 1 :=
      lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hinvs : (0 : ℝ) < s⁻¹ := inv_pos.mpr hs0
    have hsg : (0 : ℝ) ≤ Real.sqrt M.gamma := Real.sqrt_nonneg _
    have hAs : Probability.IsOneSidedOrlicz
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma 2)
        (Observable.cutoffHomogenizationError M m ⟨s, hs0⟩)
        (baseCaseErrorConst d * (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
          Real.sqrt M.gamma *
            Real.sqrt (baseLoss d ⟨min s (1 / 2), ⟨hu0, hu1⟩⟩)) :=
      isOneSidedOrlicz_cutoffHomogenizationError_of_le M m hu0
        (min_le_left s (1 / 2))
        (cutoffHomogenizationError_isOneSidedOrlicz_common M m hm
          ⟨min s (1 / 2), ⟨hu0, hu1⟩⟩)
    have hinvcmp : (Real.sqrt (Disorder.cstarPlus M))⁻¹ ≤
        (Real.sqrt (Disorder.cstar M))⁻¹ := by
      rw [inv_le_inv₀ (Real.sqrt_pos.mpr (Disorder.cstarPlus_pos M)) hsq]
      exact sqrt_cstar_le_sqrt_cstarPlus M
    have huinv : (min s (1 / 2))⁻¹ ≤ 2 * s⁻¹ := by
      have hhalf : s / 2 ≤ min s (1 / 2) :=
        le_min (by linarith) (by linarith [hsWindow.2])
      calc
        (min s (1 / 2))⁻¹ ≤ (s / 2)⁻¹ := by
          rw [inv_le_inv₀ hu0 (by linarith : (0 : ℝ) < s / 2)]
          exact hhalf
        _ = 2 * s⁻¹ := by
          rw [div_eq_mul_inv, mul_inv, inv_inv]
          ring
    have hcmp : baseCaseErrorConst d *
        (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma *
          Real.sqrt (baseLoss d ⟨min s (1 / 2), ⟨hu0, hu1⟩⟩) ≤
        Cstart * (Real.sqrt (Disorder.cstar M))⁻¹ * s⁻¹ *
          Real.sqrt M.gamma := by
      have hb1 : Real.sqrt (baseLoss d ⟨min s (1 / 2), ⟨hu0, hu1⟩⟩) ≤
          K * (2 * s⁻¹) :=
        le_trans (hbase ⟨min s (1 / 2), ⟨hu0, hu1⟩⟩)
          (mul_le_mul_of_nonneg_left huinv hKpos.le)
      have hc1 : (0 : ℝ) ≤ baseCaseErrorConst d *
          (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma := by
        exact mul_nonneg
          (mul_nonneg (baseCaseErrorConst_pos d).le
            (inv_nonneg.mpr (Real.sqrt_nonneg _)))
          (Real.sqrt_nonneg _)
      have hc2 : baseCaseErrorConst d *
          (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma ≤
          baseCaseErrorConst d * (Real.sqrt (Disorder.cstar M))⁻¹ *
            Real.sqrt M.gamma :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hinvcmp (baseCaseErrorConst_pos d).le) hsg
      calc
        baseCaseErrorConst d * (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
              Real.sqrt M.gamma *
              Real.sqrt (baseLoss d ⟨min s (1 / 2), ⟨hu0, hu1⟩⟩)
            ≤ baseCaseErrorConst d * (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
              Real.sqrt M.gamma * (K * (2 * s⁻¹)) :=
          mul_le_mul_of_nonneg_left hb1 hc1
        _ ≤ baseCaseErrorConst d * (Real.sqrt (Disorder.cstar M))⁻¹ *
              Real.sqrt M.gamma * (K * (2 * s⁻¹)) :=
          mul_le_mul_of_nonneg_right hc2 (by positivity)
        _ = 2 * baseCaseErrorConst d * K *
              ((Real.sqrt (Disorder.cstar M))⁻¹ * s⁻¹ *
                Real.sqrt M.gamma) := by ring
        _ ≤ Cstart * ((Real.sqrt (Disorder.cstar M))⁻¹ * s⁻¹ *
              Real.sqrt M.gamma) :=
          mul_le_mul_of_nonneg_right (show 2 * baseCaseErrorConst d * K ≤ Cstart by
            exact le_max_right _ _)
            (mul_nonneg
              (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hinvs.le) hsg)
        _ = Cstart * (Real.sqrt (Disorder.cstar M))⁻¹ * s⁻¹ *
              Real.sqrt M.gamma := by ring
    exact Provider.Orlicz.isTwoTermBigOWith_of_isOneSidedOrlicz
      (by norm_num) (by norm_num) hAs hcmp
      (mul_pos (mul_pos (mul_pos hCstart (inv_pos.mpr hsq)) hinvs)
        (Real.sqrt_pos.mpr hg))
      (mul_pos (pow_pos hinvs 2) (Real.exp_pos _))

end

end Algsuperdiff.Section3.Provider.Base
