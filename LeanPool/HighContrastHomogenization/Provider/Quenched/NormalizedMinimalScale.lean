/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.MinimalScaleMeasurability

/-!
# High-contrast homogenization: Provider.Quenched.NormalizedMinimalScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalization of a quenched minimal scale

This file turns the abstract triadic minimal scale into the normalized random
mixing scale used by the random-source endgame.  In addition to the closed
stretched-exponential tail, it retains domination by the same raw scale and the
corresponding almost-everywhere all-later certificate.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open Filter MeasureTheory
open Book.Ch05.Section57 IndependentSums
open scoped Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Normalize an abstract triadic minimal scale while retaining its all-later
certificate.  The factor two converts the closed tail event for the normalized
scale into the strict event used by `IsBigOWith`. -/
theorem exists_normalized_quenchedMinimalScale_of_badTailEvent_bound
    {P : Measure Ω} [IsFiniteMeasure P]
    {N0 : ℕ} {Bad : ℕ → Set Ω} {B eta : ℝ}
    (hBad : ∀ n, MeasurableSet (Bad n))
    (heta : 0 < eta) (hB : 1 ≤ B)
    (htail :
      ∀ N : ℕ, N0 ≤ N →
        P.real (badTailEvent Bad N) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) ((N - N0 : ℕ) : ℝ)) / B) ^ eta))) :
    ∃ Rmix : Ω → ℝ,
      Measurable Rmix ∧
      (∀ ω, 1 ≤ Rmix ω) ∧
      (∀ t : ℝ, 1 ≤ t →
        P.real {ω | 2 * t ≤ Rmix ω} ≤ Real.exp (-(t ^ eta))) ∧
      (∀ ω,
        quenchedMinimalScale N0 Bad ω ≤
          (3 * (3 : ℝ) ^ N0 * B) * Rmix ω) ∧
      ∀ᵐ ω ∂P, ∀ m : ℕ,
        (3 * (3 : ℝ) ^ N0 * B) * Rmix ω ≤ (3 : ℝ) ^ m →
          ω ∉ Bad m := by
  let A : ℝ := 3 * (3 : ℝ) ^ N0 * B
  let Rraw : Ω → ℝ := quenchedMinimalScale N0 Bad
  let Rmix : Ω → ℝ := fun ω => max 1 (Rraw ω / A)
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hRrawMeas : Measurable Rraw := by
    simpa only [Rraw] using measurable_quenchedMinimalScale hBad N0
  have hRrawTail : IsBigOWith P (gammaSigma eta) Rraw A := by
    simpa only [Rraw, A] using
      isBigOWith_quenchedMinimalScale_of_badTailEvent_bound
        (μ := P) (N0 := N0) (Bad := Bad) (B := B) (η := eta)
        heta hB htail
  have hsmall :
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, N0 ≤ N ∧ P.real (badTailEvent Bad N) ≤ epsilon := by
    intro epsilon hepsilon
    have hpow :
        Tendsto (fun j : ℕ => Real.rpow (3 : ℝ) (j : ℝ)) atTop atTop := by
      have h : Tendsto (fun j : ℕ => (3 : ℝ) ^ j) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)
      have hcast : ∀ j : ℕ, (3 : ℝ) ^ j = Real.rpow 3 (j : ℝ) := fun j => by simp
      simpa only [hcast] using h
    have hdiv :
        Tendsto (fun j : ℕ => Real.rpow (3 : ℝ) (j : ℝ) / B) atTop atTop :=
      hpow.atTop_div_const hBpos
    have hrpow :
        Tendsto
          (fun j : ℕ => (Real.rpow (3 : ℝ) (j : ℝ) / B) ^ eta)
          atTop atTop :=
      (tendsto_rpow_atTop heta).comp hdiv
    have hneg :
        Tendsto
          (fun j : ℕ => -((Real.rpow (3 : ℝ) (j : ℝ) / B) ^ eta))
          atTop atBot :=
      tendsto_neg_atTop_atBot.comp hrpow
    have hexp :
        Tendsto
          (fun j : ℕ =>
            Real.exp (-((Real.rpow (3 : ℝ) (j : ℝ) / B) ^ eta)))
          atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hneg
    have hevent :
        ∀ᶠ j : ℕ in atTop,
          Real.exp (-((Real.rpow (3 : ℝ) (j : ℝ) / B) ^ eta)) ≤ epsilon :=
      hexp.eventually (Iic_mem_nhds hepsilon)
    obtain ⟨j, hj⟩ := hevent.exists
    refine ⟨N0 + j, Nat.le_add_right N0 j, ?_⟩
    have htailj := htail (N0 + j) (Nat.le_add_right N0 j)
    exact htailj.trans (by simpa only [Nat.add_sub_cancel_left] using hj)
  have hgood : ∀ᵐ ω ∂P, hasGoodTailFrom N0 Bad ω :=
    ae_hasGoodTailFrom (μ := P) (N0 := N0) (Bad := Bad) hsmall
  have hRmixMeas : Measurable Rmix := by
    exact measurable_const.max (hRrawMeas.div_const A)
  have hRmixOne : ∀ ω, 1 ≤ Rmix ω := by
    intro ω
    exact le_max_left 1 (Rraw ω / A)
  have hRrawLe : ∀ ω, Rraw ω ≤ A * Rmix ω := by
    intro ω
    have hdivLe : Rraw ω / A ≤ Rmix ω :=
      le_max_right 1 (Rraw ω / A)
    have hmul := mul_le_mul_of_nonneg_left hdivLe hApos.le
    calc
      Rraw ω = A * (Rraw ω / A) := by
        rw [mul_comm, div_mul_cancel₀ _ hApos.ne']
      _ ≤ A * Rmix ω := hmul
  have hRmixTail :
      ∀ t : ℝ, 1 ≤ t →
        P.real {ω | 2 * t ≤ Rmix ω} ≤ Real.exp (-(t ^ eta)) := by
    intro t ht
    have hsubset :
        {ω | 2 * t ≤ Rmix ω} ⊆ upperTailEvent Rraw (A * t) := by
      intro ω hω
      change 2 * t ≤ max 1 (Rraw ω / A) at hω
      rcases max_cases (1 : ℝ) (Rraw ω / A) with hmax | hmax
      · rw [hmax.1] at hω
        linarith only [hω, ht]
      · rw [hmax.1] at hω
        change A * t < Rraw ω
        have htdiv : t < Rraw ω / A := by
          linarith only [hω, ht]
        have hmul : t * A < Rraw ω := (lt_div_iff₀ hApos).mp htdiv
        simpa only [mul_comm] using hmul
    calc
      P.real {ω | 2 * t ≤ Rmix ω}
          ≤ P.real (upperTailEvent Rraw (A * t)) :=
        measureReal_mono hsubset
      _ ≤ Real.exp (-(t ^ eta)) :=
        (isBigOWith_gammaSigma_iff.mp hRrawTail) ht
  have hallLater :
      ∀ᵐ ω ∂P, ∀ m : ℕ, A * Rmix ω ≤ (3 : ℝ) ^ m → ω ∉ Bad m := by
    filter_upwards [hgood] with ω hω
    intro m hm
    have hrawScale : Rraw ω ≤ (3 : ℝ) ^ m := (hRrawLe ω).trans hm
    have hindex : quenchedMinimalScaleIndex N0 Bad ω ≤ m := by
      exact quenchedMinimalScaleIndex_le_of_scale_le_pow
        (N0 := N0) (Bad := Bad) (ω := ω) hrawScale
    exact not_mem_bad_of_quenchedMinimalScaleIndex_le
      (N0 := N0) (Bad := Bad) (ω := ω) hω hindex le_rfl
  refine ⟨Rmix, hRmixMeas, hRmixOne, hRmixTail, ?_, ?_⟩
  · simpa only [Rraw, A] using hRrawLe
  · simpa only [A] using hallLater

end

end Quenched
end HighContrast
end HCPolySupport
