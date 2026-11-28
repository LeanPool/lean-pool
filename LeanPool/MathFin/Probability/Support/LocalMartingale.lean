/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lean Pool contributors
-/
module

-- Adapted from Rémy Degenne's BrownianMotion project for Lean Pool.

public import Mathlib.Probability.Process.Indistinguishable
public import TauCeti.Probability.Martingale.ContinuousStopping
public import Mathlib.Probability.Process.LocalProperty
public import TauCeti.Probability.Process.Progressive

/-!
# Local càdlàg martingales

Adapted from BrownianMotion (commit 497e5e2a) for time indexed by the
nonnegative reals, using Mathlib localization and Tau Ceti optional stopping.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}

/-- A process with càdlàg martingale stages along a localizing sequence. -/
def IsLocalMartingale (X : ℝ≥0 → Ω → E) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  Locally (fun Y ↦ Martingale Y 𝓕 P ∧ ∀ ω, IsCadlag (Y · ω)) 𝓕 X P

theorem Martingale.IsLocalMartingale (hX : Martingale X 𝓕 P) (hC : ∀ ω, IsCadlag (X · ω)) :
    IsLocalMartingale X 𝓕 P := .of_prop ⟨hX, hC⟩

omit [NormedSpace ℝ E] in
theorem _root_.MeasureTheory.StronglyAdapted.stoppedProcess_indicator
    (hX : StronglyAdapted 𝓕 X) (hC : ∀ ω, IsRightContinuous (X · ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) :
    StronglyAdapted 𝓕 (stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (X t)) τ) := by
  rw [stoppedProcess_indicator_comm']
  have hs := ((hX.isStronglyProgressive_of_isRightContinuous hC).stoppedProcess hτ).stronglyAdapted
  exact fun t ↦ (hs t).indicator (𝓕.mono bot_le _ (hτ.measurableSet_gt ⊥))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem stoppedProcess_of_eq_coe {ω : Ω} {t : ℝ≥0} {τ : Ω → WithTop ℝ≥0}
    (s : ℝ≥0) (hτ : τ ω = t) : stoppedProcess X τ s ω = X (min s t) ω := by
  rw [stoppedProcess, hτ, ← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top]
  rfl

omit [NormedSpace ℝ E] in
private theorem stoppedRightContinuous {ω : Ω} (hX : IsRightContinuous (X · ω))
    (τ : Ω → WithTop ℝ≥0) : IsRightContinuous (stoppedProcess X τ · ω) := by
  cases h : τ ω with
  | top =>
    have hstop : (stoppedProcess X τ · ω) = (X · ω) :=
      funext fun s ↦ stoppedProcess_eq_of_le (by rw [h]; exact le_top)
    rwa [hstop]
  | coe t =>
    simp only [stoppedProcess_of_eq_coe _ h]
    intro s
    obtain hst | hts := lt_or_ge s t
    · exact hX (min s t) |>.comp (f := (min · t)) (by fun_prop) (by grind [Set.MapsTo])
    · exact (continuous_const (y := X t ω)).continuousWithinAt.congr (by grind) (by grind)

omit [NormedSpace ℝ E] in
private theorem stoppedCadlag {ω : Ω} (hX : IsCadlag (X · ω)) (τ : Ω → WithTop ℝ≥0) :
    IsCadlag (stoppedProcess X τ · ω) := by
  cases h : τ ω with
  | top =>
    have hstop : (stoppedProcess X τ · ω) = (X · ω) :=
      funext fun s ↦ stoppedProcess_eq_of_le (by rw [h]; exact le_top)
    rwa [hstop]
  | coe t =>
    refine ⟨stoppedRightContinuous hX.isRightContinuous τ, fun s ↦ ?_⟩
    simp only [stoppedProcess_of_eq_coe _ h]
    obtain hst | hts := le_or_gt s t
    · obtain ⟨l, hl⟩ := hX.tendsto_nhdsLT s
      exact ⟨l, hl.congr' (Set.EqOn.eventuallyEq_nhdsWithin fun u hu ↦ by grind)⟩
    · refine ⟨X t ω, tendsto_const_nhds.congr' ?_⟩
      rw [eventuallyEq_nhdsWithin_iff, eventually_nhds_iff]
      exact ⟨Set.Ioi t, by grind, isOpen_Ioi, by grind⟩

omit [NormedSpace ℝ E] in
theorem isStable_isCadlag :
    IsStable 𝓕 (fun (Y : ℝ≥0 → Ω → E) ↦ ∀ ω, IsCadlag (Y · ω)) := by
  intro Y hY τ hτ ω
  simp only [stoppedProcess_indicator_comm']
  by_cases hω : ω ∈ {ω | ⊥ < τ ω}
  · simpa only [Set.indicator_of_mem hω] using stoppedCadlag (hY ω) τ
  · simpa only [Set.indicator_of_notMem hω] using (IsCadlag.const (c := (0 : E)) (X := ℝ≥0))

theorem isStable_martingale [IsFiniteMeasure P] [CompleteSpace E] :
    IsStable 𝓕 (fun (Y : ℝ≥0 → Ω → E) ↦ Martingale Y 𝓕 P ∧ ∀ ω, IsCadlag (Y · ω)) := by
  intro Y hY τ hτ
  have hC : ∀ ω, IsRightContinuous (Y · ω) := fun ω ↦ (hY.2 ω).isRightContinuous
  exact ⟨hY.1.stoppedProcess_indicator_of_ae_isRightContinuous
    (hY.1.stronglyAdapted.isStronglyProgressive_of_isRightContinuous hC)
    (ae_of_all _ hC) hτ, isStable_isCadlag Y hY.2 τ hτ⟩

end ProbabilityTheory
