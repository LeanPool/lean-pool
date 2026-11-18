/-
Copyright (c) 2026 BrownianMotion contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BrownianMotion contributors
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: Mathlib v4.35.0 `IsCadlag` field names
-- (`isRightContinuous`, `tendsto_nhdsLT`) in one proof (proof-only); see vendor/port.patch.
module

public import Mathlib.Probability.Process.Indistinguishable
public import LeanPool.KLS.BrownianMotion.StochasticIntegral.Cadlag
public import Mathlib.Probability.Process.Stopping

/-! # Stopped processes and path regularity -/


@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Nonempty ι]
  {τ : Ω → WithTop ι} {ω : Ω} {t : ι} {X Y : ι → Ω → E}

section stoppedProcess

variable [LinearOrder ι]

@[simp]
lemma stoppedProcess_of_eq_top (s : ι) (hτ : τ ω = ⊤) :
    stoppedProcess X τ s ω = X s ω := by
  simp [stoppedProcess, hτ]

@[simp]
lemma stoppedProcess_of_eq_coe (s : ι) (hτ : τ ω = t) :
    stoppedProcess X τ s ω = X (min s t) ω := by
  obtain h | h := le_total s t <;> simp [stoppedProcess, hτ, h]

lemma stoppedProcess_congr (h : X ≡ᵐ[P] Y) :
    stoppedProcess X τ ≡ᵐ[P] stoppedProcess Y τ := by
  filter_upwards [h] with ω h t
  simp [stoppedProcess, h]

lemma stoppedProcess_indicator_add [AddZeroClass E] {s : Set Ω} :
    stoppedProcess (fun i ↦ s.indicator ((X + Y) i)) τ
      = stoppedProcess (fun i ↦ s.indicator (X i)) τ
        + stoppedProcess (fun i ↦ s.indicator (Y i)) τ := by
  ext t ω
  by_cases hω : ω ∈ s <;> simp [stoppedProcess, hω]

lemma stoppedProcess_indicator_sub [AddGroup E] {s : Set Ω} :
    stoppedProcess (fun i ↦ s.indicator ((X - Y) i)) τ
      = stoppedProcess (fun i ↦ s.indicator (X i)) τ
        - stoppedProcess (fun i ↦ s.indicator (Y i)) τ := by
  ext t ω
  by_cases hω : ω ∈ s <;> simp [stoppedProcess, hω]

/-- Stopping at `τ` and then at a smaller time `σ` is the same as stopping at `σ`, for the
stopped processes used in the definition of local properties. -/
lemma stoppedProcess_indicator_stoppedProcess_indicator_of_le [OrderBot ι] [Zero E]
    {σ : Ω → WithTop ι} (h : σ ≤ τ) :
    stoppedProcess (fun i ↦ {ω | ⊥ < σ ω}.indicator
        (stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ i)) σ
      = stoppedProcess (fun i ↦ {ω | ⊥ < σ ω}.indicator (X i)) σ := by
  simp_rw [stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess_of_le_right h]
  ext t ω
  by_cases hω : ⊥ < σ ω
  · have hω' : ⊥ < τ ω := hω.trans_le (h ω)
    simp [hω, hω']
  · simp [hω]

/-- If a trajectory of a process is monotone, then the corresponding trajectory of the stopped
process is also monotone. -/
lemma _root_.Monotone.stoppedProcess_indicator [Preorder E] [Zero E] (hX : Monotone (X · ω))
    (s : Set Ω) (τ : Ω → WithTop ι) :
    Monotone (stoppedProcess (fun i ↦ s.indicator (X i)) τ · ω) := by
  intro a b hab
  simp only [stoppedProcess_indicator_comm]
  by_cases hω : ω ∈ s
  · simp only [Set.indicator_of_mem hω, stoppedProcess]
    refine hX (WithTop.untopA_mono ?_ (min_le_min_right _ (WithTop.coe_le_coe.2 hab)))
    exact ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  · simp [hω]

section Topology

variable [TopologicalSpace ι] [OrderTopology ι] [TopologicalSpace E]

/-- If a trajectory of a process is continuous, then the corresponding trajectory of the stopped
process is also continuous. -/
lemma _root_.Continuous.stoppedProcess {ω : Ω} (hX : Continuous (X · ω)) (τ : Ω → WithTop ι) :
    Continuous (stoppedProcess X τ · ω) := by
  cases h : τ ω with
  | top => simpa [h]
  | coe t =>
    simp only [h, WithTop.coe_inj, stoppedProcess_of_eq_coe]
    fun_prop

/-- If a trajectory of a process is right-continuous,
then the corresponding trajectory of the stopped process is also right-continuous. -/
lemma _root_.IsRightContinuous.stoppedProcess (hX : IsRightContinuous (X · ω)) (τ : Ω → WithTop ι) :
    IsRightContinuous (stoppedProcess X τ · ω) := by
  cases h : τ ω with
  | top => simpa [h]
  | coe t =>
    simp only [h, WithTop.coe_inj, stoppedProcess_of_eq_coe]
    intro s
    obtain hst | hts := lt_or_ge s t
    · exact hX (min s t) |>.comp (f := (min · t)) (by fun_prop) (by grind [Set.MapsTo])
    · exact (continuous_const (y := X t ω)).continuousWithinAt.congr (by grind) (by grind)

/-- If a trajectory of a process is càdlàg, then the corresponding trajectory of the stopped
process is also càdlàg. -/
lemma _root_.IsCadlag.stoppedProcess (hX : IsCadlag (X · ω)) (τ : Ω → WithTop ι) :
    IsCadlag (stoppedProcess X τ · ω) := by
  cases h : τ ω with
  | top => simpa [h]
  | coe t =>
    refine ⟨hX.isRightContinuous.stoppedProcess τ, fun s ↦ ?_⟩
    simp only [h, WithTop.coe_inj, stoppedProcess_of_eq_coe]
    obtain hst | hts := le_or_gt s t
    · obtain ⟨l, hl⟩ := hX.tendsto_nhdsLT s
      exact ⟨l, hl.congr' (Set.EqOn.eventuallyEq_nhdsWithin fun s hs ↦ by grind)⟩
    · refine ⟨X t ω, tendsto_const_nhds.congr' ?_⟩
      rw [eventuallyEq_nhdsWithin_iff, eventually_nhds_iff]
      exact ⟨Set.Ioi t, by grind, isOpen_Ioi, by grind⟩

end Topology

end stoppedProcess

namespace stoppedValue

@[simp] lemma add [Add E] {u v : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (u + v) τ = stoppedValue u τ + stoppedValue v τ := rfl

@[simp] lemma neg [Neg E] {u : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (-u) τ = -stoppedValue u τ := rfl

@[simp] lemma sub [Sub E] {u v : ι → Ω → E} {τ : Ω → WithTop ι} :
    stoppedValue (u - v) τ = stoppedValue u τ - stoppedValue v τ := rfl

end stoppedValue

end MeasureTheory
