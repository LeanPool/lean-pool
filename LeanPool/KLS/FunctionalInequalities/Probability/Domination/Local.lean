/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Support

/-! # Local domination of a law on an open set, in particular on the interior of its support -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace FunctionalInequalities.Probability

universe u

variable {V : Type u} [NormedAddCommGroup V] [MeasurableSpace V]


/-- On every compact subset of the set `Ω`, the reference measure `m` is dominated by a constant
multiple of `ν`. For a law with a density this says the density is locally bounded below by
positive constants on `Ω`. -/
def LocallyDominatesOn (ν : ProbabilityMeasure V) (m : Measure V) (Ω : Set V) : Prop :=
  ∀ K : Set V, IsCompact K → K ⊆ Ω →
    ∃ C : ℝ≥0, m.restrict K ≤ (C : ℝ≥0∞) • (ν : Measure V).restrict K

/-- On every compact subset of the interior of the support of `ν`, the reference measure `m` is
dominated by a constant multiple of `ν`. For a law with a density this says the density is
locally bounded below by positive constants on the interior of the support. -/
abbrev LocallyDominates (ν : ProbabilityMeasure V) (m : Measure V) : Prop :=
  LocallyDominatesOn ν m (interior (ν : Measure V).support)

namespace LocallyDominatesOn

variable {ν : ProbabilityMeasure V} {m : Measure V} {Ω : Set V}

/-- Lower integrals over a compact subset of `Ω` compare with a constant. -/
theorem exists_lintegral_le (h : LocallyDominatesOn ν m Ω) {K : Set V} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ u : V → ℝ≥0∞,
      ∫⁻ x in K, u x ∂m ≤ (C : ℝ≥0∞) * ∫⁻ x in K, u x ∂(ν : Measure V) := by
  obtain ⟨C, hC⟩ := h K hK hKΩ
  refine ⟨C, fun u ↦ ?_⟩
  calc ∫⁻ x in K, u x ∂m ≤ ∫⁻ x, u x ∂((C : ℝ≥0∞) • (ν : Measure V).restrict K) :=
        lintegral_mono' hC le_rfl
    _ = (C : ℝ≥0∞) * ∫⁻ x in K, u x ∂(ν : Measure V) := lintegral_smul_measure _ _

variable [BorelSpace V]

omit [BorelSpace V] in
/-- The restriction of `m` to a compact subset of `Ω` is absolutely continuous with respect to
the restriction of `ν`. -/
theorem restrict_absolutelyContinuous (h : LocallyDominatesOn ν m Ω) {K : Set V} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    m.restrict K ≪ (ν : Measure V).restrict K := by
  obtain ⟨C, hC⟩ := h K hK hKΩ
  refine Measure.AbsolutelyContinuous.mk fun s _ hs ↦ ?_
  have := Measure.le_iff'.mp hC s
  rw [smul_apply, hs, smul_zero] at this
  exact le_antisymm this bot_le

/-- `ν`-null sets inside a compact subset of `Ω` are `m`-null. -/
theorem measure_inter_eq_zero (h : LocallyDominatesOn ν m Ω) {K : Set V} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) {s : Set V} (hs : (ν : Measure V) s = 0) :
    m (s ∩ K) = 0 := by
  obtain ⟨C, hC⟩ := h K hK hKΩ
  have h1 := Measure.le_iff'.mp hC s
  rw [smul_apply, Measure.restrict_apply' hK.measurableSet,
    Measure.restrict_apply' hK.measurableSet] at h1
  have h2 : (ν : Measure V) (s ∩ K) = 0 := measure_mono_null Set.inter_subset_left hs
  rw [h2, smul_zero] at h1
  exact le_antisymm h1 bot_le

end LocallyDominatesOn

end FunctionalInequalities.Probability
