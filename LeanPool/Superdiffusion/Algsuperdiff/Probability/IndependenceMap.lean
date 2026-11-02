/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Probability.Independence.Basic

/-!
# IndependenceMap

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Independence under a pushforward measure

This file relates independence of two sigma-fields pulled back along a map to
independence of the original sigma-fields under the pushforward measure.

## Main results

* `indep_comap_iff_indep_map`: independence of two comap sigma-fields is
  equivalent to independence under the pushforward measure.
-/

namespace Algsuperdiff.Probability

open MeasureTheory ProbabilityTheory

/-- Two sigma-fields pulled back along an almost-everywhere measurable map are
independent exactly when the original sigma-fields are independent under the
pushforward measure. The sigma-fields on the target must be contained in its
ambient measurable space so that the pushforward can be evaluated on all of
their events. -/
theorem indep_comap_iff_indep_map
    {α β : Type*} [mAlpha : MeasurableSpace α]
    {m₁ m₂ : MeasurableSpace β} [mBeta : MeasurableSpace β]
    {μ : Measure α} {f : α → β} (hf : AEMeasurable f μ)
    (hm₁ : m₁ ≤ mBeta) (hm₂ : m₂ ≤ mBeta) :
    Indep (m₁.comap f) (m₂.comap f) μ ↔ Indep m₁ m₂ (μ.map f) := by
  constructor
  · intro h
    rw [Indep_iff] at h ⊢
    intro s t hs ht
    have hsBeta : MeasurableSet[mBeta] s := hm₁ s hs
    have htBeta : MeasurableSet[mBeta] t := hm₂ t ht
    have hsf : MeasurableSet[m₁.comap f] (f ⁻¹' s) :=
      MeasurableSpace.measurableSet_comap.2 ⟨s, hs, rfl⟩
    have htf : MeasurableSet[m₂.comap f] (f ⁻¹' t) :=
      MeasurableSpace.measurableSet_comap.2 ⟨t, ht, rfl⟩
    calc
      μ.map f (s ∩ t) = μ (f ⁻¹' (s ∩ t)) :=
        Measure.map_apply_of_aemeasurable hf (hsBeta.inter htBeta)
      _ = μ (f ⁻¹' s ∩ f ⁻¹' t) := by rw [Set.preimage_inter]
      _ = μ (f ⁻¹' s) * μ (f ⁻¹' t) := h _ _ hsf htf
      _ = μ.map f s * μ.map f t := by
        rw [Measure.map_apply_of_aemeasurable hf hsBeta,
          Measure.map_apply_of_aemeasurable hf htBeta]
  · intro h
    rw [Indep_iff] at h ⊢
    intro s t hs ht
    rcases MeasurableSpace.measurableSet_comap.1 hs with ⟨s', hs', rfl⟩
    rcases MeasurableSpace.measurableSet_comap.1 ht with ⟨t', ht', rfl⟩
    have hsBeta : MeasurableSet[mBeta] s' := hm₁ s' hs'
    have htBeta : MeasurableSet[mBeta] t' := hm₂ t' ht'
    calc
      μ (f ⁻¹' s' ∩ f ⁻¹' t') = μ (f ⁻¹' (s' ∩ t')) := by
        rw [Set.preimage_inter]
      _ = μ.map f (s' ∩ t') :=
        (Measure.map_apply_of_aemeasurable hf (hsBeta.inter htBeta)).symm
      _ = μ.map f s' * μ.map f t' := h s' t' hs' ht'
      _ = μ (f ⁻¹' s') * μ (f ⁻¹' t') := by
        rw [Measure.map_apply_of_aemeasurable hf hsBeta,
          Measure.map_apply_of_aemeasurable hf htBeta]

end Algsuperdiff.Probability
