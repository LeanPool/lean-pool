/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Measurability detected by distances

A map into a second-countable metric Borel space is measurable when all of its distance
functions to fixed target points are measurable.

An extended-distance variant of `measurable_of_dist_functions` for metric spaces.
-/

public section

open Set Filter MeasureTheory TopologicalSpace

namespace LiebThirring

/-- A map into a second-countable metric Borel space is measurable when all of
its distance functions to fixed target points are measurable. -/
theorem measurable_of_dist_functions {α E : Type*} [MeasurableSpace α]
    [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (f : α → E) (hf : ∀ h : E, Measurable (fun x => dist (f x) h)) : Measurable f := by
  apply measurable_of_isOpen
  intro s hs
  have hex : ∀ h : E, ∃ r > 0, h ∈ s → Metric.ball h r ⊆ s := by
    intro h
    by_cases hh : h ∈ s
    · obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hs h hh
      exact ⟨r, hr, fun _ => hrs⟩
    · exact ⟨1, zero_lt_one, fun hhs => (hh hhs).elim⟩
  choose r hr_pos hr_sub using hex
  obtain ⟨t, ht_sub, ht_countable, ht_cover⟩ :=
    TopologicalSpace.countable_cover_nhdsWithin
      (s := s) (f := fun h => Metric.ball h (r h))
      (fun h _ => mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds h (hr_pos h)))
  have h_eq : s = ⋃ h ∈ t, Metric.ball h (r h) := by
    apply Set.Subset.antisymm ht_cover
    exact iUnion₂_subset fun h hh => hr_sub h (ht_sub hh)
  rw [h_eq, preimage_iUnion₂]
  apply MeasurableSet.biUnion ht_countable
  intro h _
  convert (hf h) (measurableSet_Iio (a := r h)) using 1
  ext x
  simp only [mem_preimage, Metric.mem_ball, mem_Iio]

end LiebThirring

end
