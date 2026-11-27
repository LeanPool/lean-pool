/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CanonicalSourceHull
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Cofinality and directedness of all finite canonical systems

Finite-dimensionality supplies actual finite generators. Adjoining explicit
local partners then gives a canonical upper bound of any two canonical
systems, not just of two chosen generating families. Every local smooth
source belongs to one of these systems.
-/

@[expose] public section

namespace VacuumBellSeparation

theorem canonicalSourceSystems_directed {U : Set (EuclideanSpace ℝ (Fin 3))}
    {S T : Submodule ℝ TimeZeroSource}
    (hS : IsCanonicalSourceSystem U S) (hT : IsCanonicalSourceSystem U T) :
    ∃ R : Submodule ℝ TimeZeroSource, IsCanonicalSourceSystem U R ∧ S ≤ R ∧ T ≤ R := by
  let : FiniteDimensional ℝ S := hS.1
  let : FiniteDimensional ℝ T := hT.1
  obtain ⟨s, hs, heqs⟩ := Submodule.fg_def.mp (Module.Finite.iff_fg.mp
    (inferInstance : Module.Finite ℝ S))
  obtain ⟨t, ht, heqt⟩ := Submodule.fg_def.mp (Module.Finite.iff_fg.mp
    (inferInstance : Module.Finite ℝ T))
  have hsU : s ⊆ localizedTimeZeroSources U := by
    intro u hu
    apply hS.2.1
    rw [← heqs]
    exact Submodule.subset_span hu
  have htU : t ⊆ localizedTimeZeroSources U := by
    intro u hu
    apply hT.2.1
    rw [← heqt]
    exact Submodule.subset_span hu
  obtain ⟨R, hR, hsR, htR⟩ := canonicalSourceHull_directed hs ht hsU htU
  refine ⟨R, hR, ?_, ?_⟩
  · rw [← heqs]
    exact (Submodule.span_le.mpr (subset_canonicalSourceHull s)).trans hsR
  · rw [← heqt]
    exact (Submodule.span_le.mpr (subset_canonicalSourceHull t)).trans htR

/-- Exact covering of the actual local test space by finite canonical systems. -/
theorem mem_localizedTimeZeroSources_iff_exists_canonical
    {U : Set (EuclideanSpace ℝ (Fin 3))} (u : TimeZeroSource) :
    u ∈ localizedTimeZeroSources U ↔
      ∃ S : Submodule ℝ TimeZeroSource, IsCanonicalSourceSystem U S ∧ u ∈ S := by
  constructor
  · intro hu
    obtain ⟨S, hS, hs⟩ := exists_canonicalSourceSystem_containing_finite
      (Set.finite_singleton u) (Set.singleton_subset_iff.mpr hu)
    exact ⟨S, hS, hs (Set.mem_singleton u)⟩
  · rintro ⟨S, hS, hu⟩
    exact hS.2.1 hu

end VacuumBellSeparation
