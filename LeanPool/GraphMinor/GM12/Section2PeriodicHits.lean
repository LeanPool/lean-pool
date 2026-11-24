/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM12.Section2CirclePeriod

/-!
# Counting vertex hits in one real period

The trace definition in XII, page 243, counts hits on the circle.
A half-open real period parametrizes the circle bijectively and hence
has the same number of hits. Starting a closed period at a hit adds
one further copy of that endpoint. This gives the number of intervals
used to construct the trace.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- The real extension of a closed curve is continuous. -/
theorem periodicCurve_continuous {S : Type*} [TopologicalSpace S] (φ : C(Circle, S)) :
    Continuous (periodicCurve φ) := by
  exact φ.continuous.comp (Circle.exp.continuous.comp (by fun_prop))

/-- The real extension used in XII's trace definition has period one. -/
theorem periodicCurve_periodic {S : Type*} [TopologicalSpace S] (φ : C(Circle, S)) :
    Function.Periodic (periodicCurve φ) 1 := circle_parameter_periodic.comp φ

/-- A half-open real period has the same finite number of hits as the
circle, namely the curve length of XII, page 243. -/
theorem periodicCurve_halfopen_hits {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} {φ : C(Circle, S)} (hφ : IsNormalCurve Γ φ) (a : ℝ) :
    {t | t ∈ Ico a (a + 1) ∧ periodicCurve φ t ∈ Γ.U}.Finite ∧
      {t | t ∈ Ico a (a + 1) ∧ periodicCurve φ t ∈ Γ.U}.ncard = curveLength Γ φ := by
  let P : Set Circle := {z | φ z ∈ Γ.U}
  let H : Set ℝ := {t | t ∈ Ico a (a + 1) ∧ periodicCurve φ t ∈ Γ.U}
  let q : ℝ → Circle := fun t => Circle.exp (2 * Real.pi * t)
  have hbij : BijOn q H P := by
    refine ⟨fun t ht => ht.2, (circle_parameter_injOn a).mono (fun _ ht => ht.1), ?_⟩
    intro z hz
    obtain ⟨t, ht, htz⟩ := (circle_parameter_bijOn a).surjOn (mem_univ z)
    refine ⟨t, ⟨ht, ?_⟩, htz⟩
    change φ (q t) ∈ Γ.U
    change q t = z at htz
    rw [htz]
    exact hz
  exact ⟨hbij.finite_iff_finite.mpr hφ.1, hbij.ncard_eq⟩

/-- A closed period starting at a hit has one extra endpoint hit. Its
ordered hits therefore bound exactly `curveLength Γ φ` intervals. -/
theorem periodicCurve_closed_hits {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} {φ : C(Circle, S)} (hφ : IsNormalCurve Γ φ) {a : ℝ}
    (ha : periodicCurve φ a ∈ Γ.U) :
    {t | t ∈ Icc a (a + 1) ∧ periodicCurve φ t ∈ Γ.U}.Finite ∧
      {t | t ∈ Icc a (a + 1) ∧ periodicCurve φ t ∈ Γ.U}.ncard = curveLength Γ φ + 1 := by
  let H : Set ℝ := {t | t ∈ Ico a (a + 1) ∧ periodicCurve φ t ∈ Γ.U}
  have hperiod : periodicCurve φ (a + 1) = periodicCurve φ a := periodicCurve_periodic φ a
  have heq : {t | t ∈ Icc a (a + 1) ∧ periodicCurve φ t ∈ Γ.U} = insert (a + 1) H := by
    ext t
    constructor
    · rintro ⟨ht, htU⟩
      by_cases he : t = a + 1
      · exact Or.inl he
      · exact Or.inr ⟨⟨ht.1, lt_of_le_of_ne ht.2 he⟩, htU⟩
    · rintro (he | ht)
      · subst t
        exact ⟨⟨by linarith, le_rfl⟩, hperiod.symm ▸ ha⟩
      · exact ⟨⟨ht.1.1, ht.1.2.le⟩, ht.2⟩
  obtain ⟨hH, hcard⟩ := periodicCurve_halfopen_hits hφ a
  rw [heq]
  refine ⟨hH.insert _, ?_⟩
  rw [Set.ncard_insert_of_notMem (show a + 1 ∉ H from fun ht => ht.1.2.false) hH, hcard]

end GraphMinor.GM12
