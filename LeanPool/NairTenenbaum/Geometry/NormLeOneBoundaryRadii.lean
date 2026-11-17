/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne

/-! # Radial and unit-coordinate faces of the norm-one region

Every boundary point has radial coordinate zero or one, or a unit coordinate
at an endpoint. This isolates the lower-dimensional parameter faces before
introducing signs and complex angles.
-/

@[expose] public section

namespace NairTenenbaum

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.Units dirichletUnitTheorem fundamentalCone
open scoped Pointwise

variable (K : Type*) [Field K] [NumberField K]

theorem normLeOne_interior_of_radial_coordinates {x : mixedSpace K} {r : ℝ}
    {u : realSpace K} (hr0 : 0 < r) (hr1 : r < 1) (hu0 : u w₀ = 0)
    (hu : ∀ w : InfinitePlace K, w ≠ w₀ → 0 < u w ∧ u w < 1)
    (hx : normAtAllPlaces x = r • expMapBasis u) : x ∈ interior (normLeOne K) := by
  classical
  let v : realSpace K := fun w => if w = w₀ then Real.log r else u w
  have hv : v ∈ interior (paramSet K) := by
    rw [interior_paramSet]
    apply Set.mem_univ_pi.mpr
    intro w
    by_cases hw : w = w₀
    · simp only [hw, ↓reduceIte, Set.mem_Iio, v]
      exact Real.log_neg hr0 hr1
    · simp only [hw, ↓reduceIte, Set.mem_Ioo, v]
      exact hu w hw
  have heq : expMapBasis v = r • expMapBasis u := by
    rw [expMapBasis_apply'']
    have hv0 : v w₀ = Real.log r := by simp [v]
    rw [hv0, Real.exp_log hr0]
    congr 2
    ext w
    by_cases hw : w = w₀
    · subst w
      simp [hu0]
    · simp [hw, v]
  apply subset_interior_normLeOne K
  exact ⟨v, hv, heq.trans hx.symm⟩

theorem normLeOne_frontier_radial_faces {x : mixedSpace K} (hx : x ∈ frontier (normLeOne K)) :
    ∃ r : ℝ, ∃ u : realSpace K,
      r ∈ Set.Icc 0 1 ∧ u w₀ = 0 ∧
      (∀ w : InfinitePlace K, w ≠ w₀ → u w ∈ Set.Icc 0 1) ∧
      normAtAllPlaces x = r • expMapBasis u ∧
      (r = 0 ∨ r = 1 ∨ ∃ w : InfinitePlace K, w ≠ w₀ ∧ (u w = 0 ∨ u w = 1)) := by
  classical
  have H := closure_normLeOne_subset K (frontier_subset_closure hx)
  change normAtAllPlaces x ∈ (Set.Icc (0 : ℝ) 1) •
    (expMapBasis '' Set.univ.pi (fun w : InfinitePlace K => if w = w₀ then {0} else Set.Icc 0 1))
        at H
  obtain ⟨r, hr, v, ⟨u, hu, rfl⟩, heq⟩ := H
  have hu0 : u w₀ = 0 := by simpa using Set.mem_univ_pi.mp hu w₀
  have hub (w : InfinitePlace K) (hw : w ≠ w₀) : u w ∈ Set.Icc 0 1 := by
    simpa only [hw, ↓reduceIte] using Set.mem_univ_pi.mp hu w
  refine ⟨r, u, hr, hu0, hub, heq.symm, ?_⟩
  by_contra h
  push Not at h
  have hr0 : 0 < r := lt_of_le_of_ne hr.1 h.1.symm
  have hr1 : r < 1 := lt_of_le_of_ne hr.2 h.2.1
  have hui (w : InfinitePlace K) (hw : w ≠ w₀) : 0 < u w ∧ u w < 1 := by
    have hb := hub w hw
    have hn := h.2.2 w hw
    exact ⟨lt_of_le_of_ne hb.1 hn.1.symm, lt_of_le_of_ne hb.2 hn.2⟩
  have Hint := normLeOne_interior_of_radial_coordinates K hr0 hr1 hu0 hui heq.symm
  exact hx.2 Hint

end NairTenenbaum
