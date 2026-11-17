/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Smooth parametrization of coordinate faces of a cube -/

@[expose] public section


namespace NairTenenbaum

variable {ι : Type*} [Fintype ι]

open Classical in
theorem card_coordinateFaceParameter (i : ι) :
    Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
  rw [Fintype.card_subtype_compl (fun j => j = i)]
  simp

open Classical in
/-- The equivalence identifying the free coordinates of a cube face. -/
noncomputable def coordinateFaceParameterEquiv (i : ι) :
    {j : ι // j ≠ i} ≃ Fin (Fintype.card ι - 1) :=
  Fintype.equivFinOfCardEq (card_coordinateFaceParameter i)

open Classical in
/-- The embedding of the free coordinates into a specified cube face. -/
noncomputable def cubeFaceMap (i : ι) (b : ℝ) (v : Fin (Fintype.card ι - 1) → ℝ) : ι → ℝ :=
  fun j => if h : j = i then b else v (coordinateFaceParameterEquiv i ⟨j, h⟩)

theorem contDiff_cubeFaceMap (i : ι) (b : ℝ) : ContDiff ℝ ⊤ (cubeFaceMap i b) := by
  apply contDiff_pi.mpr
  intro j
  by_cases hj : j = i
  · simp only [cubeFaceMap, hj, ↓reduceDIte]
    fun_prop
  · simp only [cubeFaceMap, hj, ↓reduceDIte]
    fun_prop

theorem exists_cubeFaceMap_of_coordinate_eq {i : ι} {b : ℝ} {v : ι → ℝ}
    (hv : v ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1)) (hi : v i = b) :
    ∃ u : Fin (Fintype.card ι - 1) → ℝ,
      u ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) ∧ cubeFaceMap i b u = v := by
  let u := fun k : Fin (Fintype.card ι - 1) => v ((coordinateFaceParameterEquiv i).symm k).1
  refine ⟨u, ⟨fun k => hv.1 _, fun k => hv.2 _⟩, ?_⟩
  ext j
  by_cases hj : j = i
  · subst j
    simp [cubeFaceMap, hi]
  · simp [cubeFaceMap, hj, u]

end NairTenenbaum
