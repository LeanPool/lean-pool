/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4780T1HullHalfspaces
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Maps.Basic

-- [TABLET NODE: P4780T1StrictInterior]

/-!
# P4780T1StrictInterior

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4780T1StrictInterior :
    interior P4715T1Hexagon = {p : Real × Real |
      -2 < 2 * p.1 - p.2 ∧ 2 * p.1 - p.2 < 0 ∧
      -1 < p.1 - 2 * p.2 ∧ p.1 - 2 * p.2 < 1 ∧
      -2 < p.1 + p.2 ∧ p.1 + p.2 < 0} := by
-- BODY
  have hi (f : (Real × Real) →ₗ[Real] Real) (hf : Function.Surjective f)
      (a b : Real) : interior {p | a ≤ f p ∧ f p ≤ b} =
        {p | a < f p ∧ f p < b} := by
    have ho := LinearMap.isOpenMap_of_finiteDimensional f hf
    have hc := f.continuous_of_finiteDimensional
    have h1 : interior (f ⁻¹' Set.Ici a) = f ⁻¹' Set.Ioi a := by
      rw [← ho.preimage_interior_eq_interior_preimage hc, interior_Ici]
    have h2 : interior (f ⁻¹' Set.Iic b) = f ⁻¹' Set.Iio b := by
      rw [← ho.preimage_interior_eq_interior_preimage hc, interior_Iic]
    change interior ((f ⁻¹' Set.Ici a) ∩ (f ⁻¹' Set.Iic b)) = _
    rw [interior_inter, h1, h2]
    rfl
  let f : (Real × Real) →ₗ[Real] Real :=
    IsLinearMap.mk' (fun p : Real × Real => 2*p.1-p.2) (by
      constructor <;> intros <;> simp <;> ring)
  let g : (Real × Real) →ₗ[Real] Real :=
    IsLinearMap.mk' (fun p : Real × Real => p.1-2*p.2) (by
      constructor <;> intros <;> simp <;> ring)
  let h : (Real × Real) →ₗ[Real] Real :=
    IsLinearMap.mk' (fun p : Real × Real => p.1+p.2) (by
      constructor <;> intros <;> simp <;> ring)
  have hf : Function.Surjective f := by
    intro x
    exact ⟨(x / 2, 0), by simp [f, IsLinearMap.mk']; ring⟩
  have hg : Function.Surjective g := by
    intro x
    exact ⟨(x, 0), by simp [g, IsLinearMap.mk']⟩
  have hh : Function.Surjective h := by
    intro x
    exact ⟨(x, 0), by simp [h, IsLinearMap.mk']⟩
  rw [P4780T1HullHalfspaces]
  rw [show {p : Real × Real |
      -2 ≤ 2 * p.1 - p.2 ∧ 2 * p.1 - p.2 ≤ 0 ∧
      -1 ≤ p.1 - 2 * p.2 ∧ p.1 - 2 * p.2 ≤ 1 ∧
      -2 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 0} =
    ({p | -2 ≤ f p ∧ f p ≤ 0} ∩
    ({p | -1 ≤ g p ∧ g p ≤ 1} ∩ {p | -2 ≤ h p ∧ h p ≤ 0})) by
      ext p; simp [f, g, h, and_assoc]]
  rw [interior_inter, interior_inter, hi f hf, hi g hg, hi h hh]
  ext p
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, f, g, h,
    IsLinearMap.mk'_apply, and_assoc]

end ApollonianSuperharmonic

end
