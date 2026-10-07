/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalFinite
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MomentumIntegrand

/-!
# Stability Test Bounds

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- The time derivative of a component of a smooth compactly supported
momentum test is bounded on every local box. -/
theorem stability_timePartial_memLp_top
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (φ : Vec3 × ℝ → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I)
    (i : Fin 3) :
    MemLp (fun z : ParabolicPoint => timePartial (fun w => φ w i) z) ∞
      (volume.restrict (spaceTimeSet Ω' J)) := by
  have hcomp := component_mem_spaceTimeTestFunction hφ i
  have hcont : Continuous (fun z : ParabolicPoint =>
      timePartial (fun w => φ w i) z) :=
    (contDiff_timePartial hcomp.1).continuous.comp parabolicHomeomorph.continuous
  obtain ⟨C, hC⟩ := exists_bound_timePartial_of_mem_spaceTimeTestFunction hcomp
  exact memLp_top_of_bound hcont.aestronglyMeasurable C
    (Eventually.of_forall fun z => hC (parabolicHomeomorph z))

/-- A spatial derivative of a component of a smooth momentum test is bounded
on every local box. -/
theorem stability_spatialPartial_memLp_top
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (φ : Vec3 × ℝ → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I)
    (i j : Fin 3) :
    MemLp (fun z : ParabolicPoint => spatialPartial (fun w => φ w i) j z) ∞
      (volume.restrict (spaceTimeSet Ω' J)) := by
  have hcomp := component_mem_spaceTimeTestFunction hφ i
  have hcont : Continuous (fun z : ParabolicPoint =>
      spatialPartial (fun w => φ w i) j z) :=
    (spatialPartial_contDiff hcomp.1 j).continuous.comp parabolicHomeomorph.continuous
  obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction
    hcomp j
  exact memLp_top_of_bound hcont.aestronglyMeasurable C
    (Eventually.of_forall fun z => hC (parabolicHomeomorph z))

/-- The divergence of a smooth momentum test is bounded on every local box. -/
theorem stability_testDivergence_memLp_top
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (φ : Vec3 × ℝ → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I) :
    MemLp (fun z : ParabolicPoint =>
      ∑ i : Fin 3, spatialPartial (fun w => φ w i) i z) ∞
      (volume.restrict (spaceTimeSet Ω' J)) := by
  exact memLp_finsetSum Finset.univ (fun i _ =>
    stability_spatialPartial_memLp_top φ hφ i i)

end CKN
