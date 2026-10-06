/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityEnergyTest
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.EnergyIntegrand

/-!
# Stability Energy Derivatives

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- The time derivative of a smooth energy test is bounded on a local box. -/
theorem stability_energyTime_memLp_top
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    MemLp (fun z : ParabolicPoint => timePartial ψ z) ∞
      (volume.restrict (spaceTimeSet Ω' J)) := by
  have hcont : Continuous (fun z : ParabolicPoint => timePartial ψ z) :=
    (contDiff_timePartial hψ.1).continuous.comp parabolicHomeomorph.continuous
  obtain ⟨C, hC⟩ := exists_bound_timePartial_of_mem_spaceTimeTestFunction hψ
  exact memLp_top_of_bound hcont.aestronglyMeasurable C
    (Eventually.of_forall fun z => hC (parabolicHomeomorph z))

/-- A second spatial derivative of a smooth energy test is bounded on a
local box. -/
theorem stability_energySecond_memLp_top
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (i j : Fin 3) :
    MemLp (fun z : ParabolicPoint => spatialSecondPartial ψ i j z) ∞
      (volume.restrict (spaceTimeSet Ω' J)) := by
  have hcont : Continuous (fun z : ParabolicPoint =>
      spatialSecondPartial ψ i j z) :=
    (spatialPartial_contDiff (spatialPartial_contDiff hψ.1 i) j).continuous.comp
      parabolicHomeomorph.continuous
  obtain ⟨C, hC⟩ :=
    exists_bound_spatialSecondPartial_of_mem_spaceTimeTestFunction hψ i j
  exact memLp_top_of_bound hcont.aestronglyMeasurable C
    (Eventually.of_forall fun z => hC (parabolicHomeomorph z))

/-- The coefficient of the quadratic energy term is bounded on a local box. -/
theorem stability_energyLaplacian_memLp_top
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    MemLp (fun z : ParabolicPoint =>
      timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) ∞
      (volume.restrict (spaceTimeSet Ω' J)) :=
  (stability_energyTime_memLp_top ψ hψ).add
    (memLp_finsetSum Finset.univ (fun i _ =>
      stability_energySecond_memLp_top ψ hψ i i))

/-- A first spatial derivative of a smooth energy test is bounded on a
local box. -/
theorem stability_energySpatial_memLp_top
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (i : Fin 3) :
    MemLp (fun z : ParabolicPoint => spatialPartial ψ i z) ∞
      (volume.restrict (spaceTimeSet Ω' J)) := by
  have hcont : Continuous (fun z : ParabolicPoint => spatialPartial ψ i z) :=
    (spatialPartial_contDiff hψ.1 i).continuous.comp
      parabolicHomeomorph.continuous
  obtain ⟨C, hC⟩ :=
    exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hψ i
  exact memLp_top_of_bound hcont.aestronglyMeasurable C
    (Eventually.of_forall fun z => hC (parabolicHomeomorph z))

end CKN
