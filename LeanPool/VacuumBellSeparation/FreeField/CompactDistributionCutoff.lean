/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CompactDistributionEntire
public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Genuine cutoff identities for distributions vanishing outside a compact set

The hypothesis is actual vanishing on exterior tests. A cutoff equal to one
near the localization set may be inserted into any Schwartz pairing, and
cutoff exponential pairings are independent of that choice. Bounded sets
admit a compact smooth cutoff, constructed from a genuine radial bump.
-/

@[expose] public section

open Filter Topology
open scoped SchwartzMap

namespace VacuumBellSeparation

/-- Bounded spatial sets have actual compact Schwartz cutoffs equal to one on a neighborhood. -/
theorem exists_spatialSchwartz_cutoff {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : Bornology.IsBounded K) :
    ∃ χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ, HasCompactSupport χ ∧
      ∀ x ∈ K, (fun y => χ y) =ᶠ[𝓝 x] (fun _ => 1) := by
  obtain ⟨r, hr, hKr⟩ := hK.subset_ball_lt 0 0
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) :=
    { rIn := r, rOut := r + 1, rIn_pos := hr, rIn_lt_rOut := lt_add_one _ }
  have hb : HasCompactSupport (fun x => (b x : ℂ)) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  let χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ :=
    hb.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  refine ⟨χ, hb, fun x hx => ?_⟩
  have heq := b.eventuallyEq_one_of_mem_ball (hKr hx)
  filter_upwards [heq] with y hy
  change (b y : ℂ) = 1
  rw [show b y = 1 from hy, Complex.ofReal_one]

/-- Actual exterior vanishing allows insertion of a cutoff into every Schwartz pairing. -/
theorem distribution_eq_cutoff_pairing
    {K : Set (EuclideanSpace ℝ (Fin 3))}
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (hT : Distribution.IsVanishingOn T Kᶜ)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (hχ : ∀ x ∈ K, (fun y => χ y) =ᶠ[𝓝 x] (fun _ => 1))
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    T φ = T (SchwartzMap.smulLeftCLM ℂ χ φ) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply hT
  intro x hx hxK
  have hz : (fun y => (φ - SchwartzMap.smulLeftCLM ℂ χ φ) y) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hχ x hxK] with y hy
    simp only [sub_apply, SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth,
      smul_eq_mul, hy, one_mul, sub_self, Pi.zero_apply]
  exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hx

/-- Compact cutoff exponential evaluations do not depend on the chosen cutoff. -/
theorem distribution_cutoff_exponential_independent
    {K : Set (EuclideanSpace ℝ (Fin 3))}
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (hT : Distribution.IsVanishingOn T Kᶜ)
    (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (χ₁ χ₂ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (hc₁ : HasCompactSupport χ₁) (hc₂ : HasCompactSupport χ₂)
    (hχ₁ : ∀ x ∈ K, (fun y => χ₁ y) =ᶠ[𝓝 x] (fun _ => 1))
    (hχ₂ : ∀ x ∈ K, (fun y => χ₂ y) =ᶠ[𝓝 x] (fun _ => 1)) (z : ℂ) :
    T (spatialSchwartzExponential a χ₁ hc₁ z) =
      T (spatialSchwartzExponential a χ₂ hc₂ z) := by
  rw [distribution_eq_cutoff_pairing T hT χ₂ hχ₂ (spatialSchwartzExponential a χ₁ hc₁ z),
    distribution_eq_cutoff_pairing T hT χ₁ hχ₁ (spatialSchwartzExponential a χ₂ hc₂ z)]
  congr 1
  ext x
  simp only [SchwartzMap.smulLeftCLM_apply_apply χ₁.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply χ₂.hasTemperateGrowth,
    spatialSchwartzExponential_apply, smul_eq_mul]
  ring

end VacuumBellSeparation
