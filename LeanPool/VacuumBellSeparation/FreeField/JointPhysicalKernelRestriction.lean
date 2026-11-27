/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialSelfAdjoint

/-!
# The normalized analytic kernels are the original physical kernels

All midpoint shifts and the apparent separation in the complex radius
cancel literally. This identifies the four component kernels with the
negative original cross covariance kernels and zero on the diagonal.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian

theorem jointNormalized_coordinate_cancel {s : ℝ} (hs : s ≠ 0)
    (z : Fin 6 → ℂ) (j : Fin 6) :
    (s : ℂ) * (jointPhysicalMidpoint s z j + jointMidpointShift j) =
      z j - if j = 3 then (s : ℂ) else 0 := by
  have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  fin_cases j <;> simp [jointPhysicalMidpoint, jointPhysicalMidpointShift, jointMidpointShift] <;>
    field_simp
  ring

theorem jointNormalized_spatialSixPair {s : ℝ} (hs : s ≠ 0) (x : JointKernelSpace) :
    spatialSixPair (fun j => (s : ℂ) *
      (jointPhysicalMidpoint s (jointComplexCoordinates x) j + jointMidpointShift j)) =
        (spatialComplexOfReal x.fst, spatialComplexOfReal
          (x.snd - spatialAxisDisplacement s 0)) := by
  apply Prod.ext
  · ext j
    change (s : ℂ) * (jointPhysicalMidpoint s (jointComplexCoordinates x) (Fin.castAdd 3 j) +
      jointMidpointShift (Fin.castAdd 3 j)) = (x.fst j : ℂ)
    rw [jointNormalized_coordinate_cancel hs, jointComplexCoordinates_left]
    fin_cases j <;> simp
  · ext j
    change (s : ℂ) * (jointPhysicalMidpoint s (jointComplexCoordinates x) (Fin.natAdd 3 j) +
      jointMidpointShift (Fin.natAdd 3 j)) = ((x.snd - spatialAxisDisplacement s 0) j : ℂ)
    rw [jointNormalized_coordinate_cancel hs, jointComplexCoordinates_right]
    fin_cases j <;> simp [spatialAxisDisplacement, PiLp.sub_apply]

theorem spatialAxisDisplacement_cancel (s : ℝ) (x y : EuclideanSpace ℝ (Fin 3)) :
    spatialAxisDisplacement s ((y - spatialAxisDisplacement s 0) - x) = y - x := by
  ext j
  change (if j = 0 then s else 0) + ((y j - ((if j = 0 then s else 0) + 0)) - x j) = y j - x j
  ring

theorem jointNormalizedFieldKernel_physical {s : ℝ} (hs : s ≠ 0) (μ : ℝ) (x : JointKernelSpace) :
    jointNormalizedFieldKernel μ s
      (fun j => jointPhysicalMidpoint s (jointComplexCoordinates x) j + jointMidpointShift j) =
        (spatialFieldBesselKernel μ (x.snd - x.fst) : ℂ) := by
  unfold jointNormalizedFieldKernel spatialSixFieldKernel
  rw [jointNormalized_spatialSixPair hs, spatialPairFieldKernel_ofReal,
    spatialAxisDisplacement_cancel]

theorem jointNormalizedMomentumKernel_physical {s : ℝ} (hs : s ≠ 0) (μ : ℝ) (x : JointKernelSpace) :
    jointNormalizedMomentumKernel μ s
      (fun j => jointPhysicalMidpoint s (jointComplexCoordinates x) j + jointMidpointShift j) =
        (spatialMomentumBesselKernel μ (x.snd - x.fst) : ℂ) := by
  unfold jointNormalizedMomentumKernel spatialSixMomentumKernel
  rw [jointNormalized_spatialSixPair hs, spatialPairMomentumKernel_ofReal,
    spatialAxisDisplacement_cancel]

theorem spatialFieldBesselKernel_sub_comm (μ : ℝ) (x y : EuclideanSpace ℝ (Fin 3)) :
    spatialFieldBesselKernel μ (x - y) = spatialFieldBesselKernel μ (y - x) := by
  simp only [spatialFieldBesselKernel, norm_sub_rev x y]

theorem spatialMomentumBesselKernel_sub_comm (μ : ℝ) (x y : EuclideanSpace ℝ (Fin 3)) :
    spatialMomentumBesselKernel μ (x - y) = spatialMomentumBesselKernel μ (y - x) := by
  simp only [spatialMomentumBesselKernel, norm_sub_rev x y]

theorem jointComponentFieldKernel_physical {s : ℝ} (hs : s ≠ 0) (μ : ℝ)
    (a b : Bool) (x : JointKernelSpace) :
    jointComponentKernel (jointNormalizedFieldKernel μ s) a b
      (jointPhysicalMidpoint s (jointComplexCoordinates x)) =
        if a = b then 0 else -(spatialFieldBesselKernel μ (x.snd - x.fst) : ℂ) := by
  have ht := jointNormalizedFieldKernel_physical hs μ (jointKernelSwap x)
  rw [jointPhysicalMidpoint_swap] at ht
  change jointNormalizedFieldKernel μ s
    (fun j => (jointPhysicalMidpoint s (jointComplexCoordinates x) ∘ swapSpatialSix) j +
      jointMidpointShift j) =
      (spatialFieldBesselKernel μ (x.fst - x.snd) : ℂ) at ht
  rw [spatialFieldBesselKernel_sub_comm μ x.fst x.snd] at ht
  -- The same identity with the composition applied, in the form left by `simp`.
  have ht' : jointNormalizedFieldKernel μ s
      (fun j => jointPhysicalMidpoint s (jointComplexCoordinates x) (swapSpatialSix j) +
        jointMidpointShift j) = (spatialFieldBesselKernel μ (x.snd - x.fst) : ℂ) := ht
  cases a <;> cases b <;>
    simp [jointComponentKernel, jointOrientedComponentKernel,
      jointNormalizedFieldKernel_physical hs, ht']

theorem jointComponentMomentumKernel_physical {s : ℝ} (hs : s ≠ 0) (μ : ℝ)
    (a b : Bool) (x : JointKernelSpace) :
    jointComponentKernel (jointNormalizedMomentumKernel μ s) a b
      (jointPhysicalMidpoint s (jointComplexCoordinates x)) =
        if a = b then 0 else -(spatialMomentumBesselKernel μ (x.snd - x.fst) : ℂ) := by
  have ht := jointNormalizedMomentumKernel_physical hs μ (jointKernelSwap x)
  rw [jointPhysicalMidpoint_swap] at ht
  change jointNormalizedMomentumKernel μ s
    (fun j => (jointPhysicalMidpoint s (jointComplexCoordinates x) ∘ swapSpatialSix) j +
      jointMidpointShift j) =
      (spatialMomentumBesselKernel μ (x.fst - x.snd) : ℂ) at ht
  rw [spatialMomentumBesselKernel_sub_comm μ x.fst x.snd] at ht
  -- The same identity with the composition applied, in the form left by `simp`.
  have ht' : jointNormalizedMomentumKernel μ s
      (fun j => jointPhysicalMidpoint s (jointComplexCoordinates x) (swapSpatialSix j) +
        jointMidpointShift j) = (spatialMomentumBesselKernel μ (x.snd - x.fst) : ℂ) := ht
  cases a <;> cases b <;>
    simp [jointComponentKernel, jointOrientedComponentKernel,
      jointNormalizedMomentumKernel_physical hs, ht']

end VacuumBellSeparation
