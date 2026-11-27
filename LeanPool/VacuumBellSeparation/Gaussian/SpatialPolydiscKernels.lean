/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SpatialSeparatedKernelBounds

/-!
# Literal six-coordinate kernels on the separated polydisc

The two coordinate triples are centred at the two balls. Their actual
difference has Euclidean norm at most 2 sqrt(3) R on the coordinate
polydisc; the composed kernels are genuinely complex differentiable
there and satisfy explicit supremum bounds.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

/-- Spatial complex pair with underlying type `EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin
3)`. -/
abbrev SpatialComplexPair := EuclideanSpace ℂ (Fin 3) × EuclideanSpace ℂ (Fin 3)

/-- Spatial pair field kernel given by `besselFieldKernel μ (spatialComplexRadius s (xy.2 -
xy.1))`. -/
noncomputable def spatialPairFieldKernel (μ s : ℝ) (xy : SpatialComplexPair) : ℂ :=
  besselFieldKernel μ (spatialComplexRadius s (xy.2 - xy.1))

/-- Spatial pair momentum kernel given by `besselMomentumKernel μ (spatialComplexRadius s (xy.2 -
xy.1))`. -/
noncomputable def spatialPairMomentumKernel (μ s : ℝ) (xy : SpatialComplexPair) : ℂ :=
  besselMomentumKernel μ (spatialComplexRadius s (xy.2 - xy.1))

/-- Spatial closed polydisc with membership specified by `{xy | (∀ j, ‖xy.1 j‖ ≤ R) ∧ (∀ j, ‖xy.2
j‖ ≤ R)}`. -/
def spatialClosedPolydisc (R : ℝ) : Set SpatialComplexPair :=
  {xy | (∀ j, ‖xy.1 j‖ ≤ R) ∧ (∀ j, ‖xy.2 j‖ ≤ R)}

theorem spatial_triple_norm_le_of_coordinate_bounds {R : ℝ} (hR : 0 ≤ R)
    (x : EuclideanSpace ℂ (Fin 3)) (hx : ∀ j, ‖x j‖ ≤ R) :
    ‖x‖ ≤ Real.sqrt 3 * R := by
  have hsq : ‖x‖ ^ 2 ≤ 3 * R ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _ : Fin 3, R ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (hx j) 2
      _ = _ := by simp
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := norm_nonneg x
  have hb : 0 ≤ Real.sqrt 3 * R := mul_nonneg (Real.sqrt_nonneg _) hR
  nlinarith

theorem spatial_polydisc_difference_norm_le {R : ℝ} (hR : 0 ≤ R)
    {xy : SpatialComplexPair} (hxy : xy ∈ spatialClosedPolydisc R) :
    ‖xy.2 - xy.1‖ ≤ 2 * Real.sqrt 3 * R := by
  calc
    _ ≤ ‖xy.2‖ + ‖xy.1‖ := norm_sub_le _ _
    _ ≤ Real.sqrt 3 * R + Real.sqrt 3 * R :=
      add_le_add (spatial_triple_norm_le_of_coordinate_bounds hR xy.2 hxy.2)
        (spatial_triple_norm_le_of_coordinate_bounds hR xy.1 hxy.1)
    _ = _ := by ring

theorem differentiableAt_spatialPairFieldKernel {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 ≤ R)
    (hsep : 8 * Real.sqrt 3 * R ≤ s) {xy : SpatialComplexPair}
    (hxy : xy ∈ spatialClosedPolydisc R) :
    DifferentiableAt ℂ (spatialPairFieldKernel μ s) xy := by
  have hd : 0 ≤ 2 * Real.sqrt 3 * R := by positivity
  have hgeom : 4 * (2 * Real.sqrt 3 * R) ≤ s := by nlinarith
  have hq := spatialSquaredRadius_re_pos hs hd hgeom (xy.2 - xy.1)
    (spatial_polydisc_difference_norm_le hR hxy)
  have hcomp :=
    (differentiableAt_spatialBesselFieldKernel hμ (xy.2 - xy.1) hq).comp
      (f := fun p : SpatialComplexPair => p.2 - p.1)
      (g := fun d : EuclideanSpace ℂ (Fin 3) =>
        besselFieldKernel μ (spatialComplexRadius s d)) xy
      (differentiableAt_snd.sub differentiableAt_fst)
  simpa only [spatialPairFieldKernel, Function.comp_def] using! hcomp

theorem differentiableAt_spatialPairMomentumKernel {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 ≤ R)
    (hsep : 8 * Real.sqrt 3 * R ≤ s) {xy : SpatialComplexPair}
    (hxy : xy ∈ spatialClosedPolydisc R) :
    DifferentiableAt ℂ (spatialPairMomentumKernel μ s) xy := by
  have hd : 0 ≤ 2 * Real.sqrt 3 * R := by positivity
  have hgeom : 4 * (2 * Real.sqrt 3 * R) ≤ s := by nlinarith
  have hq := spatialSquaredRadius_re_pos hs hd hgeom (xy.2 - xy.1)
    (spatial_polydisc_difference_norm_le hR hxy)
  have hcomp :=
    (differentiableAt_spatialBesselMomentumKernel hμ (xy.2 - xy.1) hq).comp
      (f := fun p : SpatialComplexPair => p.2 - p.1)
      (g := fun d : EuclideanSpace ℂ (Fin 3) =>
        besselMomentumKernel μ (spatialComplexRadius s d)) xy
      (differentiableAt_snd.sub differentiableAt_fst)
  simpa only [spatialPairMomentumKernel, Function.comp_def] using! hcomp

theorem spatialPairFieldKernel_norm_le {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 ≤ R)
    (hsep : 8 * Real.sqrt 3 * R ≤ s) {xy : SpatialComplexPair}
    (hxy : xy ∈ spatialClosedPolydisc R) :
    ‖spatialPairFieldKernel μ s xy‖ ≤
      (6 / s ^ 2) * Real.sqrt (1 + μ * s) *
        Real.exp (-μ * s + 4 * μ * Real.sqrt 3 * R) := by
  have h := spatialBesselFieldKernel_norm_le hμ hs
    (show 0 ≤ 2 * Real.sqrt 3 * R by positivity)
    (show 4 * (2 * Real.sqrt 3 * R) ≤ s by nlinarith)
    (xy.2 - xy.1) (spatial_polydisc_difference_norm_le hR hxy)
  simpa only [spatialPairFieldKernel,
    show 2 * μ * (2 * Real.sqrt 3 * R) = 4 * μ * Real.sqrt 3 * R by ring] using h

theorem spatialPairMomentumKernel_norm_le {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 ≤ R)
    (hsep : 8 * Real.sqrt 3 * R ≤ s) {xy : SpatialComplexPair}
    (hxy : xy ∈ spatialClosedPolydisc R) :
    ‖spatialPairMomentumKernel μ s xy‖ ≤
      (128 / s ^ 4) * (1 + μ * s) * Real.sqrt (1 + μ * s) *
        Real.exp (-μ * s + 4 * μ * Real.sqrt 3 * R) := by
  have h := spatialBesselMomentumKernel_norm_le hμ hs
    (show 0 ≤ 2 * Real.sqrt 3 * R by positivity)
    (show 4 * (2 * Real.sqrt 3 * R) ≤ s by nlinarith)
    (xy.2 - xy.1) (spatial_polydisc_difference_norm_le hR hxy)
  simpa only [spatialPairMomentumKernel,
    show 2 * μ * (2 * Real.sqrt 3 * R) = 4 * μ * Real.sqrt 3 * R by ring] using h

end VacuumBellSeparation.Gaussian
