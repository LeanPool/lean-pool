/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Complex.Basic

/-!
# Spectral circles

The paper uses one positively oriented circle whose closed interior lies in
the open right half-plane.  Center and positive radius determine the standard
positive parametrization used by Mathlib's `circleIntegral`.

Besides the record itself this module carries the two elementary things every contour argument
of the development needs:

* the growth floor `g_* = Re(centre) - radius` and the imaginary height
  `M = |Im centre| + radius` (the paper's `M = max_{ζ∈𝒢} |Im ζ|` in the proof of
  `prop:background-resolvent`), with their bounds on the closed
  disc, on the boundary and on a disc enlarged by `rho`;
* the **vertical translation** `Gamma_tau = Gamma - i tau` (the display after the proof of
  `lem:exact-renormalization`), with its centre, radius, growth floor and the two
  membership criteria.  Translating downwards by `tau` is how the paper moves the seed contour to
  the axial sector (§5, used in §§6–7), and the same circle is the contour of the global Riesz
  projection of §7.2; keeping one definition here is what lets the two sides meet without a bridge.
-/

@[expose] public section

namespace FastDynamo

open Complex Metric Set

/-- A positively oriented spectral circle, represented by center and radius. -/
structure SpectralCircle where
  /-- Center of the spectral contour. -/
  center : ℂ
  /-- Radius of the spectral contour. -/
  radius : ℝ
  radius_pos : 0 < radius

namespace SpectralCircle

/-- The contour used for the Riesz integral. -/
def boundary (Γ : SpectralCircle) : Set ℂ :=
  Metric.sphere Γ.center Γ.radius

/-- The closed region enclosed by the contour. -/
def closedRegion (Γ : SpectralCircle) : Set ℂ :=
  Metric.closedBall Γ.center Γ.radius

/-- The minimum real part on the closed circular region. -/
def growthFloor (Γ : SpectralCircle) : ℝ :=
  Γ.center.re - Γ.radius

/--
Every point of the closed disc bounded by a spectral circle has real part at least the circle's
growth floor `center.re - radius`; this is the uniform lower bound on growth rates that the
contour guarantees.
-/
theorem growthFloor_le_re {Γ : SpectralCircle} {z : ℂ}
    (hz : z ∈ Γ.closedRegion) : Γ.growthFloor ≤ z.re := by
  have hdist : ‖z - Γ.center‖ ≤ Γ.radius := by
    simpa [closedRegion, dist_eq_norm] using (Metric.mem_closedBall.mp hz)
  have hre : |z.re - Γ.center.re| ≤ Γ.radius := by
    exact (Complex.abs_re_le_norm (z - Γ.center)).trans hdist
  have := neg_le_of_abs_le hre
  simp only [growthFloor]
  linarith

/-- Every point of the closed region has positive real part exactly when the
circle's growth floor is positive. -/
theorem closedRegion_re_pos {Γ : SpectralCircle} (hΓ : 0 < Γ.growthFloor) {z : ℂ}
    (hz : z ∈ Γ.closedRegion) : 0 < z.re :=
  hΓ.trans_le (growthFloor_le_re hz)

/-! ## Elementary circle bounds -/

/-- A symmetric imaginary-height bound for the closed circular region. -/
def imaginaryBound (Gamma : SpectralCircle) : ℝ :=
  |Gamma.center.im| + Gamma.radius

/-- Every point of the closed disk obeys the elementary center-plus-radius
imaginary-height bound. -/
theorem abs_im_le_imaginaryBound {Gamma : SpectralCircle} {z : ℂ}
    (hz : z ∈ Gamma.closedRegion) : |z.im| ≤ Gamma.imaginaryBound := by
  have hdist : ‖z - Gamma.center‖ ≤ Gamma.radius := by
    simpa only [closedRegion, mem_closedBall, dist_eq_norm] using hz
  have him : |z.im - Gamma.center.im| ≤ Gamma.radius := by
    exact (Complex.abs_im_le_norm (z - Gamma.center)).trans hdist
  calc
    |z.im| = |(z.im - Gamma.center.im) + Gamma.center.im| := by ring_nf
    _ ≤ |z.im - Gamma.center.im| + |Gamma.center.im| := abs_add_le _ _
    _ ≤ Gamma.radius + |Gamma.center.im| :=
      add_le_add him le_rfl
    _ = Gamma.imaginaryBound := by
      simp only [imaginaryBound, add_comm]

end SpectralCircle

/-! ## The vertically translated contour `Gamma_tau` -/

/-- The spectral circle translated downwards by `tau`: `Gamma_tau = Gamma - i tau`.  Its closed
region is the paper's `cG_tau = {zeta - i tau : zeta in cG}` (the display after the proof of
`lem:exact-renormalization`). -/
def backgroundShiftedContour (Gamma : SpectralCircle) (tau : ℝ) : SpectralCircle where
  center := Gamma.center - Complex.I * (tau : ℂ)
  radius := Gamma.radius
  radius_pos := Gamma.radius_pos

/-- The translated circle is centred at `Gamma.center - i tau`. -/
@[simp] theorem backgroundShiftedContour_center (Gamma : SpectralCircle) (tau : ℝ) :
    (backgroundShiftedContour Gamma tau).center = Gamma.center - Complex.I * (tau : ℂ) :=
  rfl

/-- Vertical translation does not change the radius. -/
@[simp] theorem backgroundShiftedContour_radius (Gamma : SpectralCircle) (tau : ℝ) :
    (backgroundShiftedContour Gamma tau).radius = Gamma.radius :=
  rfl

/-- Vertical translation does not change the growth floor `g_* = Re(centre) - radius`, which is
why the whole estimate is carried out at the unshifted `g_*`. -/
@[simp] theorem backgroundShiftedContour_growthFloor (Gamma : SpectralCircle) (tau : ℝ) :
    (backgroundShiftedContour Gamma tau).growthFloor = Gamma.growthFloor := by
  simp [SpectralCircle.growthFloor, backgroundShiftedContour, Complex.sub_re, Complex.mul_re]

/-- `z ∈ cG_tau` exactly when `z + i tau ∈ cG`. -/
theorem mem_backgroundShiftedContour_closedRegion_iff (Gamma : SpectralCircle) (tau : ℝ)
    (z : ℂ) :
    z ∈ (backgroundShiftedContour Gamma tau).closedRegion ↔
      z + Complex.I * (tau : ℂ) ∈ Gamma.closedRegion := by
  simp only [SpectralCircle.closedRegion, Metric.mem_closedBall, dist_eq_norm,
    backgroundShiftedContour_center, backgroundShiftedContour_radius]
  rw [show z - (Gamma.center - Complex.I * (tau : ℂ)) =
    z + Complex.I * (tau : ℂ) - Gamma.center by ring]

/-- `z ∈ Gamma_tau` exactly when `z + i tau ∈ Gamma`. -/
theorem mem_backgroundShiftedContour_boundary_iff (Gamma : SpectralCircle) (tau : ℝ)
    (z : ℂ) :
    z ∈ (backgroundShiftedContour Gamma tau).boundary ↔
      z + Complex.I * (tau : ℂ) ∈ Gamma.boundary := by
  simp only [SpectralCircle.boundary, Metric.mem_sphere, dist_eq_norm,
    backgroundShiftedContour_center, backgroundShiftedContour_radius]
  rw [show z - (Gamma.center - Complex.I * (tau : ℂ)) =
    z + Complex.I * (tau : ℂ) - Gamma.center by ring]

/-- The contour is part of the closed region it bounds. -/
theorem boundary_subset_closedRegion (Gamma : SpectralCircle) :
    Gamma.boundary ⊆ Gamma.closedRegion := fun _ hz ↦
  Metric.sphere_subset_closedBall hz

end FastDynamo
