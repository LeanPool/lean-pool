/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.C19Geometry
public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumPhase

/-! # Native phase charge and its local bond law -/

@[expose] public section

namespace LeanDirac.V2

open Complex BigOperators
noncomputable section

variable {Site : Type}

/-- The scalar complex phase pairing used in the native continuity identity. -/
def uniformScalarPhasePair (source target : ℂ) : ℝ :=
  (star source * target).im

/-- The native phase charge formed from position and velocity at a site. -/
def uniformNativePhaseDensity (position velocity : UniformCell2) : ℝ :=
  ∑ component, uniformScalarPhasePair
    (position component) (velocity component)

/-- The flux of native phase charge along an oriented weighted bond. -/
def uniformNativeOutwardBondCurrent
    (weight : ℝ) (source target : ℂ) : ℝ :=
  -2 * weight * uniformScalarPhasePair source target

/-- Sum the outward currents over all directed bonds from a site. -/
def uniformNativeOutwardCurrentDivergence
    (geometry : C19Lattice Site)
    (position : Site → ℂ) (site : Site) : ℝ :=
  ∑ direction : C19Neighbor,
    uniformNativeOutwardBondCurrent (c19Weight direction)
      (position site) (position (geometry.neighbor site direction))

/-- The derivative of native charge given velocity and acceleration. -/
def uniformNativePhaseDensityDerivative
    (position velocity acceleration : ℂ) : ℝ :=
  uniformScalarPhasePair velocity velocity +
    uniformScalarPhasePair position acceleration

/-- Exact action-tangent U(1) continuity for one native transverse channel.
The second channel obeys the same identity and the two laws add. -/
theorem uniform_native_tangent_local_continuity
    (massSq : ℝ) (geometry : C19Lattice Site)
    (position velocity : Site → ℂ) (site : Site) :
    uniformNativePhaseDensityDerivative
        (position site) (velocity site)
        (uniformScalarTangentAcceleration massSq geometry position site) +
      uniformNativeOutwardCurrentDivergence geometry position site = 0 := by
  simp [uniformNativePhaseDensityDerivative,
    uniformScalarTangentAcceleration, c19ScalarLaplacian,
    uniformNativeOutwardCurrentDivergence,
    uniformNativeOutwardBondCurrent, uniformScalarPhasePair,
    Complex.mul_im]
  ring_nf
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro direction _
  ring

theorem uniform_native_u1_positive_frequency
    (energy : ℝ) (position : UniformCell2) :
    uniformNativePhaseDensity
        (uniformPositiveFrequencyPhase energy position).1
        (uniformPositiveFrequencyPhase energy position).2 =
      -energy * uniformCell2Density position := by
  simp [uniformNativePhaseDensity, uniformPositiveFrequencyPhase,
    uniformScalarPhasePair, uniformCell2Density,
    Complex.normSq, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ]
  ring

end
end LeanDirac.V2
