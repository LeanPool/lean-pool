/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.WholePlaneLocal
public import LeanPool.FastDynamo.Analysis.WholePlaneCoefficientScalingCoordinateCompatibility

/-!
# Scaling data for the selected-cell scaling lemma

This module provides the data of Lemma 5.2 (`lem:exact-renormalization`) of the paper that does
not depend on the number of field components; the lemma itself, for the two-component
operator, is formalised in `FastDynamo/Reduction/ExactScalingC2.lean`.  The normalized affine
map on the state space is

`U_[p,ell] f (y) = ell⁻¹ f ((y - p) / ell)`,

whereas velocity coefficients use the unnormalized pullback.  Thus the
rescaled local velocity `rescaledWholePlaneVelocityCoefficients` has value `ell * P v` and
weak gradient `P (∇v)`.  The scalar matching data are the record
`WholePlaneExactScalingParameters`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal LineDeriv SchwartzMap

/-! ## Rescaled velocity -/

/-- The local cell copy `uLoc(y) = ell * v ((y-p)/ell)` together with its
correctly scaled first weak derivatives. -/
def rescaledWholePlaneVelocityCoefficients
    (v : WholePlaneVelocityCoefficients) (p : WholePlane)
    (ell : ℝ) (hell : 0 < ell) : WholePlaneVelocityCoefficients where
  value := (ell : ℂ) • wholePlaneCoeffPullback C3 p ell hell v.value
  deriv j := wholePlaneCoeffPullback C3 p ell hell (v.deriv j)

/--
The value of the rescaled local velocity is `ell` times the affine pullback of `v`, the
unnormalized scaling used for velocity coefficients in Paper Lemma 5.2.
-/
@[simp] theorem rescaledWholePlaneVelocityCoefficients_value
    (v : WholePlaneVelocityCoefficients) (p : WholePlane)
    (ell : ℝ) (hell : 0 < ell) :
    (rescaledWholePlaneVelocityCoefficients v p ell hell).value =
      (ell : ℂ) • wholePlaneCoeffPullback C3 p ell hell v.value :=
  rfl

/--
The stored derivative coefficients of the rescaled local velocity are the plain affine pullbacks
of the derivatives of `v`, with no extra factor of `ell`.
-/
@[simp] theorem rescaledWholePlaneVelocityCoefficients_deriv
    (v : WholePlaneVelocityCoefficients) (p : WholePlane)
    (ell : ℝ) (hell : 0 < ell) (j : Fin 2) :
    (rescaledWholePlaneVelocityCoefficients v p ell hell).deriv j =
      wholePlaneCoeffPullback C3 p ell hell (v.deriv j) :=
  rfl

/-! ## Scalar matching data -/

/-- Exact scalar relations used in Lemma 5.2.

No sign or scaling relation is implicit: `delta`, `N`, and `tau` are tied to
the physical diffusivity, Fourier index, transverse length, and axial shift
by the paper's relations `δ_n = ε/ℓ_n²`, `K_nℓ_n = 1` (here `N = (2πK)ℓ`) and
`2πK_n a_n = τ`. -/
structure WholePlaneExactScalingParameters where
  /-- Physical magnetic diffusivity in the selected cell. -/
  epsilon : ℝ
  /-- Diffusivity after transverse rescaling. -/
  delta : ℝ
  /-- Selected axial Fourier index. -/
  K : ℤ
  /-- Positive transverse cell length. -/
  ell : ℝ
  /-- Constant axial velocity added to the selected cell. -/
  a : ℝ
  /-- Axial wavenumber of the local model. -/
  N : ℝ
  /-- Imaginary spectral translation induced by the axial constant. -/
  tau : ℝ
  /-- Positivity needed for the affine change of variables. -/
  ell_pos : 0 < ell
  /-- Exact diffusivity matching relation. -/
  delta_eq : delta = epsilon / ell ^ 2
  /-- Exact local/physical axial-wavenumber matching relation. -/
  N_eq : N = wholePlaneAxialWavenumber K * ell
  /-- Exact constant-axial spectral-shift relation. -/
  tau_eq : tau = wholePlaneAxialWavenumber K * a

namespace WholePlaneExactScalingParameters

variable (s : WholePlaneExactScalingParameters)

/--
The cell scale of a set of exact scaling parameters is nonzero, so the affine change of variables
and the matching relations may be divided through by it.
-/
theorem ell_ne_zero : s.ell ≠ 0 := s.ell_pos.ne'

/-- The diffusion coefficient created by two transverse derivatives. -/
theorem epsilon_mul_inv_ell_sq :
    (s.epsilon : ℂ) * (s.ell : ℂ)⁻¹ ^ 2 = (s.delta : ℂ) := by
  rw [s.delta_eq]
  push_cast
  field_simp [s.ell_ne_zero]

/-- The physical axial diffusion mass matches the local one. -/
theorem epsilon_mul_physicalWave_sq :
    (s.epsilon : ℂ) * (wholePlaneAxialWavenumber s.K : ℂ) ^ 2 =
      (s.delta : ℂ) * (s.N : ℂ) ^ 2 := by
  rw [s.delta_eq, s.N_eq]
  push_cast
  field_simp [s.ell_ne_zero]

/-- The axial multiplier of the rescaled local velocity is `iN`. -/
theorem physicalWave_mul_ell :
    (Complex.I * (wholePlaneAxialWavenumber s.K : ℂ)) *
        (s.ell : ℂ) =
      Complex.I * (s.N : ℂ) := by
  rw [s.N_eq]
  push_cast
  ring

/-- The constant axial background becomes the fixed translation `i tau`. -/
theorem axialShift_eq :
    axialMultiplier s.K * (s.a : ℂ) =
      Complex.I * (s.tau : ℂ) := by
  rw [axialMultiplier_eq_i_mul_wholePlaneAxialWavenumber, s.tau_eq]
  push_cast
  ring

end WholePlaneExactScalingParameters

section Terms

variable (v : WholePlaneVelocityCoefficients)
  (p : WholePlane) (s : WholePlaneExactScalingParameters)

/--
Abbreviation for the rescaled local velocity copy `ell * v((y - p)/ell)` used throughout the
termwise conjugation computations.
-/
private abbrev uLoc : WholePlaneVelocityCoefficients :=
  rescaledWholePlaneVelocityCoefficients v p s.ell s.ell_pos

end Terms

end

end FastDynamo
