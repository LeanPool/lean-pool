/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneCoordinateH1

/-!
# Whole-plane local induction operators

This module defines the whole-plane induction actions on three-component fields: the local
generator of `eq:local-generator` and the selected-cell action of
`eq:selected-whole-plane-operator`, read on `ℂ³`.  The chart calculus of §7 compares the torus
operator with the selected whole-plane operator through them (proof of `lem:parametrix-error`),
and the two-component operators of the paper are built on the same velocity record in
`Operator/WholePlaneLocalC2.lean`.  The domain is the weak Fourier-graph `H²(ℝ²; ℂ³)`
constructed in `WholePlaneH2`, and every term below is a bounded map from that domain to
`L²(ℝ²; ℂ³)`.

The operator only needs the value of a velocity in `L∞` and two proposed
`L∞` derivative coefficients.  This free data is called
`WholePlaneVelocityCoefficients`, rather than a `W¹⁻∞` velocity.  The
separate certificate `WholePlaneVelocityCoefficients.HasWeakGradient` records
exactly when the proposed coefficients are the weak derivatives of an
`L²` representative.  This separation keeps the bounded operator algebra
usable while preventing arbitrary coefficient data from being mistaken for a
Sobolev velocity.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal LineDeriv SchwartzMap

/-! ## Velocity coefficient data and its analytic certificate -/

/-- The coefficient fields needed by the whole-plane induction expression.

`value` is the three-component velocity coefficient, and `deriv j` is the
coefficient intended to represent its `j`-th transverse weak derivative.
No derivative relation is built into this raw structure; use
`HasWeakGradient` for that assertion. -/
structure WholePlaneVelocityCoefficients where
  /-- The essentially bounded three-component velocity field. -/
  value : WholePlaneC3LInf
  /-- The coefficient asserted (when certified by `HasWeakGradient`) to be
  the `j`-th transverse weak derivative of `value`. -/
  deriv : Fin 2 → WholePlaneC3LInf

namespace WholePlaneVelocityCoefficients

/-- The proposed derivative coefficients are weak derivatives of the
value coefficient.

Bounded functions have at most polynomial growth and therefore define
tempered distributions.  Consequently this certificate is stated directly
through Mathlib's canonical `L∞ → 𝒮'` embedding and imposes no unnecessary
global `L²` or compact-support hypothesis.
-/
structure HasWeakGradient (u : WholePlaneVelocityCoefficients) : Prop where
  weak_deriv : ∀ j : Fin 2,
    ∂_{wholePlaneBasis j}
        (wholePlaneLInfToTempered C3 u.value) =
      wholePlaneLInfToTempered C3 (u.deriv j)

/-- A certified velocity supplies the weak-gradient hypothesis
`HasWholePlaneLInfWeakGradient` of its value and derivative coefficients. -/
theorem HasWeakGradient.hasWholePlaneLInfWeakGradient
    {u : WholePlaneVelocityCoefficients} (hu : u.HasWeakGradient) :
    HasWholePlaneLInfWeakGradient u.value u.deriv := by
  intro j
  exact hu.weak_deriv j

end WholePlaneVelocityCoefficients

/-! ## The fixed-wavenumber local generator -/

/-- The multiplier `Δ⊥ - N²` on the weak whole-plane `H²` domain. -/
def wholePlaneLocalDiffusion (N : ℝ) :
    WholePlaneC3H2 →L[ℂ] WholePlaneC3L2 :=
  wholePlaneLaplacian C3 -
    ((N : ℂ) ^ 2) • wholePlaneH2Embedding C3

/-- The transverse transport term `∑ j, v_j ∂_j b`. -/
def wholePlaneLocalTransport (v : WholePlaneVelocityCoefficients) :
    WholePlaneC3H2 →L[ℂ] WholePlaneC3L2 :=
  ∑ j : Fin 2,
    (scalarVectorMulL2 (E := C3) volume
      (wholePlaneCoordLInf j.castSucc v.value)).comp
        (wholePlaneH2FirstDerivative C3 j)

/-- The axial transport coefficient `(i N) v₃ b`. -/
def wholePlaneLocalAxialTransport
    (v : WholePlaneVelocityCoefficients) (N : ℝ) :
    WholePlaneC3H2 →L[ℂ] WholePlaneC3L2 :=
  (Complex.I * (N : ℂ)) •
    (scalarVectorMulL2 (E := C3) volume
      (wholePlaneCoordLInf (2 : Fin 3) v.value)).comp
        (wholePlaneH2Embedding C3)

/-- The stretching term `∑ j, b_j ∂_j v`. -/
def wholePlaneLocalStretching (v : WholePlaneVelocityCoefficients) :
    WholePlaneC3H2 →L[ℂ] WholePlaneC3L2 :=
  ∑ j : Fin 2,
    (vectorScalarMulL2 (E := C3) volume (v.deriv j)).comp
      ((wholePlaneCoordL2 j.castSucc).comp (wholePlaneH2Embedding C3))

/-- The three-component counterpart of the paper's local generator `eq:local-generator`
(which acts on two-component fields; `N = 2π` there),

`L_δ b = δ(Δ⊥-N²)b - v⊥·∇⊥b - iNv₃b
  + (b⊥·∇⊥)v`.
-/
def wholePlaneLocalAction (v : WholePlaneVelocityCoefficients)
    (δ N : ℝ) : WholePlaneC3H2 →L[ℂ] WholePlaneC3L2 :=
  (δ : ℂ) • wholePlaneLocalDiffusion N -
    wholePlaneLocalTransport v - wholePlaneLocalAxialTransport v N +
      wholePlaneLocalStretching v

/-! ## Selected-cell whole-plane operator -/

/-- The real axial wavenumber corresponding to the integer torus frequency
`K`. -/
def wholePlaneAxialWavenumber (K : ℤ) : ℝ :=
  2 * Real.pi * K

/-- The complex axial derivative multiplier is `i` times the corresponding
real wavenumber. -/
theorem axialMultiplier_eq_i_mul_wholePlaneAxialWavenumber (K : ℤ) :
    axialMultiplier K =
      Complex.I * (wholePlaneAxialWavenumber K : ℂ) := by
  simp [axialMultiplier, wholePlaneAxialWavenumber]
  ring

/-- The constant axial background contributes the scalar action
`-(2π i K a)b`. -/
def selectedWholePlaneAxialShift (K : ℤ) (a : ℝ) :
    WholePlaneC3H2 →L[ℂ] WholePlaneC3L2 :=
  (axialMultiplier K * (a : ℂ)) •
    wholePlaneH2Embedding C3

/-- The selected-cell whole-plane action of `eq:selected-whole-plane-operator`, here on
three-component fields. -/
def selectedWholePlaneInductionAction
    (uLoc : WholePlaneVelocityCoefficients) (ε : ℝ) (K : ℤ) (a : ℝ) :
    WholePlaneC3H2 →L[ℂ] WholePlaneC3L2 :=
  wholePlaneLocalAction uLoc ε (wholePlaneAxialWavenumber K) -
    selectedWholePlaneAxialShift K a

/-! ## Exact expanded formulas -/

/--
The local diffusion is `Δ_⊥ b - N² b`: the transverse Laplacian minus the axial
symbol at wavenumber `N`.
-/
theorem wholePlaneLocalDiffusion_apply (N : ℝ) (b : WholePlaneC3H2) :
    wholePlaneLocalDiffusion N b =
      wholePlaneLaplacian C3 b -
        ((N : ℂ) ^ 2) • wholePlaneH2Embedding C3 b := by
  rfl

/--
Expanded form of the transverse transport term: the sum over `j < 2` of the `j`-th velocity
component times the `j`-th weak derivative of `b`.
-/
theorem wholePlaneLocalTransport_apply
    (v : WholePlaneVelocityCoefficients) (b : WholePlaneC3H2) :
    wholePlaneLocalTransport v b =
      ∑ j : Fin 2,
        scalarVectorMulL2 (E := C3) volume
          (wholePlaneCoordLInf j.castSucc v.value)
            (wholePlaneH2FirstDerivative C3 j b) := by
  simp [wholePlaneLocalTransport]

/--
Expanded form of the axial transport term: `i N` times the third velocity component times `b`,
the axial derivative acting as the multiplier `i N` on the axial mode.
-/
theorem wholePlaneLocalAxialTransport_apply
    (v : WholePlaneVelocityCoefficients) (N : ℝ) (b : WholePlaneC3H2) :
    wholePlaneLocalAxialTransport v N b =
      (Complex.I * (N : ℂ)) •
        scalarVectorMulL2 (E := C3) volume
          (wholePlaneCoordLInf (2 : Fin 3) v.value)
            (wholePlaneH2Embedding C3 b) := by
  rfl

/--
Expanded form of the stretching term: the sum over `j < 2` of `∂_j u` times the `j`-th component
of `b`.
-/
theorem wholePlaneLocalStretching_apply
    (v : WholePlaneVelocityCoefficients) (b : WholePlaneC3H2) :
    wholePlaneLocalStretching v b =
      ∑ j : Fin 2,
        vectorScalarMulL2 (E := C3) volume (v.deriv j)
          (wholePlaneCoordL2 j.castSucc (wholePlaneH2Embedding C3 b)) := by
  simp [wholePlaneLocalStretching]

/--
The selected-cell spectral translation acts as multiplication by the constant
`axialMultiplier K * a = 2π i K a`, the shift subtracted in the selected-cell action.
-/
theorem selectedWholePlaneAxialShift_apply
    (K : ℤ) (a : ℝ) (b : WholePlaneC3H2) :
    selectedWholePlaneAxialShift K a b =
      (axialMultiplier K * (a : ℂ)) •
        wholePlaneH2Embedding C3 b := by
  rfl

end

end FastDynamo
