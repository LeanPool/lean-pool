/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumTangent
public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumPhase

/-!
# Euler--Lagrange tangent at the native uniform vacuum

This module closes the operator link that an energy expansion by itself does
not close. It extracts the exact quadratic modal Lagrangian from the native
two-field action and proves its weak Euler--Lagrange equation. No Dirac
operator occurs in this file.
-/

@[expose] public section

namespace LeanDirac.V2

variable {Site : Type} {Edge : Type*}

open Complex Filter Topology
noncomputable section

/-- The real part of the complex Hermitian pairing of two scalar amplitudes. -/
def uniformScalarRealPair (source target : ℂ) : ℝ :=
  (star source * target).re

/-- The configuration with vanishing first field and an arbitrary second field. -/
def zeroPsiState (chiField : Site → C3) : State Site where
  psi := fun _ _ => 0
  chi := chiField

/-- A variation of the first native field with the second field fixed. -/
def purePsiDirection (psiField : Site → C3) : State Site where
  psi := psiField
  chi := fun _ _ => 0

/-- A variation of the second native field with the first field fixed. -/
def pureChiDirection (chiField : Site → C3) : State Site where
  psi := fun _ _ => 0
  chi := chiField

/-- At every zero-Psi configuration, not merely at the selected axial
representative, the first variation in every Psi direction vanishes.  Hence
changing the live chi field cannot generate a linear source for Psi at the
vacuum.  This is the action-level zero cross block in that direction. -/
theorem zero_psi_state_has_no_linear_psi_source
    [Fintype Site] [Fintype Edge]
    (r : ℝ) (chiField psiField : Site → C3)
    (bond : Edge → Bond Site) :
    potentialFirstVariation r (zeroPsiState chiField)
      (purePsiDirection psiField) bond = 0 := by
  unfold potentialFirstVariation
  have hsite : ∀ site,
      sitePotentialFirstVariation r (zeroPsiState chiField)
        (purePsiDirection psiField) site = 0 := by
    intro site
    simp [sitePotentialFirstVariation, zeroPsiState,
      purePsiDirection, density, c3RealPair]
  have hbond : ∀ edge,
      exteriorAreaBondFirstVariation r (zeroPsiState chiField)
        (purePsiDirection psiField) (bond edge) = 0 := by
    intro edge
    simp [exteriorAreaBondFirstVariation, bondAreaDifference,
      bondAreaFirstVariation, zeroPsiState, purePsiDirection,
      wedge, wedgeFirstVariation, difference, c3RealPair]
  simp [hsite, hbond]

theorem uniform_transverse_bond_area_scales
    (r eps : ℝ) (f g : Site → ℂ) (edge : Bond Site) :
    bondAreaDifference (uniformTransverseState r eps f g) edge =
      c3ScaleReal eps
        (bondAreaDifference (uniformTransverseState r 1 f g) edge) := by
  funext component
  fin_cases component <;>
    simp [bondAreaDifference, uniformTransverseState, wedge,
      difference, c3ScaleReal] <;> ring

theorem uniform_transverse_chi_bond_variation_scales
    (r eps : ℝ) (f g : Site → ℂ) (chiField : Site → C3)
    (edge : Bond Site) :
    bondAreaFirstVariation (uniformTransverseState r eps f g)
        (pureChiDirection chiField) edge =
      c3ScaleReal eps
        (bondAreaFirstVariation (uniformTransverseState r 1 f g)
          (pureChiDirection chiField) edge) := by
  funext component
  fin_cases component <;>
    simp [bondAreaFirstVariation, wedgeFirstVariation,
      uniformTransverseState, pureChiDirection, wedge, difference,
      c3Add, c3ScaleReal] <;> ring

/-- The reciprocal chi equation receives no term linear in a transverse Psi
perturbation: its complete variational source is quadratic in the perturbation
amplitude.  Together with `zero_psi_state_has_no_linear_psi_source`, this
proves invariance of the transverse two-channel sector in the full linearized
Psi--chi system. -/
theorem uniform_transverse_chi_source_is_quadratic
    [Fintype Site] [Fintype Edge]
    (r eps : ℝ) (f g : Site → ℂ) (chiField : Site → C3)
    (bond : Edge → Bond Site) :
    potentialFirstVariation r (uniformTransverseState r eps f g)
        (pureChiDirection chiField) bond =
      eps ^ 2 *
        potentialFirstVariation r (uniformTransverseState r 1 f g)
          (pureChiDirection chiField) bond := by
  unfold potentialFirstVariation
  have hsite : ∀ site,
      sitePotentialFirstVariation r (uniformTransverseState r eps f g)
          (pureChiDirection chiField) site =
        eps ^ 2 * sitePotentialFirstVariation r
          (uniformTransverseState r 1 f g)
          (pureChiDirection chiField) site := by
    intro site
    unfold sitePotentialFirstVariation
    rw [uniform_transverse_psi_density,
      uniform_transverse_chi_density,
      uniform_transverse_psi_density,
      uniform_transverse_chi_density]
    simp [uniformTransverseState, pureChiDirection, c3RealPair,
      Fin.sum_univ_succ, Complex.mul_re]
    ring
  have hbond : ∀ edge,
      exteriorAreaBondFirstVariation r
          (uniformTransverseState r eps f g)
          (pureChiDirection chiField) (bond edge) =
        eps ^ 2 * exteriorAreaBondFirstVariation r
          (uniformTransverseState r 1 f g)
          (pureChiDirection chiField) (bond edge) := by
    intro edge
    unfold exteriorAreaBondFirstVariation
    rw [uniform_transverse_bond_area_scales,
      uniform_transverse_chi_bond_variation_scales]
    simp [c3RealPair, c3ScaleReal, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im]
    ring
  simp_rw [hsite, hbond]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The sum of squared moduli of the two transverse components. -/
def uniformCell2Density (z : UniformCell2) : ℝ :=
  ∑ component, Complex.normSq (z component)

/-- The real pairing on two transverse complex components. -/
def uniformCell2RealPair (z w : UniformCell2) : ℝ :=
  ∑ component, uniformScalarRealPair (z component) (w component)

/-- The exact squared mode frequency from the mass term and C19 transport symbol. -/
def uniformVacuumModalSquare (r : ℝ) (momentum : LatticeMomentum) : ℝ :=
  r ^ 2 + c19TransportSymbol momentum

/-- The quadratic kinetic energy of the transverse velocity. -/
def uniformVacuumModalKinetic (velocity : UniformCell2) : ℝ :=
  uniformCell2Density velocity / 2

/-- The quadratic potential of a transverse mode at the uniform vacuum. -/
def uniformVacuumModalPotential
    (r : ℝ) (momentum : LatticeMomentum)
    (position : UniformCell2) : ℝ :=
  uniformVacuumModalSquare r momentum * uniformCell2Density position / 2

/-- The quadratic transverse Lagrangian, formed from kinetic and potential terms. -/
def uniformVacuumModalLagrangian
    (r : ℝ) (momentum : LatticeMomentum)
    (position velocity : UniformCell2) : ℝ :=
  uniformVacuumModalKinetic velocity -
    uniformVacuumModalPotential r momentum position

/-- The per-site action density of the transverse character ansatz. -/
def uniformCharacterActionDensity
    (r eps : ℝ) (position velocity : UniformCell2)
    (momentum : LatticeMomentum) (site : InfiniteCubicSite) : ℝ :=
  density ((uniformTransverseVelocity eps
      (fun x => cubicLatticeCharacter momentum x * velocity 0)
      (fun x => cubicLatticeCharacter momentum x * velocity 1)).psiDot site) / 2 -
    (sitePotential r
      (uniformTransverseState r eps
        (fun x => cubicLatticeCharacter momentum x * position 0)
        (fun x => cubicLatticeCharacter momentum x * position 1)) site +
      uniformTransverseCharacterTransportEnergy r eps
        (position 0) (position 1) momentum site)

theorem uniform_character_velocity_density
    (eps : ℝ) (velocity : UniformCell2)
    (momentum : LatticeMomentum) (site : InfiniteCubicSite) :
    density ((uniformTransverseVelocity eps
        (fun x => cubicLatticeCharacter momentum x * velocity 0)
        (fun x => cubicLatticeCharacter momentum x * velocity 1)).psiDot site) =
      eps ^ 2 * uniformCell2Density velocity := by
  unfold uniformTransverseVelocity uniformCell2Density density
  simp only [Fin.sum_univ_succ]
  simp [Complex.normSq_mul, cubic_character_normSq_one]
  ring

theorem uniform_character_site_potential
    (r eps : ℝ) (position : UniformCell2)
    (momentum : LatticeMomentum) (site : InfiniteCubicSite) :
    sitePotential r
        (uniformTransverseState r eps
          (fun x => cubicLatticeCharacter momentum x * position 0)
          (fun x => cubicLatticeCharacter momentum x * position 1)) site =
      r ^ 2 * eps ^ 2 * uniformCell2Density position / 2 +
        eps ^ 4 * uniformCell2Density position ^ 2 / 4 := by
  rw [uniform_transverse_site_potential]
  unfold uniformCell2Density
  simp only [Fin.sum_univ_succ]
  simp [Complex.normSq_mul, cubic_character_normSq_one]

/-- The exact native action density is its quadratic tangent action plus the
displayed quartic remainder. Thus the tangent operator below is extracted
from the action rather than postulated. -/
theorem uniform_character_action_density_expansion
    (r eps : ℝ) (hr : r ≠ 0)
    (position velocity : UniformCell2)
    (momentum : LatticeMomentum) (site : InfiniteCubicSite) :
    uniformCharacterActionDensity r eps position velocity momentum site =
      eps ^ 2 * uniformVacuumModalLagrangian r momentum position velocity -
        eps ^ 4 * uniformCell2Density position ^ 2 / 4 := by
  unfold uniformCharacterActionDensity uniformVacuumModalLagrangian
    uniformVacuumModalKinetic uniformVacuumModalPotential
    uniformVacuumModalSquare
  rw [uniform_character_velocity_density eps velocity momentum site,
    uniform_character_site_potential r eps position momentum site,
    uniform_transverse_character_has_c19_symbol r eps hr
      (position 0) (position 1) momentum site]
  unfold uniformCell2Density
  simp only [Fin.sum_univ_succ]
  simp only [show (1 : Fin 2) = Fin.succ 0 by rfl]
  ring

/-- Symmetric second-difference of the exact native action density.  The
zero value is filled by its algebraically determined limit. -/
def uniformCharacterTangentQuotient
    (r eps : ℝ) (position velocity : UniformCell2)
    (momentum : LatticeMomentum) (site : InfiniteCubicSite) : ℝ :=
  if eps = 0 then
    2 * uniformVacuumModalLagrangian r momentum position velocity
  else
    (uniformCharacterActionDensity r eps position velocity momentum site +
      uniformCharacterActionDensity r (-eps) position velocity momentum site -
      2 * uniformCharacterActionDensity r 0
        position velocity momentum site) / eps ^ 2

/-- Exact Hessian extraction from the full nonlinear native action.  This
prevents the modal tangent operator from being introduced by definition. -/
theorem uniform_character_tangent_quotient_exact
    (r eps : ℝ) (hr : r ≠ 0)
    (position velocity : UniformCell2)
    (momentum : LatticeMomentum) (site : InfiniteCubicSite) :
    uniformCharacterTangentQuotient r eps position velocity momentum site =
      2 * uniformVacuumModalLagrangian r momentum position velocity -
        eps ^ 2 * uniformCell2Density position ^ 2 / 2 := by
  by_cases heps : eps = 0
  · subst eps
    simp [uniformCharacterTangentQuotient]
  · unfold uniformCharacterTangentQuotient
    rw [ite_eq_right heps,
      uniform_character_action_density_expansion
        r eps hr position velocity momentum site,
      uniform_character_action_density_expansion
        r (-eps) hr position velocity momentum site,
      uniform_character_action_density_expansion
        r 0 hr position velocity momentum site]
    field_simp [heps]
    ring

theorem uniform_character_tangent_quotient_tends_to_hessian
    (r : ℝ) (hr : r ≠ 0)
    (position velocity : UniformCell2)
    (momentum : LatticeMomentum) (site : InfiniteCubicSite) :
    Tendsto
      (fun eps : ℝ =>
        uniformCharacterTangentQuotient
          r eps position velocity momentum site)
      (nhds 0)
      (nhds (2 * uniformVacuumModalLagrangian
        r momentum position velocity)) := by
  have hfun :
      (fun eps : ℝ =>
        uniformCharacterTangentQuotient
          r eps position velocity momentum site) =
      (fun eps : ℝ =>
        2 * uniformVacuumModalLagrangian r momentum position velocity -
          eps ^ 2 * uniformCell2Density position ^ 2 / 2) := by
    funext eps
    exact uniform_character_tangent_quotient_exact
      r eps hr position velocity momentum site
  rw [hfun]
  have hcontinuous : ContinuousAt
      (fun eps : ℝ =>
        2 * uniformVacuumModalLagrangian r momentum position velocity -
          eps ^ 2 * uniformCell2Density position ^ 2 / 2) 0 := by
    fun_prop
  simpa [ContinuousAt] using hcontinuous

/-- The affine variation of a two-component transverse amplitude. -/
def uniformCell2Line
    (position direction : UniformCell2) (eps : ℝ) : UniformCell2 :=
  fun component => position component + (eps : ℂ) * direction component

theorem uniform_cell2_density_line
    (position direction : UniformCell2) (eps : ℝ) :
    uniformCell2Density (uniformCell2Line position direction eps) =
      uniformCell2Density position +
        2 * eps * uniformCell2RealPair position direction +
        eps ^ 2 * uniformCell2Density direction := by
  simp [uniformCell2Density, uniformCell2RealPair, uniformCell2Line,
    uniformScalarRealPair, Complex.normSq, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ]
  ring

/-- The directional derivative of the quadratic transverse potential. -/
def uniformVacuumModalPotentialVariation
    (r : ℝ) (momentum : LatticeMomentum)
    (position direction : UniformCell2) : ℝ :=
  uniformVacuumModalSquare r momentum *
    uniformCell2RealPair position direction

/-- Exact line expansion of the action-derived modal potential. Its linear
coefficient is the variational derivative used in the Euler--Lagrange
equation. -/
theorem uniform_modal_potential_line
    (r eps : ℝ) (momentum : LatticeMomentum)
    (position direction : UniformCell2) :
    uniformVacuumModalPotential r momentum
        (uniformCell2Line position direction eps) =
      uniformVacuumModalPotential r momentum position +
        eps * uniformVacuumModalPotentialVariation
          r momentum position direction +
        eps ^ 2 * uniformVacuumModalSquare r momentum *
          uniformCell2Density direction / 2 := by
  unfold uniformVacuumModalPotential
    uniformVacuumModalPotentialVariation
  rw [uniform_cell2_density_line]
  ring

/-- The linearized acceleration multiplying each mode by minus its exact squared frequency. -/
def uniformVacuumModalAcceleration
    (r : ℝ) (momentum : LatticeMomentum)
    (position : UniformCell2) : UniformCell2 :=
  fun component =>
    -(uniformVacuumModalSquare r momentum : ℂ) * position component

/-- Weak Euler--Lagrange equation for every complex two-channel variation.
Together with the preceding exact action expansion, this identifies the
concrete native tangent generator. -/
theorem uniform_modal_euler_lagrange
    (r : ℝ) (momentum : LatticeMomentum)
    (position direction : UniformCell2) :
    uniformCell2RealPair
        (uniformVacuumModalAcceleration r momentum position) direction +
      uniformVacuumModalPotentialVariation
        r momentum position direction = 0 := by
  simp [uniformCell2RealPair, uniformVacuumModalAcceleration,
    uniformVacuumModalPotentialVariation, uniformScalarRealPair,
    Complex.mul_re, Complex.mul_im, Fin.sum_univ_succ]
  ring

/-- The first-order form of the exact native transverse mode equation. -/
def uniformVacuumNativeGenerator
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : UniformTwoChannelPhase :=
  (phase.2, uniformVacuumModalAcceleration r momentum phase.1)

/-- The modal acceleration using the quadratic spatial symbol. -/
def uniformVacuumContinuumAcceleration
    (r : ℝ) (momentum : LatticeMomentum)
    (position : UniformCell2) : UniformCell2 :=
  fun component =>
    -((r ^ 2 + c19QuadraticSymbol momentum : ℝ) : ℂ) * position component

/-- The first-order form of the continuum mode equation in native phase coordinates. -/
def uniformVacuumContinuumGenerator
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : UniformTwoChannelPhase :=
  (phase.2, uniformVacuumContinuumAcceleration r momentum phase.1)

/-- The only spatial difference between the exact C19 tangent generator and
its continuum KG generator is the already-derived C19 remainder. -/
theorem uniform_native_acceleration_splits
    (r : ℝ) (momentum : LatticeMomentum)
    (position : UniformCell2) :
    uniformVacuumModalAcceleration r momentum position =
      fun component =>
        uniformVacuumContinuumAcceleration r momentum position component -
          (c19SpatialRemainder momentum : ℂ) * position component := by
  funext component
  simp only [uniformVacuumModalAcceleration, uniformVacuumModalSquare,
    uniformVacuumContinuumAcceleration]
  rw [c19_symbol_exact_quadratic_plus_remainder]
  push_cast
  ring

theorem uniform_native_generator_splits
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformVacuumNativeGenerator r momentum phase =
      ((uniformVacuumContinuumGenerator r momentum phase).1,
        fun component =>
          (uniformVacuumContinuumGenerator r momentum phase).2 component -
            (c19SpatialRemainder momentum : ℂ) * phase.1 component) := by
  apply Prod.ext
  · rfl
  · exact uniform_native_acceleration_splits r momentum phase.1

end
end LeanDirac.V2
