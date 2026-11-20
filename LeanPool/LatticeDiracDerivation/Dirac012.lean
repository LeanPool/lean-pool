/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac012.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac011

/-!
# DIRAC-012: controlled continuum Dirac evolution

This gate assembles, rather than hides, the two approximations left by
DIRAC-011.  The spatial part is the exact C19 symbol derived from the native
bond action in DIRAC-006.  The time part is the centered second difference
used by the native reversible update in DIRAC-004.  The cubical first-order
operator from DIRAC-009--011 squares to the quadratic continuum part.

The theorem below keeps both errors explicit.  It does not claim an exact
finite-lattice Dirac equation, a localized electron, or physical spin.
-/

@[expose] public section

namespace LeanDirac

noncomputable section
open Complex

theorem density_c3_scale_complex (z : ℂ) (u : C3) :
    density (c3ScaleComplex z u) = Complex.normSq z * density u := by
  unfold density c3ScaleComplex
  simp_rw [Complex.normSq_mul]
  exact (Finset.mul_sum _ _ _).symm

/-! The local action supplies the rest-mass quadratic term on the prepared
complex-chi vacuum.  The remaining fourth-order term is displayed rather
than silently discarded. -/
theorem native_site_potential_on_prepared_vacuum
    (psiAmplitude : Cell8) (corner : CubeCorner) :
    sitePotential chi0
        (alignedEightSiteState psiAmplitude
          (fun _ => (chi0 : ℂ))) corner =
      chi0 ^ 2 * Complex.normSq (psiAmplitude corner) / 2 +
        Complex.normSq (psiAmplitude corner) ^ 2 / 4 := by
  unfold sitePotential alignedEightSiteState
  dsimp
  rw [show density
      (c3ScaleComplex (psiAmplitude corner) (tetraCorner corner)) =
        Complex.normSq (psiAmplitude corner) by
      rw [density_c3_scale_complex, tetra_corner_density_one, mul_one],
    show density
      (c3ScaleComplex (chi0 : ℂ) (companion corner)) = chi0 ^ 2 by
      rw [density_c3_scale_complex, companion_density_one, mul_one]
      norm_num [Complex.normSq, chi0]]
  ring

/-! With the same prepared chi magnitude, the native bond action supplies
exactly one half of the C19 symbol times the perturbation norm. -/
theorem native_prepared_vacuum_transport_energy
    (psiAmplitude : ℂ) (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) :
    nativeRepeatedCharacterTransportEnergy chi0 periodTwoCornerAt
        psiAmplitude (chi0 : ℂ) momentum site =
      Complex.normSq psiAmplitude / 2 * c19TransportSymbol momentum := by
  rw [native_period_two_state_energy_has_c19_symbol]
  rw [Complex.normSq_mul]
  have hchi : Complex.normSq (chi0 : ℂ) = chi0 ^ 2 := by
    norm_num [Complex.normSq, chi0]
  rw [hchi]
  have hscale :
      chi0 ^ 2 * Complex.normSq psiAmplitude / (2 * chi0 ^ 2) =
        Complex.normSq psiAmplitude / 2 := by
    norm_num [chi0]
    ring
  rw [hscale]

theorem native_repeated_site_potential_on_prepared_vacuum
    (psiAmplitude : ℂ) (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) :
    sitePotential chi0
        (repeatedAlignedCharacterState periodTwoCornerAt
          psiAmplitude (chi0 : ℂ) momentum) site =
      chi0 ^ 2 * Complex.normSq psiAmplitude / 2 +
        Complex.normSq psiAmplitude ^ 2 / 4 := by
  unfold sitePotential repeatedAlignedCharacterState
  dsimp
  rw [density_c3_scale_complex, density_c3_scale_complex,
    tetra_corner_density_one, companion_density_one, mul_one, mul_one,
    Complex.normSq_mul, cubic_character_normSq_one, one_mul]
  have hchi : Complex.normSq (chi0 : ℂ) = chi0 ^ 2 := by
    norm_num [Complex.normSq, chi0]
  rw [hchi]
  ring

/-- The site potential plus the C19 transport energy at `site` of the period-two
`repeatedAlignedCharacterState` with `psi` amplitude `eps * amplitude` and `chi` amplitude
`chi0`. -/
def nativePreparedModalPotential
    (eps : ℝ) (amplitude : ℂ) (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) : ℝ :=
  sitePotential chi0
      (repeatedAlignedCharacterState periodTwoCornerAt
        ((eps : ℂ) * amplitude) (chi0 : ℂ) momentum) site +
    nativeRepeatedCharacterTransportEnergy chi0 periodTwoCornerAt
      ((eps : ℂ) * amplitude) (chi0 : ℂ) momentum site

/-! The quadratic coefficient of the native local-plus-bond potential. -/
/-- The scalar symbol `chi0 ^ 2 + c19TransportSymbol momentum`. -/
def nativePsiTangentSymbol (momentum : LatticeMomentum) : ℝ :=
  chi0 ^ 2 + c19TransportSymbol momentum

theorem native_prepared_modal_potential_expansion
    (eps : ℝ) (amplitude : ℂ) (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) :
    nativePreparedModalPotential eps amplitude momentum site =
      eps ^ 2 * Complex.normSq amplitude / 2 *
          nativePsiTangentSymbol momentum +
        eps ^ 4 * Complex.normSq amplitude ^ 2 / 4 := by
  unfold nativePreparedModalPotential
  rw [native_repeated_site_potential_on_prepared_vacuum,
    native_prepared_vacuum_transport_energy,
    Complex.normSq_mul]
  have heps : Complex.normSq (eps : ℂ) = eps ^ 2 := by
    simp [Complex.normSq]
    ring
  rw [heps]
  unfold nativePsiTangentSymbol
  ring

theorem native_psi_tangent_symbol_is_exact_scalar_coefficient
    (momentum : LatticeMomentum) :
    nativePsiTangentSymbol momentum =
      chi0 ^ 2 + c19QuadraticSymbol momentum +
        c19SpatialRemainder momentum := by
  simp [nativePsiTangentSymbol, c19SpatialRemainder]

/-! Centered Verlet measures a mode of angular frequency `frequency` through
`2(1-cos(dt*frequency))`, not through `(dt*frequency) ^ 2` exactly. -/
/-- The quantity `2 * (1 - cos (dt * frequency))`. -/
def centeredTimeNumerator (dt frequency : ℝ) : ℝ :=
  2 * (1 - Real.cos (dt * frequency))

/-- The difference `centeredTimeNumerator dt frequency - (dt * frequency) ^ 2`. -/
def centeredTimeRemainder (dt frequency : ℝ) : ℝ :=
  centeredTimeNumerator dt frequency - (dt * frequency) ^ 2

theorem centered_time_remainder_bound
    (dt frequency : ℝ) (hsmall : |dt * frequency| ≤ 1) :
    |centeredTimeRemainder dt frequency| ≤
      (5/48 : ℝ) * |dt * frequency| ^ 4 := by
  have h := cosine_phase_error_bound (dt * frequency)
    (|dt * frequency| / 2) (by positivity)
    (by nlinarith [abs_nonneg (dt * frequency)])
    (by nlinarith)
  unfold centeredTimeRemainder centeredTimeNumerator
  convert h using 1
  ring

/-! Residual of a continuum Dirac frequency when inserted into the actual
centered-time, exact-C19 scalar recurrence. -/
/-- The residual `centeredTimeNumerator dt frequency - dt ^ 2 * nativePsiTangentSymbol momentum`
of the centered-time scalar recurrence at the given frequency. -/
def nativeDiracModeResidual
    (dt frequency : ℝ) (momentum : LatticeMomentum) : ℝ :=
  centeredTimeNumerator dt frequency -
    dt ^ 2 * nativePsiTangentSymbol momentum

/-- The centered second-difference defect of the mode `amplitude * exp (-I * t * frequency)`
sampled at times `-dt, 0, dt`, plus `dt ^ 2 * nativePsiTangentSymbol momentum * amplitude`. -/
def nativeCenteredModeDefect
    (dt frequency : ℝ) (momentum : LatticeMomentum)
    (amplitude : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (dt * frequency : ℂ)) * amplitude -
    2 * amplitude +
    Complex.exp (Complex.I * (dt * frequency : ℂ)) * amplitude +
    (dt ^ 2 * nativePsiTangentSymbol momentum : ℝ) * amplitude

theorem complex_centered_phase_sum (angle : ℝ) :
    Complex.exp (-Complex.I * (angle : ℂ)) +
        Complex.exp (Complex.I * (angle : ℂ)) =
      2 * (Real.cos angle : ℂ) := by
  rw [show -Complex.I * (angle : ℂ) = ((-angle : ℝ) : ℂ) * Complex.I by
      push_cast
      ring,
    show Complex.I * (angle : ℂ) = (angle : ℂ) * Complex.I by ring,
    Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · simp [Real.cos_neg, Real.sin_neg]
    ring
  · simp [Real.cos_neg, Real.sin_neg]

theorem native_centered_mode_defect_is_residual
    (dt frequency : ℝ) (momentum : LatticeMomentum)
    (amplitude : ℂ) :
    nativeCenteredModeDefect dt frequency momentum amplitude =
      -(nativeDiracModeResidual dt frequency momentum : ℂ) * amplitude := by
  unfold nativeCenteredModeDefect nativeDiracModeResidual
    centeredTimeNumerator
  have hcast : ((dt * frequency : ℝ) : ℂ) =
      (dt : ℂ) * (frequency : ℂ) := by norm_num
  rw [← hcast]
  calc
    _ = (Complex.exp (-Complex.I * ((dt * frequency : ℝ) : ℂ)) +
          Complex.exp (Complex.I * ((dt * frequency : ℝ) : ℂ)) - 2 +
          ((dt ^ 2 * nativePsiTangentSymbol momentum : ℝ) : ℂ)) *
        amplitude := by ring
    _ = -(nativeDiracModeResidual dt frequency momentum : ℂ) *
        amplitude := by
      rw [complex_centered_phase_sum]
      unfold nativeDiracModeResidual centeredTimeNumerator
      push_cast
      ring

theorem native_dirac_mode_residual_splits
    (dt frequency : ℝ) (momentum : LatticeMomentum)
    (hdispersion : frequency ^ 2 =
      chi0 ^ 2 + c19QuadraticSymbol momentum) :
    nativeDiracModeResidual dt frequency momentum =
      centeredTimeRemainder dt frequency -
        dt ^ 2 * c19SpatialRemainder momentum := by
  unfold nativeDiracModeResidual centeredTimeRemainder
    nativePsiTangentSymbol
  rw [c19_symbol_exact_quadratic_plus_remainder]
  nlinarith

theorem native_dirac_mode_residual_bound
    (dt frequency radius : ℝ) (momentum : LatticeMomentum)
    (hradius : 0 ≤ radius)
    (hmomentum : ∀ axis, |momentum axis| ≤ radius)
    (hspace : 2 * radius ≤ 1)
    (htime : |dt * frequency| ≤ 1)
    (hdispersion : frequency ^ 2 =
      chi0 ^ 2 + c19QuadraticSymbol momentum) :
    |nativeDiracModeResidual dt frequency momentum| ≤
      (5/48 : ℝ) * |dt * frequency| ^ 4 +
        dt ^ 2 * (40 * radius ^ 4) := by
  rw [native_dirac_mode_residual_splits dt frequency momentum hdispersion]
  calc
    |centeredTimeRemainder dt frequency -
        dt ^ 2 * c19SpatialRemainder momentum| ≤
      |centeredTimeRemainder dt frequency| +
        |dt ^ 2 * c19SpatialRemainder momentum| := abs_sub _ _
    _ ≤ (5/48 : ℝ) * |dt * frequency| ^ 4 +
        dt ^ 2 * (40 * radius ^ 4) := by
      have ht := centered_time_remainder_bound dt frequency htime
      have hs := c19_spatial_remainder_bound momentum radius hradius
        hmomentum hspace
      rw [abs_mul, abs_of_nonneg (sq_nonneg dt)]
      exact add_le_add ht (mul_le_mul_of_nonneg_left hs (sq_nonneg dt))

/-- The residual `nativeDiracModeResidual dt frequency momentum` divided by `dt ^ 2`. -/
def normalizedNativeDiracModeResidual
    (dt frequency : ℝ) (momentum : LatticeMomentum) : ℝ :=
  nativeDiracModeResidual dt frequency momentum / dt ^ 2

theorem normalized_native_dirac_mode_residual_bound
    (dt frequency radius : ℝ) (momentum : LatticeMomentum)
    (hdt : dt ≠ 0)
    (hradius : 0 ≤ radius)
    (hmomentum : ∀ axis, |momentum axis| ≤ radius)
    (hspace : 2 * radius ≤ 1)
    (htime : |dt * frequency| ≤ 1)
    (hdispersion : frequency ^ 2 =
      chi0 ^ 2 + c19QuadraticSymbol momentum) :
    |normalizedNativeDiracModeResidual dt frequency momentum| ≤
      (5/48 : ℝ) * |dt * frequency| ^ 4 / dt ^ 2 + 40 * radius ^ 4 := by
  have hdt2 : 0 < dt ^ 2 := sq_pos_of_ne_zero hdt
  have hbound := native_dirac_mode_residual_bound dt frequency radius momentum
    hradius hmomentum hspace htime hdispersion
  unfold normalizedNativeDiracModeResidual
  rw [abs_div, abs_of_pos hdt2]
  apply (div_le_iff₀ hdt2).2
  calc
    |nativeDiracModeResidual dt frequency momentum| ≤
        (5/48 : ℝ) * |dt * frequency| ^ 4 +
          dt ^ 2 * (40 * radius ^ 4) := hbound
    _ = ((5/48 : ℝ) * |dt * frequency| ^ 4 / dt ^ 2 +
          40 * radius ^ 4) * dt ^ 2 := by field_simp

/-! The same four-component Hamiltonian used at DIRAC-010/011 squares to the
continuum part appearing in the bound. -/
theorem standard_c19_hamiltonian_square_is_continuum_dispersion
    (momentum : LatticeMomentum) (z : Cell4) :
    standardC19Hamiltonian (chi0 : ℂ) momentum
        (standardC19Hamiltonian (chi0 : ℂ) momentum z) =
      fun component =>
        ((chi0 ^ 2 + c19QuadraticSymbol momentum : ℝ) : ℂ) * z component := by
  unfold standardC19Hamiltonian
  rw [standard_dirac_hamiltonian_square]
  funext component
  apply congrArg (fun scalar : ℂ => scalar * z component)
  have hc : ((c19ContinuumSpeed : ℂ) ^ 2) = 12 := by
    exact_mod_cast c19_continuum_speed_square
  push_cast
  simp only [neg_sq, mul_pow]
  rw [hc]
  simp [c19QuadraticSymbol]
  ring

/-- The collected results on the prepared-vacuum potential expansion, the square of
`standardC19Hamiltonian`, and the explicit bounds `(5/48) |dt * frequency| ^ 4` (time) and
`40 * radius ^ 4` (space) on the centered-time mode residual. -/
structure Dirac012Certificate : Prop where
  previousGate : Dirac011Certificate
  localMassFromAction : ∀ psiAmplitude corner,
    sitePotential chi0
        (alignedEightSiteState psiAmplitude
          (fun _ => (chi0 : ℂ))) corner =
      chi0 ^ 2 * Complex.normSq (psiAmplitude corner) / 2 +
        Complex.normSq (psiAmplitude corner) ^ 2 / 4
  transportFromAction : ∀ psiAmplitude momentum site,
    nativeRepeatedCharacterTransportEnergy chi0 periodTwoCornerAt
        psiAmplitude (chi0 : ℂ) momentum site =
      Complex.normSq psiAmplitude / 2 * c19TransportSymbol momentum
  tangentPotentialFromAction : ∀ eps amplitude momentum site,
    nativePreparedModalPotential eps amplitude momentum site =
      eps ^ 2 * Complex.normSq amplitude / 2 *
          nativePsiTangentSymbol momentum +
        eps ^ 4 * Complex.normSq amplitude ^ 2 / 4
  continuumSquare : ∀ momentum z,
    standardC19Hamiltonian (chi0 : ℂ) momentum
        (standardC19Hamiltonian (chi0 : ℂ) momentum z) =
      fun component =>
        ((chi0 ^ 2 + c19QuadraticSymbol momentum : ℝ) : ℂ) * z component
  controlledNativeResidual : ∀ dt frequency radius momentum,
    0 ≤ radius →
    (∀ axis, |momentum axis| ≤ radius) →
    2 * radius ≤ 1 →
    |dt * frequency| ≤ 1 →
    frequency ^ 2 = chi0 ^ 2 + c19QuadraticSymbol momentum →
    |nativeDiracModeResidual dt frequency momentum| ≤
      (5/48 : ℝ) * |dt * frequency| ^ 4 + dt ^ 2 * (40 * radius ^ 4)
  normalizedEquationResidual : ∀ dt frequency radius momentum,
    dt ≠ 0 →
    0 ≤ radius →
    (∀ axis, |momentum axis| ≤ radius) →
    2 * radius ≤ 1 →
    |dt * frequency| ≤ 1 →
    frequency ^ 2 = chi0 ^ 2 + c19QuadraticSymbol momentum →
    |normalizedNativeDiracModeResidual dt frequency momentum| ≤
      (5/48 : ℝ) * |dt * frequency| ^ 4 / dt ^ 2 + 40 * radius ^ 4
  nativeCenteredRecurrence : ∀ dt frequency momentum amplitude,
    nativeCenteredModeDefect dt frequency momentum amplitude =
      -(nativeDiracModeResidual dt frequency momentum : ℂ) * amplitude

theorem dirac012_controlled_continuum_evolution : Dirac012Certificate where
  previousGate := dirac011_common_frequency_and_mass
  localMassFromAction := native_site_potential_on_prepared_vacuum
  transportFromAction := native_prepared_vacuum_transport_energy
  tangentPotentialFromAction := native_prepared_modal_potential_expansion
  continuumSquare := standard_c19_hamiltonian_square_is_continuum_dispersion
  controlledNativeResidual := native_dirac_mode_residual_bound
  normalizedEquationResidual := normalized_native_dirac_mode_residual_bound
  nativeCenteredRecurrence := native_centered_mode_defect_is_residual

end
end LeanDirac
