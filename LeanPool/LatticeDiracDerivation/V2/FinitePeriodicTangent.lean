/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumEulerLagrange
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# The full finite periodic action and its Fourier tangent

This module removes the gap between the finite native `c19Lagrangian` and
the modal generator used by the free-Dirac factorization.  A
`PeriodicC19FourierMode` is an actual character on the finite periodic cubic
lattice whose translation eigenvalues are the already-defined C19 phases.
No spinor or Clifford object occurs here.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex BigOperators Filter Topology
noncomputable section

/-- A quantized Fourier character on the actual finite periodic C19 lattice.
The neighbor law is precisely the definition of compatibility between the
real momentum chart and the finite torus. -/
structure PeriodicC19FourierMode (L : ℕ) [NeZero L]
    (momentum : LatticeMomentum) where
  /-- The complex value of the mode at each site of the finite periodic lattice. -/
  character : PeriodicCubicSite L → ℂ
  normSq_one : ∀ site, Complex.normSq (character site) = 1
  neighbor_character : ∀ site direction,
    character (periodicC19Neighbor L site direction) =
      character site * c19Character momentum direction

/-- The constant character is the explicit zero-momentum member of the
finite periodic Fourier family. -/
def periodicC19ZeroMode (L : ℕ) [NeZero L] :
    PeriodicC19FourierMode L (fun _ => 0) where
  character := fun _ => 1
  normSq_one := by
    intro site
    simp [Complex.normSq]
  neighbor_character := by
    intro site direction
    simp [c19_character_zero]

/-! ## Every quantized finite-torus Fourier mode -/

/-- The native momentum labels of the finite cubic torus.  This has exactly
`L ^ 3` elements, the same number as `PeriodicCubicSite L`. -/
abbrev PeriodicCubicMomentum (L : ℕ) := Fin 3 → ZMod L

/-- Real momentum chart for a finite-torus label.  The use of `ZMod.val`
chooses the usual representatives `0,...,L-1`; different representatives
give the same character. -/
def periodicQuantizedMomentum (L : ℕ)
    (mode : PeriodicCubicMomentum L) : LatticeMomentum :=
  fun axis => 2 * Real.pi * (mode axis).val / L

/-- The product character of the three cyclic axes, written as one standard
additive character. -/
def periodicQuantizedCharacter (L : ℕ) [NeZero L]
    (mode : PeriodicCubicMomentum L) (site : PeriodicCubicSite L) : ℂ :=
  ZMod.stdAddChar (∑ axis : Fin 3, mode axis * site axis)

private theorem periodic_quantized_step_sum
    (L : ℕ) [NeZero L] (mode : PeriodicCubicMomentum L)
    (direction : C19Neighbor) :
    (∑ axis : Fin 3,
        mode axis * (c19Coord axis direction : ZMod L)) =
      ((∑ axis : Fin 3,
          ((mode axis).val : ℤ) * c19Coord axis direction : ℤ) : ZMod L) := by
  push_cast
  apply Finset.sum_congr rfl
  intro axis _
  simp only [ZMod.natCast_zmod_val]

private theorem periodic_quantized_phase
    (L : ℕ) [NeZero L] (mode : PeriodicCubicMomentum L)
    (direction : C19Neighbor) :
    ZMod.stdAddChar
        (∑ axis : Fin 3,
          mode axis * (c19Coord axis direction : ZMod L)) =
      c19Character (periodicQuantizedMomentum L mode) direction := by
  rw [periodic_quantized_step_sum]
  rw [ZMod.stdAddChar_coe]
  unfold c19Character c19PhaseAngle periodicQuantizedMomentum
  congr 1
  push_cast
  rw [Finset.mul_sum]
  rw [Finset.sum_div]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro axis _
  ring_nf

theorem periodic_quantized_character_normSq_one
    (L : ℕ) [NeZero L] (mode : PeriodicCubicMomentum L)
    (site : PeriodicCubicSite L) :
    Complex.normSq (periodicQuantizedCharacter L mode site) = 1 := by
  rw [periodicQuantizedCharacter, ZMod.stdAddChar_apply]
  exact Circle.normSq_coe _

theorem periodic_quantized_character_neighbor
    (L : ℕ) [NeZero L] (mode : PeriodicCubicMomentum L)
    (site : PeriodicCubicSite L) (direction : C19Neighbor) :
    periodicQuantizedCharacter L mode
        (periodicC19Neighbor L site direction) =
      periodicQuantizedCharacter L mode site *
        c19Character (periodicQuantizedMomentum L mode) direction := by
  unfold periodicQuantizedCharacter periodicC19Neighbor
  simp only [mul_add, Finset.sum_add_distrib, AddChar.map_add_eq_mul]
  rw [periodic_quantized_phase]

/-- Every momentum label of the finite torus produces a genuine compatible
C19 Fourier mode.  In particular this constructs all nonzero modes, not only
the constant character. -/
def periodicC19QuantizedMode (L : ℕ) [NeZero L]
    (mode : PeriodicCubicMomentum L) :
    PeriodicC19FourierMode L (periodicQuantizedMomentum L mode) where
  character := periodicQuantizedCharacter L mode
  normSq_one := periodic_quantized_character_normSq_one L mode
  neighbor_character := periodic_quantized_character_neighbor L mode

/-- Multiply a periodic Fourier character by its scalar amplitude. -/
def periodicModeField {L : ℕ} [NeZero L]
    {momentum : LatticeMomentum}
    (mode : PeriodicC19FourierMode L momentum) (amplitude : ℂ) :
    PeriodicCubicSite L → ℂ :=
  fun site => mode.character site * amplitude

/-- The native state with two transverse Fourier amplitudes about the axial vacuum. -/
def periodicModeState {L : ℕ} [NeZero L]
    {momentum : LatticeMomentum}
    (r eps : ℝ) (mode : PeriodicC19FourierMode L momentum)
    (position : UniformCell2) : State (PeriodicCubicSite L) :=
  uniformTransverseState r eps
    (periodicModeField mode (position 0))
    (periodicModeField mode (position 1))

/-- The native velocity with two transverse Fourier amplitudes and a stationary second field. -/
def periodicModeVelocity {L : ℕ} [NeZero L]
    {momentum : LatticeMomentum}
    (eps : ℝ) (mode : PeriodicC19FourierMode L momentum)
    (velocity : UniformCell2) : Velocity (PeriodicCubicSite L) :=
  uniformTransverseVelocity eps
    (periodicModeField mode (velocity 0))
    (periodicModeField mode (velocity 1))

/-- The number of lattice sites used to normalize periodic averages. -/
def periodicSiteCount (L : ℕ) [NeZero L] : ℝ :=
  Fintype.card (PeriodicCubicSite L)

theorem c19_phase_angle_reverse
    (momentum : LatticeMomentum) (direction : C19Neighbor) :
    c19PhaseAngle momentum (c19Reverse direction) =
      -c19PhaseAngle momentum direction := by
  unfold c19PhaseAngle
  simp_rw [c19_reverse_coord]
  push_cast
  simp_rw [mul_neg]
  exact Finset.sum_neg_distrib
    (s := (Finset.univ : Finset (Fin 3)))
    (f := fun axis => momentum axis * (c19Coord axis direction : ℝ))

theorem c19_character_reverse_conj
    (momentum : LatticeMomentum) (direction : C19Neighbor) :
    c19Character momentum (c19Reverse direction) =
      star (c19Character momentum direction) := by
  unfold c19Character
  rw [c19_phase_angle_reverse]
  rw [show I * ((-c19PhaseAngle momentum direction : ℝ) : ℂ) =
      star (I * (c19PhaseAngle momentum direction : ℂ)) by simp]
  exact Complex.exp_conj _

theorem c19_character_normSq_one
    (momentum : LatticeMomentum) (direction : C19Neighbor) :
    Complex.normSq (c19Character momentum direction) = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  unfold c19Character
  rw [Complex.norm_exp]
  simp

theorem normSq_one_sub_unit
    (z : ℂ) (hz : Complex.normSq z = 1) :
    ((Complex.normSq (1 - z) : ℝ) : ℂ) =
      (1 - z) + (1 - star z) := by
  have hz' : z.re * z.re + z.im * z.im = 1 := by
    simpa [Complex.normSq] using hz
  apply Complex.ext
  · simp [Complex.normSq, Complex.mul_re]
    nlinarith
  · simp [Complex.normSq, Complex.mul_im]

/-- The involutive permutation that reverses the eighteen C19 offsets. -/
def c19ReverseEquiv : C19Neighbor ≃ C19Neighbor where
  toFun := c19Reverse
  invFun := c19Reverse
  left_inv := c19_reverse_involutive
  right_inv := c19_reverse_involutive

theorem c19_conjugate_difference_sum
    (momentum : LatticeMomentum) :
    ∑ direction : C19Neighbor, (c19Weight direction : ℂ) *
        (1 - star (c19Character momentum direction)) =
      ∑ direction : C19Neighbor, (c19Weight direction : ℂ) *
        (1 - c19Character momentum direction) := by
  apply Fintype.sum_equiv c19ReverseEquiv
  intro direction
  change (c19Weight direction : ℂ) *
      (1 - star (c19Character momentum direction)) =
    (c19Weight (c19Reverse direction) : ℂ) *
      (1 - c19Character momentum (c19Reverse direction))
  rw [c19_reverse_weight, c19_character_reverse_conj]

/-- The local C19 difference operator and the bond-energy symbol have the
same eigenvalue.  This is the force-side identity needed below. -/
theorem c19_complex_difference_is_transport_symbol
    (momentum : LatticeMomentum) :
    2 * ∑ direction : C19Neighbor,
        (c19Weight direction : ℂ) *
          (1 - c19Character momentum direction) =
      (c19TransportSymbol momentum : ℂ) := by
  rw [show (c19TransportSymbol momentum : ℂ) =
      ∑ direction : C19Neighbor, (c19Weight direction : ℂ) *
        ((1 - c19Character momentum direction) +
          (1 - star (c19Character momentum direction))) by
    unfold c19TransportSymbol
    push_cast
    apply Finset.sum_congr rfl
    intro direction _
    rw [normSq_one_sub_unit _
      (c19_character_normSq_one momentum direction)]]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, c19_conjugate_difference_sum]
  ring

theorem periodic_mode_field_density
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (mode : PeriodicC19FourierMode L momentum)
    (amplitude : ℂ) (site : PeriodicCubicSite L) :
    Complex.normSq (periodicModeField mode amplitude site) =
      Complex.normSq amplitude := by
  simp [periodicModeField, Complex.normSq_mul, mode.normSq_one]

theorem periodic_mode_field_neighbor
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (mode : PeriodicC19FourierMode L momentum)
    (amplitude : ℂ) (site : PeriodicCubicSite L)
    (direction : C19Neighbor) :
    periodicModeField mode amplitude
        (periodicC19Neighbor L site direction) =
      mode.character site * c19Character momentum direction * amplitude := by
  simp [periodicModeField, mode.neighbor_character]

theorem periodic_mode_density_sum
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (mode : PeriodicC19FourierMode L momentum)
    (position : UniformCell2) :
    ∑ site : PeriodicCubicSite L,
        (Complex.normSq (periodicModeField mode (position 0) site) +
          Complex.normSq (periodicModeField mode (position 1) site)) =
      periodicSiteCount L * uniformCell2Density position := by
  simp_rw [periodic_mode_field_density]
  simp [periodicSiteCount, uniformCell2Density, Fin.sum_univ_succ]
  ring

theorem periodic_mode_quartic_sum
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (mode : PeriodicC19FourierMode L momentum)
    (position : UniformCell2) :
    ∑ site : PeriodicCubicSite L,
        (Complex.normSq (periodicModeField mode (position 0) site) +
          Complex.normSq (periodicModeField mode (position 1) site)) ^ 2 =
      periodicSiteCount L * uniformCell2Density position ^ 2 := by
  simp_rw [periodic_mode_field_density]
  simp [periodicSiteCount, uniformCell2Density, Fin.sum_univ_succ]

theorem periodic_mode_bond_difference
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (mode : PeriodicC19FourierMode L momentum)
    (amplitude : ℂ) (site : PeriodicCubicSite L)
    (direction : C19Neighbor) :
    Complex.normSq
        (periodicModeField mode amplitude
            (periodicC19Neighbor L site direction) -
          periodicModeField mode amplitude site) =
      Complex.normSq (1 - c19Character momentum direction) *
        Complex.normSq amplitude := by
  rw [periodic_mode_field_neighbor]
  unfold periodicModeField
  rw [show mode.character site * c19Character momentum direction * amplitude -
      mode.character site * amplitude =
        -(mode.character site *
          ((1 - c19Character momentum direction) * amplitude)) by ring]
  rw [Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_mul,
    mode.normSq_one]
  ring

theorem periodic_mode_quadratic_is_modal
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (r : ℝ) (mode : PeriodicC19FourierMode L momentum)
    (position : UniformCell2) :
    uniformTransverseQuadratic r
        (periodicModeField mode (position 0))
        (periodicModeField mode (position 1))
        (c19Bond (periodicC19Geometry L)) =
      periodicSiteCount L *
        uniformVacuumModalPotential r momentum position := by
  unfold uniformTransverseQuadratic uniformVacuumModalPotential
    uniformVacuumModalSquare
  simp_rw [periodic_mode_field_density]
  rw [show (∑ _site : PeriodicCubicSite L,
      (Complex.normSq (position 0) + Complex.normSq (position 1)) / 2) =
      periodicSiteCount L * uniformCell2Density position / 2 by
    simp [periodicSiteCount, uniformCell2Density, Fin.sum_univ_succ]
    ring]
  rw [Fintype.sum_prod_type]
  simp only [c19Bond, periodicC19Geometry]
  simp_rw [periodic_mode_bond_difference]
  rw [show (∑ site : PeriodicCubicSite L,
      ∑ direction : C19Neighbor,
        c19Weight direction / 2 *
          (Complex.normSq (1 - c19Character momentum direction) *
              Complex.normSq (position 0) +
            Complex.normSq (1 - c19Character momentum direction) *
              Complex.normSq (position 1))) =
      periodicSiteCount L *
        (c19TransportSymbol momentum / 2 *
          uniformCell2Density position) by
    simp [periodicSiteCount, c19TransportSymbol,
      uniformCell2Density, Fin.sum_univ_succ]
    ring]
  ring

/-- Exact expansion of the actual finite periodic `c19Lagrangian` on a
compatible Fourier character.  This is the missing finite-action link. -/
theorem periodic_c19_lagrangian_mode_expansion
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (r B eps : ℝ) (hr : r ≠ 0)
    (mode : PeriodicC19FourierMode L momentum)
    (position velocity : UniformCell2) :
    c19Lagrangian r B
        (periodicModeState r eps mode position)
        (periodicModeVelocity eps mode velocity)
        (periodicC19Geometry L) =
      eps ^ 2 * periodicSiteCount L *
          uniformVacuumModalLagrangian r momentum position velocity -
        eps ^ 4 / 4 * periodicSiteCount L *
          uniformCell2Density position ^ 2 := by
  unfold c19Lagrangian lagrangian
  rw [show periodicModeState r eps mode position =
      uniformTransverseState r eps
        (periodicModeField mode (position 0))
        (periodicModeField mode (position 1)) by rfl]
  rw [show periodicModeVelocity eps mode velocity =
      uniformTransverseVelocity eps
        (periodicModeField mode (velocity 0))
        (periodicModeField mode (velocity 1)) by rfl]
  rw [uniform_transverse_kinetic]
  rw [uniform_transverse_potential_expansion r eps hr]
  rw [periodic_mode_density_sum,
    periodic_mode_quadratic_is_modal r mode position,
    periodic_mode_quartic_sum]
  unfold uniformVacuumModalLagrangian uniformVacuumModalKinetic
  ring

/-- The exact finite Fourier tangent of the full action is the modal action,
up to the unavoidable volume factor. -/
def periodicC19LagrangianTangentQuotient
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (r B eps : ℝ) (mode : PeriodicC19FourierMode L momentum)
    (position velocity : UniformCell2) : ℝ :=
  if eps = 0 then
    2 * periodicSiteCount L *
      uniformVacuumModalLagrangian r momentum position velocity
  else
    (c19Lagrangian r B
        (periodicModeState r eps mode position)
        (periodicModeVelocity eps mode velocity)
        (periodicC19Geometry L) +
      c19Lagrangian r B
        (periodicModeState r (-eps) mode position)
        (periodicModeVelocity (-eps) mode velocity)
        (periodicC19Geometry L) -
      2 * c19Lagrangian r B
        (periodicModeState r 0 mode position)
        (periodicModeVelocity 0 mode velocity)
        (periodicC19Geometry L)) / eps ^ 2

theorem periodic_c19_lagrangian_tangent_exact
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (r B eps : ℝ) (hr : r ≠ 0)
    (mode : PeriodicC19FourierMode L momentum)
    (position velocity : UniformCell2) :
    periodicC19LagrangianTangentQuotient r B eps mode position velocity =
      2 * periodicSiteCount L *
          uniformVacuumModalLagrangian r momentum position velocity -
        eps ^ 2 / 2 * periodicSiteCount L *
          uniformCell2Density position ^ 2 := by
  by_cases heps : eps = 0
  · subst eps
    simp [periodicC19LagrangianTangentQuotient]
  · unfold periodicC19LagrangianTangentQuotient
    rw [ite_eq_right heps,
      periodic_c19_lagrangian_mode_expansion r B eps hr,
      periodic_c19_lagrangian_mode_expansion r B (-eps) hr,
      periodic_c19_lagrangian_mode_expansion r B 0 hr]
    field_simp [heps]
    ring

theorem periodic_c19_lagrangian_tangent_tends_to_modal
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (r B : ℝ) (hr : r ≠ 0)
    (mode : PeriodicC19FourierMode L momentum)
    (position velocity : UniformCell2) :
    Tendsto
      (fun eps : ℝ =>
        periodicC19LagrangianTangentQuotient
          r B eps mode position velocity)
      (nhds 0)
      (nhds (2 * periodicSiteCount L *
        uniformVacuumModalLagrangian r momentum position velocity)) := by
  have hfun :
      (fun eps : ℝ =>
        periodicC19LagrangianTangentQuotient
          r B eps mode position velocity) =
      (fun eps : ℝ =>
        2 * periodicSiteCount L *
            uniformVacuumModalLagrangian r momentum position velocity -
          eps ^ 2 / 2 * periodicSiteCount L *
            uniformCell2Density position ^ 2) := by
    funext eps
    exact periodic_c19_lagrangian_tangent_exact
      r B eps hr mode position velocity
  rw [hfun]
  have hcontinuous : ContinuousAt
      (fun eps : ℝ =>
        2 * periodicSiteCount L *
            uniformVacuumModalLagrangian r momentum position velocity -
          eps ^ 2 / 2 * periodicSiteCount L *
            uniformCell2Density position ^ 2) 0 := by
    fun_prop
  simpa [ContinuousAt] using hcontinuous

/-- The massive linearized force for a scalar profile on the periodic C19 lattice. -/
def periodicC19LinearizedAcceleration
    {L : ℕ}
    (r : ℝ) (field : PeriodicCubicSite L → ℂ)
    (site : PeriodicCubicSite L) : ℂ :=
  uniformScalarTangentAcceleration (r ^ 2) (periodicC19Geometry L) field site

theorem periodicC19LinearizedAcceleration_apply {L : ℕ}
    (r : ℝ) (field : PeriodicCubicSite L → ℂ) (site : PeriodicCubicSite L) :
    periodicC19LinearizedAcceleration r field site =
      -(r ^ 2 : ℂ) * field site -
        2 * ∑ direction : C19Neighbor,
          (c19Weight direction : ℂ) *
            (field site - field (periodicC19Neighbor L site direction)) := by
  simp only [periodicC19LinearizedAcceleration, uniformScalarTangentAcceleration,
    Complex.ofReal_pow, periodicC19Geometry]

/-- A variation of the first native transverse `Psi` component.  It is an
ordinary native-field direction, not a modal or Dirac coordinate. -/
def periodicFirstTransverseDirection
    {L : ℕ} (field : PeriodicCubicSite L → ℂ) :
    State (PeriodicCubicSite L) where
  psi := fun site component => if component = 0 then field site else 0
  chi := fun _ _ => 0

/-- Place a scalar test profile in the second transverse channel. -/
def periodicSecondTransverseDirection
    {L : ℕ} (field : PeriodicCubicSite L → ℂ) :
    State (PeriodicCubicSite L) where
  psi := fun site component => if component = 1 then field site else 0
  chi := fun _ _ => 0

/-- The two transverse axes available at the fixed axial vacuum. -/
abbrev PeriodicTransverseChannel := Fin 2

/-- Place a scalar perturbation in the selected transverse channel of the vacuum. -/
def periodicTransverseComponentState
    {L : ℕ} (r eps : ℝ) (component : PeriodicTransverseChannel)
    (field : PeriodicCubicSite L → ℂ) : State (PeriodicCubicSite L) :=
  if component = 0 then uniformTransverseState r eps field 0
  else uniformTransverseState r eps 0 field

/-- Place a scalar test direction in the selected transverse channel. -/
def periodicTransverseComponentDirection
    {L : ℕ} (component : PeriodicTransverseChannel)
    (field : PeriodicCubicSite L → ℂ) : State (PeriodicCubicSite L) :=
  if component = 0 then periodicFirstTransverseDirection field
  else periodicSecondTransverseDirection field

/-- The bilinear variation of the quadratic transverse C19 potential.  This
definition mentions only the mass scale, the periodic C19 bonds, and two
native scalar field profiles. -/
def periodicC19TransverseQuadraticVariation
    {L : ℕ} [NeZero L]
    (r : ℝ) (field direction : PeriodicCubicSite L → ℂ) : ℝ :=
  r ^ 2 * ∑ site, uniformScalarRealPair (field site) (direction site) +
    ∑ edge : C19Edge (PeriodicCubicSite L),
      (c19Bond (periodicC19Geometry L) edge).weight *
        uniformScalarRealPair
          (field (c19Bond (periodicC19Geometry L) edge).target -
            field (c19Bond (periodicC19Geometry L) edge).source)
          (direction (c19Bond (periodicC19Geometry L) edge).target -
            direction (c19Bond (periodicC19Geometry L) edge).source)

private theorem periodic_transverse_site_variation
    {L : ℕ} (r eps : ℝ)
    (channel : PeriodicTransverseChannel)
    (field direction : PeriodicCubicSite L → ℂ)
    (site : PeriodicCubicSite L) :
    sitePotentialFirstVariation r
        (periodicTransverseComponentState r eps channel field)
        (periodicTransverseComponentDirection channel direction) site =
      eps * r ^ 2 * uniformScalarRealPair (field site) (direction site) +
        eps ^ 3 * Complex.normSq (field site) *
          uniformScalarRealPair (field site) (direction site) := by
  fin_cases channel <;>
    simp only [periodicTransverseComponentState, periodicTransverseComponentDirection] <;>
    norm_num <;>
    unfold sitePotentialFirstVariation <;>
    rw [uniform_transverse_psi_density, uniform_transverse_chi_density] <;>
    simp [uniformTransverseState, periodicFirstTransverseDirection,
      periodicSecondTransverseDirection, c3RealPair, uniformScalarRealPair, Fin.sum_univ_succ] <;>
    ring

private theorem periodic_transverse_wedge_variation
    {L : ℕ} (r eps : ℝ)
    (channel : PeriodicTransverseChannel)
    (field direction : PeriodicCubicSite L → ℂ)
    (site : PeriodicCubicSite L) :
    wedgeFirstVariation
        (periodicTransverseComponentState r eps channel field)
        (periodicTransverseComponentDirection channel direction) site =
      fun component =>
        if component = channel.succ then -(r : ℂ) * direction site else 0 := by
  funext component
  fin_cases channel <;> fin_cases component <;>
    simp [wedgeFirstVariation, periodicTransverseComponentState,
      periodicTransverseComponentDirection, uniformTransverseState,
      periodicFirstTransverseDirection, periodicSecondTransverseDirection, c3Add, wedge,
      Fin.succ]

private theorem periodic_transverse_bond_variation
    {L : ℕ} (r eps : ℝ) (hr : r ≠ 0)
    (channel : PeriodicTransverseChannel)
    (field direction : PeriodicCubicSite L → ℂ)
    (edge : Bond (PeriodicCubicSite L)) :
    exteriorAreaBondFirstVariation r
        (periodicTransverseComponentState r eps channel field)
        (periodicTransverseComponentDirection channel direction) edge =
      eps * edge.weight *
        uniformScalarRealPair
          (field edge.target - field edge.source)
          (direction edge.target - direction edge.source) := by
  unfold exteriorAreaBondFirstVariation bondAreaDifference
    bondAreaFirstVariation
  rw [periodic_transverse_wedge_variation, periodic_transverse_wedge_variation]
  fin_cases channel <;>
    simp only [periodicTransverseComponentState] <;> norm_num <;>
    rw [uniform_transverse_wedge, uniform_transverse_wedge] <;>
    simp [difference, c3RealPair, uniformScalarRealPair, Fin.sum_univ_succ, Fin.succ] <;>
    field_simp [hr] <;> ring

/-- Exact first variation of the *full native potential* along an arbitrary
transverse field and arbitrary transverse test direction.  The coefficient
linear in `eps` is the Hessian of the full action at the axial vacuum; the
displayed cubic term is the complete finite-amplitude remainder. -/
theorem periodic_c19_transverse_component_potential_first_variation
    {L : ℕ} [NeZero L]
    (r eps : ℝ) (hr : r ≠ 0)
    (channel : PeriodicTransverseChannel)
    (field direction : PeriodicCubicSite L → ℂ) :
    potentialFirstVariation r
        (periodicTransverseComponentState r eps channel field)
        (periodicTransverseComponentDirection channel direction)
        (c19Bond (periodicC19Geometry L)) =
      eps * periodicC19TransverseQuadraticVariation r field direction +
        eps ^ 3 * ∑ site,
          Complex.normSq (field site) *
            uniformScalarRealPair (field site) (direction site) := by
  unfold potentialFirstVariation
    periodicC19TransverseQuadraticVariation
  simp_rw [periodic_transverse_site_variation,
    periodic_transverse_bond_variation r eps hr]
  rw [Finset.sum_add_distrib]
  simp only [Finset.mul_sum]
  rw [mul_add]
  rw [Finset.mul_sum, Finset.mul_sum]
  ring_nf

/-- Exact first variation of the *full native potential* along an arbitrary
transverse field and arbitrary transverse test direction.  The coefficient
linear in `eps` is the Hessian of the full action at the axial vacuum; the
displayed cubic term is the complete finite-amplitude remainder. -/
theorem periodic_c19_transverse_potential_first_variation
    {L : ℕ} [NeZero L]
    (r eps : ℝ) (hr : r ≠ 0)
    (field direction : PeriodicCubicSite L → ℂ) :
    potentialFirstVariation r
        (uniformTransverseState r eps field 0)
        (periodicFirstTransverseDirection direction)
        (c19Bond (periodicC19Geometry L)) =
      eps * periodicC19TransverseQuadraticVariation r field direction +
        eps ^ 3 * ∑ site,
          Complex.normSq (field site) *
            uniformScalarRealPair (field site) (direction site) :=
  periodic_c19_transverse_component_potential_first_variation
    r eps hr 0 field direction

theorem periodic_c19_second_transverse_potential_first_variation
    {L : ℕ} [NeZero L]
    (r eps : ℝ) (hr : r ≠ 0)
    (field direction : PeriodicCubicSite L → ℂ) :
    potentialFirstVariation r
        (uniformTransverseState r eps 0 field)
        (periodicSecondTransverseDirection direction)
        (c19Bond (periodicC19Geometry L)) =
      eps * periodicC19TransverseQuadraticVariation r field direction +
        eps ^ 3 * ∑ site,
          Complex.normSq (field site) *
            uniformScalarRealPair (field site) (direction site) :=
  periodic_c19_transverse_component_potential_first_variation
    r eps hr 1 field direction

/-- The scalar field increment along one oriented periodic lattice edge. -/
def periodicC19ScalarDifference
    {L : ℕ}
    (field : PeriodicCubicSite L → ℂ)
    (edge : C19Edge (PeriodicCubicSite L)) : ℂ :=
  field (periodicC19Neighbor L edge.1 edge.2) - field edge.1

/-- The weighted sum of forward differences from a periodic lattice site. -/
def periodicC19ScalarLaplacian
    {L : ℕ}
    (field : PeriodicCubicSite L → ℂ)
    (site : PeriodicCubicSite L) : ℂ :=
  ∑ direction : C19Neighbor,
    (c19Weight direction : ℂ) *
      (field site - field (periodicC19Neighbor L site direction))

/-- Reverse a periodic edge by exchanging its endpoints and reversing its offset. -/
def periodicReverseC19EdgeEquiv
    (L : ℕ) :
    C19Edge (PeriodicCubicSite L) ≃ C19Edge (PeriodicCubicSite L) where
  toFun := reverseC19Edge (periodicC19Geometry L)
  invFun := reverseC19Edge (periodicC19Geometry L)
  left_inv := by
    intro edge
    rcases edge with ⟨site, direction⟩
    apply Prod.ext
    · exact periodic_c19_neighbor_reverse L site direction
    · exact c19_reverse_involutive direction
  right_inv := by
    intro edge
    rcases edge with ⟨site, direction⟩
    apply Prod.ext
    · exact periodic_c19_neighbor_reverse L site direction
    · exact c19_reverse_involutive direction

private theorem periodic_c19_weighted_target_sum_eq_source_sum
    {L : ℕ} [NeZero L] (field : PeriodicCubicSite L → ℂ) :
    (∑ edge : C19Edge (PeriodicCubicSite L),
      (c19Weight edge.2 : ℂ) *
        field (periodicC19Neighbor L edge.1 edge.2)) =
      ∑ edge : C19Edge (PeriodicCubicSite L),
        (c19Weight edge.2 : ℂ) * field edge.1 := by
  refine Fintype.sum_equiv (periodicReverseC19EdgeEquiv L) _ _ ?_
  intro edge
  simp [periodicReverseC19EdgeEquiv, reverseC19Edge,
    c19_reverse_weight, periodicC19Geometry]

private theorem periodic_c19_weighted_cross_sum_reverse
    {L : ℕ} [NeZero L]
    (left right : PeriodicCubicSite L → ℂ) :
    (∑ edge : C19Edge (PeriodicCubicSite L),
      (c19Weight edge.2 : ℂ) *
        star (left (periodicC19Neighbor L edge.1 edge.2)) * right edge.1) =
      ∑ edge : C19Edge (PeriodicCubicSite L),
        (c19Weight edge.2 : ℂ) * star (left edge.1) *
          right (periodicC19Neighbor L edge.1 edge.2) := by
  refine Fintype.sum_equiv (periodicReverseC19EdgeEquiv L) _ _ ?_
  intro edge
  simp [periodicReverseC19EdgeEquiv, reverseC19Edge,
    c19_reverse_weight, periodicC19Geometry,
    periodic_c19_neighbor_reverse]

/-- Discrete integration by parts for the actual finite periodic C19
geometry.  This is the Riesz identity that turns the action Hessian into a
sitewise force; it is proved from reverse-bond geometry, not postulated as a
reduced generator. -/
theorem periodic_c19_scalar_green_real_identity
    {L : ℕ} [NeZero L]
    (left right : PeriodicCubicSite L → ℂ) :
    (∑ edge : C19Edge (PeriodicCubicSite L),
      c19Weight edge.2 *
        (star (periodicC19ScalarDifference left edge) *
          periodicC19ScalarDifference right edge).re) =
      2 * ∑ site : PeriodicCubicSite L,
        (star (periodicC19ScalarLaplacian left site) * right site).re := by
  let targetTarget : ℂ :=
    ∑ edge : C19Edge (PeriodicCubicSite L),
      (c19Weight edge.2 : ℂ) *
        star (left (periodicC19Neighbor L edge.1 edge.2)) *
          right (periodicC19Neighbor L edge.1 edge.2)
  let targetSource : ℂ :=
    ∑ edge : C19Edge (PeriodicCubicSite L),
      (c19Weight edge.2 : ℂ) *
        star (left (periodicC19Neighbor L edge.1 edge.2)) * right edge.1
  let sourceTarget : ℂ :=
    ∑ edge : C19Edge (PeriodicCubicSite L),
      (c19Weight edge.2 : ℂ) * star (left edge.1) *
        right (periodicC19Neighbor L edge.1 edge.2)
  let sourceSource : ℂ :=
    ∑ edge : C19Edge (PeriodicCubicSite L),
      (c19Weight edge.2 : ℂ) * star (left edge.1) * right edge.1
  have htt : targetTarget = sourceSource := by
    dsimp [targetTarget, sourceSource]
    simpa [mul_assoc] using
      periodic_c19_weighted_target_sum_eq_source_sum
        (L := L) (fun site => star (left site) * right site)
  have hts : targetSource = sourceTarget := by
    dsimp [targetSource, sourceTarget]
    exact periodic_c19_weighted_cross_sum_reverse (L := L) left right
  have hleft :
      (∑ edge : C19Edge (PeriodicCubicSite L),
        (c19Weight edge.2 : ℂ) *
          star (periodicC19ScalarDifference left edge) *
            periodicC19ScalarDifference right edge) =
        targetTarget - targetSource - sourceTarget + sourceSource := by
    dsimp [targetTarget, targetSource, sourceTarget, sourceSource]
    simp only [periodicC19ScalarDifference, map_sub]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro edge _
    ring
  have hright :
      (∑ site : PeriodicCubicSite L,
        star (periodicC19ScalarLaplacian left site) * right site) =
        sourceSource - targetSource := by
    dsimp [sourceSource, targetSource]
    rw [Fintype.sum_prod_type]
    simp only [periodicC19ScalarLaplacian, map_sum, map_mul, map_sub]
    rw [Fintype.sum_prod_type]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro site _
    rw [Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro direction _
    simp
    ring
  have hcomplex :
      (∑ edge : C19Edge (PeriodicCubicSite L),
        (c19Weight edge.2 : ℂ) *
          star (periodicC19ScalarDifference left edge) *
            periodicC19ScalarDifference right edge) =
        2 * ∑ site : PeriodicCubicSite L,
          star (periodicC19ScalarLaplacian left site) * right site := by
    rw [hleft, htt, ← hts, hright]
    ring
  have hre := congrArg Complex.re hcomplex
  simpa [Complex.mul_re, mul_add, add_mul, mul_assoc] using hre

/-- The quadratic coefficient extracted from the full native potential is
the real Riesz pairing with the negative of
`periodicC19LinearizedAcceleration`.  Thus that acceleration is the actual
Euler--Lagrange Hessian force, rather than a separately declared expected
Laplacian. -/
theorem periodic_c19_transverse_quadratic_variation_is_force_pair
    {L : ℕ} [NeZero L]
    (r : ℝ) (field direction : PeriodicCubicSite L → ℂ) :
    periodicC19TransverseQuadraticVariation r field direction =
      -∑ site,
        uniformScalarRealPair
          (periodicC19LinearizedAcceleration r field site)
          (direction site) := by
  have hgreen := periodic_c19_scalar_green_real_identity field direction
  unfold periodicC19TransverseQuadraticVariation
  have hbond :
      (∑ edge : C19Edge (PeriodicCubicSite L),
        (c19Bond (periodicC19Geometry L) edge).weight *
          uniformScalarRealPair
            (field (c19Bond (periodicC19Geometry L) edge).target -
              field (c19Bond (periodicC19Geometry L) edge).source)
            (direction (c19Bond (periodicC19Geometry L) edge).target -
              direction (c19Bond (periodicC19Geometry L) edge).source)) =
        2 * ∑ site : PeriodicCubicSite L,
          uniformScalarRealPair
            (periodicC19ScalarLaplacian field site) (direction site) := by
    simpa [c19Bond, periodicC19Geometry,
      periodicC19ScalarDifference, uniformScalarRealPair] using hgreen
  rw [hbond]
  simp only [periodicC19LinearizedAcceleration_apply, periodicC19ScalarLaplacian,
    uniformScalarRealPair]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro site _
  simp only [RCLike.star_def, mul_re, conj_re, conj_im, neg_mul, sub_neg_eq_add,
    star_sum, star_mul', conj_ofReal, star_sub, re_sum, ofReal_re, sub_re, ofReal_im,
    sub_im, zero_mul, sub_zero, im_sum, mul_im, add_zero, star_neg, star_pow, star_ofNat,
    neg_re, mul_neg, neg_add_rev, re_ofNat, im_ofNat, neg_im, neg_neg, neg_sub]
  rw [show ((r : ℂ) ^ 2).re = r ^ 2 by
      simp [pow_two, Complex.mul_re],
    show ((r : ℂ) ^ 2).im = 0 by
      simp [pow_two, Complex.mul_im]]
  ring

/-- The Hessian of the full native potential at the uniform axial vacuum,
evaluated on an arbitrary transverse profile and arbitrary transverse test
profile, is represented by the sitewise C19 acceleration. -/
theorem periodic_c19_transverse_component_potential_hessian_is_force
    {L : ℕ} [NeZero L]
    (r : ℝ) (hr : r ≠ 0)
    (channel : PeriodicTransverseChannel)
    (field direction : PeriodicCubicSite L → ℂ) :
    AnalyticHasDerivAt
      (fun eps : ℝ =>
        potentialFirstVariation r
          (periodicTransverseComponentState r eps channel field)
          (periodicTransverseComponentDirection channel direction)
          (c19Bond (periodicC19Geometry L)))
      (-∑ site,
        uniformScalarRealPair
          (periodicC19LinearizedAcceleration r field site)
          (direction site)) 0 := by
  let q := periodicC19TransverseQuadraticVariation r field direction
  let cubic := ∑ site,
    Complex.normSq (field site) *
      uniformScalarRealPair (field site) (direction site)
  have hlinear := (hasDerivAt_id (0 : ℝ)).mul_const q
  have hcubic := (hasDerivAt_pow 3 (0 : ℝ)).mul_const cubic
  have hsum := hlinear.add hcubic
  have hfun :
      (fun eps : ℝ =>
        potentialFirstVariation r
          (periodicTransverseComponentState r eps channel field)
          (periodicTransverseComponentDirection channel direction)
          (c19Bond (periodicC19Geometry L))) =
      (fun eps : ℝ => eps * q + eps ^ 3 * cubic) := by
    funext eps
    exact periodic_c19_transverse_component_potential_first_variation
      r eps hr channel field direction
  rw [hfun]
  convert hsum using 1
  · funext eps
    rfl
  · dsimp [q]
    norm_num
    exact (periodic_c19_transverse_quadratic_variation_is_force_pair
      r field direction).symm

/-- The Hessian of the full native potential at the uniform axial vacuum,
evaluated on an arbitrary transverse profile and arbitrary transverse test
profile, is represented by the sitewise C19 acceleration. -/
theorem periodic_c19_transverse_potential_hessian_is_force
    {L : ℕ} [NeZero L]
    (r : ℝ) (hr : r ≠ 0)
    (field direction : PeriodicCubicSite L → ℂ) :
    AnalyticHasDerivAt
      (fun eps : ℝ =>
        potentialFirstVariation r
          (uniformTransverseState r eps field 0)
          (periodicFirstTransverseDirection direction)
          (c19Bond (periodicC19Geometry L)))
      (-∑ site,
        uniformScalarRealPair
          (periodicC19LinearizedAcceleration r field site)
          (direction site)) 0 :=
  periodic_c19_transverse_component_potential_hessian_is_force
    r hr 0 field direction

theorem periodic_c19_second_transverse_potential_hessian_is_force
    {L : ℕ} [NeZero L]
    (r : ℝ) (hr : r ≠ 0)
    (field direction : PeriodicCubicSite L → ℂ) :
    AnalyticHasDerivAt
      (fun eps : ℝ =>
        potentialFirstVariation r
          (uniformTransverseState r eps 0 field)
          (periodicSecondTransverseDirection direction)
          (c19Bond (periodicC19Geometry L)))
      (-∑ site,
        uniformScalarRealPair
          (periodicC19LinearizedAcceleration r field site)
          (direction site)) 0 :=
  periodic_c19_transverse_component_potential_hessian_is_force
    r hr 1 field direction

/-- A scalar test profile supported at one periodic site. -/
def periodicSingleSiteScalarDirection
    {L : ℕ}
    (site : PeriodicCubicSite L) (amplitude : ℂ) :
    PeriodicCubicSite L → ℂ :=
  fun testSite => if testSite = site then amplitude else 0

/-- Both transverse native `Psi` components have the same localized Hessian
force, proved from the full potential. -/
theorem periodic_c19_transverse_component_hessian_localized
    {L : ℕ} [NeZero L]
    (r : ℝ) (hr : r ≠ 0)
    (component : PeriodicTransverseChannel)
    (field : PeriodicCubicSite L → ℂ)
    (site : PeriodicCubicSite L) (amplitude : ℂ) :
    AnalyticHasDerivAt
      (fun eps : ℝ =>
        potentialFirstVariation r
          (periodicTransverseComponentState r eps component field)
          (periodicTransverseComponentDirection component
            (periodicSingleSiteScalarDirection site amplitude))
          (c19Bond (periodicC19Geometry L)))
      (-uniformScalarRealPair
        (periodicC19LinearizedAcceleration r field site) amplitude) 0 := by
  have h := periodic_c19_transverse_component_potential_hessian_is_force
    r hr component field (periodicSingleSiteScalarDirection site amplitude)
  convert h using 1
  rw [Finset.sum_eq_single site]
  · simp [periodicSingleSiteScalarDirection]
  · intro testSite _ hne
    simp [periodicSingleSiteScalarDirection, hne, uniformScalarRealPair]
  · simp

theorem periodic_c19_transverse_potential_hessian_localized
    {L : ℕ} [NeZero L]
    (r : ℝ) (hr : r ≠ 0)
    (field : PeriodicCubicSite L → ℂ)
    (site : PeriodicCubicSite L) (amplitude : ℂ) :
    AnalyticHasDerivAt
      (fun eps : ℝ =>
        potentialFirstVariation r
          (uniformTransverseState r eps field 0)
          (periodicFirstTransverseDirection
            (periodicSingleSiteScalarDirection site amplitude))
          (c19Bond (periodicC19Geometry L)))
      (-uniformScalarRealPair
        (periodicC19LinearizedAcceleration r field site) amplitude) 0 :=
  periodic_c19_transverse_component_hessian_localized
    r hr 0 field site amplitude

theorem periodic_c19_second_transverse_potential_hessian_localized
    {L : ℕ} [NeZero L]
    (r : ℝ) (hr : r ≠ 0)
    (field : PeriodicCubicSite L → ℂ)
    (site : PeriodicCubicSite L) (amplitude : ℂ) :
    AnalyticHasDerivAt
      (fun eps : ℝ =>
        potentialFirstVariation r
          (uniformTransverseState r eps 0 field)
          (periodicSecondTransverseDirection
            (periodicSingleSiteScalarDirection site amplitude))
          (c19Bond (periodicC19Geometry L)))
      (-uniformScalarRealPair
        (periodicC19LinearizedAcceleration r field site) amplitude) 0 :=
  periodic_c19_transverse_component_hessian_localized
    r hr 1 field site amplitude

/-- The test direction parallel to the vacuum axis of the first field. -/
def periodicLongitudinalPsiDirection
    {L : ℕ} (field : PeriodicCubicSite L → ℂ) :
    State (PeriodicCubicSite L) where
  psi := fun site component => if component = 2 then field site else 0
  chi := fun _ _ => 0

/-- A longitudinal `Psi` test direction has no Hessian cross-block with the
two transverse fields at the axial vacuum. -/
theorem periodic_c19_transverse_longitudinal_cross_variation_zero
    {L : ℕ} [NeZero L]
    (r eps : ℝ) (field first second : PeriodicCubicSite L → ℂ) :
    potentialFirstVariation r
        (uniformTransverseState r eps first second)
        (periodicLongitudinalPsiDirection field)
        (c19Bond (periodicC19Geometry L)) = 0 := by
  unfold potentialFirstVariation
  have hsite :
      (∑ site,
        sitePotentialFirstVariation r
          (uniformTransverseState r eps first second)
          (periodicLongitudinalPsiDirection field) site) = 0 := by
    apply Finset.sum_eq_zero
    intro site _
    simp [sitePotentialFirstVariation, uniformTransverseState,
      periodicLongitudinalPsiDirection, c3RealPair,
      Fin.sum_univ_succ]
  have hbond :
      (∑ edge,
        exteriorAreaBondFirstVariation r
          (uniformTransverseState r eps first second)
          (periodicLongitudinalPsiDirection field)
          (c19Bond (periodicC19Geometry L) edge)) = 0 := by
    apply Finset.sum_eq_zero
    intro edge _
    simp [exteriorAreaBondFirstVariation, bondAreaDifference,
      bondAreaFirstVariation, wedgeFirstVariation,
      uniformTransverseState, periodicLongitudinalPsiDirection,
      difference, c3Add, wedge, c3RealPair]
  rw [hsite, hbond, zero_add]

/-- The reciprocal live-`chi` source begins at quadratic order in a
transverse `Psi` perturbation, so the `Psi`--`chi` Hessian cross-block at the
uniform vacuum vanishes for every native chi test field. -/
theorem periodic_c19_transverse_chi_cross_hessian_zero
    {L : ℕ} [NeZero L]
    (r : ℝ) (first second : PeriodicCubicSite L → ℂ)
    (chiDirection : PeriodicCubicSite L → C3) :
    AnalyticHasDerivAt
      (fun eps : ℝ =>
        potentialFirstVariation r
          (uniformTransverseState r eps first second)
          (pureChiDirection chiDirection)
          (c19Bond (periodicC19Geometry L))) 0 0 := by
  let coefficient :=
    potentialFirstVariation r
      (uniformTransverseState r 1 first second)
      (pureChiDirection chiDirection)
      (c19Bond (periodicC19Geometry L))
  have hquad := (hasDerivAt_pow 2 (0 : ℝ)).mul_const coefficient
  have hfun :
      (fun eps : ℝ =>
        potentialFirstVariation r
          (uniformTransverseState r eps first second)
          (pureChiDirection chiDirection)
          (c19Bond (periodicC19Geometry L))) =
      (fun eps : ℝ => eps ^ 2 * coefficient) := by
    funext eps
    exact uniform_transverse_chi_source_is_quadratic
      r eps first second chiDirection
        (c19Bond (periodicC19Geometry L))
  rw [hfun]
  convert hquad using 1
  norm_num

/-- The actual sitewise linearized C19 force diagonalizes on every finite
periodic Fourier character with eigenvalue `r ^ 2 + c19TransportSymbol`. -/
theorem periodic_c19_linearized_force_diagonalizes
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (r : ℝ) (mode : PeriodicC19FourierMode L momentum)
    (amplitude : ℂ) (site : PeriodicCubicSite L) :
    periodicC19LinearizedAcceleration r
        (periodicModeField mode amplitude) site =
      -((r ^ 2 + c19TransportSymbol momentum : ℝ) : ℂ) *
        periodicModeField mode amplitude site := by
  rw [periodicC19LinearizedAcceleration_apply]
  unfold periodicModeField
  simp_rw [mode.neighbor_character]
  rw [show (∑ direction : C19Neighbor,
      (c19Weight direction : ℂ) *
        (mode.character site * amplitude -
          mode.character site * c19Character momentum direction * amplitude)) =
      (∑ direction : C19Neighbor,
        (c19Weight direction : ℂ) *
          (1 - c19Character momentum direction)) *
        (mode.character site * amplitude) by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro direction _
    ring]
  rw [show 2 *
      ((∑ direction : C19Neighbor,
          (c19Weight direction : ℂ) *
            (1 - c19Character momentum direction)) *
        (mode.character site * amplitude)) =
      (2 * ∑ direction : C19Neighbor,
          (c19Weight direction : ℂ) *
            (1 - c19Character momentum direction)) *
        (mode.character site * amplitude) by ring]
  rw [c19_complex_difference_is_transport_symbol]
  push_cast
  ring

/-- On a genuine finite-torus Fourier character, the native C19 acceleration
is exactly the modal Euler--Lagrange acceleration. -/
theorem periodic_c19_linearized_force_is_modal_acceleration
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (r : ℝ)
    (mode : PeriodicC19FourierMode L momentum)
    (position : UniformCell2) (component : Fin 2)
    (site : PeriodicCubicSite L) :
    periodicC19LinearizedAcceleration r
        (periodicModeField mode (position component)) site =
      periodicModeField mode
        ((uniformVacuumModalAcceleration
          r momentum position) component) site := by
  rw [periodic_c19_linearized_force_diagonalizes]
  simp [uniformVacuumModalAcceleration, uniformVacuumModalSquare,
    periodicModeField]
  ring

/-- The Fourier-mode force is now obtained by differentiating the actual
native potential twice and then applying a localized Riesz probe.  The modal
acceleration on the right is therefore derived from the action rather than
introduced as an independent expected operator. -/
theorem periodic_c19_action_hessian_mode_force
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (r : ℝ) (hr : r ≠ 0)
    (mode : PeriodicC19FourierMode L momentum)
    (position : UniformCell2) (component : Fin 2)
    (site : PeriodicCubicSite L) (testAmplitude : ℂ) :
    AnalyticHasDerivAt
      (fun eps : ℝ =>
        potentialFirstVariation r
          (periodicTransverseComponentState r eps component
            (periodicModeField mode (position component)))
          (periodicTransverseComponentDirection component
            (periodicSingleSiteScalarDirection site testAmplitude))
          (c19Bond (periodicC19Geometry L)))
      (-uniformScalarRealPair
        (periodicModeField mode
          ((uniformVacuumModalAcceleration r momentum position) component)
          site) testAmplitude) 0 := by
  have h := periodic_c19_transverse_component_hessian_localized
    r hr component (periodicModeField mode (position component))
      site testAmplitude
  rw [periodic_c19_linearized_force_is_modal_acceleration] at h
  exact h

end
end LeanDirac.V2
