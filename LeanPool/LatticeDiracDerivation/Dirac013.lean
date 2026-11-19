/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac013.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac012Branch

/-!
# DIRAC-013: action-derived density, bond flow, and current limit

This gate derives the phase flow of the same prepared-vacuum tangent action
used in DIRAC-012.  It does not define a desired Dirac current and work
backwards.  First, the infinitesimal phase variation of one native C19 bond
is calculated.  Second, that bond flow is shown to satisfy the exact local
continuity identity of the spatially discrete, continuous-time tangent
equation.  Finally, the already-derived positive-frequency graph fixes the
normalization that converts the native phase density and C19 first-moment
flow into the standard four-component density and current in the continuum
limit.

The positive-frequency restriction is essential and explicit.  The native
second-order phase charge is indefinite when positive- and negative-frequency
branches are mixed; it is not silently identified with a positive Dirac
density for arbitrary second-order data.
-/

@[expose] public section

namespace LeanDirac

variable {Site : Type} {Edge : Type*}

noncomputable section
open BigOperators Complex

/-- The real part of `star source * target`, that is, the real inner product of two complex numbers
viewed as vectors in `ℝ²`. -/
def scalarRealPair (source target : ℂ) : ℝ :=
  (star source * target).re

/-- The imaginary part of `star source * target`. -/
def scalarPhasePair (source target : ℂ) : ℝ :=
  (star source * target).im

/-- The first-order phase rotation `value + eps * I * value` of the complex number `value` by the
real parameter `eps`. -/
def infinitesimalPhaseLine (eps : ℝ) (value : ℂ) : ℂ :=
  value + (eps : ℂ) * Complex.I * value

/-- The energy `weight / 2 * Complex.normSq (source - target)` of a weighted bond between two
complex amplitudes. -/
def preparedTangentBondEnergy (weight : ℝ) (source target : ℂ) : ℝ :=
  weight / 2 * Complex.normSq (source - target)

theorem prepared_tangent_bond_is_native_restricted_bond
    (weight : ℝ) (source target : ℂ) :
    restrictedBondEnergy chi0 weight
        ((chi0 : ℂ) * source) ((chi0 : ℂ) * target) =
      preparedTangentBondEnergy weight source target := by
  unfold restrictedBondEnergy preparedTangentBondEnergy
  rw [show (chi0 : ℂ) * source - (chi0 : ℂ) * target =
      (chi0 : ℂ) * (source - target) by ring,
    Complex.normSq_mul]
  have hchi : Complex.normSq (chi0 : ℂ) = chi0 ^ 2 := by
    norm_num [Complex.normSq, chi0]
  rw [hchi]
  norm_num [chi0]
  ring

theorem prepared_tangent_bond_symmetric
    (weight : ℝ) (source target : ℂ) :
    preparedTangentBondEnergy weight source target =
      preparedTangentBondEnergy weight target source := by
  have hnorm : Complex.normSq (source - target) =
      Complex.normSq (target - source) := by
    calc
      Complex.normSq (source - target) =
          Complex.normSq (-(source - target)) :=
        (Complex.normSq_neg (source - target)).symm
      _ = Complex.normSq (target - source) := by
        congr 1
        ring
  unfold preparedTangentBondEnergy
  exact congrArg (fun value : ℝ => weight / 2 * value) hnorm

/-! The coefficient linear in a local phase change is the action-derived
oriented flow.  The quadratic remainder is kept explicit. -/
theorem prepared_bond_local_phase_expansion
    (weight eps : ℝ) (source target : ℂ) :
    preparedTangentBondEnergy weight
        (infinitesimalPhaseLine eps source) target =
      preparedTangentBondEnergy weight source target -
        eps * weight * scalarPhasePair source target +
        eps ^ 2 * weight / 2 * Complex.normSq source := by
  simp [preparedTangentBondEnergy, infinitesimalPhaseLine,
    scalarPhasePair, Complex.normSq, Complex.mul_re, Complex.mul_im]
  ring

/-- The outward current `-2 * weight * scalarPhasePair source target` along a weighted bond from
`source` to `target`. -/
def nativeOutwardBondCurrent (weight : ℝ) (source target : ℂ) : ℝ :=
  -2 * weight * scalarPhasePair source target

theorem native_outward_current_reverses
    (weight : ℝ) (source target : ℂ) :
    nativeOutwardBondCurrent weight target source =
      -nativeOutwardBondCurrent weight source target := by
  simp [nativeOutwardBondCurrent, scalarPhasePair, Complex.mul_im]
  ring

/-- The phase density `scalarPhasePair position velocity` of a complex position and velocity. -/
def nativePhaseDensity (position velocity : ℂ) : ℝ :=
  scalarPhasePair position velocity

/-- The acceleration of the complex field `position` at `site` of a C19 lattice:
`-massSq * position site` minus twice the `c19Weight`-weighted sum of the differences between
`position site` and its neighbours. -/
def scalarTangentAcceleration
    (massSq : ℝ) (geometry : C19Lattice Site)
    (position : Site → ℂ) (site : Site) : ℂ :=
  -(massSq : ℂ) * position site -
    2 * ∑ direction : C19Neighbor,
      (c19Weight direction : ℂ) *
        (position site - position (geometry.neighbor site direction))

/-- The sum over the C19 neighbour directions of the outward bond currents, with weights
`c19Weight`, from `site` to its neighbours. -/
def nativeOutwardCurrentDivergence
    (geometry : C19Lattice Site) (position : Site → ℂ) (site : Site) : ℝ :=
  ∑ direction : C19Neighbor,
    nativeOutwardBondCurrent (c19Weight direction)
      (position site) (position (geometry.neighbor site direction))

/-! This is exactly the part of the full tangent potential that depends on
one site: the local quadratic term plus both appearances of every adjacent
directed bond.  It is not a new energy. -/
/-- The part of the scalar potential that depends on `site`:
`massSq / 2 * Complex.normSq (position site)` plus twice the `preparedTangentBondEnergy` of each C19
bond at `site`. -/
def scalarTangentLocalPotential
    (massSq : ℝ) (geometry : C19Lattice Site)
    (position : Site → ℂ) (site : Site) : ℝ :=
  massSq / 2 * Complex.normSq (position site) +
    ∑ direction : C19Neighbor,
      2 * preparedTangentBondEnergy (c19Weight direction)
        (position site) (position (geometry.neighbor site direction))

/-- The local potential `scalarTangentLocalPotential` with the value at `site` replaced by its
first-order phase rotation `infinitesimalPhaseLine eps (position site)`. -/
def scalarTangentLocalPhasePotential
    (massSq eps : ℝ) (geometry : C19Lattice Site)
    (position : Site → ℂ) (site : Site) : ℝ :=
  massSq / 2 * Complex.normSq
      (infinitesimalPhaseLine eps (position site)) +
    ∑ direction : C19Neighbor,
      2 * preparedTangentBondEnergy (c19Weight direction)
        (infinitesimalPhaseLine eps (position site))
        (position (geometry.neighbor site direction))

theorem infinitesimal_phase_line_normSq
    (eps : ℝ) (value : ℂ) :
    Complex.normSq (infinitesimalPhaseLine eps value) =
      (1 + eps ^ 2) * Complex.normSq value := by
  simp [infinitesimalPhaseLine, Complex.normSq,
    Complex.mul_re, Complex.mul_im]
  ring

/-! The coefficient linear in the site's phase change is exactly the outward
bond-current divergence. This is the explicit action-to-current bridge. -/
theorem scalar_tangent_local_phase_variation_from_action
    (massSq eps : ℝ) (geometry : C19Lattice Site)
    (position : Site → ℂ) (site : Site) :
    scalarTangentLocalPhasePotential massSq eps geometry position site =
      scalarTangentLocalPotential massSq geometry position site +
        eps * nativeOutwardCurrentDivergence geometry position site +
        eps ^ 2 * (massSq / 2 +
          ∑ direction : C19Neighbor, c19Weight direction) *
            Complex.normSq (position site) := by
  unfold scalarTangentLocalPhasePotential scalarTangentLocalPotential
  rw [infinitesimal_phase_line_normSq]
  simp_rw [prepared_bond_local_phase_expansion]
  unfold nativeOutwardCurrentDivergence nativeOutwardBondCurrent
  have hthird :
      (∑ direction : C19Neighbor,
        eps ^ 2 * c19Weight direction * Complex.normSq (position site)) =
      eps ^ 2 * Complex.normSq (position site) *
        (∑ direction : C19Neighbor, c19Weight direction) := by
    calc
      _ = eps ^ 2 * (∑ direction : C19Neighbor,
          c19Weight direction * Complex.normSq (position site)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro direction _
        ring
      _ = eps ^ 2 * ((∑ direction : C19Neighbor, c19Weight direction) *
          Complex.normSq (position site)) := by
        rw [Finset.sum_mul]
      _ = _ := by ring
  have hsecond :
      (∑ direction : C19Neighbor,
        -(eps * c19Weight direction * scalarPhasePair
          (position site) (position (geometry.neighbor site direction)) * 2)) =
      eps * (∑ direction : C19Neighbor,
        -(c19Weight direction * scalarPhasePair
          (position site) (position (geometry.neighbor site direction)) * 2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro direction _
    ring
  have hsum :
      (∑ direction : C19Neighbor,
        2 * (preparedTangentBondEnergy (c19Weight direction)
            (position site) (position (geometry.neighbor site direction)) -
          eps * c19Weight direction * scalarPhasePair
            (position site) (position (geometry.neighbor site direction)) +
          eps ^ 2 * c19Weight direction / 2 *
            Complex.normSq (position site))) =
        (∑ direction : C19Neighbor,
          2 * preparedTangentBondEnergy (c19Weight direction)
            (position site) (position (geometry.neighbor site direction))) +
        eps * (∑ direction : C19Neighbor,
          -2 * c19Weight direction * scalarPhasePair
            (position site) (position (geometry.neighbor site direction))) +
        eps ^ 2 * (∑ direction : C19Neighbor, c19Weight direction) *
          Complex.normSq (position site) := by
    calc
      _ = ∑ direction : C19Neighbor,
          (2 * preparedTangentBondEnergy (c19Weight direction)
              (position site) (position (geometry.neighbor site direction)) +
            eps * (-2 * c19Weight direction * scalarPhasePair
              (position site) (position (geometry.neighbor site direction))) +
            eps ^ 2 * c19Weight direction *
              Complex.normSq (position site)) := by
        apply Finset.sum_congr rfl
        intro direction _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        rw [hthird]
        ring_nf
        rw [hsecond]
        ring
  rw [hsum]
  ring

/-! This is the time derivative of the native phase density when position,
velocity, and acceleration are evaluated at one instant. -/
/-- The derivative `scalarPhasePair velocity velocity + scalarPhasePair position acceleration` of
the phase density, given position, velocity and acceleration at one instant. -/
def nativePhaseDensityDerivative
    (position velocity acceleration : ℂ) : ℝ :=
  scalarPhasePair velocity velocity + scalarPhasePair position acceleration

theorem scalar_phase_pair_self_zero (value : ℂ) :
    scalarPhasePair value value = 0 := by
  simp [scalarPhasePair, Complex.mul_im]
  ring

theorem native_tangent_local_continuity
    (massSq : ℝ) (geometry : C19Lattice Site)
    (position velocity : Site → ℂ) (site : Site) :
    nativePhaseDensityDerivative (position site) (velocity site)
        (scalarTangentAcceleration massSq geometry position site) +
      nativeOutwardCurrentDivergence geometry position site = 0 := by
  simp [nativePhaseDensityDerivative,
    scalarTangentAcceleration, nativeOutwardCurrentDivergence,
    nativeOutwardBondCurrent, scalarPhasePair,
    Complex.mul_im]
  ring_nf
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_mul, Finset.sum_mul]
  rw [← Finset.sum_neg_distrib]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro direction _
  ring

/-! Four-component density and current are introduced only after the native
continuity law.  They are explicit readouts of the standard basis already
intertwined with both cubical copies in DIRAC-010/011. -/
/-- The squared norm `∑ i, Complex.normSq (z i)` of a four-component vector. -/
def cell4Density (z : Cell4) : ℝ :=
  ∑ component, Complex.normSq (z component)

/-- The real inner product `∑ i, scalarRealPair (z i) (w i)` of two four-component vectors. -/
def cell4RealPair (z w : Cell4) : ℝ :=
  ∑ component, scalarRealPair (z component) (w component)

/-- The velocity operator along `axis` on four-component vectors: `c19ContinuumSpeed` times
`standardDiracAlphaZ`, `-standardDiracAlphaY` or `-standardDiracAlphaX` for the axes `0`, `1` and
`2` respectively. -/
def standardC19VelocityOperator
    (axis : Fin 3) (z : Cell4) : Cell4 :=
  match axis with
  | 0 => fun component =>
      (c19ContinuumSpeed : ℂ) * standardDiracAlphaZ z component
  | 1 => fun component =>
      -(c19ContinuumSpeed : ℂ) * standardDiracAlphaY z component
  | _ => fun component =>
      -(c19ContinuumSpeed : ℂ) * standardDiracAlphaX z component

/-- The current `cell4RealPair z (standardC19VelocityOperator axis z)` of the four-component vector
`z` along `axis`. -/
def standardC19DiracCurrent
    (axis : Fin 3) (z : Cell4) : ℝ :=
  cell4RealPair z (standardC19VelocityOperator axis z)

/-- The lattice momentum obtained from `momentum` by adding `delta` to its component along
`axis`. -/
def shiftLatticeMomentum
    (axis : Fin 3) (delta : ℝ) (momentum : LatticeMomentum) :
    LatticeMomentum :=
  fun component => if component = axis then momentum component + delta
    else momentum component

/-! The velocity operator is forced by the exact change of the already-derived
Hamiltonian under a momentum shift; it is not an independently supplied
current matrix. -/
theorem standard_c19_velocity_is_hamiltonian_momentum_response
    (mass : ℝ) (momentum : LatticeMomentum) (axis : Fin 3)
    (delta : ℝ) (z : Cell4) :
    standardC19Hamiltonian (mass : ℂ)
        (shiftLatticeMomentum axis delta momentum) z =
      fun component =>
        standardC19Hamiltonian (mass : ℂ) momentum z component +
          (delta : ℂ) * standardC19VelocityOperator axis z component := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [standardC19Hamiltonian, shiftLatticeMomentum,
      standardC19VelocityOperator, standardDiracHamiltonian,
      standardDiracSpatial, standardDiracBeta, standardDiracAlphaX,
      standardDiracAlphaY, standardDiracAlphaZ] <;>
    ring

theorem cell4_density_is_real_pair_self (z : Cell4) :
    cell4RealPair z z = cell4Density z := by
  simp [cell4RealPair, cell4Density, scalarRealPair,
    Complex.normSq, Complex.mul_re, Fin.sum_univ_succ]

theorem cell4_real_pair_add_right (z u v : Cell4) :
    cell4RealPair z (fun component => u component + v component) =
      cell4RealPair z u + cell4RealPair z v := by
  simp [cell4RealPair, scalarRealPair, Complex.mul_re,
    Fin.sum_univ_succ]
  ring

theorem cell4_real_pair_real_scale_right
    (scale : ℝ) (z w : Cell4) :
    cell4RealPair z (fun component => (scale : ℂ) * w component) =
      scale * cell4RealPair z w := by
  simp [cell4RealPair, scalarRealPair, Complex.mul_re,
    Fin.sum_univ_succ]
  ring

theorem standard_c19_velocity_real_linear
    (axis : Fin 3) (scale : ℝ) (z : Cell4) :
    standardC19VelocityOperator axis
        (fun component => (scale : ℂ) * z component) =
      fun component =>
        (scale : ℂ) * standardC19VelocityOperator axis z component := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [standardC19VelocityOperator, standardDiracAlphaX,
      standardDiracAlphaY, standardDiracAlphaZ] <;> ring

theorem standard_c19_hamiltonian_real_pair_symmetric
    (mass : ℝ) (momentum : LatticeMomentum) (z w : Cell4) :
    cell4RealPair (standardC19Hamiltonian (mass : ℂ) momentum z) w =
      cell4RealPair z (standardC19Hamiltonian (mass : ℂ) momentum w) := by
  simp [cell4RealPair, scalarRealPair, standardC19Hamiltonian,
    standardDiracHamiltonian, standardDiracSpatial,
    standardDiracBeta, standardDiracAlphaX, standardDiracAlphaY,
    standardDiracAlphaZ, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ]
  ring

theorem standard_c19_hamiltonian_velocity_anticommutator
    (mass : ℝ) (momentum : LatticeMomentum)
    (axis : Fin 3) (z : Cell4) :
    (fun component =>
      standardC19Hamiltonian (mass : ℂ) momentum
          (standardC19VelocityOperator axis z) component +
        standardC19VelocityOperator axis
          (standardC19Hamiltonian (mass : ℂ) momentum z) component) =
      fun component =>
        ((2 * c19ContinuumSpeed ^ 2 * momentum axis : ℝ) : ℂ) * z component := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [standardC19Hamiltonian, standardC19VelocityOperator,
      standardDiracHamiltonian, standardDiracSpatial,
      standardDiracBeta, standardDiracAlphaX, standardDiracAlphaY,
      standardDiracAlphaZ] <;>
    ring_nf <;>
    rw [Complex.I_sq] <;>
    ring

theorem positive_frequency_dirac_current_relation
    (mass energy : ℝ) (momentum : LatticeMomentum)
    (axis : Fin 3) (z : Cell4)
    (heigen : standardC19Hamiltonian (mass : ℂ) momentum z =
      fun component => (energy : ℂ) * z component) :
    energy * standardC19DiracCurrent axis z =
      c19ContinuumSpeed ^ 2 * momentum axis * cell4Density z := by
  have hanti := standard_c19_hamiltonian_velocity_anticommutator
    mass momentum axis z
  have hleft :
      cell4RealPair z
          (standardC19Hamiltonian (mass : ℂ) momentum
            (standardC19VelocityOperator axis z)) =
        energy * standardC19DiracCurrent axis z := by
    rw [← standard_c19_hamiltonian_real_pair_symmetric]
    rw [heigen]
    simp [standardC19DiracCurrent, cell4RealPair, scalarRealPair,
      Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]
    ring
  have hright :
      cell4RealPair z
          (standardC19VelocityOperator axis
            (standardC19Hamiltonian (mass : ℂ) momentum z)) =
        energy * standardC19DiracCurrent axis z := by
    rw [heigen, standard_c19_velocity_real_linear]
    simp [standardC19DiracCurrent, cell4_real_pair_real_scale_right]
  have hpair := congrArg (cell4RealPair z) hanti
  rw [cell4_real_pair_add_right, hleft, hright,
    cell4_real_pair_real_scale_right,
    cell4_density_is_real_pair_self] at hpair
  linarith

theorem positive_frequency_dirac_current_is_group_velocity
    (mass energy : ℝ) (momentum : LatticeMomentum)
    (axis : Fin 3) (z : Cell4) (henergy : energy ≠ 0)
    (heigen : standardC19Hamiltonian (mass : ℂ) momentum z =
      fun component => (energy : ℂ) * z component) :
    standardC19DiracCurrent axis z =
      (c19ContinuumSpeed ^ 2 * momentum axis / energy) * cell4Density z := by
  have h := positive_frequency_dirac_current_relation
    mass energy momentum axis z heigen
  field_simp
  nlinarith

/-! The vector first moment of the exact C19 bond flow.  The factor one half
relative to the directed-bond sum avoids counting both orientations of every
physical bond. -/
/-- The sum over the C19 directions of
`c19Weight direction * c19Coord axis direction * Real.sin (c19PhaseAngle momentum direction)`. -/
def c19FluxSymbol (axis : Fin 3) (momentum : LatticeMomentum) : ℝ :=
  ∑ direction : C19Neighbor,
    c19Weight direction * (c19Coord axis direction : ℝ) *
      Real.sin (c19PhaseAngle momentum direction)

theorem c19_phase_angle_scale
    (scale : ℝ) (momentum : LatticeMomentum)
    (direction : C19Neighbor) :
    c19PhaseAngle (fun axis => scale * momentum axis) direction =
      scale * c19PhaseAngle momentum direction := by
  unfold c19PhaseAngle
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]

theorem c19_flux_linear_coefficient
    (axis : Fin 3) (momentum : LatticeMomentum) :
    (∑ direction : C19Neighbor,
      c19Weight direction * (c19Coord axis direction : ℝ) *
        c19PhaseAngle momentum direction) =
      12 * momentum axis := by
  have hsplit : ∀ other : Fin 3,
      (∑ direction : C19Neighbor, c19Weight direction * (c19Coord axis direction : ℝ) *
        (momentum other * (c19Coord other direction : ℝ))) =
        momentum other * (c19SecondMoment axis other : ℝ) := by
    intro other
    unfold c19SecondMoment
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun direction _ => ?_
    rw [c19_weight_is_integer_weight]
    ring
  simp only [c19PhaseAngle, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [hsplit, c19_second_moment_isotropic, Fin.sum_univ_three]
  fin_cases axis <;> norm_num <;> ring

theorem c19_flux_has_continuum_derivative
    (axis : Fin 3) (momentum : LatticeMomentum) :
    HasDerivAt
      (fun scale => c19FluxSymbol axis
        (fun component => scale * momentum component))
      (12 * momentum axis) 0 := by
  unfold c19FluxSymbol
  have hsum : HasDerivAt
      (fun scale => ∑ direction : C19Neighbor,
        c19Weight direction * (c19Coord axis direction : ℝ) *
          Real.sin (scale * c19PhaseAngle momentum direction))
      (∑ direction : C19Neighbor,
        c19Weight direction * (c19Coord axis direction : ℝ) *
          c19PhaseAngle momentum direction) 0 := by
    apply HasDerivAt.fun_sum
    intro direction _
    have hlinear : HasDerivAt
        (fun scale : ℝ => scale * c19PhaseAngle momentum direction)
        (c19PhaseAngle momentum direction) 0 := by
      simpa using ((hasDerivAt_id 0).mul_const
        (c19PhaseAngle momentum direction))
    have hsine : HasDerivAt
        (Real.sin ∘ fun scale : ℝ =>
          scale * c19PhaseAngle momentum direction)
        (c19PhaseAngle momentum direction) 0 := by
      simpa only [zero_mul, Real.cos_zero, one_mul] using
        (Real.hasDerivAt_sin
          (0 * c19PhaseAngle momentum direction)).comp 0 hlinear
    simpa only [Function.comp_apply, mul_assoc, mul_comm, mul_left_comm] using
      hsine.const_mul
        (c19Weight direction * (c19Coord axis direction : ℝ))
  convert hsum using 1
  · funext scale
    apply Finset.sum_congr rfl
    intro direction _
    rw [c19_phase_angle_scale]
  · exact (c19_flux_linear_coefficient axis momentum).symm

theorem prepared_plane_wave_bond_current
    (weight : ℝ) (amplitude : ℂ) (momentum : LatticeMomentum)
    (direction : C19Neighbor) :
    nativeOutwardBondCurrent weight amplitude
        (c19Character momentum direction * amplitude) =
      -2 * weight * Complex.normSq amplitude *
        Real.sin (c19PhaseAngle momentum direction) := by
  unfold nativeOutwardBondCurrent scalarPhasePair c19Character
  rw [show Complex.I * (c19PhaseAngle momentum direction : ℂ) =
      (c19PhaseAngle momentum direction : ℂ) * Complex.I by ring,
    Complex.exp_ofReal_mul_I]
  simp [Complex.normSq, Complex.mul_re, Complex.mul_im,
    Complex.sin_ofReal_re]
  ring

/-- The phase density of `amplitude` with velocity `-I * energy * amplitude`, multiplied by `-2`; it
equals `2 * energy * Complex.normSq amplitude`. -/
def nativePositiveFrequencyDensity
    (energy : ℝ) (amplitude : ℂ) : ℝ :=
  -2 * nativePhaseDensity amplitude
    (-Complex.I * (energy : ℂ) * amplitude)

theorem native_positive_frequency_density
    (energy : ℝ) (amplitude : ℂ) :
    nativePositiveFrequencyDensity energy amplitude =
      2 * energy * Complex.normSq amplitude := by
  simp [nativePositiveFrequencyDensity, nativePhaseDensity,
    scalarPhasePair, Complex.normSq, Complex.mul_re, Complex.mul_im]
  ring

/-- The flux `2 * c19FluxSymbol axis momentum * Complex.normSq amplitude` along `axis`; it does not
depend on the energy argument. -/
def nativePositiveFrequencyFlux
    (_energy : ℝ) (axis : Fin 3) (momentum : LatticeMomentum)
    (amplitude : ℂ) : ℝ :=
  2 * c19FluxSymbol axis momentum * Complex.normSq amplitude

theorem native_positive_frequency_flux_over_density
    (energy : ℝ) (axis : Fin 3) (momentum : LatticeMomentum)
    (amplitude : ℂ) (henergy : energy ≠ 0) :
    nativePositiveFrequencyFlux energy axis momentum amplitude =
      (c19FluxSymbol axis momentum / energy) *
        nativePositiveFrequencyDensity energy amplitude := by
  rw [native_positive_frequency_density]
  unfold nativePositiveFrequencyFlux
  field_simp

/-- The four-component vector `z` divided componentwise by `Real.sqrt (2 * energy)`. -/
def normalizedPositiveFrequencyAmplitude
    (energy : ℝ) (z : Cell4) : Cell4 :=
  fun component => z component / (Real.sqrt (2 * energy) : ℂ)

/-- The sum over the four components of `nativePositiveFrequencyDensity energy` applied to the
normalized vector `normalizedPositiveFrequencyAmplitude energy z`. -/
def nativeCell4PositiveDensity (energy : ℝ) (z : Cell4) : ℝ :=
  ∑ component,
    nativePositiveFrequencyDensity energy
      (normalizedPositiveFrequencyAmplitude energy z component)

/-- The sum over the four components of `nativePositiveFrequencyFlux energy axis momentum` applied
to the normalized vector `normalizedPositiveFrequencyAmplitude energy z`. -/
def nativeCell4PositiveFlux
    (energy : ℝ) (axis : Fin 3) (momentum : LatticeMomentum)
    (z : Cell4) : ℝ :=
  ∑ component,
    nativePositiveFrequencyFlux energy axis momentum
      (normalizedPositiveFrequencyAmplitude energy z component)

theorem normalized_positive_frequency_normSq
    (energy : ℝ) (henergy : 0 < energy) (value : ℂ) :
    Complex.normSq (value / (Real.sqrt (2 * energy) : ℂ)) =
      Complex.normSq value / (2 * energy) := by
  rw [Complex.normSq_div]
  have hnonneg : 0 ≤ 2 * energy := by positivity
  have hsqrt : (Real.sqrt (2 * energy)) ^ 2 = 2 * energy := by
    exact Real.sq_sqrt hnonneg
  have hnorm : Complex.normSq (Real.sqrt (2 * energy) : ℂ) =
      2 * energy := by
    change Real.sqrt (2 * energy) * Real.sqrt (2 * energy) + 0 * 0 =
      2 * energy
    nlinarith [hsqrt]
  rw [hnorm]

theorem native_cell4_positive_density_is_dirac_density
    (energy : ℝ) (henergy : 0 < energy) (z : Cell4) :
    nativeCell4PositiveDensity energy z = cell4Density z := by
  unfold nativeCell4PositiveDensity normalizedPositiveFrequencyAmplitude
  simp_rw [native_positive_frequency_density,
    normalized_positive_frequency_normSq energy henergy]
  unfold cell4Density
  apply Finset.sum_congr rfl
  intro component _
  field_simp

theorem native_cell4_positive_flux_is_c19_group_flow
    (energy : ℝ) (henergy : 0 < energy)
    (axis : Fin 3) (momentum : LatticeMomentum) (z : Cell4) :
    nativeCell4PositiveFlux energy axis momentum z =
      (c19FluxSymbol axis momentum / energy) * cell4Density z := by
  unfold nativeCell4PositiveFlux
  simp_rw [native_positive_frequency_flux_over_density
    energy axis momentum _ (ne_of_gt henergy)]
  rw [← Finset.mul_sum]
  change (c19FluxSymbol axis momentum / energy) *
      nativeCell4PositiveDensity energy z =
    (c19FluxSymbol axis momentum / energy) * cell4Density z
  rw [native_cell4_positive_density_is_dirac_density energy henergy]

theorem native_cell4_flux_continuum_derivative
    (energy : ℝ) (henergy : 0 < energy)
    (axis : Fin 3) (momentum : LatticeMomentum) (z : Cell4) :
    HasDerivAt
      (fun scale => nativeCell4PositiveFlux energy axis
        (fun component => scale * momentum component) z)
      ((c19ContinuumSpeed ^ 2 * momentum axis / energy) * cell4Density z) 0 := by
  have hflux := c19_flux_has_continuum_derivative axis momentum
  have hscale := hflux.const_mul (cell4Density z / energy)
  have hfun :
      (fun scale => nativeCell4PositiveFlux energy axis
        (fun component => scale * momentum component) z) =
      (fun scale => cell4Density z / energy *
        c19FluxSymbol axis (fun component => scale * momentum component)) := by
    funext scale
    rw [native_cell4_positive_flux_is_c19_group_flow
      energy henergy axis]
    ring
  rw [hfun]
  have hcoefficient :
      (c19ContinuumSpeed ^ 2 * momentum axis / energy) * cell4Density z =
        cell4Density z / energy * (12 * momentum axis) := by
    rw [c19_continuum_speed_square]
    ring
  rw [hcoefficient]
  exact hscale

theorem native_cell4_flux_continuum_limit_is_dirac_current
    (mass energy : ℝ) (henergy : 0 < energy)
    (axis : Fin 3) (momentum : LatticeMomentum) (z : Cell4)
    (heigen : standardC19Hamiltonian (mass : ℂ) momentum z =
      fun component => (energy : ℂ) * z component) :
    HasDerivAt
      (fun scale => nativeCell4PositiveFlux energy axis
        (fun component => scale * momentum component) z)
      (standardC19DiracCurrent axis z) 0 := by
  have hnative := native_cell4_flux_continuum_derivative
    energy henergy axis momentum z
  have hdirac := positive_frequency_dirac_current_is_group_velocity
    mass energy momentum axis z (ne_of_gt henergy) heigen
  rw [hdirac]
  exact hnative

/-! The density/current bridge uses the same two cubical embeddings that
intertwine the native operator with the conventional four-component basis.
Each unnormalized embedding stores every four-component entry at two corners,
so its native eight-corner norm is exactly twice the Cell4 norm.  This factor
is exposed rather than hidden in a new state convention. -/
/-- The squared norm `∑ corner, Complex.normSq (z corner)` of an eight-corner amplitude. -/
def cell8Density (z : Cell8) : ℝ :=
  ∑ corner, Complex.normSq (z corner)

theorem minus_cube_basis_preserves_density (z : Cell4) :
    cell4Density (standardToMinusCubeSpinor z) = cell4Density z := by
  simp [cell4Density, standardToMinusCubeSpinor,
    Complex.normSq, Fin.sum_univ_succ]
  ring

theorem plus_cube_basis_preserves_density (z : Cell4) :
    cell4Density (standardToPlusCubeSpinor z) = cell4Density z := by
  simp [cell4Density, standardToPlusCubeSpinor,
    Complex.normSq, Fin.sum_univ_succ]
  ring

theorem cube_embed_minus_density (z : Cell4) :
    cell8Density (cubeEmbedMinus z) = 2 * cell4Density z := by
  simp [cell8Density, cell4Density, cubeEmbedMinus,
    Complex.normSq, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ]
  ring

theorem cube_embed_plus_density (z : Cell4) :
    cell8Density (cubeEmbedPlus z) = 2 * cell4Density z := by
  simp [cell8Density, cell4Density, cubeEmbedPlus,
    Complex.normSq, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ]
  ring

theorem cube_dirac_embed_minus_density (z : Cell4) :
    cell8Density (cubeDiracEmbedMinus z) = 2 * cell4Density z := by
  unfold cubeDiracEmbedMinus
  rw [cube_embed_minus_density, minus_cube_basis_preserves_density]

theorem cube_dirac_embed_plus_density (z : Cell4) :
    cell8Density (cubeDiracEmbedPlus z) = 2 * cell4Density z := by
  unfold cubeDiracEmbedPlus
  rw [cube_embed_plus_density, plus_cube_basis_preserves_density]

/-- The results of this file collected in one proposition, together with
`Dirac012CompleteCertificate`: the bond energy and bond current identities, the local phase
variation and continuity laws, the positive-frequency density and flux normalizations, the momentum
response of the Hamiltonian, the continuum current limit, and the factor `2` in the density of both
cubical embeddings. -/
structure Dirac013Certificate : Prop where
  previousGate : Dirac012CompleteCertificate
  restrictedBondFromAction : ∀ weight source target,
    restrictedBondEnergy chi0 weight
        ((chi0 : ℂ) * source) ((chi0 : ℂ) * target) =
      preparedTangentBondEnergy weight source target
  directedBondSymmetry : ∀ weight source target,
    preparedTangentBondEnergy weight source target =
      preparedTangentBondEnergy weight target source
  bondPhaseVariation : ∀ weight eps source target,
    preparedTangentBondEnergy weight
        (infinitesimalPhaseLine eps source) target =
      preparedTangentBondEnergy weight source target -
        eps * weight * scalarPhasePair source target +
        eps ^ 2 * weight / 2 * Complex.normSq source
  reverseBondLaw : ∀ weight source target,
    nativeOutwardBondCurrent weight target source =
      -nativeOutwardBondCurrent weight source target
  localPhaseVariationFromAction : ∀ {Site : Type}
      (massSq eps : ℝ) (geometry : C19Lattice Site)
      (position : Site → ℂ) (site : Site),
    scalarTangentLocalPhasePotential massSq eps geometry position site =
      scalarTangentLocalPotential massSq geometry position site +
        eps * nativeOutwardCurrentDivergence geometry position site +
        eps ^ 2 * (massSq / 2 +
          ∑ direction : C19Neighbor, c19Weight direction) *
            Complex.normSq (position site)
  exactLocalContinuity : ∀ {Site : Type}
      (massSq : ℝ) (geometry : C19Lattice Site)
      (position velocity : Site → ℂ) (site : Site),
    nativePhaseDensityDerivative (position site) (velocity site)
        (scalarTangentAcceleration massSq geometry position site) +
      nativeOutwardCurrentDivergence geometry position site = 0
  positiveDensityNormalization : ∀ energy : ℝ,
    0 < energy → ∀ z,
      nativeCell4PositiveDensity energy z = cell4Density z
  finiteC19Flux : ∀ energy : ℝ,
    0 < energy → ∀ axis momentum z,
      nativeCell4PositiveFlux energy axis momentum z =
        (c19FluxSymbol axis momentum / energy) * cell4Density z
  velocityFromHamiltonian : ∀ (mass : ℝ) momentum axis delta z,
    standardC19Hamiltonian (mass : ℂ)
        (shiftLatticeMomentum axis delta momentum) z =
      fun component =>
        standardC19Hamiltonian (mass : ℂ) momentum z component +
          (delta : ℂ) * standardC19VelocityOperator axis z component
  continuumCurrent : ∀ mass energy : ℝ,
    0 < energy → ∀ axis momentum z,
      standardC19Hamiltonian (mass : ℂ) momentum z =
        (fun component => (energy : ℂ) * z component) →
      HasDerivAt
        (fun scale => nativeCell4PositiveFlux energy axis
          (fun component => scale * momentum component) z)
        (standardC19DiracCurrent axis z) 0
  minusEmbeddingDensity : ∀ z,
    cell8Density (cubeDiracEmbedMinus z) = 2 * cell4Density z
  plusEmbeddingDensity : ∀ z,
    cell8Density (cubeDiracEmbedPlus z) = 2 * cell4Density z

theorem dirac013_native_density_current_continuity :
    Dirac013Certificate where
  previousGate := dirac012_complete_centered_recurrence_evolution
  restrictedBondFromAction := prepared_tangent_bond_is_native_restricted_bond
  directedBondSymmetry := prepared_tangent_bond_symmetric
  bondPhaseVariation := prepared_bond_local_phase_expansion
  reverseBondLaw := native_outward_current_reverses
  localPhaseVariationFromAction :=
    scalar_tangent_local_phase_variation_from_action
  exactLocalContinuity := native_tangent_local_continuity
  positiveDensityNormalization :=
    native_cell4_positive_density_is_dirac_density
  finiteC19Flux := native_cell4_positive_flux_is_c19_group_flow
  velocityFromHamiltonian :=
    standard_c19_velocity_is_hamiltonian_momentum_response
  continuumCurrent := native_cell4_flux_continuum_limit_is_dirac_current
  minusEmbeddingDensity := cube_dirac_embed_minus_density
  plusEmbeddingDensity := cube_dirac_embed_plus_density

end
end LeanDirac
