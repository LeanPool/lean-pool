/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.FinitePeriodicCharacters
public import LeanPool.LatticeDiracDerivation.V2.FinitePeriodicFourierBasis
public import LeanPool.LatticeDiracDerivation.V2.PositiveFrequencyCurrentBridge

/-!
# Integrated positive-frequency packet bridge

Pointwise native U(1) density is not the same as Dirac density for a
multi-momentum packet.  On a finite periodic torus, however, the integrated
cross terms vanish by character orthogonality.  This module proves that
global statement with the same native amplitudes and canonical spectral
readout used by the mode theorem.
-/

@[expose] public section

namespace LeanDirac.V2

variable {Site : Type} {Mode : Type*}

open Complex BigOperators
open scoped InnerProductSpace
noncomputable section

/-- The finite inverse Fourier sum taking scalar mode amplitudes to lattice values. -/
def periodicScalarSynthesis (L : ℕ) [NeZero L]
    (amplitude : PeriodicCubicMomentum L → ℂ) :
    PeriodicCubicSite L → ℂ :=
  fun site => ∑ mode,
    periodicQuantizedAddChar L mode site * amplitude mode

private theorem wInner_cWeight_fintype_sum_left
    [Fintype Mode] [Fintype Site]
    (field : Mode → Site → ℂ) (target : Site → ℂ) :
    ⟪(fun site => ∑ mode, field mode site), target⟫ₙ_[ℂ] =
      ∑ mode, ⟪field mode, target⟫ₙ_[ℂ] := by
  classical
  rw [show (fun site => ∑ mode, field mode site) =
      ∑ mode, field mode by
    funext site
    simp]
  induction (Finset.univ : Finset Mode) using Finset.induction_on with
  | empty => simp
  | @insert mode modes hmode ih =>
      rw [Finset.sum_insert hmode, RCLike.wInner_add_left,
        ih, Finset.sum_insert hmode]

private theorem wInner_cWeight_fintype_sum_right
    [Fintype Mode] [Fintype Site]
    (source : Site → ℂ) (field : Mode → Site → ℂ) :
    ⟪source, (fun site => ∑ mode, field mode site)⟫ₙ_[ℂ] =
      ∑ mode, ⟪source, field mode⟫ₙ_[ℂ] := by
  classical
  rw [show (fun site => ∑ mode, field mode site) =
      ∑ mode, field mode by
    funext site
    simp]
  induction (Finset.univ : Finset Mode) using Finset.induction_on with
  | empty => simp
  | @insert mode modes hmode ih =>
      rw [Finset.sum_insert hmode, RCLike.wInner_add_right,
        ih, Finset.sum_insert hmode]

theorem periodic_quantized_scaled_character_orthogonal
    (L : ℕ) [NeZero L]
    (first second : PeriodicCubicMomentum L) (a b : ℂ) :
    ⟪(fun site => periodicQuantizedAddChar L first site * a),
      (fun site => periodicQuantizedAddChar L second site * b)⟫ₙ_[ℂ] =
        if first = second then star a * b else 0 := by
  have hinj := periodic_quantized_add_char_injective L
  have hchar : periodicQuantizedAddChar L first =
      periodicQuantizedAddChar L second ↔ first = second := hinj.eq_iff
  rw [show (fun site => periodicQuantizedAddChar L first site * a) =
      a • (periodicQuantizedAddChar L first : PeriodicCubicSite L → ℂ) by
    funext site
    simp [mul_comm]]
  rw [show (fun site => periodicQuantizedAddChar L second site * b) =
      b • (periodicQuantizedAddChar L second : PeriodicCubicSite L → ℂ) by
    funext site
    simp [mul_comm]]
  rw [RCLike.wInner_smul_left, RCLike.wInner_smul_right,
    AddChar.wInner_cWeight_eq_boole]
  simp [hchar, smul_eq_mul]

theorem periodic_scalar_synthesis_parseval
    (L : ℕ) [NeZero L]
    (first second : PeriodicCubicMomentum L → ℂ) :
    ⟪periodicScalarSynthesis L first,
      periodicScalarSynthesis L second⟫ₙ_[ℂ] =
      ∑ mode, star (first mode) * second mode := by
  unfold periodicScalarSynthesis
  rw [wInner_cWeight_fintype_sum_left]
  apply Finset.sum_congr rfl
  intro firstMode _
  rw [wInner_cWeight_fintype_sum_right]
  simp [periodic_quantized_scaled_character_orthogonal]

/-- The native position obtained by synthesizing the positive-frequency amplitudes. -/
def periodicPositiveNativePosition (L : ℕ) [NeZero L]
    (amplitude : PeriodicCubicMomentum L → UniformCell2) :
    PeriodicCubicSite L → UniformCell2 :=
  fun site component => periodicScalarSynthesis L
    (fun mode => amplitude mode component) site

/-- The native velocity obtained by multiplying each positive mode by its time generator. -/
def periodicPositiveNativeVelocity (L : ℕ) [NeZero L]
    (energy : PeriodicCubicMomentum L → ℝ)
    (amplitude : PeriodicCubicMomentum L → UniformCell2) :
    PeriodicCubicSite L → UniformCell2 :=
  fun site component => periodicScalarSynthesis L
    (fun mode => -I * (energy mode : ℂ) * amplitude mode component) site

/-- The native phase charge averaged over the periodic lattice. -/
def periodicAveragedNativePositiveCharge (L : ℕ) [NeZero L]
    (energy : PeriodicCubicMomentum L → ℝ)
    (amplitude : PeriodicCubicMomentum L → UniformCell2) : ℝ :=
  -∑ component : Fin 2,
    (⟪(fun site => periodicPositiveNativePosition L amplitude site component),
      (fun site => periodicPositiveNativeVelocity L energy amplitude site component)
      ⟫ₙ_[ℂ]).im

theorem periodic_positive_native_packet_charge
    (L : ℕ) [NeZero L]
    (energy : PeriodicCubicMomentum L → ℝ)
    (amplitude : PeriodicCubicMomentum L → UniformCell2) :
    periodicAveragedNativePositiveCharge L energy amplitude =
      ∑ mode, energy mode * uniformCell2Density (amplitude mode) := by
  unfold periodicAveragedNativePositiveCharge
    periodicPositiveNativePosition periodicPositiveNativeVelocity
  simp_rw [periodic_scalar_synthesis_parseval]
  simp_rw [Complex.im_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Fintype.sum_congr
  intro mode
  simp [uniformCell2Density, Complex.normSq, Complex.mul_re,
    Complex.mul_im, Fin.sum_univ_succ]
  ring

/-- Synthesize a four-component lattice field by applying the scalar Fourier sum componentwise. -/
def periodicCell4Synthesis (L : ℕ) [NeZero L]
    (amplitude : PeriodicCubicMomentum L → CubicalCell4) :
    PeriodicCubicSite L → CubicalCell4 :=
  fun site component => periodicScalarSynthesis L
    (fun mode => amplitude mode component) site

theorem periodic_cell4_synthesis_real_pair
    (L : ℕ) [NeZero L]
    (first second : PeriodicCubicMomentum L → CubicalCell4) :
    (∑ component : Fin 4,
      ⟪(fun site => periodicCell4Synthesis L first site component),
        (fun site => periodicCell4Synthesis L second site component)
        ⟫ₙ_[ℂ]).re =
      ∑ mode, cubicalCell4RealPair (first mode) (second mode) := by
  unfold periodicCell4Synthesis cubicalCell4RealPair
  simp_rw [periodic_scalar_synthesis_parseval]
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum]
  rw [Finset.sum_comm]

/-- The canonical positive-frequency spinor at a single quantized momentum. -/
def periodicPositiveSpectralMode
    (L : ℕ) (mass : ℝ)
    (energy : PeriodicCubicMomentum L → ℝ)
    (amplitude : PeriodicCubicMomentum L → UniformCell2)
    (mode : PeriodicCubicMomentum L) : CubicalCell4 :=
  canonicalSpectralReadout mass (energy mode)
    (c19ScaledMomentum (periodicQuantizedMomentum L mode) 0)
    (c19ScaledMomentum (periodicQuantizedMomentum L mode) 1)
    (c19ScaledMomentum (periodicQuantizedMomentum L mode) 2)
    (nativePhaseOfFrequencyAmplitudes (energy mode) (amplitude mode) (fun _ => 0))

/-- The spinor Fourier packet obtained by applying canonical spectral coordinates to each mode. -/
def periodicPositiveSpectralPacket
    (L : ℕ) [NeZero L] (mass : ℝ)
    (energy : PeriodicCubicMomentum L → ℝ)
    (amplitude : PeriodicCubicMomentum L → UniformCell2) :
    PeriodicCubicSite L → CubicalCell4 :=
  periodicCell4Synthesis L (periodicPositiveSpectralMode L mass energy amplitude)

/-- The four-component density averaged over all sites of a periodic packet. -/
def periodicAveragedDiracDensity
    {L : ℕ} [NeZero L]
    (field : PeriodicCubicSite L → CubicalCell4) : ℝ :=
  (∑ component : Fin 4,
    ⟪(fun site => field site component),
      (fun site => field site component)⟫ₙ_[ℂ]).re

theorem periodic_positive_spectral_packet_density
    (L : ℕ) [NeZero L] (mass : ℝ)
    (energy : PeriodicCubicMomentum L → ℝ)
    (amplitude : PeriodicCubicMomentum L → UniformCell2)
    (henergy : ∀ mode, energy mode ≠ 0)
    (hpositive : ∀ mode, 0 < energy mode + mass)
    (hshell : ∀ mode,
      (energy mode) ^ 2 = mass ^ 2 +
        c19ScaledMomentum (periodicQuantizedMomentum L mode) 0 ^ 2 +
        c19ScaledMomentum (periodicQuantizedMomentum L mode) 1 ^ 2 +
        c19ScaledMomentum (periodicQuantizedMomentum L mode) 2 ^ 2) :
    periodicAveragedDiracDensity
        (periodicPositiveSpectralPacket L mass energy amplitude) =
      ∑ mode, energy mode * uniformCell2Density (amplitude mode) := by
  unfold periodicAveragedDiracDensity periodicPositiveSpectralPacket
  rw [periodic_cell4_synthesis_real_pair]
  refine Fintype.sum_congr _ _ fun mode => ?_
  unfold periodicPositiveSpectralMode
  rw [cubical_cell4_real_pair_self, canonical_spectral_readout_positive_phase _ _ _ _ _
    (henergy mode)]
  exact normalized_positive_frequency_density _ _ _ _ _ (hpositive mode) (hshell mode) _

theorem periodic_integrated_positive_packet_charge_bridge
    (L : ℕ) [NeZero L] (mass : ℝ)
    (energy : PeriodicCubicMomentum L → ℝ)
    (amplitude : PeriodicCubicMomentum L → UniformCell2)
    (henergy : ∀ mode, energy mode ≠ 0)
    (hpositive : ∀ mode, 0 < energy mode + mass)
    (hshell : ∀ mode,
      (energy mode) ^ 2 = mass ^ 2 +
        c19ScaledMomentum (periodicQuantizedMomentum L mode) 0 ^ 2 +
        c19ScaledMomentum (periodicQuantizedMomentum L mode) 1 ^ 2 +
        c19ScaledMomentum (periodicQuantizedMomentum L mode) 2 ^ 2) :
    periodicAveragedDiracDensity
        (periodicPositiveSpectralPacket L mass energy amplitude) =
      periodicAveragedNativePositiveCharge L energy amplitude := by
  rw [periodic_positive_spectral_packet_density
      L mass energy amplitude henergy hpositive hshell,
    periodic_positive_native_packet_charge]

/-! ## Integrated bond current -/

/-- Moving a periodic Fourier synthesis through one literal C19 bond is the
same as multiplying each mode amplitude by that bond's C19 character. -/
theorem periodic_scalar_synthesis_neighbor
    (L : ℕ) [NeZero L]
    (amplitude : PeriodicCubicMomentum L → ℂ)
    (site : PeriodicCubicSite L) (direction : C19Neighbor) :
    periodicScalarSynthesis L amplitude
        (periodicC19Neighbor L site direction) =
      periodicScalarSynthesis L
        (fun mode =>
          c19Character (periodicQuantizedMomentum L mode) direction *
            amplitude mode) site := by
  unfold periodicScalarSynthesis periodicQuantizedAddChar
  apply Finset.sum_congr rfl
  intro mode _
  change periodicQuantizedCharacter L mode
        (periodicC19Neighbor L site direction) * amplitude mode =
    periodicQuantizedCharacter L mode site *
      (c19Character (periodicQuantizedMomentum L mode) direction *
        amplitude mode)
  rw [periodic_quantized_character_neighbor]
  ring

/-- Bilinear periodic Parseval identity for a source field and its value at
the far endpoint of a directed C19 bond.  This is the precise identity that
removes packet cross terms only after the spatial average is taken. -/
theorem periodic_scalar_packet_bond_pair
    (L : ℕ) [NeZero L]
    (amplitude : PeriodicCubicMomentum L → ℂ)
    (direction : C19Neighbor) :
    (⟪periodicScalarSynthesis L amplitude,
      (fun site => periodicScalarSynthesis L amplitude
        (periodicC19Neighbor L site direction))⟫ₙ_[ℂ]).im =
      ∑ mode,
        (star (amplitude mode) *
          (c19Character (periodicQuantizedMomentum L mode) direction *
            amplitude mode)).im := by
  rw [show (fun site => periodicScalarSynthesis L amplitude
        (periodicC19Neighbor L site direction)) =
      periodicScalarSynthesis L
        (fun mode =>
          c19Character (periodicQuantizedMomentum L mode) direction *
            amplitude mode) by
    funext site
    exact periodic_scalar_synthesis_neighbor L amplitude site direction]
  rw [periodic_scalar_synthesis_parseval, Complex.im_sum]

/-- Spatially averaged positive native flux of a periodic packet.  The inner
product is the normalized finite-torus sum of the actual source-to-neighbor
bond pair, so this is not a separately supplied momentum-space current. -/
def periodicAveragedNativePositiveAxisFlux
    (L : ℕ) [NeZero L] (axis : Fin 3)
    (amplitude : PeriodicCubicMomentum L → UniformCell2) : ℝ :=
  -1 / 2 * ∑ direction : C19Neighbor,
    (c19Coord axis direction : ℝ) *
      (∑ component : Fin 2,
        -2 * c19Weight direction *
          (⟪periodicScalarSynthesis L
              (fun mode => amplitude mode component),
            (fun site => periodicScalarSynthesis L
              (fun mode => amplitude mode component)
              (periodicC19Neighbor L site direction))⟫ₙ_[ℂ]).im)

/-- Character orthogonality removes every mixed-momentum bond-current term
from the global finite-torus average. -/
theorem periodic_positive_native_packet_axis_flux
    (L : ℕ) [NeZero L] (axis : Fin 3)
    (amplitude : PeriodicCubicMomentum L → UniformCell2) :
    periodicAveragedNativePositiveAxisFlux L axis amplitude =
      ∑ mode, uniformNativePositiveAxisFlux
        (periodicQuantizedMomentum L mode) axis (amplitude mode) := by
  unfold periodicAveragedNativePositiveAxisFlux
    uniformNativePositiveAxisFlux uniformNativeOutwardBondCurrent
    uniformScalarPhasePair uniformCell2PlaneWaveNeighbor
  simp_rw [periodic_scalar_packet_bond_pair]
  let F : C19Neighbor → Fin 2 → PeriodicCubicMomentum L → ℝ :=
    fun direction component mode =>
      (-1 / 2) * (c19Coord axis direction : ℝ) *
        (-2 * c19Weight direction) *
          (star (amplitude mode component) *
            (c19Character (periodicQuantizedMomentum L mode) direction *
              amplitude mode component)).im
  calc
    -1 / 2 * ∑ direction : C19Neighbor,
        (c19Coord axis direction : ℝ) *
          (∑ component : Fin 2,
            -2 * c19Weight direction *
              ∑ mode,
                (star (amplitude mode component) *
                  (c19Character (periodicQuantizedMomentum L mode) direction *
                    amplitude mode component)).im) =
      ∑ direction : C19Neighbor, ∑ component : Fin 2, ∑ mode, F direction component mode := by
        simp only [F, Finset.mul_sum]
        ring_nf
    _ = ∑ direction : C19Neighbor, ∑ mode, ∑ component : Fin 2,
          F direction component mode := by
        apply Finset.sum_congr rfl
        intro direction _
        rw [Finset.sum_comm]
    _ = ∑ mode, ∑ direction : C19Neighbor, ∑ component : Fin 2,
          F direction component mode := by
        rw [Finset.sum_comm]
    _ = ∑ mode,
        -1 / 2 * ∑ direction : C19Neighbor,
          (c19Coord axis direction : ℝ) *
            ∑ component : Fin 2,
              -2 * c19Weight direction *
                (star (amplitude mode component) *
                  (c19Character (periodicQuantizedMomentum L mode) direction *
                    amplitude mode component)).im := by
        apply Finset.sum_congr rfl
        intro mode _
        simp only [F, Finset.mul_sum]
        ring_nf

/-! ## Integrated four-component current -/

/-- Normalized finite-torus integral of the four-component Dirac current. -/
def periodicAveragedDiracCurrent
    {L : ℕ} [NeZero L] (axis : Fin 3)
    (field : PeriodicCubicSite L → CubicalCell4) : ℝ :=
  (∑ component : Fin 4,
    ⟪(fun site => field site component),
      (fun site => cubicalVelocityOperator axis (field site) component)
      ⟫ₙ_[ℂ]).re

theorem periodic_cell4_synthesis_velocity
    (L : ℕ) [NeZero L] (axis : Fin 3)
    (amplitude : PeriodicCubicMomentum L → CubicalCell4) :
    (fun site => cubicalVelocityOperator axis
      (periodicCell4Synthesis L amplitude site)) =
      periodicCell4Synthesis L
        (fun mode => cubicalVelocityOperator axis (amplitude mode)) := by
  funext site
  change cubicalVelocityOperator axis (fun component => ∑ mode,
      periodicQuantizedAddChar L mode site * amplitude mode component) =
    fun component => ∑ mode, periodicQuantizedAddChar L mode site *
      cubicalVelocityOperator axis (amplitude mode) component
  rw [cubical_velocity_sum]
  simp_rw [cubical_velocity_mul]

theorem periodic_cell4_synthesis_velocity_component
    (L : ℕ) [NeZero L] (axis : Fin 3)
    (amplitude : PeriodicCubicMomentum L → CubicalCell4)
    (component : Fin 4) :
    (fun site => cubicalVelocityOperator axis
      (periodicCell4Synthesis L amplitude site) component) =
      fun site => periodicCell4Synthesis L
        (fun mode => cubicalVelocityOperator axis (amplitude mode))
        site component := by
  exact congrArg (fun field => fun site => field site component)
    (periodic_cell4_synthesis_velocity L axis amplitude)

/-- The spatially integrated Dirac packet current is diagonal in the same
periodic character basis. -/
theorem periodic_averaged_dirac_current_diagonalizes
    (L : ℕ) [NeZero L] (axis : Fin 3)
    (amplitude : PeriodicCubicMomentum L → CubicalCell4) :
    periodicAveragedDiracCurrent axis
        (periodicCell4Synthesis L amplitude) =
      ∑ mode, cubicalDiracCurrent axis (amplitude mode) := by
  unfold periodicAveragedDiracCurrent
  simp_rw [periodic_cell4_synthesis_velocity_component]
  simpa [cubicalDiracCurrent] using
    (periodic_cell4_synthesis_real_pair L amplitude
      (fun mode => cubicalVelocityOperator axis (amplitude mode)))

theorem periodic_positive_spectral_packet_current
    (L : ℕ) [NeZero L] (mass : ℝ)
    (energy : PeriodicCubicMomentum L → ℝ)
    (amplitude : PeriodicCubicMomentum L → UniformCell2)
    (axis : Fin 3) :
    periodicAveragedDiracCurrent axis
        (periodicPositiveSpectralPacket L mass energy amplitude) =
      ∑ mode, cubicalDiracCurrent axis
        (canonicalSpectralReadout mass (energy mode)
          (c19ScaledMomentum (periodicQuantizedMomentum L mode) 0)
          (c19ScaledMomentum (periodicQuantizedMomentum L mode) 1)
          (c19ScaledMomentum (periodicQuantizedMomentum L mode) 2)
          (nativePhaseOfFrequencyAmplitudes (energy mode)
            (amplitude mode) (fun _ => 0))) := by
  exact periodic_averaged_dirac_current_diagonalizes L axis
    (periodicPositiveSpectralMode L mass energy amplitude)

/-- Global finite-torus packet current bridge.  The exact native bond flux is
the integrated Dirac current of the same canonical positive-frequency packet
plus the sum of the explicit finite-C19 remainders. -/
theorem periodic_integrated_positive_packet_current_bridge
    (L : ℕ) [NeZero L] (mass : ℝ)
    (energy : PeriodicCubicMomentum L → ℝ)
    (amplitude : PeriodicCubicMomentum L → UniformCell2)
    (henergy : ∀ mode, energy mode ≠ 0)
    (hpositive : ∀ mode, 0 < energy mode + mass)
    (hshell : ∀ mode,
      (energy mode) ^ 2 = mass ^ 2 +
        c19ScaledMomentum (periodicQuantizedMomentum L mode) 0 ^ 2 +
        c19ScaledMomentum (periodicQuantizedMomentum L mode) 1 ^ 2 +
        c19ScaledMomentum (periodicQuantizedMomentum L mode) 2 ^ 2)
    (axis : Fin 3) :
    periodicAveragedNativePositiveAxisFlux L axis amplitude =
      periodicAveragedDiracCurrent axis
          (periodicPositiveSpectralPacket L mass energy amplitude) +
        ∑ mode, finiteC19CurrentRemainder
          (periodicQuantizedMomentum L mode) axis (amplitude mode) := by
  rw [periodic_positive_native_packet_axis_flux,
    periodic_positive_spectral_packet_current]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro mode _
  rw [canonical_spectral_readout_positive_phase mass (energy mode)
    (c19ScaledMomentum (periodicQuantizedMomentum L mode) 0)
    (c19ScaledMomentum (periodicQuantizedMomentum L mode) 1)
    (c19ScaledMomentum (periodicQuantizedMomentum L mode) 2)
    (henergy mode) (amplitude mode)]
  exact native_plane_wave_flux_is_dirac_current_plus_remainder
    mass (energy mode) (periodicQuantizedMomentum L mode)
    (hpositive mode) (hshell mode) axis (amplitude mode)

end
end LeanDirac.V2
