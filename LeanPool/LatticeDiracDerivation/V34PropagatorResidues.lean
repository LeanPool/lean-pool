/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation at commit 7b2a51cf933798eeb931731609fda0ffa81123fe.
Upstream source is dual-licensed under MIT or CC0 1.0; used here under MIT.
-/

module

public import LeanPool.LatticeDiracDerivation.V34CovariantSpinSums
public import LeanPool.LatticeDiracDerivation.V33FreePropagator

/-!
# V3.4 Stage 6: propagator poles, projectors, and spin sums

The V3.3 resolvent is decomposed into the positive- and negative-energy
projectors proved in V3.2.  Its pole numerators are therefore not new states:
they are exactly the same spectral sectors.  The positive covariant spin sum
is also tied to the positive projector after the standard beta conversion.
-/

@[expose] public section

namespace LeanDirac.V2

noncomputable section

/-- The free resolvent decomposed into its positive- and negative-energy poles. -/
def v34SpectralResolvent
    (spectralEnergy : ℂ) (mass px py pz energy : ℝ)
    (z : CubicalCell4) : CubicalCell4 :=
  fun component =>
    v32PositiveProjector mass px py pz energy z component /
        (spectralEnergy - (energy : ℂ)) +
      v32NegativeProjector mass px py pz energy z component /
        (spectralEnergy + (energy : ℂ))

theorem v34_resolvent_spectral_decomposition
    (spectralEnergy : ℂ) (mass px py pz energy : ℝ)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (henergy : energy ≠ 0)
    (hplus : spectralEnergy + (energy : ℂ) ≠ 0)
    (hminus : spectralEnergy - (energy : ℂ) ≠ 0)
    (z : CubicalCell4) :
    v33FreeResolvent spectralEnergy (mass : ℂ)
        (px : ℂ) (py : ℂ) (pz : ℂ) z =
      v34SpectralResolvent spectralEnergy mass px py pz energy z := by
  have hshellC : (energy : ℂ) ^ 2 =
      (mass : ℂ) ^ 2 + (px : ℂ) ^ 2 + (py : ℂ) ^ 2 + (pz : ℂ) ^ 2 := by
    exact_mod_cast hshell
  have hquad : spectralEnergy ^ 2 - (energy : ℂ) ^ 2 ≠ 0 := by
    intro hzero
    have hfactor :
        (spectralEnergy - (energy : ℂ)) *
          (spectralEnergy + (energy : ℂ)) = 0 := by
      linear_combination hzero
    exact (mul_ne_zero hminus hplus) hfactor
  funext component
  simp only [v33FreeResolvent, v34SpectralResolvent,
    v32PositiveProjector, v32SpectralProjector, one_div,
    Complex.ofReal_inv, v32ContinuumHamiltonian, v32NegativeProjector,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one]
  rw [← hshellC]
  field_simp [henergy, hplus, hminus, hquad]
  ring

/-- The positive-energy pole numerator, identified with its spectral projector. -/
abbrev v34PositivePoleNumerator
    (mass px py pz energy : ℝ) (z : CubicalCell4) : CubicalCell4 :=
  v32PositiveProjector mass px py pz energy z

/-- The negative-energy pole numerator, identified with its spectral projector. -/
abbrev v34NegativePoleNumerator
    (mass px py pz energy : ℝ) (z : CubicalCell4) : CubicalCell4 :=
  v32NegativeProjector mass px py pz energy z

theorem v34_positive_pole_is_projector
    (mass px py pz energy : ℝ) (z : CubicalCell4) :
    v34PositivePoleNumerator mass px py pz energy z =
      v32PositiveProjector mass px py pz energy z := rfl

theorem v34_negative_pole_is_projector
    (mass px py pz energy : ℝ) (z : CubicalCell4) :
    v34NegativePoleNumerator mass px py pz energy z =
      v32NegativeProjector mass px py pz energy z := rfl

theorem v34_positive_spin_sum_is_projector_beta
    (mass energy px py pz : ℝ) (henergy : energy ≠ 0) :
    v34PositiveCovariantNumerator mass energy px py pz =
      fun row column =>
        (energy : ℂ) * v34OperatorEntry
          (fun z => v32PositiveProjector mass px py pz energy
            (cubicalStandardBeta z)) row column := by
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [v34PositiveCovariantNumerator, v34OperatorEntry,
      v34MomentumSlash, v34CovariantMomentum, v34Gamma,
      cubicalGammaTime, cubicalGammaSpace, cubicalAlpha,
      v32PositiveProjector, v32SpectralProjector,
      v32ContinuumHamiltonian, cubicalStandardHamiltonian,
      cubicalStandardSpatial, cubicalStandardBeta,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ, standardCell4Basis,
      Fin.sum_univ_four] <;>
    field_simp [henergy]

/-- Certificate relating propagator residues, projectors, and covariant spin sums. -/
structure V34PropagatorResidueCertificate : Prop where
  decomposition : ∀ (spectralEnergy : ℂ) (mass px py pz energy : ℝ),
    energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 →
    energy ≠ 0 →
    spectralEnergy + (energy : ℂ) ≠ 0 →
    spectralEnergy - (energy : ℂ) ≠ 0 → ∀ z,
      v33FreeResolvent spectralEnergy (mass : ℂ)
          (px : ℂ) (py : ℂ) (pz : ℂ) z =
        v34SpectralResolvent spectralEnergy mass px py pz energy z
  positivePole : ∀ (mass px py pz energy : ℝ),
    ∀ z,
      v34PositivePoleNumerator mass px py pz energy z =
        v32PositiveProjector mass px py pz energy z
  negativePole : ∀ (mass px py pz energy : ℝ),
    ∀ z,
      v34NegativePoleNumerator mass px py pz energy z =
        v32NegativeProjector mass px py pz energy z
  spinSumProjector : ∀ (mass energy px py pz : ℝ),
    energy ≠ 0 →
      v34PositiveCovariantNumerator mass energy px py pz =
        fun row column =>
          (energy : ℂ) * v34OperatorEntry
            (fun z => v32PositiveProjector mass px py pz energy
              (cubicalStandardBeta z)) row column

theorem v34_propagator_residues : V34PropagatorResidueCertificate where
  decomposition := v34_resolvent_spectral_decomposition
  positivePole := v34_positive_pole_is_projector
  negativePole := v34_negative_pole_is_projector
  spinSumProjector := v34_positive_spin_sum_is_projector_beta

end
end LeanDirac.V2
