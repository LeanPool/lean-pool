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

public import LeanPool.LatticeDiracDerivation.V33CompleteFreeSpinor
public import LeanPool.LatticeDiracDerivation.V2.CanonicalSpectralReadout
public import LeanPool.LatticeDiracDerivation.V2.CovariantFreeDirac

/-!
# V3.4 Stage 1: covariant operators and native-derived spinors

The gamma operators below are definitions in terms of the already-derived
cubical alpha/beta operators.  The branch spinors are the V2 normalized
frequency embeddings evaluated on the two native channels; no textbook
spinor or independent Dirac matrix is inserted.
-/

@[expose] public section

namespace LeanDirac.V2

noncomputable section
open Complex BigOperators

/-- A real four-momentum indexed by time and three spatial components. -/
abbrev V34FourMomentum := Fin 4 → ℝ

/-- The contravariant four-momentum with positive time component. -/
def v34ContravariantMomentum
    (energy px py pz : ℝ) : V34FourMomentum
  | 0 => energy
  | 1 => px
  | 2 => py
  | _ => pz

/-- The covariant four-momentum in the mostly-minus convention. -/
def v34CovariantMomentum
    (energy px py pz : ℝ) : V34FourMomentum
  | 0 => energy
  | 1 => -px
  | 2 => -py
  | _ => -pz

/-- The gamma-matrix action inherited from the cubical Dirac representation. -/
def v34Gamma (mu : Fin 4) (z : CubicalCell4) : CubicalCell4 :=
  match mu with
  | 0 => cubicalGammaTime z
  | 1 => cubicalGammaSpace 0 z
  | 2 => cubicalGammaSpace 1 z
  | _ => cubicalGammaSpace 2 z

/-- Contraction of covariant momentum with the cubical gamma action. -/
def v34MomentumSlash
    (energy px py pz : ℝ) (z : CubicalCell4) : CubicalCell4 :=
  fun component =>
    ∑ mu : Fin 4,
      (v34CovariantMomentum energy px py pz mu : ℂ) *
        v34Gamma mu z component

/-- The positive-energy covariant Dirac residual. -/
def v34DiracResidual
    (mass energy px py pz : ℝ) (z : CubicalCell4) : CubicalCell4 :=
  fun component =>
    v34MomentumSlash energy px py pz z component -
      (mass : ℂ) * z component

/-- The antiparticle covariant Dirac residual. -/
def v34AntiparticleResidual
    (mass energy px py pz : ℝ) (z : CubicalCell4) : CubicalCell4 :=
  fun component =>
    v34MomentumSlash energy px py pz z component +
      (mass : ℂ) * z component

/-- A component of the Dirac adjoint in the cubical representation. -/
def v34DiracAdjointComponent (z : CubicalCell4) (component : Fin 4) : ℂ :=
  star (cubicalStandardBeta z component)

/-- The bilinear formed from a Dirac adjoint and a four-component spinor. -/
def v34DiracBilinear
    (left : CubicalCell4)
    (operator : CubicalCell4 → CubicalCell4)
    (right : CubicalCell4) : ℂ :=
  ∑ component : Fin 4,
    v34DiracAdjointComponent left component * operator right component

/-- A standard basis state of the native two-channel amplitude. -/
def v34TwoChannelBasis (spin : Fin 2) : UniformCell2 :=
  fun component => if component = spin then 1 else 0

/-- The normalized positive-energy spinor for a chosen two-channel basis state. -/
def v34PositiveSpinor
    (mass energy px py pz : ℝ) (spin : Fin 2) : CubicalCell4 :=
  normalizedPositiveFrequencyEmbedding mass energy px py pz
    (v34TwoChannelBasis spin)

/-- Negative-energy branch at the same Hamiltonian momentum. -/
def v34NegativeBranchSpinor
    (mass energy px py pz : ℝ) (spin : Fin 2) : CubicalCell4 :=
  normalizedNegativeFrequencyEmbedding mass energy px py pz
    (v34TwoChannelBasis spin)

/-- Antiparticle momentum convention.  Reversing the spatial argument of the
negative-frequency embedding gives the conventional covariant `v(p)` sign. -/
def v34AntiparticleSpinor
    (mass energy px py pz : ℝ) (spin : Fin 2) : CubicalCell4 :=
  normalizedNegativeFrequencyEmbedding mass energy (-px) (-py) (-pz)
    (v34TwoChannelBasis spin)

theorem v34_dirac_residual_is_hamiltonian_residual
    (mass energy px py pz : ℝ) (z : CubicalCell4) :
    v34DiracResidual mass energy px py pz z =
      cubicalStandardBeta (fun component =>
        (energy : ℂ) * z component -
          cubicalStandardHamiltonian (mass : ℂ)
            (px : ℂ) (py : ℂ) (pz : ℂ) z component) := by
  funext component
  fin_cases component <;>
    simp [v34DiracResidual, v34MomentumSlash, v34CovariantMomentum,
      v34Gamma, cubicalGammaTime, cubicalGammaSpace, cubicalAlpha,
      cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      Fin.sum_univ_four] <;> ring

theorem v34_positive_spinor_covariant_equation
    (mass energy px py pz : ℝ)
    (hdenom : energy + mass ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (spin : Fin 2) :
    v34DiracResidual mass energy px py pz
        (v34PositiveSpinor mass energy px py pz spin) = 0 := by
  rw [v34_dirac_residual_is_hamiltonian_residual]
  unfold v34PositiveSpinor
  rw [normalized_positive_frequency_is_energy_eigenstate
    mass energy px py pz hdenom hshell (v34TwoChannelBasis spin)]
  funext component
  fin_cases component <;> simp [cubicalStandardBeta]

theorem v34_antiparticle_spinor_covariant_equation
    (mass energy px py pz : ℝ)
    (hdenom : energy + mass ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (spin : Fin 2) :
    v34AntiparticleResidual mass energy px py pz
        (v34AntiparticleSpinor mass energy px py pz spin) = 0 := by
  let z := v34AntiparticleSpinor mass energy px py pz spin
  have hnegative := normalized_negative_frequency_is_energy_eigenstate
    mass energy (-px) (-py) (-pz) hdenom (by nlinarith [hshell])
      (v34TwoChannelBasis spin)
  have hnegative' :
      cubicalStandardHamiltonian (mass : ℂ)
          ((-px : ℝ) : ℂ) ((-py : ℝ) : ℂ) ((-pz : ℝ) : ℂ) z =
        fun component => -(energy : ℂ) * z component := by
    simpa [z, v34AntiparticleSpinor] using hnegative
  have hbeta :
      cubicalStandardBeta
          (v34AntiparticleResidual mass energy px py pz z) = 0 := by
    funext component
    have hcomponent := congrFun hnegative' component
    fin_cases component <;>
      simp [v34AntiparticleResidual, v34MomentumSlash,
        v34CovariantMomentum, v34Gamma, cubicalGammaTime,
        cubicalGammaSpace, cubicalAlpha,
        cubicalStandardHamiltonian, cubicalStandardSpatial,
        cubicalStandardBeta, cubicalStandardAlphaX,
        cubicalStandardAlphaY, cubicalStandardAlphaZ,
        Fin.sum_univ_four] at hcomponent ⊢ <;>
      linear_combination hcomponent
  funext component
  have hcomponent := congrFun hbeta component
  fin_cases component <;>
    simpa [cubicalStandardBeta, z] using hcomponent

/-- Certificate for the covariant free-particle and antiparticle spinors. -/
structure V34CovariantSpinorCertificate : Prop where
  positiveEquation : ∀ mass energy px py pz,
    energy + mass ≠ 0 →
    energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 → ∀ spin,
      v34DiracResidual mass energy px py pz
          (v34PositiveSpinor mass energy px py pz spin) = 0
  negativeEquation : ∀ mass energy px py pz,
    energy + mass ≠ 0 →
    energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 → ∀ spin,
      v34AntiparticleResidual mass energy px py pz
          (v34AntiparticleSpinor mass energy px py pz spin) = 0

theorem v34_covariant_spinors : V34CovariantSpinorCertificate where
  positiveEquation := v34_positive_spinor_covariant_equation
  negativeEquation := v34_antiparticle_spinor_covariant_equation

end
end LeanDirac.V2
