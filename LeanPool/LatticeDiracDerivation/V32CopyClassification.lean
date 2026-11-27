/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation at commit e2161e0936f181d4a5a9d49963a666f7cea42502.
Upstream source is dual-licensed under MIT or CC0 1.0; used here under MIT.
-/

module

public import LeanPool.LatticeDiracDerivation.V32SpectralProjectors
public import LeanPool.LatticeDiracDerivation.V32BrillouinZoneAudit
public import LeanPool.LatticeDiracDerivation.V2.FlavorClassification

/-!
# V3.2 Stage 5: internal-copy classification

This stage keeps the two exhaustive cubical four-component sectors distinct
from momentum-space doubling.  Both sectors intertwine the same derived free
Hamiltonian, their intersection is zero, and every eight-corner amplitude has
their canonical flavor decomposition.
-/

@[expose] public section



namespace LeanDirac.V2

noncomputable section

/-- The V3.2 C op yP ai r definition used by this stage. -/
abbrev V32CopyPair := CubicalCell4 × CubicalCell4

/-- The V3.2 C op yP ai rH am il to ni an definition used by this stage. -/
def v32CopyPairHamiltonian
    (mass px py pz : ℂ) (pair : V32CopyPair) : V32CopyPair :=
  (cubicalStandardHamiltonian mass px py pz pair.1,
    cubicalStandardHamiltonian mass px py pz pair.2)

/-- The V3.2 C op yE xc ha ng e definition used by this stage. -/
def v32CopyExchange (pair : V32CopyPair) : V32CopyPair :=
  (pair.2, pair.1)

theorem v32_copy_exchange_involution (pair : V32CopyPair) :
    v32CopyExchange (v32CopyExchange pair) = pair := by
  rfl

theorem v32_copy_exchange_commutes_hamiltonian
    (mass px py pz : ℂ) (pair : V32CopyPair) :
    v32CopyExchange (v32CopyPairHamiltonian mass px py pz pair) =
      v32CopyPairHamiltonian mass px py pz (v32CopyExchange pair) := by
  rfl

/-- The V3.2 C op yM at ri xA ct io n definition used by this stage. -/
def v32CopyMatrixAction
    (a b c d : ℂ) (pair : V32CopyPair) : V32CopyPair :=
  (fun component => a * pair.1 component + b * pair.2 component,
    fun component => c * pair.1 component + d * pair.2 component)

theorem v32_standard_hamiltonian_linear_combination
    (mass px py pz a b : ℂ) (z w : CubicalCell4) :
    cubicalStandardHamiltonian mass px py pz
        (fun component => a * z component + b * w component) =
      fun component =>
        a * cubicalStandardHamiltonian mass px py pz z component +
          b * cubicalStandardHamiltonian mass px py pz w component := by
  funext component
  fin_cases component <;>
    simp [cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;> ring

theorem v32_every_copy_matrix_commutes_hamiltonian
    (mass px py pz a b c d : ℂ) (pair : V32CopyPair) :
    v32CopyMatrixAction a b c d
        (v32CopyPairHamiltonian mass px py pz pair) =
      v32CopyPairHamiltonian mass px py pz
        (v32CopyMatrixAction a b c d pair) := by
  apply Prod.ext
  · exact (v32_standard_hamiltonian_linear_combination
      mass px py pz a b pair.1 pair.2).symm
  · exact (v32_standard_hamiltonian_linear_combination
      mass px py pz c d pair.1 pair.2).symm

theorem v32_copy_exchange_is_off_diagonal_matrix (pair : V32CopyPair) :
    v32CopyMatrixAction 0 1 1 0 pair = v32CopyExchange pair := by
  apply Prod.ext <;> funext component <;>
    simp [v32CopyMatrixAction, v32CopyExchange]

/-- The V3.2 C op yP ai rE mb ed definition used by this stage. -/
def v32CopyPairEmbed (pair : V32CopyPair) : CubicalCell8 :=
  fun corner =>
    cubicalDiracEmbedMinus pair.1 corner +
      cubicalDiracEmbedPlus pair.2 corner

theorem v32_copy_pair_embed_intertwines
    (mass px py pz : ℂ) (pair : V32CopyPair) :
    cubicalNativeHamiltonian mass px py pz (v32CopyPairEmbed pair) =
      v32CopyPairEmbed (v32CopyPairHamiltonian mass px py pz pair) := by
  funext corner
  have hminus := congrFun
    (cubical_hamiltonian_intertwines_minus mass px py pz pair.1) corner
  have hplus := congrFun
    (cubical_hamiltonian_intertwines_plus mass px py pz pair.2) corner
  fin_cases corner <;>
    simp [v32CopyPairEmbed, v32CopyPairHamiltonian,
      cubicalNativeHamiltonian, cubicalNativeSpatial,
      cubicalBeta, cubicalIncidenceLinear, cubicalGamma,
      cubicalIncidenceSign, cubicalFlip, cubicalFlip0,
      cubicalFlip1, cubicalFlip2, cubicalBit0, cubicalBit1,
      cubicalBit2] at hminus hplus ⊢ <;> linear_combination hminus + hplus

/-- The bundled V3.2 C op yC la ss if ic at io nC er ti fi ca te. -/
structure V32CopyClassificationCertificate : Prop where
  noMomentumDoublers : V32BrillouinZoneCertificate
  exhaustiveInternalCopies : CubicalFlavorClassificationCertificate
  minusCopyIntertwines : ∀ mass px py pz z,
    cubicalNativeHamiltonian mass px py pz (cubicalDiracEmbedMinus z) =
      cubicalDiracEmbedMinus (cubicalStandardHamiltonian mass px py pz z)
  plusCopyIntertwines : ∀ mass px py pz z,
    cubicalNativeHamiltonian mass px py pz (cubicalDiracEmbedPlus z) =
      cubicalDiracEmbedPlus (cubicalStandardHamiltonian mass px py pz z)
  exchangeInvolution : ∀ pair,
    v32CopyExchange (v32CopyExchange pair) = pair
  exchangeCommutes : ∀ mass px py pz pair,
    v32CopyExchange (v32CopyPairHamiltonian mass px py pz pair) =
      v32CopyPairHamiltonian mass px py pz (v32CopyExchange pair)
  copyCommutant : ∀ mass px py pz a b c d pair,
    v32CopyMatrixAction a b c d
        (v32CopyPairHamiltonian mass px py pz pair) =
      v32CopyPairHamiltonian mass px py pz
        (v32CopyMatrixAction a b c d pair)
  embeddedPairIntertwines : ∀ mass px py pz pair,
    cubicalNativeHamiltonian mass px py pz (v32CopyPairEmbed pair) =
      v32CopyPairEmbed (v32CopyPairHamiltonian mass px py pz pair)

theorem v32_copy_classification : V32CopyClassificationCertificate where
  noMomentumDoublers := v32_brillouin_zone_audit
  exhaustiveInternalCopies := cubical_flavor_classification
  minusCopyIntertwines := cubical_hamiltonian_intertwines_minus
  plusCopyIntertwines := cubical_hamiltonian_intertwines_plus
  exchangeInvolution := v32_copy_exchange_involution
  exchangeCommutes := v32_copy_exchange_commutes_hamiltonian
  copyCommutant := v32_every_copy_matrix_commutes_hamiltonian
  embeddedPairIntertwines := v32_copy_pair_embed_intertwines


end
end LeanDirac.V2
