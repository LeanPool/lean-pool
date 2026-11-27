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

public import LeanPool.LatticeDiracDerivation.V33ProjectedSpinors

/-!
# V3.3 Stage 4: exact energy-branch spectral sum

This is projector completeness.  It is deliberately not advertised as the
covariant QFT outer-product spin sum, which would require additional
normalization and adjoint conventions.
-/

@[expose] public section

namespace LeanDirac.V2

noncomputable section

/-- The basis outer-product sum acting on a four-component cubical spinor. -/
def v33BasisOuterSum (z : CubicalCell4) : CubicalCell4 :=
  fun component =>
    ∑ seed : Fin 4,
      standardCell4Basis seed component *
        cubicalCell4Inner (standardCell4Basis seed) z

theorem v33_basis_outer_sum_is_identity (z : CubicalCell4) :
    v33BasisOuterSum z = z := by
  funext component
  fin_cases component <;>
    simp [v33BasisOuterSum, cubicalCell4Inner, standardCell4Basis]

/-- The sum of the positive- and negative-energy spectral projectors. -/
def v33FreeSpectralSum
    (mass px py pz energy : ℝ) (z : CubicalCell4) : CubicalCell4 :=
  fun component =>
    v32PositiveProjector mass px py pz energy z component +
      v32NegativeProjector mass px py pz energy z component

theorem v33_free_spectral_sum_is_identity
    (mass px py pz energy : ℝ) (z : CubicalCell4) :
    v33FreeSpectralSum mass px py pz energy z = z := by
  exact v32_projectors_complete mass px py pz energy z

theorem v33_opposite_energy_branches_are_disjoint
    (mass px py pz energy : ℝ)
    (hshell : energy ^ 2 = v32ContinuumEnergySq mass px py pz)
    (hne : energy ≠ 0) (z : CubicalCell4) :
    v32PositiveProjector mass px py pz energy
        (v32NegativeProjector mass px py pz energy z) = 0 := by
  exact v32_projectors_orthogonal mass px py pz energy hshell hne z

/-- Certificate for basis completeness and free spectral spin sums. -/
structure V33SpinSumCertificate : Prop where
  basisOuterResolution : ∀ z, v33BasisOuterSum z = z
  resolution : ∀ mass px py pz energy z,
    v33FreeSpectralSum mass px py pz energy z = z
  branchDisjointness : ∀ mass px py pz energy,
    energy ^ 2 = v32ContinuumEnergySq mass px py pz → energy ≠ 0 → ∀ z,
      v32PositiveProjector mass px py pz energy
          (v32NegativeProjector mass px py pz energy z) = 0

theorem v33_spin_sums : V33SpinSumCertificate where
  basisOuterResolution := v33_basis_outer_sum_is_identity
  resolution := v33_free_spectral_sum_is_identity
  branchDisjointness := v33_opposite_energy_branches_are_disjoint

end
end LeanDirac.V2
