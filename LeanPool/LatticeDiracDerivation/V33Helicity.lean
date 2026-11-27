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

public import LeanPool.LatticeDiracDerivation.V33BilinearObservables

/-!
# V3.3 Stage 6: cube-derived spin spectrum and scoped helicity

In the cubical orientation convention, `standardCubicalSpin 0` is paired with
the `pz` momentum coordinate.  This stage constructs the two axis-aligned
positive-frequency moving spinors and proves their half-valued helicities.  It
does not add a new spin postulate.
-/

@[expose] public section

namespace LeanDirac.V2

noncomputable section

/-- The helicity action for momentum along the first lattice axis. -/
def v33Axis0Helicity (z : CubicalCell4) : CubicalCell4 :=
  standardCubicalSpin 0 z

/-- The down basis state in the native two-channel sector. -/
def v33TwoChannelDown : UniformCell2
  | 0 => 1
  | _ => 0

/-- The up basis state in the native two-channel sector. -/
def v33TwoChannelUp : UniformCell2
  | 0 => 0
  | _ => 1

theorem v33_axis0_helicity_down :
    v33Axis0Helicity (standardCell4Basis 0) =
      fun component => (-1 / 2 : ℂ) * standardCell4Basis 0 component := by
  exact standard_spin0_basis_spectrum.1

theorem v33_axis0_helicity_up :
    v33Axis0Helicity (standardCell4Basis 1) =
      fun component => (1 / 2 : ℂ) * standardCell4Basis 1 component := by
  exact standard_spin0_basis_spectrum.2.1

theorem v33_axis0_helicity_square (z : CubicalCell4) :
    v33Axis0Helicity (v33Axis0Helicity z) =
      fun component => (1 / 4 : ℂ) * z component := by
  exact standard_spin_component_square 0 z

theorem v33_axis_aligned_moving_helicity_down
    (mass energy pz : ℝ) :
    v33Axis0Helicity
        (normalizedPositiveFrequencyEmbedding
          mass energy 0 0 pz v33TwoChannelDown) =
      fun component => (-1 / 2 : ℂ) *
        normalizedPositiveFrequencyEmbedding
          mass energy 0 0 pz v33TwoChannelDown component := by
  funext component
  fin_cases component <;>
    simp [v33Axis0Helicity, v33TwoChannelDown,
      normalized_positive_frequency_embedding_apply,
      positive_pauli_spatial_apply_zero, positive_pauli_spatial_apply_one,
      standardCubicalSpin, standardCubicalPlaneBivector,
      standardCubicalGamma, cubicalStandardAlphaX,
      cubicalStandardAlphaY] <;>
    ring_nf <;> norm_num [Complex.I_sq]

theorem v33_axis_aligned_moving_helicity_up
    (mass energy pz : ℝ) :
    v33Axis0Helicity
        (normalizedPositiveFrequencyEmbedding
          mass energy 0 0 pz v33TwoChannelUp) =
      fun component => (1 / 2 : ℂ) *
        normalizedPositiveFrequencyEmbedding
          mass energy 0 0 pz v33TwoChannelUp component := by
  funext component
  fin_cases component <;>
    simp [v33Axis0Helicity, v33TwoChannelUp,
      normalized_positive_frequency_embedding_apply,
      positive_pauli_spatial_apply_zero, positive_pauli_spatial_apply_one,
      standardCubicalSpin, standardCubicalPlaneBivector,
      standardCubicalGamma, cubicalStandardAlphaX,
      cubicalStandardAlphaY] <;>
    ring_nf <;> norm_num [Complex.I_sq]

/-- Certificate for the axis helicity eigenstates of both energy branches. -/
structure V33HelicityCertificate : Prop where
  down : v33Axis0Helicity (standardCell4Basis 0) =
    fun component => (-1 / 2 : ℂ) * standardCell4Basis 0 component
  up : v33Axis0Helicity (standardCell4Basis 1) =
    fun component => (1 / 2 : ℂ) * standardCell4Basis 1 component
  square : ∀ z, v33Axis0Helicity (v33Axis0Helicity z) =
    fun component => (1 / 4 : ℂ) * z component
  movingDown : ∀ mass energy pz,
    v33Axis0Helicity
        (normalizedPositiveFrequencyEmbedding
          mass energy 0 0 pz v33TwoChannelDown) =
      fun component => (-1 / 2 : ℂ) *
        normalizedPositiveFrequencyEmbedding
          mass energy 0 0 pz v33TwoChannelDown component
  movingUp : ∀ mass energy pz,
    v33Axis0Helicity
        (normalizedPositiveFrequencyEmbedding
          mass energy 0 0 pz v33TwoChannelUp) =
      fun component => (1 / 2 : ℂ) *
        normalizedPositiveFrequencyEmbedding
          mass energy 0 0 pz v33TwoChannelUp component

theorem v33_helicity : V33HelicityCertificate where
  down := v33_axis0_helicity_down
  up := v33_axis0_helicity_up
  square := v33_axis0_helicity_square
  movingDown := v33_axis_aligned_moving_helicity_down
  movingUp := v33_axis_aligned_moving_helicity_up

end
end LeanDirac.V2
