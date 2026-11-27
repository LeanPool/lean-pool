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

public import LeanPool.LatticeDiracDerivation.V34SpinorSectorBasis

/-!
# V3.4 Stage 3: covariant spin sums

The sums are built from the two native-channel branch bases.  With the
repository normalization `u ^ dagger u = energy` and `ubar u = mass`, the
standard covariant numerators carry a factor of one half.
-/

@[expose] public section

namespace LeanDirac.V2

noncomputable section
open Complex BigOperators

/-- A matrix entry obtained by applying a linear operator to a standard basis state. -/
def v34OperatorEntry
    (operator : CubicalCell4 → CubicalCell4)
    (row column : Fin 4) : ℂ :=
  operator (standardCell4Basis column) row

/-- A matrix entry of the covariant spinor outer product. -/
def v34CovariantOuterEntry
    (left right : CubicalCell4) (row column : Fin 4) : ℂ :=
  left row * v34DiracAdjointComponent right column

/-- The sum over the two positive-energy spin states. -/
def v34PositiveSpinSum
    (mass energy px py pz : ℝ) (row column : Fin 4) : ℂ :=
  ∑ spin : Fin 2,
    v34CovariantOuterEntry
      (v34PositiveSpinor mass energy px py pz spin)
      (v34PositiveSpinor mass energy px py pz spin) row column

/-- The sum over the two antiparticle spin states. -/
def v34AntiparticleSpinSum
    (mass energy px py pz : ℝ) (row column : Fin 4) : ℂ :=
  ∑ spin : Fin 2,
    v34CovariantOuterEntry
      (v34AntiparticleSpinor mass energy px py pz spin)
      (v34AntiparticleSpinor mass energy px py pz spin) row column

/-- The standard covariant numerator for the positive-energy branch. -/
def v34PositiveCovariantNumerator
    (mass energy px py pz : ℝ) (row column : Fin 4) : ℂ :=
  (1 / 2 : ℂ) *
    (v34OperatorEntry (v34MomentumSlash energy px py pz) row column +
      (mass : ℂ) * standardCell4Basis column row)

/-- The standard covariant numerator for the antiparticle branch. -/
def v34AntiparticleCovariantNumerator
    (mass energy px py pz : ℝ) (row column : Fin 4) : ℂ :=
  (1 / 2 : ℂ) *
    (v34OperatorEntry (v34MomentumSlash energy px py pz) row column -
      (mass : ℂ) * standardCell4Basis column row)

private theorem v34_scale_ratio_half
    (mass energy : ℝ) (hpositive : 0 < energy + mass) :
    positiveFrequencyScale mass energy *
        positiveFrequencyRatio mass energy = 1 / 2 := by
  have hdenom : energy + mass ≠ 0 := ne_of_gt hpositive
  have hscale := positive_frequency_scale_square mass energy
    (le_of_lt hpositive)
  rw [positiveFrequencyRatio]
  field_simp [hdenom]
  nlinarith

private theorem v34_ratio_square_momentum_square
    (mass energy px py pz : ℝ)
    (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) :
    positiveFrequencyRatio mass energy ^ 2 *
        (px ^ 2 + py ^ 2 + pz ^ 2) = (energy - mass) / 2 := by
  have hdenom : energy + mass ≠ 0 := ne_of_gt hpositive
  have hscale := positive_frequency_scale_square mass energy
    (le_of_lt hpositive)
  rw [positiveFrequencyRatio]
  field_simp [hdenom]
  nlinarith

private structure V34SpinSumNormalizationFacts
    (mass energy px py pz : ℝ) : Prop where
  scaleSq :
    (positiveFrequencyScale mass energy : ℂ) ^ 2 =
      ((energy : ℂ) + (mass : ℂ)) / 2
  scaleRatio :
    (positiveFrequencyScale mass energy : ℂ) *
      (positiveFrequencyRatio mass energy : ℂ) = 1 / 2
  lowerSq :
    (positiveFrequencyRatio mass energy : ℂ) ^ 2 * (px : ℂ) ^ 2 +
        (positiveFrequencyRatio mass energy : ℂ) ^ 2 * (py : ℂ) ^ 2 +
        (positiveFrequencyRatio mass energy : ℂ) ^ 2 * (pz : ℂ) ^ 2 =
      ((energy : ℂ) - (mass : ℂ)) / 2
  crossLeft : ∀ z : ℂ,
    (positiveFrequencyRatio mass energy : ℂ) * z *
        (positiveFrequencyScale mass energy : ℂ) = z / 2
  crossRight : ∀ z : ℂ,
    (positiveFrequencyRatio mass energy : ℂ) *
        (positiveFrequencyScale mass energy : ℂ) * z = z / 2

private theorem v34_spin_sum_normalization_facts
    (mass energy px py pz : ℝ)
    (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) :
    V34SpinSumNormalizationFacts mass energy px py pz := by
  have hscale := positive_frequency_scale_square mass energy
    (le_of_lt hpositive)
  have hcross := v34_scale_ratio_half mass energy hpositive
  have hlower := v34_ratio_square_momentum_square
    mass energy px py pz hpositive hshell
  have hscaleC :
      (positiveFrequencyScale mass energy : ℂ) ^ 2 =
        (((energy + mass) / 2 : ℝ) : ℂ) := by exact_mod_cast hscale
  have hcrossC :
      (positiveFrequencyScale mass energy : ℂ) *
        (positiveFrequencyRatio mass energy : ℂ) = (1 / 2 : ℂ) := by
    calc
      _ = ((positiveFrequencyScale mass energy *
          positiveFrequencyRatio mass energy : ℝ) : ℂ) := by push_cast; rfl
      _ = (((1 / 2 : ℝ)) : ℂ) := by rw [hcross]
      _ = (1 / 2 : ℂ) := by norm_num
  have hlowerC :
      (positiveFrequencyRatio mass energy : ℂ) ^ 2 *
          ((px : ℂ) ^ 2 + (py : ℂ) ^ 2 + (pz : ℂ) ^ 2) =
        (((energy - mass) / 2 : ℝ) : ℂ) := by exact_mod_cast hlower
  push_cast at hscaleC hlowerC
  have hlowerExpanded :
      (positiveFrequencyRatio mass energy : ℂ) ^ 2 * (px : ℂ) ^ 2 +
          (positiveFrequencyRatio mass energy : ℂ) ^ 2 * (py : ℂ) ^ 2 +
          (positiveFrequencyRatio mass energy : ℂ) ^ 2 * (pz : ℂ) ^ 2 =
        ((energy : ℂ) - (mass : ℂ)) / 2 := by
    linear_combination hlowerC
  refine ⟨hscaleC, hcrossC, hlowerExpanded, ?_, ?_⟩
  · intro z
    calc
      _ = z * ((positiveFrequencyScale mass energy : ℂ) *
          (positiveFrequencyRatio mass energy : ℂ)) := by ring
      _ = z / 2 := by rw [hcrossC]; ring
  · intro z
    calc
      _ = ((positiveFrequencyScale mass energy : ℂ) *
          (positiveFrequencyRatio mass energy : ℂ)) * z := by ring
      _ = z / 2 := by rw [hcrossC]; ring

theorem v34_positive_covariant_spin_sum
    (mass energy px py pz : ℝ)
    (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) :
    v34PositiveSpinSum mass energy px py pz =
      v34PositiveCovariantNumerator mass energy px py pz := by
  have facts := v34_spin_sum_normalization_facts
    mass energy px py pz hpositive hshell
  have hlowerNegativeX :
      -((positiveFrequencyRatio mass energy : ℂ) ^ 2 * (px : ℂ) ^ 2) -
          (positiveFrequencyRatio mass energy : ℂ) ^ 2 * (py : ℂ) ^ 2 -
          (positiveFrequencyRatio mass energy : ℂ) ^ 2 * (pz : ℂ) ^ 2 =
        (energy : ℂ) * (-1 / 2) + (mass : ℂ) * (1 / 2) := by
    linear_combination -facts.lowerSq
  have hlowerNegativeZ :
      -((positiveFrequencyRatio mass energy : ℂ) ^ 2 * (pz : ℂ) ^ 2) -
          (positiveFrequencyRatio mass energy : ℂ) ^ 2 * (px : ℂ) ^ 2 -
          (positiveFrequencyRatio mass energy : ℂ) ^ 2 * (py : ℂ) ^ 2 =
        (energy : ℂ) * (-1 / 2) + (mass : ℂ) * (1 / 2) := by
    linear_combination -facts.lowerSq
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [v34PositiveSpinSum, v34PositiveCovariantNumerator,
      v34CovariantOuterEntry, v34DiracAdjointComponent,
      v34PositiveSpinor, v34TwoChannelBasis, v34OperatorEntry,
      v34MomentumSlash, v34CovariantMomentum, v34Gamma,
      cubicalGammaTime, cubicalGammaSpace, cubicalAlpha,
      normalized_positive_frequency_embedding_apply,
      positive_pauli_spatial_apply_zero, positive_pauli_spatial_apply_one,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      standardCell4Basis, Fin.sum_univ_four] <;>
    ring_nf
  all_goals try rw [Complex.I_sq]
  all_goals try ring_nf
  all_goals try rw [facts.scaleSq]
  all_goals try rw [facts.scaleRatio]
  all_goals try rw [facts.crossLeft]
  all_goals try rw [facts.crossRight]
  all_goals try rw [hlowerNegativeX]
  all_goals try rw [hlowerNegativeZ]
  all_goals first
    | linear_combination facts.scaleRatio
    | linear_combination facts.lowerSq
    | linear_combination facts.scaleSq
    | ring

theorem v34_antiparticle_covariant_spin_sum
    (mass energy px py pz : ℝ)
    (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) :
    v34AntiparticleSpinSum mass energy px py pz =
      v34AntiparticleCovariantNumerator mass energy px py pz := by
  have facts := v34_spin_sum_normalization_facts
    mass energy px py pz hpositive hshell
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [v34AntiparticleSpinSum, v34AntiparticleCovariantNumerator,
      v34CovariantOuterEntry, v34DiracAdjointComponent,
      v34AntiparticleSpinor, v34TwoChannelBasis, v34OperatorEntry,
      v34MomentumSlash, v34CovariantMomentum, v34Gamma,
      cubicalGammaTime, cubicalGammaSpace, cubicalAlpha,
      normalized_negative_frequency_embedding_apply,
      positive_pauli_spatial_apply_zero, positive_pauli_spatial_apply_one,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      standardCell4Basis, Fin.sum_univ_four] <;>
    ring_nf
  all_goals try rw [Complex.I_sq]
  all_goals try ring_nf
  all_goals try rw [facts.scaleSq]
  all_goals try rw [facts.scaleRatio]
  all_goals try rw [facts.crossLeft]
  all_goals try rw [facts.crossRight]
  all_goals try rw [facts.lowerSq]
  all_goals first
    | linear_combination facts.scaleRatio
    | linear_combination facts.lowerSq
    | linear_combination facts.scaleSq
    | ring

/-- Certificate identifying both explicit spin sums with their covariant numerators. -/
structure V34CovariantSpinSumCertificate : Prop where
  positive : ∀ mass energy px py pz,
    0 < energy + mass →
    energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 →
      v34PositiveSpinSum mass energy px py pz =
        v34PositiveCovariantNumerator mass energy px py pz
  antiparticle : ∀ mass energy px py pz,
    0 < energy + mass →
    energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 →
      v34AntiparticleSpinSum mass energy px py pz =
        v34AntiparticleCovariantNumerator mass energy px py pz

theorem v34_covariant_spin_sums : V34CovariantSpinSumCertificate where
  positive := v34_positive_covariant_spin_sum
  antiparticle := v34_antiparticle_covariant_spin_sum

end
end LeanDirac.V2
