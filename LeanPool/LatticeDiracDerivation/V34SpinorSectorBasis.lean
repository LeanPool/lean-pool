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

public import LeanPool.LatticeDiracDerivation.V34CovariantSpinors

/-!
# V3.4 Stage 2: exact two-state energy sectors

The explicit upper/lower read maps prove that each normalized frequency
embedding is an injective image of exactly two native complex amplitudes.
Together with the pre-existing inverse spectral readout, this gives a genuine
two-plus-two branch decomposition rather than four projected seed vectors.
-/

@[expose] public section

namespace LeanDirac.V2

noncomputable section
open Complex BigOperators

theorem v34_positive_spinors_span_branch
    (mass energy px py pz : ℝ) (q : UniformCell2) :
    (fun component =>
      ∑ spin : Fin 2, q spin *
        v34PositiveSpinor mass energy px py pz spin component) =
      normalizedPositiveFrequencyEmbedding mass energy px py pz q := by
  funext component
  fin_cases component <;>
    simp [v34PositiveSpinor, v34TwoChannelBasis,
      normalized_positive_frequency_embedding_apply,
      positive_pauli_spatial_apply_zero,
      positive_pauli_spatial_apply_one] <;> ring

theorem v34_negative_spinors_span_branch
    (mass energy px py pz : ℝ) (q : UniformCell2) :
    (fun component =>
      ∑ spin : Fin 2, q spin *
        v34NegativeBranchSpinor mass energy px py pz spin component) =
      normalizedNegativeFrequencyEmbedding mass energy px py pz q := by
  funext component
  fin_cases component <;>
    simp [v34NegativeBranchSpinor, v34TwoChannelBasis,
      normalized_negative_frequency_embedding_apply,
      positive_pauli_spatial_apply_zero,
      positive_pauli_spatial_apply_one] <;> ring

theorem v34_positive_negative_inner_orthogonal
    (mass energy px py pz : ℝ) (positive negative : UniformCell2) :
    cubicalCell4Inner
        (normalizedPositiveFrequencyEmbedding mass energy px py pz positive)
        (normalizedNegativeFrequencyEmbedding mass energy px py pz negative) = 0 := by
  apply Complex.ext <;>
    simp [cubicalCell4Inner, normalized_positive_frequency_embedding_apply,
      normalized_negative_frequency_embedding_apply,
      positive_pauli_spatial_apply_zero, positive_pauli_spatial_apply_one,
      Fin.sum_univ_four, Complex.mul_re, Complex.mul_im] <;> ring

theorem v34_positive_spinors_energy_orthogonal
    (mass energy px py pz : ℝ)
    (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (first second : Fin 2) :
    cubicalCell4Inner
        (v34PositiveSpinor mass energy px py pz first)
        (v34PositiveSpinor mass energy px py pz second) =
      if first = second then (energy : ℂ) else 0 := by
  have hcoeff := spectral_normalization_coefficient
    mass energy px py pz hpositive hshell
  have hcoeffC :
      (positiveFrequencyScale mass energy : ℂ) ^ 2 +
          (positiveFrequencyRatio mass energy : ℂ) ^ 2 *
            ((px : ℂ) ^ 2 + (py : ℂ) ^ 2 + (pz : ℂ) ^ 2) =
        (energy : ℂ) := by
    exact_mod_cast hcoeff
  fin_cases first <;> fin_cases second <;>
    simp [v34PositiveSpinor, v34TwoChannelBasis, cubicalCell4Inner,
      normalized_positive_frequency_embedding_apply,
      positive_pauli_spatial_apply_zero, positive_pauli_spatial_apply_one,
      Fin.sum_univ_four] <;> ring_nf
  all_goals
    rw [Complex.I_sq]
    ring_nf
    linear_combination hcoeffC

theorem v34_negative_spinors_energy_orthogonal
    (mass energy px py pz : ℝ)
    (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (first second : Fin 2) :
    cubicalCell4Inner
        (v34NegativeBranchSpinor mass energy px py pz first)
        (v34NegativeBranchSpinor mass energy px py pz second) =
      if first = second then (energy : ℂ) else 0 := by
  have hcoeff := spectral_normalization_coefficient
    mass energy px py pz hpositive hshell
  have hcoeffC :
      (positiveFrequencyScale mass energy : ℂ) ^ 2 +
          (positiveFrequencyRatio mass energy : ℂ) ^ 2 *
            ((px : ℂ) ^ 2 + (py : ℂ) ^ 2 + (pz : ℂ) ^ 2) =
        (energy : ℂ) := by
    exact_mod_cast hcoeff
  fin_cases first <;> fin_cases second <;>
    simp [v34NegativeBranchSpinor, v34TwoChannelBasis,
      cubicalCell4Inner, normalized_negative_frequency_embedding_apply,
      positive_pauli_spatial_apply_zero, positive_pauli_spatial_apply_one,
      Fin.sum_univ_four] <;> ring_nf
  all_goals
    rw [Complex.I_sq]
    ring_nf
    linear_combination hcoeffC

theorem v34_every_spinor_has_unique_two_plus_two_coordinates
    (mass energy px py pz : ℝ)
    (henergy : energy ≠ 0) (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (z : CubicalCell4) :
    ∃! coordinates : UniformCell2 × UniformCell2,
      (fun component =>
        normalizedPositiveFrequencyEmbedding mass energy px py pz
            coordinates.1 component +
          normalizedNegativeFrequencyEmbedding mass energy px py pz
            coordinates.2 component) = z := by
  let positive := spectralPositiveCoordinate mass energy px py pz z
  let negative := spectralNegativeCoordinate mass energy px py pz z
  refine ⟨(positive, negative), ?_, ?_⟩
  · exact spectral_embeddings_reconstruct_cell
      mass energy px py pz henergy hpositive hshell z
  · intro other hother
    have hextract := spectral_coordinates_extract_embeddings
      mass energy px py pz henergy hpositive hshell other.1 other.2
    have hpositiveCoordinate := congrArg
      (spectralPositiveCoordinate mass energy px py pz) hother
    have hnegativeCoordinate := congrArg
      (spectralNegativeCoordinate mass energy px py pz) hother
    apply Prod.ext
    · calc
        other.1 = spectralPositiveCoordinate mass energy px py pz
            (fun component =>
              normalizedPositiveFrequencyEmbedding mass energy px py pz
                  other.1 component +
                normalizedNegativeFrequencyEmbedding mass energy px py pz
                  other.2 component) := hextract.1.symm
        _ = spectralPositiveCoordinate mass energy px py pz z :=
          hpositiveCoordinate
        _ = positive := rfl
    · calc
        other.2 = spectralNegativeCoordinate mass energy px py pz
            (fun component =>
              normalizedPositiveFrequencyEmbedding mass energy px py pz
                  other.1 component +
                normalizedNegativeFrequencyEmbedding mass energy px py pz
                  other.2 component) := hextract.2.symm
        _ = spectralNegativeCoordinate mass energy px py pz z :=
          hnegativeCoordinate
        _ = negative := rfl

/-- Certificate for the exact two-plus-two energy-sector basis decomposition. -/
structure V34SpinorSectorBasisCertificate : Prop where
  positiveSpan : ∀ mass energy px py pz q,
    (fun component =>
      ∑ spin : Fin 2, q spin *
        v34PositiveSpinor mass energy px py pz spin component) =
      normalizedPositiveFrequencyEmbedding mass energy px py pz q
  negativeSpan : ∀ mass energy px py pz q,
    (fun component =>
      ∑ spin : Fin 2, q spin *
        v34NegativeBranchSpinor mass energy px py pz spin component) =
      normalizedNegativeFrequencyEmbedding mass energy px py pz q
  branchOrthogonal : ∀ mass energy px py pz positive negative,
    cubicalCell4Inner
        (normalizedPositiveFrequencyEmbedding mass energy px py pz positive)
        (normalizedNegativeFrequencyEmbedding mass energy px py pz negative) = 0
  positiveGram : ∀ mass energy px py pz,
    0 < energy + mass →
    energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 → ∀ first second,
      cubicalCell4Inner
          (v34PositiveSpinor mass energy px py pz first)
          (v34PositiveSpinor mass energy px py pz second) =
        if first = second then (energy : ℂ) else 0
  negativeGram : ∀ mass energy px py pz,
    0 < energy + mass →
    energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 → ∀ first second,
      cubicalCell4Inner
          (v34NegativeBranchSpinor mass energy px py pz first)
          (v34NegativeBranchSpinor mass energy px py pz second) =
        if first = second then (energy : ℂ) else 0
  uniqueCoordinates : ∀ mass energy px py pz,
    energy ≠ 0 → 0 < energy + mass →
    energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 → ∀ z,
      ∃! coordinates : UniformCell2 × UniformCell2,
        (fun component =>
          normalizedPositiveFrequencyEmbedding mass energy px py pz
              coordinates.1 component +
            normalizedNegativeFrequencyEmbedding mass energy px py pz
              coordinates.2 component) = z

theorem v34_spinor_sector_basis : V34SpinorSectorBasisCertificate where
  positiveSpan := v34_positive_spinors_span_branch
  negativeSpan := v34_negative_spinors_span_branch
  branchOrthogonal := v34_positive_negative_inner_orthogonal
  positiveGram := v34_positive_spinors_energy_orthogonal
  negativeGram := v34_negative_spinors_energy_orthogonal
  uniqueCoordinates := v34_every_spinor_has_unique_two_plus_two_coordinates

end
end LeanDirac.V2
