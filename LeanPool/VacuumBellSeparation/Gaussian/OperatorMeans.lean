/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CompressionPower

/-!
# Weighted geometric means under compression

The strictly positive case of the weighted geometric-mean compression used in
Lemma 4.4. The proof uses the explicitly constructed weighted isometry
`A^(1/2) ι (ι* A ι)^(-1/2)` and the power Jensen theorem. Neither a Kubo–Ando
compression theorem nor a Gaussian comparison is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

@[simp]
theorem compression_real_smul (ι : E →ₗᵢ[ℂ] F) (r : ℝ) (A : F →L[ℂ] F) :
    compression ι (r • A) = r • compression ι A := by
  ext x
  simp [compression]

@[simp]
theorem compression_real_algebraMap (ι : E →ₗᵢ[ℂ] F) (r : ℝ) :
    compression ι (algebraMap ℝ (F →L[ℂ] F) r) = algebraMap ℝ (E →L[ℂ] E) r := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- Strict positivity is preserved by an isometric compression. -/
theorem compression_isStrictlyPositive (ι : E →ₗᵢ[ℂ] F) {A : F →L[ℂ] F}
    (hA : IsStrictlyPositive A) : IsStrictlyPositive (compression ι A) := by
  cases subsingleton_or_nontrivial F with
  | inl h =>
    let := h
    have hAeq : A = 1 := Subsingleton.elim _ _
    rw [hAeq, compression_one]
    exact isStrictlyPositive_one
  | inr h =>
    let := h
    obtain ⟨r, hr, hbound⟩ := (CFC.exists_pos_algebraMap_le_iff A hA.nonneg.isSelfAdjoint).mpr
      (fun _ hx => hA.spectrum_pos hx)
    have h := compression_mono ι hbound
    rw [compression_real_algebraMap] at h
    exact (isStrictlyPositive_algebraMap hr).of_le h

/-- The source's weighted geometric mean on a strictly positive first input.
The theorem below states the domain explicitly; outside it CFC uses its usual
totalized conventions. -/
noncomputable def weightedGeometricMean (p : ℝ) (A B : F →L[ℂ] F) : F →L[ℂ] F :=
  A ^ (1 / 2 : ℝ) * (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) ^ p *
    A ^ (1 / 2 : ℝ)

/-- The continuous linear map underlying the weighted isometry. -/
noncomputable def weightedEmbeddingMap (ι : E →ₗᵢ[ℂ] F) (A : F →L[ℂ] F) : E →L[ℂ] F :=
  (A ^ (1 / 2 : ℝ)) ∘L ι.toContinuousLinearMap ∘L
    ((compression ι A) ^ (-(1 / 2) : ℝ))

theorem half_rpow_mul_self {A : F →L[ℂ] F} (hA : IsStrictlyPositive A) :
    A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) = A := by
  rw [← CFC.rpow_add hA.isUnit]
  norm_num [CFC.rpow_one A hA.nonneg]

/-- The weighted embedding satisfies `J*J = I`, proved from its formula. -/
theorem weightedEmbeddingMap_adjoint_comp_self (ι : E →ₗᵢ[ℂ] F)
    {A : F →L[ℂ] F} (hA : IsStrictlyPositive A) :
    (weightedEmbeddingMap ι A).adjoint ∘L weightedEmbeddingMap ι A = 1 := by
  have hhalf : (A ^ (1 / 2 : ℝ)).adjoint = A ^ (1 / 2 : ℝ) :=
    (CFC.rpow_nonneg : 0 ≤ A ^ (1 / 2 : ℝ)).isSelfAdjoint.adjoint_eq
  have hneg : ((compression ι A) ^ (-(1 / 2) : ℝ)).adjoint =
      (compression ι A) ^ (-(1 / 2) : ℝ) :=
    (CFC.rpow_nonneg : 0 ≤ (compression ι A) ^ (-(1 / 2) : ℝ)).isSelfAdjoint.adjoint_eq
  ext x
  simp only [weightedEmbeddingMap, adjoint_comp, hhalf, hneg, comp_apply]
  rw [← mul_apply_eq_comp, half_rpow_mul_self hA]
  change (((compression ι A) ^ (-(1 / 2) : ℝ)) * compression ι A *
    ((compression ι A) ^ (-(1 / 2) : ℝ))) x = x
  rw [CFC.conjugate_rpow_neg_one_half _ (compression_isStrictlyPositive ι hA), one_apply_eq_self]

/-- The weighted embedding as an actual linear isometry. -/
noncomputable def weightedEmbedding (ι : E →ₗᵢ[ℂ] F) {A : F →L[ℂ] F}
    (hA : IsStrictlyPositive A) : E →ₗᵢ[ℂ] F where
  toLinearMap := (weightedEmbeddingMap ι A).toLinearMap
  norm_map' := (weightedEmbeddingMap ι A).norm_map_iff_adjoint_comp_self.mpr
    (weightedEmbeddingMap_adjoint_comp_self ι hA)

/-- Compression by the weighted isometry, expressed as an ordinary
compression followed by inverse square-root normalization. -/
theorem compression_weightedEmbedding (ι : E →ₗᵢ[ℂ] F) {A : F →L[ℂ] F}
    (hA : IsStrictlyPositive A) (Z : F →L[ℂ] F) :
    compression (weightedEmbedding ι hA) Z =
      (compression ι A) ^ (-(1 / 2) : ℝ) *
        compression ι (A ^ (1 / 2 : ℝ) * Z * A ^ (1 / 2 : ℝ)) *
        (compression ι A) ^ (-(1 / 2) : ℝ) := by
  have hhalf : (A ^ (1 / 2 : ℝ)).adjoint = A ^ (1 / 2 : ℝ) :=
    (CFC.rpow_nonneg : 0 ≤ A ^ (1 / 2 : ℝ)).isSelfAdjoint.adjoint_eq
  have hneg : ((compression ι A) ^ (-(1 / 2) : ℝ)).adjoint =
      (compression ι A) ^ (-(1 / 2) : ℝ) :=
    (CFC.rpow_nonneg : 0 ≤ (compression ι A) ^ (-(1 / 2) : ℝ)).isSelfAdjoint.adjoint_eq
  change (weightedEmbeddingMap ι A).adjoint ∘L Z ∘L weightedEmbeddingMap ι A = _
  simp only [weightedEmbeddingMap, adjoint_comp, hhalf, hneg]
  ext x
  simp only [comp_apply, compression, mul_apply_eq_comp]

theorem half_inverseHalf_conjugation {A : F →L[ℂ] F} (hA : IsStrictlyPositive A)
    (B : F →L[ℂ] F) :
    A ^ (1 / 2 : ℝ) * (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) *
      A ^ (1 / 2 : ℝ) = B := by
  have hleft := CFC.rpow_mul_rpow_neg (1 / 2 : ℝ) hA
  have hright := CFC.rpow_neg_mul_rpow (1 / 2 : ℝ) hA
  calc
    _ = (A ^ (1 / 2 : ℝ) * A ^ (-(1 / 2) : ℝ)) * B *
        (A ^ (-(1 / 2) : ℝ) * A ^ (1 / 2 : ℝ)) := by noncomm_ring
    _ = B := by rw [hleft, hright, one_mul, mul_one]

/-- Weighted geometric means increase under isometric compression, for
strictly positive `A`, positive `B`, and `0 < p ≤ 1`. -/
theorem compression_weightedGeometricMean_le (ι : E →ₗᵢ[ℂ] F)
    {A B : F →L[ℂ] F} (hA : IsStrictlyPositive A) (hB : 0 ≤ B)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    compression ι (weightedGeometricMean p A B) ≤
      weightedGeometricMean p (compression ι A) (compression ι B) := by
  let X := A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)
  have hX : 0 ≤ X :=
    (CFC.rpow_nonneg : 0 ≤ A ^ (-(1 / 2) : ℝ)).isSelfAdjoint.conjugate_nonneg hB
  have h := compression_rpow_le (weightedEmbedding ι hA) hX hp0 hp1
  rw [compression_weightedEmbedding, compression_weightedEmbedding,
    half_inverseHalf_conjugation hA B] at h
  have hconj := (CFC.rpow_nonneg : 0 ≤ (compression ι A) ^
    (1 / 2 : ℝ)).isSelfAdjoint.conjugate_le_conjugate h
  rw [half_inverseHalf_conjugation (compression_isStrictlyPositive ι hA)] at hconj
  exact hconj

end VacuumBellSeparation.Gaussian
