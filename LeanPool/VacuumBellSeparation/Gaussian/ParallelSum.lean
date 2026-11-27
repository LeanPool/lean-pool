/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.OperatorMeans

/-!
# Inverse quadratic forms under compression

Foundations for parallel-sum compression in Lemma 4.4. The generalized
Schwarz inequality is proved from the positive orthogonal-complement
projection of the weighted embedding. It is not assumed as a literature
theorem.

The binary parallel sum is the actual inverse of the sum of inverses. Its
compression inequality follows from the inverse quadratic-form bound.
Finite nonempty families are handled by the actual inverse-sum formula and
binary induction.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Operator form of Bessel's inequality for an isometric embedding. -/
theorem gram_compression_le (ι : E →ₗᵢ[ℂ] F) (T : E →L[ℂ] F) :
    (ι.toContinuousLinearMap.adjoint ∘L T).adjoint ∘L
        (ι.toContinuousLinearMap.adjoint ∘L T) ≤ T.adjoint ∘L T := by
  have h := (nonneg_iff_isPositive.mp (one_sub_imageProjection_nonneg ι)).adjoint_conj T
  have heq : T.adjoint ∘L (1 - imageProjection ι) ∘L T =
      T.adjoint ∘L T - (ι.toContinuousLinearMap.adjoint ∘L T).adjoint ∘L
        (ι.toContinuousLinearMap.adjoint ∘L T) := by
    ext x
    simp [imageProjection]
  rw [heq] at h
  exact le_def.mpr h

theorem negHalf_rpow_mul_self {A : F →L[ℂ] F} (hA : IsStrictlyPositive A) :
    A ^ (-(1 / 2) : ℝ) * A ^ (-(1 / 2) : ℝ) = A ^ (-1 : ℝ) := by
  rw [← CFC.rpow_add hA.isUnit]
  norm_num

/-- The inverse quadratic-form compression bound
`(ι*Bι) (ι*Aι)^(-1) (ι*Bι) ≤ ι*(B A^(-1) B)ι`.
This is the key noncommutative inequality behind parallel-sum compression. -/
theorem compression_inverse_schwarz (ι : E →ₗᵢ[ℂ] F)
    {A B : F →L[ℂ] F} (hA : IsStrictlyPositive A) (hB : IsSelfAdjoint B) :
    compression ι B * (compression ι A) ^ (-1 : ℝ) * compression ι B ≤
      compression ι (B * A ^ (-1 : ℝ) * B) := by
  let T : E →L[ℂ] F := (A ^ (-(1 / 2) : ℝ)) ∘L B ∘L ι.toContinuousLinearMap
  let J := weightedEmbedding ι hA
  have hhalf : (A ^ (1 / 2 : ℝ)).adjoint = A ^ (1 / 2 : ℝ) :=
    (CFC.rpow_nonneg : 0 ≤ A ^ (1 / 2 : ℝ)).isSelfAdjoint.adjoint_eq
  have hneg : (A ^ (-(1 / 2) : ℝ)).adjoint = A ^ (-(1 / 2) : ℝ) :=
    (CFC.rpow_nonneg : 0 ≤ A ^ (-(1 / 2) : ℝ)).isSelfAdjoint.adjoint_eq
  have hHneg : ((compression ι A) ^ (-(1 / 2) : ℝ)).adjoint =
      (compression ι A) ^ (-(1 / 2) : ℝ) :=
    (CFC.rpow_nonneg : 0 ≤ (compression ι A) ^ (-(1 / 2) : ℝ)).isSelfAdjoint.adjoint_eq
  have hcancel := CFC.rpow_mul_rpow_neg (1 / 2 : ℝ) hA
  have hJT : J.toContinuousLinearMap.adjoint ∘L T =
      (compression ι A) ^ (-(1 / 2) : ℝ) * compression ι B := by
    change (weightedEmbeddingMap ι A).adjoint ∘L T = _
    ext x
    simp only [weightedEmbeddingMap, T, adjoint_comp, hhalf, hHneg,
      comp_apply, mul_apply_eq_comp]
    rw [← mul_apply_eq_comp, hcancel, one_apply_eq_self]
    rfl
  have hTT : T.adjoint ∘L T = compression ι (B * A ^ (-1 : ℝ) * B) := by
    ext x
    simp only [T, adjoint_comp, hneg, hB.adjoint_eq, comp_apply, compression, mul_apply_eq_comp]
    rw [← mul_apply_eq_comp (A ^ (-(1 / 2) : ℝ)) (A ^ (-(1 / 2) : ℝ)),
      negHalf_rpow_mul_self hA]
  have h := gram_compression_le J T
  rw [hJT, hTT] at h
  have hQ : IsSelfAdjoint (compression ι B) := compression_isSelfAdjoint ι hB
  have hN : IsSelfAdjoint ((compression ι A) ^ (-(1 / 2) : ℝ)) := CFC.rpow_nonneg.isSelfAdjoint
  have heq : ((compression ι A) ^ (-(1 / 2) : ℝ) * compression ι B).adjoint ∘L
        ((compression ι A) ^ (-(1 / 2) : ℝ) * compression ι B) =
      compression ι B * (compression ι A) ^ (-1 : ℝ) * compression ι B := by
    change star ((compression ι A) ^ (-(1 / 2) : ℝ) * compression ι B) *
      ((compression ι A) ^ (-(1 / 2) : ℝ) * compression ι B) = _
    rw [star_mul, hQ.star_eq, hN.star_eq]
    calc
      _ = compression ι B *
          (((compression ι A) ^ (-(1 / 2) : ℝ)) *
            ((compression ι A) ^ (-(1 / 2) : ℝ))) * compression ι B := by noncomm_ring
      _ = _ := by rw [negHalf_rpow_mul_self (compression_isStrictlyPositive ι hA)]
  rwa [heq] at h

/-- Inverse Jensen inequality for strictly positive operators. -/
theorem inverse_compression_le (ι : E →ₗᵢ[ℂ] F) {A : F →L[ℂ] F}
    (hA : IsStrictlyPositive A) :
    (compression ι A) ^ (-1 : ℝ) ≤ compression ι (A ^ (-1 : ℝ)) := by
  simpa only [compression_one, one_mul, mul_one] using
    compression_inverse_schwarz ι hA (IsSelfAdjoint.one (F →L[ℂ] F))

@[simp]
theorem compression_add (ι : E →ₗᵢ[ℂ] F) (A B : F →L[ℂ] F) :
    compression ι (A + B) = compression ι A + compression ι B := by
  ext x
  simp [compression]

/-- Binary parallel sum on strictly positive operators. Its theorem domains
below ensure that all three inverses are genuine inverses. -/
noncomputable def parallelSum (A B : F →L[ℂ] F) : F →L[ℂ] F :=
  Ring.inverse (Ring.inverse A + Ring.inverse B)

theorem parallelSum_isStrictlyPositive {A B : F →L[ℂ] F}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) :
    IsStrictlyPositive (parallelSum A B) :=
  (hA.ringInverse.add_nonneg hB.ringInverse.nonneg).ringInverse

/-- The inverse-sum algebraic identity used to compare parallel sums. -/
theorem parallelSum_eq_sub_inverse {A B : F →L[ℂ] F}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) :
    parallelSum A B = A - A * Ring.inverse (A + B) * A := by
  have hsum : IsStrictlyPositive (A + B) := hA.add_nonneg hB.nonneg
  unfold parallelSum
  rw [Ring.inverse_add_inverse ⟨fun _ => hB.isUnit, fun _ => hA.isUnit⟩,
    Ring.inverse_mul (Or.inr hB.isUnit.ringInverse),
    Ring.inverse_mul (Or.inl hA.isUnit.ringInverse),
    Ring.inverse_inverse hB.isUnit, Ring.inverse_inverse hA.isUnit]
  calc
    B * (Ring.inverse (A + B) * A) =
        (A + B) * Ring.inverse (A + B) * A - A * Ring.inverse (A + B) * A := by
      noncomm_ring
    _ = A - A * Ring.inverse (A + B) * A := by
      rw [Ring.mul_inverse_cancel _ hsum.isUnit, one_mul]

/-- The same formula in the functional-calculus inverse notation. -/
theorem parallelSum_eq_sub_rpow {A B : F →L[ℂ] F}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) :
    parallelSum A B = A - A * (A + B) ^ (-1 : ℝ) * A := by
  rw [parallelSum_eq_sub_inverse hA hB,
    CFC.inverse_eq_rpow_neg_one (hA.add_nonneg hB.nonneg)]

/-- Parallel sums increase under isometric compression. -/
theorem compression_parallelSum_le (ι : E →ₗᵢ[ℂ] F) {A B : F →L[ℂ] F}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) :
    compression ι (parallelSum A B) ≤ parallelSum (compression ι A) (compression ι B) := by
  rw [parallelSum_eq_sub_rpow hA hB, compression_sub,
    parallelSum_eq_sub_rpow (compression_isStrictlyPositive ι hA)
      (compression_isStrictlyPositive ι hB), ← compression_add]
  exact sub_le_sub_left (compression_inverse_schwarz ι (hA.add_nonneg hB.nonneg)
    hA.nonneg.isSelfAdjoint) _

/-- Monotonicity of binary parallel sums, proved by reversing the operator
order twice under inversion. -/
theorem parallelSum_mono {A B C D : F →L[ℂ] F}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B)
    (hAC : A ≤ C) (hBD : B ≤ D) : parallelSum A B ≤ parallelSum C D := by
  have hC := hA.of_le hAC
  have hD := hB.of_le hBD
  have h := add_le_add (CStarAlgebra.ringInverse_le_ringInverse hAC hA)
    (CStarAlgebra.ringInverse_le_ringInverse hBD hB)
  exact CStarAlgebra.ringInverse_le_ringInverse h
    (hC.ringInverse.add_nonneg hD.ringInverse.nonneg)

/-- Parallel sum of a finite nonempty family, with its actual inverse-sum
definition rather than an abstract operation carrying assumed properties. -/
noncomputable def parallelFamily {n : ℕ} (A : Fin (n + 1) → (F →L[ℂ] F)) : F →L[ℂ] F :=
  Ring.inverse (∑ j, Ring.inverse (A j))

theorem sum_inverse_isStrictlyPositive {n : ℕ} {A : Fin (n + 1) → (F →L[ℂ] F)}
    (hA : ∀ j, IsStrictlyPositive (A j)) :
    IsStrictlyPositive (∑ j, Ring.inverse (A j)) := by
  rw [Fin.sum_univ_succ]
  exact (hA 0).ringInverse.add_nonneg
    (Finset.sum_nonneg fun j _ => (hA j.succ).ringInverse.nonneg)

theorem parallelFamily_isStrictlyPositive {n : ℕ} {A : Fin (n + 1) → (F →L[ℂ] F)}
    (hA : ∀ j, IsStrictlyPositive (A j)) : IsStrictlyPositive (parallelFamily A) :=
  (sum_inverse_isStrictlyPositive hA).ringInverse

omit [CompleteSpace F] in
theorem parallelFamily_one (A : Fin 1 → (F →L[ℂ] F))
    (hA : IsStrictlyPositive (A 0)) : parallelFamily A = A 0 := by
  change Ring.inverse (∑ j : Fin 1, Ring.inverse (A j)) = A 0
  rw [Fin.sum_univ_one, Ring.inverse_inverse hA.isUnit]

theorem parallelFamily_succ {n : ℕ} (A : Fin (n + 2) → (F →L[ℂ] F))
    (hA : ∀ j, IsStrictlyPositive (A j)) :
    parallelFamily A = parallelSum (A 0) (parallelFamily (fun j => A j.succ)) := by
  unfold parallelFamily parallelSum
  rw [Fin.sum_univ_succ,
    Ring.inverse_inverse (sum_inverse_isStrictlyPositive (fun j => hA j.succ)).isUnit]

/-- Monotonicity of finite parallel sums. -/
theorem parallelFamily_mono {n : ℕ} {A B : Fin (n + 1) → (F →L[ℂ] F)}
    (hA : ∀ j, IsStrictlyPositive (A j)) (hAB : ∀ j, A j ≤ B j) :
    parallelFamily A ≤ parallelFamily B := by
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
    CStarAlgebra.ringInverse_le_ringInverse (hAB j) (hA j)
  exact CStarAlgebra.ringInverse_le_ringInverse hsum
    (sum_inverse_isStrictlyPositive (fun j => (hA j).of_le (hAB j)))

/-- Parallel sums of any finite nonempty family increase under isometric
compression. This is the form needed for the `r-1` thermal weights. -/
theorem compression_parallelFamily_le (ι : E →ₗᵢ[ℂ] F) {n : ℕ}
    (A : Fin (n + 1) → (F →L[ℂ] F)) (hA : ∀ j, IsStrictlyPositive (A j)) :
    compression ι (parallelFamily A) ≤ parallelFamily (fun j => compression ι (A j)) := by
  induction n with
  | zero =>
    rw [parallelFamily_one A (hA 0),
      parallelFamily_one _ (compression_isStrictlyPositive ι (hA 0))]
  | succ n ih =>
    rw [parallelFamily_succ A hA,
      parallelFamily_succ _ (fun j => compression_isStrictlyPositive ι (hA j))]
    exact (compression_parallelSum_le ι (hA 0)
      (parallelFamily_isStrictlyPositive (fun j => hA j.succ))).trans
      (parallelSum_mono (compression_isStrictlyPositive ι (hA 0))
        (compression_isStrictlyPositive ι (parallelFamily_isStrictlyPositive
          (fun j => hA j.succ))) le_rfl (ih (fun j => A j.succ) (fun j => hA j.succ)))

end VacuumBellSeparation.Gaussian
