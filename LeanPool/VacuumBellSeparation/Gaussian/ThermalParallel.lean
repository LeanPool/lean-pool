/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ParallelSum

/-!
# Finite parallel families of weighted geometric means

The order-theoretic composition used in Lemma 4.4, equation (4.12). For
`r = n + 2`, the actual family consists of the `r - 1` means with weights
`1/r, ..., (r-1)/r`. The theorem here proves its compression inequality
on strictly positive inputs.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Strict positivity of a weighted mean follows from its defining
congruences and powers. No commutation of the inputs is needed. -/
theorem weightedGeometricMean_isStrictlyPositive {A B : F →L[ℂ] F}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) (p : ℝ) :
    IsStrictlyPositive (weightedGeometricMean p A B) := by
  have hN := IsStrictlyPositive.rpow A (-(1 / 2) : ℝ) hA
  have hH := IsStrictlyPositive.rpow A (1 / 2 : ℝ) hA
  have hX : IsStrictlyPositive
      (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) :=
    IsStrictlyPositive.conjugate_of_isUnit_of_isSelfAdjoint _ _ hN.isUnit
      hN.nonneg.isSelfAdjoint hB
  exact IsStrictlyPositive.conjugate_of_isUnit_of_isSelfAdjoint _ _ hH.isUnit
    hH.nonneg.isSelfAdjoint (IsStrictlyPositive.rpow _ p hX)

/-- The `j+1`-st thermal weight for the integer `r = n+2`. -/
def thermalMeanWeight {n : ℕ} (j : Fin (n + 1)) : ℝ :=
  ((j.val + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)

theorem thermalMeanWeight_pos {n : ℕ} (j : Fin (n + 1)) :
    0 < thermalMeanWeight j := by
  unfold thermalMeanWeight
  positivity

theorem thermalMeanWeight_lt_one {n : ℕ} (j : Fin (n + 1)) :
    thermalMeanWeight j < 1 := by
  unfold thermalMeanWeight
  apply (div_lt_one (by positivity : (0 : ℝ) < ((n + 2 : ℕ) : ℝ))).mpr
  exact_mod_cast (show j.val + 1 < n + 2 by omega)

/-- The right-hand side of the source's parallel thermal formula, before
its identification with functional calculus of the commutation operator. -/
noncomputable def geometricParallel (n : ℕ) (A B : F →L[ℂ] F) : F →L[ℂ] F :=
  parallelFamily (fun j : Fin (n + 1) => weightedGeometricMean (thermalMeanWeight j) A B)

theorem geometricParallel_isStrictlyPositive (n : ℕ) {A B : F →L[ℂ] F}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) :
    IsStrictlyPositive (geometricParallel n A B) :=
  parallelFamily_isStrictlyPositive fun j =>
    weightedGeometricMean_isStrictlyPositive hA hB (thermalMeanWeight j)

/-- Compression increases the parallel family of the `r-1` geometric
means. This is the order step in the first inequality of (4.11), with
strict positivity stated explicitly. -/
theorem compression_geometricParallel_le (ι : E →ₗᵢ[ℂ] F) (n : ℕ)
    {A B : F →L[ℂ] F} (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) :
    compression ι (geometricParallel n A B) ≤
      geometricParallel n (compression ι A) (compression ι B) := by
  exact (compression_parallelFamily_le ι _ (fun j =>
    weightedGeometricMean_isStrictlyPositive hA hB (thermalMeanWeight j))).trans
    (parallelFamily_mono (fun j => compression_isStrictlyPositive ι
      (weightedGeometricMean_isStrictlyPositive hA hB (thermalMeanWeight j)))
      (fun j => compression_weightedGeometricMean_le ι hA hB.nonneg
        (thermalMeanWeight_pos j) (thermalMeanWeight_lt_one j).le))

end VacuumBellSeparation.Gaussian
