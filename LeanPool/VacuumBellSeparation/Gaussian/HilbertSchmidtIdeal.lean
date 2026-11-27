/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.HilbertSchmidtTrace

/-!
# Operator-ideal bounds for the actual extended trace

Composition with a bounded operator multiplies a squared Hilbert--Schmidt
sum by at most its squared norm. The rectangular adjoint identity provides
the right-composition bound and the usual positive trace-class sandwich
bound, including infinite extended traces.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  {ι κ : Type*}

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
theorem basisHilbertSchmidtSquare_comp_left_le (b : HilbertBasis ι ℂ E)
    (T : E →L[ℂ] F) (B : F →L[ℂ] G) :
    basisHilbertSchmidtSquare b (B.comp T) ≤
      ENNReal.ofReal (‖B‖ ^ 2) * basisHilbertSchmidtSquare b T := by
  unfold basisHilbertSchmidtSquare
  rw [← ENNReal.tsum_mul_left]
  apply tsum_le_tsum
  intro i
  dsimp only
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    ‖(B.comp T) (b i)‖ ^ 2 ≤ (‖B‖ * ‖T (b i)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm _) 2
    _ = ‖B‖ ^ 2 * ‖T (b i)‖ ^ 2 := mul_pow _ _ _

theorem basisHilbertSchmidtSquare_comp_right_le (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ F) (A : E →L[ℂ] F) (T : F →L[ℂ] G) :
    basisHilbertSchmidtSquare b (T.comp A) ≤
      ENNReal.ofReal (‖A‖ ^ 2) * basisHilbertSchmidtSquare c T := by
  obtain ⟨s, d, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := G)
  rw [basisHilbertSchmidtSquare_adjoint b d, adjoint_comp]
  have h := basisHilbertSchmidtSquare_comp_left_le d T.adjoint A.adjoint
  rw [basisHilbertSchmidtSquare_adjoint d c, adjoint_adjoint, adjoint.norm_map] at h
  exact h

theorem positiveTrace_adjoint_sandwich_le {S : F →L[ℂ] F} (hS : 0 ≤ S)
    (A : E →L[ℂ] F) :
    positiveTrace (A.adjoint.comp (S.comp A)) ≤
      ENNReal.ofReal (‖A‖ ^ 2) * positiveTrace S := by
  obtain ⟨s, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := E)
  obtain ⟨t, c, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := F)
  have hs : IsSelfAdjoint (CFC.sqrt S) := (CFC.sqrt_nonneg S).isSelfAdjoint
  have heq : (CFC.sqrt S).comp (CFC.sqrt S) = S := by
    change CFC.sqrt S * CFC.sqrt S = S
    rw [← pow_two, CFC.sq_sqrt S hS]
  have hfactor : ((CFC.sqrt S).comp A).adjoint.comp ((CFC.sqrt S).comp A) =
      A.adjoint.comp (S.comp A) := by
    rw [adjoint_comp, hs.adjoint_eq]
    calc
      (A.adjoint.comp (CFC.sqrt S)).comp ((CFC.sqrt S).comp A) =
          A.adjoint.comp (((CFC.sqrt S).comp (CFC.sqrt S)).comp A) := by
        simp only [comp_assoc]
      _ = _ := by rw [heq]
  rw [← hfactor, positiveTrace_adjoint_comp b]
  have h := basisHilbertSchmidtSquare_comp_right_le b c A (CFC.sqrt S)
  rw [positiveTrace_eq_basisSquareTrace c]
  exact h

theorem IsPositiveTraceClass.adjoint_sandwich {S : F →L[ℂ] F}
    (hS : IsPositiveTraceClass S) (A : E →L[ℂ] F) :
    IsPositiveTraceClass (A.adjoint.comp (S.comp A)) := by
  refine ⟨?_, (positiveTrace_adjoint_sandwich_le hS.1 A).trans_lt ?_⟩
  · apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    simpa only [comp_assoc] using
      (ContinuousLinearMap.nonneg_iff_isPositive.mp hS.1).adjoint_conj A
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS.2

end VacuumBellSeparation.Gaussian
