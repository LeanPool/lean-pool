/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTrace

/-!
# Hilbert--Schmidt sums and cyclic positive traces

The squared Hilbert--Schmidt sum is allowed to be infinite and applies to
bounded maps between different Hilbert spaces. Parseval and Tonelli prove
the adjoint identity and hence `Tr(T†T)=Tr(TT†)`, without finite-rank or
finite-trace assumptions.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {ι κ : Type*}

/-- Basis Hilbert schmidt square given by `∑' i, ENNReal.ofReal (‖T (b i)‖ ^ 2)`. -/
noncomputable def basisHilbertSchmidtSquare (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F) :
    ℝ≥0∞ := ∑' i, ENNReal.ofReal (‖T (b i)‖ ^ 2)

theorem basisHilbertSchmidtSquare_adjoint (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ F) (T : E →L[ℂ] F) :
    basisHilbertSchmidtSquare b T = basisHilbertSchmidtSquare c T.adjoint := by
  have hentry (i : ι) (j : κ) :
      ‖inner ℂ (c j) (T (b i))‖ = ‖inner ℂ (b i) (T.adjoint (c j))‖ := by
    rw [← T.adjoint_inner_left, norm_inner_symm]
  unfold basisHilbertSchmidtSquare
  calc
    (∑' i, ENNReal.ofReal (‖T (b i)‖ ^ 2)) =
        ∑' i, ∑' j, ENNReal.ofReal (‖inner ℂ (c j) (T (b i))‖ ^ 2) := by
      exact tsum_congr fun i => (tsum_basis_inner_norm_sq c (T (b i))).symm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner ℂ (c j) (T (b i))‖ ^ 2) :=
      tsum_comm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner ℂ (b i) (T.adjoint (c j))‖ ^ 2) := by
      exact tsum_congr fun j => tsum_congr fun i => by rw [hentry]
    _ = ∑' j, ENNReal.ofReal (‖T.adjoint (c j)‖ ^ 2) := by
      exact tsum_congr fun j => tsum_basis_inner_norm_sq b (T.adjoint (c j))

theorem basisHilbertSchmidtSquare_eq (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ E) (T : E →L[ℂ] F) :
    basisHilbertSchmidtSquare b T = basisHilbertSchmidtSquare c T := by
  obtain ⟨s, d, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := F)
  rw [basisHilbertSchmidtSquare_adjoint b d T,
    basisHilbertSchmidtSquare_adjoint d c T.adjoint, adjoint_adjoint]

theorem positiveTrace_adjoint_comp (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F) :
    positiveTrace (T.adjoint.comp T) = basisHilbertSchmidtSquare b T := by
  rw [positiveTrace_eq_tsum_diagonal b
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self T))]
  unfold basisHilbertSchmidtSquare
  apply tsum_congr
  intro i
  rw [comp_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- The positive cyclic trace identity on genuine possibly different
infinite-dimensional Hilbert spaces. -/
theorem positiveTrace_adjoint_comp_eq_comp_adjoint (T : E →L[ℂ] F) :
    positiveTrace (T.adjoint.comp T) = positiveTrace (T.comp T.adjoint) := by
  obtain ⟨s, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := E)
  obtain ⟨t, c, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := F)
  rw [positiveTrace_adjoint_comp b T, basisHilbertSchmidtSquare_adjoint b c T]
  have h := positiveTrace_adjoint_comp c T.adjoint
  simpa only [adjoint_adjoint] using h.symm

theorem positiveTrace_sqrt_sandwich_swap {A B : E →L[ℂ] E}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    positiveTrace (CFC.sqrt A * B * CFC.sqrt A) =
      positiveTrace (CFC.sqrt B * A * CFC.sqrt B) := by
  have hsA := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hsB := (CFC.sqrt_nonneg B).isSelfAdjoint
  have hAA : CFC.sqrt A * CFC.sqrt A = A := by rw [← pow_two, CFC.sq_sqrt A hA]
  have hBB : CFC.sqrt B * CFC.sqrt B = B := by rw [← pow_two, CFC.sq_sqrt B hB]
  have hleft : (CFC.sqrt B * CFC.sqrt A).adjoint.comp (CFC.sqrt B * CFC.sqrt A) =
      CFC.sqrt A * B * CFC.sqrt A := by
    change star (CFC.sqrt B * CFC.sqrt A) * (CFC.sqrt B * CFC.sqrt A) = _
    rw [star_mul, hsA.star_eq, hsB.star_eq]
    calc
      (CFC.sqrt A * CFC.sqrt B) * (CFC.sqrt B * CFC.sqrt A) =
          CFC.sqrt A * (CFC.sqrt B * CFC.sqrt B) * CFC.sqrt A := by noncomm_ring
      _ = _ := by rw [hBB]
  have hright : (CFC.sqrt B * CFC.sqrt A).comp (CFC.sqrt B * CFC.sqrt A).adjoint =
      CFC.sqrt B * A * CFC.sqrt B := by
    change (CFC.sqrt B * CFC.sqrt A) * star (CFC.sqrt B * CFC.sqrt A) = _
    rw [star_mul, hsA.star_eq, hsB.star_eq]
    calc
      (CFC.sqrt B * CFC.sqrt A) * (CFC.sqrt A * CFC.sqrt B) =
          CFC.sqrt B * (CFC.sqrt A * CFC.sqrt A) * CFC.sqrt B := by noncomm_ring
      _ = _ := by rw [hAA]
  rw [← hleft, positiveTrace_adjoint_comp_eq_comp_adjoint, hright]

end VacuumBellSeparation.Gaussian
