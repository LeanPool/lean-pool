/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianBargmannFourier
public import LeanPool.VacuumBellSeparation.Gaussian.BargmannCoordinates

/-!
# Explicit interleaved-to-grouped Bargmann quadratures

The manuscript orders all q coordinates before all p coordinates. The
oscillator construction uses mode/quadrature pairs. This actual finite
bijection and the literal D_B matrix relate those conventions, including
the complex Fourier coefficient and its bilinear inverse quadratic form.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexConjugate

/-- Reindex grouped position and momentum coordinates into adjacent pairs for each mode. -/
def groupedToMode (m : ℕ) : (Fin m ⊕ Fin m) ≃ (Fin m × Fin 2) where
  toFun := Sum.elim (fun j => (j, 0)) (fun j => (j, 1))
  invFun i := if i.2 = 0 then Sum.inl i.1 else Sum.inr i.1
  left_inv := by intro i; cases i <;> simp
  right_inv := by rintro ⟨j, k⟩; fin_cases k <;> simp

/-- Bargmann pair given by `Sum.elim (fun j => conj (a j)) (fun j => b j)`. -/
def bargmannPair {m : ℕ} (a b : MultiModePhaseSpace m) : Fin m ⊕ Fin m → ℂ :=
  Sum.elim (fun j => conj (a j)) (fun j => b j)

/-- Interleaved Bargmann quadratures given by `(bargmannD *ᵥ bargmannPair a b) ∘ (groupedToMode
m).symm`. -/
def interleavedBargmannQuadratures {m : ℕ} (a b : MultiModePhaseSpace m) : Fin m × Fin 2 → ℂ :=
  (bargmannD *ᵥ bargmannPair a b) ∘ (groupedToMode m).symm

theorem bargmannD_mulVec_pair_left {m : ℕ} (a b : MultiModePhaseSpace m) (j : Fin m) :
    (bargmannD *ᵥ bargmannPair a b) (Sum.inl j) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (conj (a j) + b j) := by
  simp only [bargmannD, unscaledBargmannD, bargmannPair, smul_mulVec,
    fromBlocks_mulVec, one_mulVec, Pi.smul_apply, Pi.add_apply,
    Function.comp_apply, Sum.elim_inl, Sum.elim_inr, smul_eq_mul]

theorem bargmannD_mulVec_pair_right {m : ℕ} (a b : MultiModePhaseSpace m) (j : Fin m) :
    (bargmannD *ᵥ bargmannPair a b) (Sum.inr j) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * Complex.I * (conj (a j) - b j) := by
  simp only [bargmannD, unscaledBargmannD, bargmannPair, smul_mulVec,
    fromBlocks_mulVec, one_mulVec, Pi.smul_apply, Pi.add_apply,
    Function.comp_apply, Sum.elim_inl, Sum.elim_inr, smul_eq_mul]
  ring

theorem complex_modeSymplectic_mulVec_zero {m : ℕ} (r : Fin m × Fin 2 → ℂ) (j : Fin m) :
    (complexifyMatrix modeSymplecticForm *ᵥ r) (j, 0) = r (j, 1) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    complexifyMatrix, modeSymplecticForm, oneModeSymplecticForm,
    Matrix.one_apply, apply_ite, ite_mul]

theorem complex_modeSymplectic_mulVec_one {m : ℕ} (r : Fin m × Fin 2 → ℂ) (j : Fin m) :
    (complexifyMatrix modeSymplecticForm *ᵥ r) (j, 1) = -r (j, 0) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    complexifyMatrix, modeSymplecticForm, oneModeSymplecticForm,
    Matrix.one_apply, apply_ite, ite_mul]

theorem bargmannFourierCoefficient_eq_rotated {m : ℕ} (a b : MultiModePhaseSpace m) :
    bargmannFourierCoefficient a b =
      (Complex.I * (Real.sqrt 2 : ℂ)) •
        (complexifyMatrix modeSymplecticForm *ᵥ interleavedBargmannQuadratures a b) := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
  have hzero (j : Fin m) : interleavedBargmannQuadratures a b (j, 0) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (conj (a j) + b j) := by
    change (bargmannD *ᵥ bargmannPair a b) (Sum.inl j) = _
    exact bargmannD_mulVec_pair_left a b j
  have hone (j : Fin m) : interleavedBargmannQuadratures a b (j, 1) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * Complex.I * (conj (a j) - b j) := by
    change (bargmannD *ᵥ bargmannPair a b) (Sum.inr j) = _
    exact bargmannD_mulVec_pair_right a b j
  funext i
  obtain ⟨j, k⟩ := i
  fin_cases k
  · change b j - conj (a j) = (Complex.I * (Real.sqrt 2 : ℂ)) *
      (complexifyMatrix modeSymplecticForm *ᵥ interleavedBargmannQuadratures a b) (j, 0)
    rw [complex_modeSymplectic_mulVec_zero, hone]
    simp only [Complex.ofReal_inv]
    field_simp [hs]; ring_nf; simp [Complex.I_sq, sub_eq_add_neg]
  · change -Complex.I * (b j + conj (a j)) = (Complex.I * (Real.sqrt 2 : ℂ)) *
      (complexifyMatrix modeSymplecticForm *ᵥ interleavedBargmannQuadratures a b) (j, 1)
    rw [complex_modeSymplectic_mulVec_one, hzero]
    simp only [Complex.ofReal_inv]
    field_simp [hs]; ring

theorem complex_dotProduct_congruence {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix ι κ ℂ) (A : Matrix κ κ ℂ) (x y : ι → ℂ) :
    (Sᵀ *ᵥ x) ⬝ᵥ (A *ᵥ (Sᵀ *ᵥ y)) = x ⬝ᵥ ((S * A * Sᵀ) *ᵥ y) := by
  calc
    _ = (A *ᵥ (Sᵀ *ᵥ y)) ⬝ᵥ (Sᵀ *ᵥ x) := dotProduct_comm _ _
    _ = x ⬝ᵥ (S *ᵥ (A *ᵥ (Sᵀ *ᵥ y))) := Matrix.dotProduct_transpose_mulVec S _ x
    _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem complex_physicalDisplacementCovariance_quadratic {m : ℕ}
    (C : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (r : Fin m × Fin 2 → ℂ) :
    (complexifyMatrix modeSymplecticForm *ᵥ r) ⬝ᵥ
      (complexifyMatrix (physicalDisplacementCovariance C) *ᵥ
        (complexifyMatrix modeSymplecticForm *ᵥ r)) =
      r ⬝ᵥ (complexifyMatrix C *ᵥ r) := by
  let O := complexifyMatrix (modeSymplecticForm (ι := Fin m))
  have hOt : Oᵀ = -O := by
    dsimp only [O]
    rw [complexifyMatrix_transpose_bilinear, transpose_modeSymplecticForm]
    ext i j
    simp [complexifyMatrix]
  have hOO : O * O = -1 := by
    dsimp only [O]
    rw [← complexifyMatrix_mul, modeSymplecticForm_mul_self]
    ext i j
    by_cases h : i = j <;> simp [complexifyMatrix, h]
  have hB : complexifyMatrix (physicalDisplacementCovariance C) = Oᵀ * complexifyMatrix C * O := by
    rw [physicalDisplacementCovariance, complexifyMatrix_mul, complexifyMatrix_mul,
      ← complexifyMatrix_transpose_bilinear]
  have hr := complex_dotProduct_congruence Oᵀ
    (complexifyMatrix (physicalDisplacementCovariance C)) r r
  rw [Matrix.transpose_transpose, hB] at hr
  have hm : Oᵀ * (Oᵀ * complexifyMatrix C * O) * O = complexifyMatrix C := by
    calc
      _ = (Oᵀ * Oᵀ) * complexifyMatrix C * (O * O) := by noncomm_ring
      _ = _ := by rw [hOt, neg_mul_neg, hOO]; simp
  rw [hm] at hr
  simpa only [hB, O] using hr

theorem bargmannFourierCoefficient_quadratic {m : ℕ}
    (C : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (a b : MultiModePhaseSpace m) :
    (1 / 4 : ℂ) * (bargmannFourierCoefficient a b ⬝ᵥ
      (complexifyMatrix (physicalDisplacementCovariance C) *ᵥ bargmannFourierCoefficient a b)) =
      -(1 / 2 : ℂ) * (interleavedBargmannQuadratures a b ⬝ᵥ
        (complexifyMatrix C *ᵥ interleavedBargmannQuadratures a b)) := by
  rw [bargmannFourierCoefficient_eq_rotated]
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [complex_physicalDisplacementCovariance_quadratic]
  have hs : (Complex.I * (Real.sqrt 2 : ℂ)) ^ 2 = -2 := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  calc
    _ = (1 / 4 : ℂ) * (Complex.I * (Real.sqrt 2 : ℂ)) ^ 2 *
        (interleavedBargmannQuadratures a b ⬝ᵥ
          (complexifyMatrix C *ᵥ interleavedBargmannQuadratures a b)) := by ring
    _ = _ := by rw [hs]; ring

theorem reindexed_complex_quadratic {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M : Matrix κ κ ℂ) (u : ι → ℂ) :
    u ⬝ᵥ (M.submatrix e e *ᵥ u) = (u ∘ e.symm) ⬝ᵥ (M *ᵥ (u ∘ e.symm)) := by
  rw [Matrix.submatrix_mulVec_equiv]
  exact dotProduct_comp_equiv_symm _ _ e.symm

end VacuumBellSeparation.Gaussian
