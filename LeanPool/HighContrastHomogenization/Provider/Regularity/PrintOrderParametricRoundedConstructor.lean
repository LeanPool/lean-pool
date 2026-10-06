/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderParametricRoundedAbsorptionRepair

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderParametricRoundedConstructor

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Rounded references at an arbitrarily prescribed tolerance

Increasing the rounding generation makes the normalized-root error arbitrarily
small.  The resulting inverse-grid congruence is therefore positive definite,
lies in the requested near-identity ellipticity window, and has operator-norm
defect bounded by that tolerance.
-/

namespace HCPolySupport
namespace HighContrast
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

private theorem norm_roundedGrid_sub_normalizedRoot_raw_at_generation
    {d : ℕ} [NeZero d] (l : ℤ) {m : Mat d} (hm : m.PosDef) :
    ‖roundedGrid l m - Selection.normalizedRoot m‖ ≤
      (d : ℝ) * (3 : ℝ) ^ (-l) := by
  let E : Mat d := roundedGrid l m - Selection.normalizedRoot m
  let delta : ℝ := (3 : ℝ) ^ (-l)
  let c : ℝ := (d : ℝ) * delta
  have hentry : ∀ i k, |E i k| ≤ delta := by
    intro i k
    obtain ⟨hlo, hhi⟩ :=
      Recurrence.roundedGrid_sub_normalized_matSqrt_mem l m i k
    rw [show E = roundedGrid l m - Selection.normalizedRoot m from rfl,
      Selection.normalizedRoot, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, abs_of_nonneg hlo]
    exact hhi
  have hrounded : (roundedGrid l m).IsHermitian := by
    refine Matrix.IsHermitian.ext fun i k ↦ ?_
    simpa using Recurrence.roundedGrid_symm l hm.posSemidef i k
  have hsymm : Eᴴ = E := by
    rw [Matrix.IsHermitian.eq (hrounded.sub
      (normalizedRoot_posDef_of_posDef hm).isHermitian)]
  have htrans : Eᵀ = E := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hsymm
  have hquadLo : ∀ x : Fin d → ℝ, -c * (x ⬝ᵥ x) ≤ x ⬝ᵥ E *ᵥ x := by
    intro x
    have h := Recurrence.neg_le_dotProduct_mulVec_of_abs_entry_le hentry x
    rw [show c = (d : ℝ) * delta from rfl,
      show delta = (3 : ℝ) ^ (-l) from rfl]
    simpa only [dotProduct, star_trivial, neg_mul, mul_assoc, mul_left_comm,
      mul_comm] using h
  have hquadHi : ∀ x : Fin d → ℝ, x ⬝ᵥ E *ᵥ x ≤ c * (x ⬝ᵥ x) := by
    intro x
    have h := Recurrence.neg_le_dotProduct_mulVec_of_abs_entry_le
      (E := -E) (fun i k ↦ by simpa using hentry i k) x
    rw [Matrix.neg_mulVec, dotProduct_neg, dotProduct] at h
    have h' := neg_le_neg_iff.mp h
    rw [dotProduct, show c = (d : ℝ) * delta from rfl,
      show delta = (3 : ℝ) ^ (-l) from rfl]
    simpa only [dotProduct, star_trivial, pow_two, mul_comm] using h'
  have hhi : E ≤ c • (1 : Mat d) := by
    rw [Matrix.le_iff]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x ↦ ?_
    · simp [Matrix.IsHermitian, htrans]
    · rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
        Matrix.one_mulVec, dotProduct_smul]
      simp only [star_trivial, smul_eq_mul]
      linarith only [hquadHi x]
  have hlo : (-c) • (1 : Mat d) ≤ E := by
    rw [Matrix.le_iff]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x ↦ ?_
    · simp [Matrix.IsHermitian, htrans]
    · rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
        Matrix.one_mulVec, dotProduct_smul]
      simp only [star_trivial, smul_eq_mul]
      linarith only [hquadLo x]
  exact PortableHistory.norm_le_of_sandwich hsymm
    (mul_nonneg (Nat.cast_nonneg _) (by positivity)) hhi hlo

private theorem exists_admissible_generation_with_rounding_error
    (d : ℕ) [NeZero d] {eta : ℝ} (heta : 0 < eta) :
    ∃ l : ℤ, (kZero d : ℤ) ≤ l ∧
      (d : ℝ) * (3 : ℝ) ^ (-l) ≤ eta := by
  have hd : (0 : ℝ) < d := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos heta hd)
    (by norm_num : (1 / 3 : ℝ) < 1)
  let l : ℤ := max (kZero d : ℤ) (N : ℤ)
  have hl : (kZero d : ℤ) ≤ l := le_max_left _ _
  have hNl : (N : ℤ) ≤ l := le_max_right _ _
  have hpow : (3 : ℝ) ^ (-l) ≤ (3 : ℝ) ^ (-(N : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hpowN : (3 : ℝ) ^ (-(N : ℤ)) = (1 / 3 : ℝ) ^ N := by
    rw [zpow_neg, zpow_natCast]
    simpa only [one_div] using (inv_pow (3 : ℝ) N).symm
  refine ⟨l, hl, ?_⟩
  exact le_of_lt (calc
      (d : ℝ) * (3 : ℝ) ^ (-l) ≤
          (d : ℝ) * (3 : ℝ) ^ (-(N : ℤ)) :=
        mul_le_mul_of_nonneg_left hpow hd.le
      _ = (d : ℝ) * (1 / 3 : ℝ) ^ N := by rw [hpowN]
      _ < (d : ℝ) * (eta / (d : ℝ)) :=
        mul_lt_mul_of_pos_left hN hd
      _ = eta := by field_simp [hd.ne'])

private theorem rounded_reference_posDef_at_generation
    {d : ℕ} [NeZero d] {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    (roundedReferenceMatrixAtGeneration l abar hS).PosDef := by
  let q : Mat d := roundedGrid l (symmPart abar)
  let L : Mat d := Selection.normalizedRoot (symmPart abar)
  have hq : q.PosDef := Recurrence.posDef_roundedGrid hl hS
  have hL : L.PosDef := normalizedRoot_posDef_of_posDef hS
  have hLT : Lᴴ = L := hL.isHermitian
  have hqInvHerm : (q⁻¹)ᴴ = q⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hq.isHermitian]
  have hqInvT : matTranspose q⁻¹ = q⁻¹ := by
    simpa only [matTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hqInvHerm
  have hLsq : L * L = specBound ((symmPart abar)⁻¹) • symmPart abar := by
    simpa only [L] using normalizedRoot_mul_self hS
  have hLsqPos : (L * L).PosDef := by
    have hconj := posDef_conj (Q := (1 : Mat d)) Matrix.PosDef.one hL.isUnit
    simpa only [hLT, Matrix.mul_one] using hconj
  have hqInvUnit : IsUnit q⁻¹ :=
    Matrix.isUnit_nonsing_inv_iff.mpr hq.isUnit
  have hconj := posDef_conj hLsqPos hqInvUnit
  rw [hqInvHerm, hLsq] at hconj
  simpa only [roundedReferenceMatrixAtGeneration, q, hqInvT] using hconj

private theorem norm_rounded_reference_sub_one_le
    {d : ℕ} [NeZero d] {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {eps : ℝ} (heps0 : 0 < eps) (hepsHalf : eps ≤ 1 / 2)
    (hround : (d : ℝ) * (3 : ℝ) ^ (-l) ≤ eps / 4)
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    ‖roundedReferenceMatrixAtGeneration l abar hS - 1‖ ≤ eps := by
  let q : Mat d := roundedGrid l (symmPart abar)
  let L : Mat d := Selection.normalizedRoot (symmPart abar)
  let E : Mat d := q - L
  let D : Mat d := q⁻¹ * E
  have hq : q.PosDef := Recurrence.posDef_roundedGrid hl hS
  have hL : L.PosDef := normalizedRoot_posDef_of_posDef hS
  have hqdet : IsUnit q.det := isUnit_det_of_posDef hq
  have hqInvHerm : (q⁻¹)ᴴ = q⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hq.isHermitian]
  have hqInvT : matTranspose q⁻¹ = q⁻¹ := by
    simpa only [matTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hqInvHerm
  have hEherm : Eᴴ = E := by
    exact Matrix.IsHermitian.eq (hq.isHermitian.sub hL.isHermitian)
  have hDstar : Dᴴ = E * q⁻¹ := by
    rw [show D = q⁻¹ * E from rfl, Matrix.conjTranspose_mul,
      hEherm, hqInvHerm]
  have hLsq : L * L = specBound ((symmPart abar)⁻¹) • symmPart abar := by
    simpa only [L] using normalizedRoot_mul_self hS
  have hform :
      q⁻¹ * (specBound ((symmPart abar)⁻¹) • symmPart abar) *
          matTranspose q⁻¹ - 1 = (-D + -Dᴴ) + D * Dᴴ := by
    rw [← hLsq, hqInvT, show L = q - E by simp [E]]
    rw [hDstar, show D = q⁻¹ * E from rfl]
    have hleft : q⁻¹ * q = 1 := Matrix.nonsing_inv_mul q hqdet
    have hright : q * q⁻¹ = 1 := Matrix.mul_nonsing_inv q hqdet
    have hmiddle : q⁻¹ * (q * (E * q⁻¹)) = E * q⁻¹ := by
      rw [← Matrix.mul_assoc, hleft, Matrix.one_mul]
    noncomm_ring [hleft, hright, hmiddle]
  have hEnorm : ‖E‖ ≤ eps / 4 := by
    have hraw : ‖E‖ ≤ (d : ℝ) * (3 : ℝ) ^ (-l) := by
      simpa only [E, q, L] using
        norm_roundedGrid_sub_normalizedRoot_raw_at_generation l hS
    exact hraw.trans hround
  have hqInvNorm : ‖q⁻¹‖ ≤ (101 / 100 : ℝ) := by
    simpa only [q] using Selection.norm_inv_roundedGrid_le hl hS
  have hDnorm : ‖D‖ ≤ (101 / 400 : ℝ) * eps := by
    calc
      ‖D‖ = ‖q⁻¹ * E‖ := rfl
      _ ≤ ‖q⁻¹‖ * ‖E‖ := norm_mul_le _ _
      _ ≤ (101 / 100 : ℝ) * (eps / 4) :=
        mul_le_mul hqInvNorm hEnorm (norm_nonneg E) (by norm_num)
      _ = (101 / 400 : ℝ) * eps := by ring
  have hnormStar : ‖Dᴴ‖ = ‖D‖ := Matrix.l2_opNorm_conjTranspose D
  have hfirst : ‖-D + -Dᴴ‖ ≤ ‖D‖ + ‖D‖ := by
    simpa only [norm_neg, hnormStar] using norm_add_le (-D) (-Dᴴ)
  have hproduct : ‖D * Dᴴ‖ ≤ ‖D‖ * ‖D‖ := by
    simpa only [hnormStar] using norm_mul_le D Dᴴ
  rw [show roundedReferenceMatrixAtGeneration l abar hS =
      q⁻¹ * (specBound ((symmPart abar)⁻¹) • symmPart abar) *
        matTranspose q⁻¹ from rfl, hform]
  calc
    ‖(-D + -Dᴴ) + D * Dᴴ‖ ≤
        ‖-D + -Dᴴ‖ + ‖D * Dᴴ‖ := norm_add_le _ _
    _ ≤ (‖D‖ + ‖D‖) + ‖D‖ * ‖D‖ :=
      add_le_add hfirst hproduct
    _ ≤ eps := by
      nlinarith only [hDnorm, norm_nonneg D, heps0, hepsHalf,
        sq_nonneg ((101 / 400 : ℝ) * eps - ‖D‖)]

private theorem vecDot_matVecMul_le_of_matrix_le
    {d : ℕ} {A B : Mat d} (h : A ≤ B) (x : Vec d) :
    vecDot x (matVecMul A x) ≤ vecDot x (matVecMul B x) := by
  have hdiff : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hx := hdiff.dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, dotProduct_sub] at hx
  change x ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ B *ᵥ x
  exact sub_nonneg.mp (by simpa only [star_trivial] using hx)

private theorem vecDot_matVecMul_smul_one
    {d : ℕ} (c : ℝ) (x : Vec d) :
    vecDot x (matVecMul (c • (1 : Mat d)) x) = c * vecNormSq x := by
  have hone : matVecMul (1 : Mat d) x = x := by
    funext i
    simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  rw [smul_matVecMul, hone, vecDot_smul_right]
  rfl

private theorem scalar_mul_vecNormSq_le_of_smul_one_le
    {d : ℕ} {c : ℝ} {A : Mat d} (h : c • (1 : Mat d) ≤ A)
    (x : Vec d) : c * vecNormSq x ≤ vecDot x (matVecMul A x) := by
  have hquad := vecDot_matVecMul_le_of_matrix_le h x
  rw [vecDot_matVecMul_smul_one] at hquad
  exact hquad

private theorem isEllipticMatrix_of_posDef_norm_sub_one_le
    {d : ℕ} {A : Mat d} {eps : ℝ} (heps0 : 0 < eps)
    (hepsHalf : eps ≤ 1 / 2) (hA : A.PosDef) (
      hnorm : ‖A - 1‖ ≤ eps) :
    IsEllipticMatrix (1 - eps) (1 + eps) A := by
  have hdiffHerm : (A - 1)ᴴ = A - 1 :=
    Matrix.IsHermitian.eq (hA.isHermitian.sub Matrix.PosSemidef.one.isHermitian)
  obtain ⟨hupperDiff, hlowerDiff⟩ := PortableHistory.sandwich_of_norm_le hdiffHerm hnorm
  have hlower : (1 - eps) • (1 : Mat d) ≤ A := by
    calc
      (1 - eps) • (1 : Mat d) = (-eps) • (1 : Mat d) + 1 := by module
      _ ≤ (A - 1) + 1 := by
        simpa only [add_comm] using add_le_add_right hlowerDiff 1
      _ = A := by abel
  have hupper : A ≤ (1 + eps) • (1 : Mat d) := by
    calc
      A = (A - 1) + 1 := by abel
      _ ≤ eps • (1 : Mat d) + 1 := by
        simpa only [add_comm] using add_le_add_right hupperDiff 1
      _ = (1 + eps) • (1 : Mat d) := by module
  have hlowerPos : 0 < 1 - eps := by linarith only [hepsHalf]
  have hupperPos : 0 < 1 + eps := by linarith only [heps0]
  have hupperPD : ((1 + eps) • (1 : Mat d)).PosDef :=
    Matrix.PosDef.one.smul hupperPos
  have hinvOrder : (1 + eps)⁻¹ • (1 : Mat d) ≤ A⁻¹ := by
    have h := inv_le_inv_of_le hA hupperPD hupper
    rw [inv_smul_of_isUnit hupperPos.ne'
      (by simp : IsUnit (1 : Mat d).det), inv_one] at h
    exact h
  refine ⟨hlowerPos, ?_, ?_, ?_⟩
  · linarith only [heps0]
  · intro xi
    exact scalar_mul_vecNormSq_le_of_smul_one_le hlower xi
  · intro xi
    exact scalar_mul_vecNormSq_le_of_smul_one_le hinvOrder xi

/-- Every positive tolerance at most one half is attained by one rounding
generation, uniformly over all positive-definite reference matrices. -/
theorem exists_printOrderRoundedReferenceConstructorAtTolerance
    (d : ℕ) [NeZero d] {eps : ℝ} (heps0 : 0 < eps)
    (hepsHalf : eps ≤ 1 / 2) :
    PrintOrderRoundedReferenceConstructorAtTolerance d eps := by
  obtain ⟨l, hl, hround⟩ :=
    exists_admissible_generation_with_rounding_error d
      (show 0 < eps / 4 by positivity)
  refine ⟨l, hl, ?_⟩
  intro abar hS
  have hpos := rounded_reference_posDef_at_generation hl abar hS
  have hnorm := norm_rounded_reference_sub_one_le hl heps0 hepsHalf
    hround abar hS
  exact ⟨hpos,
    isEllipticMatrix_of_posDef_norm_sub_one_le heps0 hepsHalf hpos hnorm,
    hnorm⟩

end

end HighContrast
end HCPolySupport
