/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedWeakTransport
public import LeanPool.HighContrastHomogenization.Provider.Response.ReferenceWeakBridge
public import LeanPool.HighContrastHomogenization.Provider.Selection.RoundedHops

/-!
# High-contrast homogenization: Provider.Response.AdaptedWeakProduct

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Separate affine distortions for the weak product

The gradient and flux slots of the reference-cube div--curl estimate are
transported separately.  For a rounded grid the scalar normalization of the
metric square root appears reciprocally in the two slots and cancels in their
product.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ} [NeZero d]

private theorem product_specBound_pos {m : Mat d} (hm : m.PosDef) :
    0 < specBound m := by
  rw [specBound_eq_norm hm.posSemidef]
  exact norm_pos_iff.mpr hm.isUnit.ne_zero

private theorem product_normalizedRoot_posDef {m : Mat d} (hm : m.PosDef) :
    (Selection.normalizedRoot m).PosDef := by
  refine (posDef_matSqrt hm).smul (Real.sqrt_pos.mpr ?_)
  exact product_specBound_pos hm.inv

private theorem product_normalizedRoot_inv_norm_le_one {m : Mat d}
    (hm : m.PosDef) :
    ‖(Selection.normalizedRoot m)⁻¹‖ ≤ 1 := by
  have hL := product_normalizedRoot_posDef hm
  have horder : (1 : Mat d) ≤ Selection.normalizedRoot m := by
    simpa only [Selection.normalizedRoot_eq] using Recurrence.one_le_normalized_matSqrt hm
  have hinv : (Selection.normalizedRoot m)⁻¹ ≤ (1 : Mat d) := by
    simpa using inv_le_inv_of_le Matrix.PosDef.one hL horder
  have hnorm := norm_le_norm_of_le hL.inv.posSemidef Matrix.PosSemidef.one hinv
  simpa using hnorm

private theorem product_rounded_error_norm {l : ℤ} {m : Mat d}
    (hm : m.PosDef) :
    ‖roundedGrid l m - Selection.normalizedRoot m‖ ≤ (d : ℝ) * (3 : ℝ) ^ (-l) := by
  set E : Mat d := roundedGrid l m - Selection.normalizedRoot m with hE
  set delta : ℝ := (3 : ℝ) ^ (-l) with hdelta
  set c : ℝ := (d : ℝ) * delta with hc
  have hentry : ∀ i k, |E i k| ≤ delta := by
    intro i k
    obtain ⟨hlo, hhi⟩ := Recurrence.roundedGrid_sub_normalized_matSqrt_mem l m i k
    rw [hE, Selection.normalizedRoot, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, abs_of_nonneg hlo]
    exact hhi
  have hsymm : Eᴴ = E := by
    rw [Matrix.IsHermitian.eq (Matrix.IsHermitian.sub
      (by
        refine Matrix.IsHermitian.ext fun i k ↦ ?_
        simpa using Recurrence.roundedGrid_symm l hm.posSemidef i k)
      (product_normalizedRoot_posDef hm).isHermitian)]
  have htrans : Eᵀ = E := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hsymm
  have hquadLo : ∀ x : Fin d → ℝ, -c * (x ⬝ᵥ x) ≤ x ⬝ᵥ E *ᵥ x := by
    intro x
    have h := Recurrence.neg_le_dotProduct_mulVec_of_abs_entry_le hentry x
    rw [hc]
    simpa only [dotProduct, star_trivial, neg_mul, mul_assoc, mul_left_comm, mul_comm]
      using h
  have hquadHi : ∀ x : Fin d → ℝ, x ⬝ᵥ E *ᵥ x ≤ c * (x ⬝ᵥ x) := by
    intro x
    have h := Recurrence.neg_le_dotProduct_mulVec_of_abs_entry_le
      (E := -E) (fun i k ↦ by simpa using hentry i k) x
    rw [Matrix.neg_mulVec, dotProduct_neg, dotProduct] at h
    have h' := neg_le_neg_iff.mp h
    rw [dotProduct, hc]
    simpa only [dotProduct, star_trivial, pow_two, mul_comm] using h'
  have hhi : E ≤ c • (1 : Mat d) := by
    rw [Matrix.le_iff]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x ↦ ?_
    · simp [Matrix.IsHermitian, htrans]
    · rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_smul]
      simp only [star_trivial, smul_eq_mul]
      linarith only [hquadHi x]
  have hlo : (-c) • (1 : Mat d) ≤ E := by
    rw [Matrix.le_iff]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x ↦ ?_
    · simp [Matrix.IsHermitian, htrans]
    · rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_smul]
      simp only [star_trivial, smul_eq_mul]
      linarith only [hquadLo x]
  exact PortableHistory.norm_le_of_sandwich hsymm
    (mul_nonneg (Nat.cast_nonneg _) (by positivity)) hhi hlo

private theorem product_rounded_error_norm_le {l : ℤ}
    (hl : (kZero d : ℤ) ≤ l) {m : Mat d} (hm : m.PosDef) :
    ‖roundedGrid l m - Selection.normalizedRoot m‖ ≤ 1 / 101 := by
  refine (product_rounded_error_norm hm).trans ?_
  have hpow : (3 : ℝ) ^ (-l) ≤ (3 : ℝ) ^ (-(kZero d : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  exact (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)).trans (kZero_spec d)

private theorem product_normalizedRoot_inv_mul_roundedGrid_le {l : ℤ}
    (hl : (kZero d : ℤ) ≤ l) {m : Mat d} (hm : m.PosDef) :
    ‖(Selection.normalizedRoot m)⁻¹ * roundedGrid l m‖ ≤ 102 / 101 := by
  let L := Selection.normalizedRoot m
  let E := roundedGrid l m - L
  have hfac : L⁻¹ * roundedGrid l m = 1 + L⁻¹ * E := by
    have hunit : IsUnit L.det := isUnit_det_of_posDef (product_normalizedRoot_posDef hm)
    have hsplit : roundedGrid l m = L + E := by simp [E]
    rw [hsplit, Matrix.mul_add, Matrix.nonsing_inv_mul _ hunit]
  have hE := (norm_mul_le L⁻¹ E).trans
    (mul_le_mul (product_normalizedRoot_inv_norm_le_one hm)
      (product_rounded_error_norm_le hl hm) (norm_nonneg _) zero_le_one)
  rw [hfac]
  calc
    ‖1 + L⁻¹ * E‖ ≤ 1 + ‖L⁻¹ * E‖ := by simpa using norm_add_le (1 : Mat d) (L⁻¹ * E)
    _ ≤ 102 / 101 := by linarith only [hE]

private theorem product_roundedGrid_inv_mul_normalizedRoot_le {l : ℤ}
    (hl : (kZero d : ℤ) ≤ l) {m : Mat d} (hm : m.PosDef) :
    ‖(roundedGrid l m)⁻¹ * Selection.normalizedRoot m‖ ≤ 101 / 100 := by
  let L := Selection.normalizedRoot m
  let E := roundedGrid l m - L
  let B := L⁻¹ * E
  have hB := (norm_mul_le L⁻¹ E).trans
    (mul_le_mul (product_normalizedRoot_inv_norm_le_one hm)
      (product_rounded_error_norm_le hl hm) (norm_nonneg _) zero_le_one)
  have hBlt : ‖-B‖ < 1 := by rw [norm_neg]; linarith only [hB]
  have hfac : L⁻¹ * roundedGrid l m = 1 + B := by
    have hunit : IsUnit L.det := isUnit_det_of_posDef (product_normalizedRoot_posDef hm)
    have hsplit : roundedGrid l m = L + E := by simp [E]
    rw [hsplit, Matrix.mul_add, Matrix.nonsing_inv_mul _ hunit]
  have hinv : (L⁻¹ * roundedGrid l m)⁻¹ = (roundedGrid l m)⁻¹ * L := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _
      (isUnit_det_of_posDef (product_normalizedRoot_posDef hm))]
  have hgeom := tsum_geometric_le_of_norm_lt_one (-B) hBlt
  rw [geom_series_eq_inverse (-B) hBlt, sub_neg_eq_add, norm_neg, norm_one,
    sub_self, zero_add, ← hfac, ← Matrix.nonsing_inv_eq_ringInverse, hinv] at hgeom
  refine hgeom.trans ?_
  have hB' : ‖B‖ ≤ 1 / 101 := by simpa only [B, one_mul] using hB
  rw [inv_le_iff_one_le_mul₀' (by linarith only [hB'])]
  linarith only [hB']

/-- The product of the two metric-slot Frobenius distortions is bounded only
by the dimension when the grid is the rounded normalized metric root. -/
theorem roundedGrid_metricFrobenius_product_le {l : ℤ}
    (hl : (kZero d : ℤ) ≤ l) {m : Mat d} (hm : m.PosDef) :
    Real.sqrt (matrixFrobeniusNormSq
        (matTranspose (roundedGrid l m) * (matSqrt m)⁻¹)) *
      Real.sqrt (matrixFrobeniusNormSq
        ((roundedGrid l m)⁻¹ * matSqrt m)) ≤
      (51 / 50 : ℝ) * (d : ℝ) ^ 2 := by
  let q := roundedGrid l m
  let S := matSqrt m
  let L := Selection.normalizedRoot m
  let alpha := Real.sqrt (specBound m⁻¹)
  have halpha : 0 < alpha := Real.sqrt_pos.mpr (product_specBound_pos hm.inv)
  have hS : S.PosDef := posDef_matSqrt hm
  have hSunit : IsUnit S.det := isUnit_det_of_posDef hS
  have hL : L = alpha • S := by rfl
  have hqSymm : qᵀ = q := by
    apply Matrix.ext
    intro i k
    simpa [q] using Recurrence.roundedGrid_symm l hm.posSemidef i k
  have hqMatTranspose : matTranspose q = q := by
    simpa [matTranspose] using hqSymm
  have hSSymm : Sᵀ = S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using! hS.isHermitian
  have hAform : matTranspose q * S⁻¹ = alpha • (L⁻¹ * q)ᵀ := by
    rw [hqMatTranspose, hL, inv_smul_of_isUnit halpha.ne' hSunit,
      Matrix.transpose_mul,
      Matrix.transpose_smul, Matrix.transpose_nonsing_inv, hSSymm, hqSymm,
      Matrix.mul_smul, smul_smul, mul_inv_cancel₀ halpha.ne', one_smul]
  have hBform : q⁻¹ * S = alpha⁻¹ • (q⁻¹ * L) := by
    rw [hL, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ halpha.ne', one_smul]
  have hnormA : ‖matTranspose q * S⁻¹‖ = alpha * ‖L⁻¹ * q‖ := by
    have hnormT : ‖(L⁻¹ * q)ᵀ‖ = ‖L⁻¹ * q‖ := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.l2_opNorm_conjTranspose (L⁻¹ * q)
    rw [hAform, norm_smul, Real.norm_eq_abs, abs_of_pos halpha, hnormT]
  have hnormB : ‖q⁻¹ * S‖ = alpha⁻¹ * ‖q⁻¹ * L‖ := by
    rw [hBform, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr halpha)]
  have hop : ‖matTranspose q * S⁻¹‖ * ‖q⁻¹ * S‖ ≤ 51 / 50 := by
    rw [hnormA, hnormB]
    calc
      (alpha * ‖L⁻¹ * q‖) * (alpha⁻¹ * ‖q⁻¹ * L‖) =
          ‖L⁻¹ * q‖ * ‖q⁻¹ * L‖ := by
            rw [show alpha * ‖L⁻¹ * q‖ * (alpha⁻¹ * ‖q⁻¹ * L‖) =
              (alpha * alpha⁻¹) * (‖L⁻¹ * q‖ * ‖q⁻¹ * L‖) by ring,
              mul_inv_cancel₀ halpha.ne', one_mul]
      _ ≤ (102 / 101 : ℝ) * (101 / 100 : ℝ) :=
        mul_le_mul (product_normalizedRoot_inv_mul_roundedGrid_le hl hm)
          (product_roundedGrid_inv_mul_normalizedRoot_le hl hm)
          (norm_nonneg _) (by positivity)
      _ = 51 / 50 := by ring
  change matrixFrobeniusNorm (matTranspose q * S⁻¹) *
      matrixFrobeniusNorm (q⁻¹ * S) ≤ _
  have hAf := matrixFrobeniusNorm_le_dim_mul_matrixOperatorNorm
    (matTranspose q * S⁻¹)
  have hBf := matrixFrobeniusNorm_le_dim_mul_matrixOperatorNorm (q⁻¹ * S)
  rw [matrixOperatorNorm_eq_l2_opNorm] at hAf hBf
  calc
    matrixFrobeniusNorm (matTranspose q * S⁻¹) * matrixFrobeniusNorm (q⁻¹ * S) ≤
        ((d : ℝ) * ‖matTranspose q * S⁻¹‖) * ((d : ℝ) * ‖q⁻¹ * S‖) :=
      mul_le_mul hAf hBf (matrixFrobeniusNorm_nonneg _) (by positivity)
    _ = (d : ℝ) ^ 2 * (‖matTranspose q * S⁻¹‖ * ‖q⁻¹ * S‖) := by ring
    _ ≤ (d : ℝ) ^ 2 * (51 / 50 : ℝ) :=
      mul_le_mul_of_nonneg_left hop (sq_nonneg _)
    _ = (51 / 50 : ℝ) * (d : ℝ) ^ 2 := by ring

omit [NeZero d] in
/-- The gradient partial seminorm uses only the first affine distortion. -/
theorem ofReal_partialSeminorm_metricPullback_fst_le_separate
    {q S : Mat d} (hq : q.PosDef) (hS : S.PosDef)
    (t : ℤ) (s : ℝ) (N : ℕ) (F : Vec d → BlockVec d)
    (hF₁ : MemVectorL2 (adaptedCell q t)
      (fun x ↦ matVecMul S (F x).1))
    (hF₂ : MemVectorL2 (adaptedCell q t)
      (fun x ↦ matVecMul S⁻¹ (F x).2)) :
    ENNReal.ofReal (cubeBesovNegativeVectorPartialSeminorm
        (originCube d t) s N
        (fun y ↦ matVecMul (matTranspose q) (F (matVecMul q y)).1)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        ENNReal.ofReal (Real.sqrt
          (matrixFrobeniusNormSq (matTranspose q * S⁻¹))) *
        adaptedWeakSeminorm q t s
          (fun x ↦ ((matVecMul S (F x).1,
            matVecMul S⁻¹ (F x).2) : BlockVec d)) := by
  let H : Vec d → BlockVec d := fun x ↦
    ((matVecMul S (F x).1, matVecMul S⁻¹ (F x).2) : BlockVec d)
  let G : Vec d → BlockVec d := fun y ↦
    ((matVecMul (matTranspose q) (F (matVecMul q y)).1, 0) : BlockVec d)
  have hSdet : IsUnit S.det := isUnit_det_of_posDef hS
  have hcancel : (matTranspose q * S⁻¹) * S = matTranspose q := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul S hSdet, Matrix.mul_one]
  have htransport := adaptedWeakSeminorm_affinePullback_le hq
    (matTranspose q * S⁻¹) (0 : Mat d) t s H hF₁ hF₂
  have hzero : matrixFrobeniusNormSq (0 : Mat d) = 0 := by
    simp [matrixFrobeniusNormSq]
  rw [hzero, max_eq_left (matrixFrobeniusNormSq_nonneg _)] at htransport
  have htransport' : adaptedWeakSeminorm (1 : Mat d) t s G ≤
      ENNReal.ofReal (Real.sqrt
        (matrixFrobeniusNormSq (matTranspose q * S⁻¹))) *
        adaptedWeakSeminorm q t s H := by
    simpa [G, H, matVecMul_mul, hcancel, zero_matVecMul] using htransport
  have href :=
    ofReal_partialSeminorm_fst_le_normalized_adaptedWeakSeminorm t s N G
  calc
    ENNReal.ofReal (cubeBesovNegativeVectorPartialSeminorm
        (originCube d t) s N
        (fun y ↦ matVecMul (matTranspose q) (F (matVecMul q y)).1)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        adaptedWeakSeminorm (1 : Mat d) t s G := by
          simpa [G] using href
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        (ENNReal.ofReal (Real.sqrt
          (matrixFrobeniusNormSq (matTranspose q * S⁻¹))) *
          adaptedWeakSeminorm q t s H) := mul_le_mul_right htransport' _
    _ = _ := by simp only [H]; ac_rfl

omit [NeZero d] in
/-- The flux partial seminorm uses only the second affine distortion. -/
theorem ofReal_partialSeminorm_metricPullback_snd_le_separate
    {q S : Mat d} (hq : q.PosDef) (hS : S.PosDef)
    (t : ℤ) (s : ℝ) (N : ℕ) (F : Vec d → BlockVec d)
    (hF₁ : MemVectorL2 (adaptedCell q t)
      (fun x ↦ matVecMul S (F x).1))
    (hF₂ : MemVectorL2 (adaptedCell q t)
      (fun x ↦ matVecMul S⁻¹ (F x).2)) :
    ENNReal.ofReal (cubeBesovNegativeVectorPartialSeminorm
        (originCube d t) s N
        (fun y ↦ matVecMul q⁻¹ (F (matVecMul q y)).2)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        ENNReal.ofReal (Real.sqrt (matrixFrobeniusNormSq (q⁻¹ * S))) *
        adaptedWeakSeminorm q t s
          (fun x ↦ ((matVecMul S (F x).1,
            matVecMul S⁻¹ (F x).2) : BlockVec d)) := by
  let H : Vec d → BlockVec d := fun x ↦
    ((matVecMul S (F x).1, matVecMul S⁻¹ (F x).2) : BlockVec d)
  let G : Vec d → BlockVec d := fun y ↦
    ((0, matVecMul q⁻¹ (F (matVecMul q y)).2) : BlockVec d)
  have hSdet : IsUnit S.det := isUnit_det_of_posDef hS
  have hcancel : (q⁻¹ * S) * S⁻¹ = q⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv S hSdet, Matrix.mul_one]
  have htransport := adaptedWeakSeminorm_affinePullback_le hq
    (0 : Mat d) (q⁻¹ * S) t s H hF₁ hF₂
  have hzero : matrixFrobeniusNormSq (0 : Mat d) = 0 := by
    simp [matrixFrobeniusNormSq]
  rw [hzero, max_eq_right (matrixFrobeniusNormSq_nonneg _)] at htransport
  have htransport' : adaptedWeakSeminorm (1 : Mat d) t s G ≤
      ENNReal.ofReal (Real.sqrt (matrixFrobeniusNormSq (q⁻¹ * S))) *
        adaptedWeakSeminorm q t s H := by
    simpa [G, H, matVecMul_mul, hcancel, zero_matVecMul] using htransport
  have href :=
    ofReal_partialSeminorm_snd_le_normalized_adaptedWeakSeminorm t s N G
  calc
    ENNReal.ofReal (cubeBesovNegativeVectorPartialSeminorm
        (originCube d t) s N
        (fun y ↦ matVecMul q⁻¹ (F (matVecMul q y)).2)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        adaptedWeakSeminorm (1 : Mat d) t s G := by
          simpa [G] using href
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        (ENNReal.ofReal (Real.sqrt (matrixFrobeniusNormSq (q⁻¹ * S))) *
          adaptedWeakSeminorm q t s H) := mul_le_mul_right htransport' _
    _ = _ := by simp only [H]; ac_rfl

end

end HCPolySupport.HighContrast.Response
