/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastGoodQuads
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHattedCarrier
public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationQuadratic
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCalibrationAlgebra

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSchurExtraction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Schur data extraction

A doubled block in Schur form has its intrinsic Schur data equal to the
form's data, and the good-quadratics norm gap converts into the
`σ*`-quadratic of the skew difference against the `σ`-form.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem norm_toLp_sq' (x : Vec d) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2 = x ⬝ᵥ x := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [dotProduct, Real.norm_eq_abs, pow_two]

/-- **Schur data extraction.** -/
theorem schurData_of_form {H : BlockMat d} {S SStar K : Mat d}
    (hStar : SStar.PosDef)
    (hform : toFullBlockMat H = schurBlock S SStar K) :
    H.lowerRight = SStar⁻¹ ∧ schurSigmaStar H = SStar ∧
      schurSkew H = K ∧ schurSigma H = S := by
  have hlowerRight : H.lowerRight = SStar⁻¹ := by
    have h : H.lowerRight = (toFullBlockMat H).toBlocks₂₂ := rfl
    rw [h, hform, toBlocks₂₂_schurBlock]
  have hstar : schurSigmaStar H = SStar := by
    rw [schurSigmaStar, hlowerRight,
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hStar)]
  have hskew : schurSkew H = K := by
    have hlowerLeft : H.lowerLeft = -(SStar⁻¹ * K) := by
      have h : H.lowerLeft = (toFullBlockMat H).toBlocks₂₁ := rfl
      rw [h, hform, toBlocks₂₁_schurBlock]
    rw [schurSkew, hlowerRight, hlowerLeft]
    rw [show SStar⁻¹⁻¹ = SStar from
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hStar)]
    rw [Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hStar),
      Matrix.one_mul, neg_neg]
  have hsigma : schurSigma H = S := by
    have hupperLeft : H.upperLeft = S + Kᴴ * SStar⁻¹ * K := by
      have h : H.upperLeft = (toFullBlockMat H).toBlocks₁₁ := rfl
      rw [h, hform, toBlocks₁₁_schurBlock]
    rw [schurSigma, hupperLeft, hlowerRight, hskew,
      ← conjTranspose_eq_matTranspose]
    abel
  exact ⟨hlowerRight, hstar, hskew, hsigma⟩

/-- The inverse of a positive scalar multiple. -/
theorem inv_smul_posDef {A : Mat d} (hA : A.PosDef) {c : ℝ} (hc : 0 < c) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef hA),
    inv_mul_cancel₀ (ne_of_gt hc), one_smul]

/-- A spectral bound on the mixed-normalized matrix gives the quadratic
comparison of the images. -/
theorem quad_le_of_norm_normalized_le {W Sp SStarp : Mat d}
    (hSp : Sp.PosDef) (hStarp : SStarp.PosDef) {c : ℝ}
    (hnorm : ‖matSqrt SStarp⁻¹ * W * matSqrt Sp⁻¹‖ ≤ c)
    (x : Vec d) :
    (W *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ (W *ᵥ x) ≤ c ^ 2 * (x ⬝ᵥ Sp *ᵥ x) := by
  have hc0 : 0 ≤ c := le_trans (norm_nonneg _) hnorm
  set M : Mat d := matSqrt SStarp⁻¹ * W * matSqrt Sp⁻¹ with hMdef
  set u : Vec d := matSqrt Sp *ᵥ x with hudef
  have hcancel : matSqrt Sp⁻¹ * matSqrt Sp = 1 := by
    rw [matSqrt_inv hSp]
    exact Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt hSp))
  have hMu : M *ᵥ u = matSqrt SStarp⁻¹ *ᵥ (W *ᵥ x) := by
    rw [hMdef, hudef, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Matrix.mul_assoc, hcancel, Matrix.mul_one,
      ← Matrix.mulVec_mulVec]
  -- the two euclidean norms
  have hquadMu : (M *ᵥ u) ⬝ᵥ (M *ᵥ u) =
      (W *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ (W *ᵥ x) := by
    rw [hMu]
    have hherm : (matSqrt SStarp⁻¹)ᴴ = matSqrt SStarp⁻¹ :=
      (matSqrt_spec hStarp.inv.posSemidef).1.isHermitian
    have hNN : matSqrt SStarp⁻¹ * matSqrt SStarp⁻¹ = SStarp⁻¹ :=
      (matSqrt_spec hStarp.inv.posSemidef).2
    calc (matSqrt SStarp⁻¹ *ᵥ (W *ᵥ x)) ⬝ᵥ
        (matSqrt SStarp⁻¹ *ᵥ (W *ᵥ x)) =
        (W *ᵥ x) ⬝ᵥ matSqrt SStarp⁻¹ *ᵥ (matSqrt SStarp⁻¹ *ᵥ (W *ᵥ x)) :=
          mulVec_dotProduct_symm hherm _ _
      _ = (W *ᵥ x) ⬝ᵥ (matSqrt SStarp⁻¹ * matSqrt SStarp⁻¹) *ᵥ (W *ᵥ x) := by
          rw [Matrix.mulVec_mulVec]
      _ = (W *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ (W *ᵥ x) := by rw [hNN]
  have hquadu : u ⬝ᵥ u = x ⬝ᵥ Sp *ᵥ x := by
    rw [hudef]
    have hherm : (matSqrt Sp)ᴴ = matSqrt Sp :=
      (matSqrt_spec hSp.posSemidef).1.isHermitian
    have hNN : matSqrt Sp * matSqrt Sp = Sp :=
      (matSqrt_spec hSp.posSemidef).2
    calc (matSqrt Sp *ᵥ x) ⬝ᵥ (matSqrt Sp *ᵥ x) =
        x ⬝ᵥ matSqrt Sp *ᵥ (matSqrt Sp *ᵥ x) :=
          mulVec_dotProduct_symm hherm _ _
      _ = x ⬝ᵥ (matSqrt Sp * matSqrt Sp) *ᵥ x := by
          rw [Matrix.mulVec_mulVec]
      _ = x ⬝ᵥ Sp *ᵥ x := by rw [hNN]
  -- the operator bound on euclidean vectors
  have hop : (M *ᵥ u) ⬝ᵥ (M *ᵥ u) ≤ c ^ 2 * (u ⬝ᵥ u) := by
    have h1 : ‖(WithLp.toLp 2 (M *ᵥ u) : EuclideanSpace ℝ (Fin d))‖ ≤
        ‖M‖ * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ :=
      Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 u)
    have hnormMu : ‖(WithLp.toLp 2 (M *ᵥ u) : EuclideanSpace ℝ (Fin d))‖ ≤
        c * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ :=
      le_trans h1 (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
    have hsq := mul_self_le_mul_self (norm_nonneg _) hnormMu
    have hlhs : ‖(WithLp.toLp 2 (M *ᵥ u) : EuclideanSpace ℝ (Fin d))‖ *
        ‖(WithLp.toLp 2 (M *ᵥ u) : EuclideanSpace ℝ (Fin d))‖ =
        (M *ᵥ u) ⬝ᵥ (M *ᵥ u) := by
      rw [← pow_two]
      exact norm_toLp_sq' (M *ᵥ u)
    have hrhs : c * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ *
        (c * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖) =
        c ^ 2 * (u ⬝ᵥ u) := by
      have hu2 : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ ^ 2 =
          u ⬝ᵥ u := norm_toLp_sq' u
      calc c * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ *
          (c * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖) =
          c ^ 2 * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
            ring
        _ = c ^ 2 * (u ⬝ᵥ u) := by rw [hu2]
    rw [hlhs, hrhs] at hsq
    exact hsq
  calc (W *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ (W *ᵥ x) = (M *ᵥ u) ⬝ᵥ (M *ᵥ u) :=
      hquadMu.symm
    _ ≤ c ^ 2 * (u ⬝ᵥ u) := hop
    _ = c ^ 2 * (x ⬝ᵥ Sp *ᵥ x) := by rw [hquadu]

end

end HCPolySupport.HighContrast.Quenched
