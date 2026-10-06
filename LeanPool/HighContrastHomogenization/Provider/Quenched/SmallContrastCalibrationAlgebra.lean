/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseOrder
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.TraceGap
public import LeanPool.HighContrastHomogenization.Geometry.GeometricMeanToolkit
public import LeanPool.HighContrastHomogenization.Provider.SourceControl.SchurHelpers

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCalibrationAlgebra

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Calibration algebra for the centering estimate

The response metric is the geometric mean `m = b # S₊` of the corrected block
and the lower Schur datum.  This file records the finite-dimensional facts the
centering estimate consumes: a positive semidefinite matrix is dominated by
its trace, the calibrated `S₊`-energies of the two loads are the quadratics of
the normalized corrected block `B = m^{-1/2} b m^{-1/2}` and of its inverse,
and `B` dominates the identity.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Dot-product transport -/

/-- Transport of a symmetric factor across the dot product. -/
theorem mulVec_dotProduct_symm {C : Mat d} (hC : Cᴴ = C) (x w : Vec d) :
    (C *ᵥ x) ⬝ᵥ w = x ⬝ᵥ C *ᵥ w := by
  have hCt : Cᵀ = C := by
    rw [← conjTranspose_eq_transpose', hC]
  calc
    (C *ᵥ x) ⬝ᵥ w = w ⬝ᵥ C *ᵥ x := dotProduct_comm _ _
    _ = Cᵀ *ᵥ w ⬝ᵥ x := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    _ = x ⬝ᵥ Cᵀ *ᵥ w := dotProduct_comm _ _
    _ = x ⬝ᵥ C *ᵥ w := by rw [hCt]

/-- The dot square of a vector is nonnegative. -/
theorem dotProduct_self_nonneg' (x : Vec d) : 0 ≤ x ⬝ᵥ x := by
  simp only [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- Cauchy–Schwarz for the dot product. -/
theorem dotProduct_sq_le (x y : Vec d) :
    (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hx : x ⬝ᵥ x = ∑ i, x i ^ 2 := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => (pow_two (x i)).symm
  have hy : y ⬝ᵥ y = ∑ i, y i ^ 2 := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => (pow_two (y i)).symm
  rw [hx, hy]
  simpa only [dotProduct] using h

/-! ## A positive semidefinite matrix is dominated by its trace -/

/-- The rank-one square applied to a vector. -/
theorem vecMulVec_mulVec_self (x y : Vec d) :
    Matrix.vecMulVec x x *ᵥ y = (x ⬝ᵥ y) • x := by
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The rank-one square is positive semidefinite. -/
theorem posSemidef_vecMulVec_self (x : Vec d) :
    (Matrix.vecMulVec x x).PosSemidef := by
  have hherm : (Matrix.vecMulVec x x).IsHermitian := by
    show (Matrix.vecMulVec x x)ᴴ = Matrix.vecMulVec x x
    funext i j
    simp [Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun y => ?_
  rw [vecMulVec_mulVec_self, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  exact mul_self_nonneg _

/-- The rank-one square is dominated by the vector energy. -/
theorem vecMulVec_le_smul_one (x : Vec d) :
    Matrix.vecMulVec x x ≤ (x ⬝ᵥ x) • (1 : Mat d) := by
  refine Initialization.le_of_dotProduct_mulVec_le
    (posSemidef_vecMulVec_self x).isHermitian ?_ fun y => ?_
  · show ((x ⬝ᵥ x) • (1 : Mat d))ᴴ = (x ⬝ᵥ x) • (1 : Mat d)
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_one]
  · rw [vecMulVec_mulVec_self, dotProduct_smul, smul_eq_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    calc
      (x ⬝ᵥ y) * (y ⬝ᵥ x) = (x ⬝ᵥ y) ^ 2 := by
        rw [dotProduct_comm y x]
        ring
      _ ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := dotProduct_sq_le x y

/-- The trace against a rank-one square is the quadratic form. -/
theorem trace_mul_vecMulVec (T : Mat d) (x : Vec d) :
    Matrix.trace (T * Matrix.vecMulVec x x) = x ⬝ᵥ T *ᵥ x := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **A positive semidefinite quadratic form is dominated by the trace.** -/
theorem psd_quad_le_trace {T : Mat d} (hT : T.PosSemidef) (x : Vec d) :
    x ⬝ᵥ T *ᵥ x ≤ Matrix.trace T * (x ⬝ᵥ x) := by
  calc
    x ⬝ᵥ T *ᵥ x = Matrix.trace (T * Matrix.vecMulVec x x) :=
      (trace_mul_vecMulVec T x).symm
    _ ≤ ‖Matrix.vecMulVec x x‖ * Matrix.trace T :=
      PortableHistory.trace_mul_le_norm_mul_trace hT (posSemidef_vecMulVec_self x)
    _ ≤ (x ⬝ᵥ x) * Matrix.trace T := by
      have hnorm : ‖Matrix.vecMulVec x x‖ ≤ x ⬝ᵥ x :=
        norm_le_of_le_smul_one (posSemidef_vecMulVec_self x)
          (dotProduct_self_nonneg' x) (vecMulVec_le_smul_one x)
      exact mul_le_mul_of_nonneg_right hnorm hT.trace_nonneg
    _ = Matrix.trace T * (x ⬝ᵥ x) := mul_comm _ _

/-- **A positive semidefinite matrix is dominated by any scalar bound on its
quadratic form.** -/
theorem psd_le_smul_one {T : Mat d} (hT : T.PosSemidef) {c : ℝ}
    (hc : ∀ x : Vec d, x ⬝ᵥ T *ᵥ x ≤ c * (x ⬝ᵥ x)) :
    T ≤ c • (1 : Mat d) := by
  refine Initialization.le_of_dotProduct_mulVec_le hT.isHermitian ?_ fun x => ?_
  · show (c • (1 : Mat d))ᴴ = c • (1 : Mat d)
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_one]
  · rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    exact hc x

/-- The square of a positive semidefinite matrix below `c·1` is below `c`
times the matrix. -/
theorem psd_sq_le_smul {T : Mat d} (hT : T.PosSemidef) {c : ℝ}
    (hc : T ≤ c • (1 : Mat d)) :
    T * T ≤ c • T := by
  have hroot : matSqrt T * matSqrt T = T := (matSqrt_spec hT).2
  have hrootHerm : (matSqrt T)ᴴ = matSqrt T := conjTranspose_matSqrt hT
  have hconj := conj_le_conj (matSqrt T) hc
  rw [hrootHerm] at hconj
  have hTT : matSqrt T * T * matSqrt T = T * T := by
    calc
      matSqrt T * T * matSqrt T =
          matSqrt T * (matSqrt T * matSqrt T) * matSqrt T := by rw [hroot]
      _ = (matSqrt T * matSqrt T) * (matSqrt T * matSqrt T) := by
        noncomm_ring
      _ = T * T := by rw [hroot]
  have hrhs : matSqrt T * (c • (1 : Mat d)) * matSqrt T = c • T := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hroot]
  calc
    T * T = matSqrt T * T * matSqrt T := hTT.symm
    _ ≤ matSqrt T * (c • (1 : Mat d)) * matSqrt T := hconj
    _ = c • T := hrhs

/-! ## The normalized corrected block -/

/-- The normalized corrected block `B = m^{-1/2} b m^{-1/2}` at the metric
`m = b # S₊`. -/
@[expose]
def calibrationB (b SStar : Mat d) : Mat d :=
  matSqrt (matGeomMean b SStar)⁻¹ * b * matSqrt (matGeomMean b SStar)⁻¹

theorem calibrationB_posDef {b SStar : Mat d} (hb : b.PosDef)
    (hStar : SStar.PosDef) : (calibrationB b SStar).PosDef :=
  posDef_normalize hb (posDef_matGeomMean hb hStar)

/-- The inverse of the normalized corrected block. -/
theorem calibrationB_inv {b SStar : Mat d} (hb : b.PosDef)
    (hStar : SStar.PosDef) :
    (calibrationB b SStar)⁻¹ =
      matSqrt (matGeomMean b SStar) * b⁻¹ * matSqrt (matGeomMean b SStar) := by
  have hm : (matGeomMean b SStar).PosDef := posDef_matGeomMean hb hStar
  have hmUnit : IsUnit (matSqrt (matGeomMean b SStar)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt hm)
  apply Matrix.inv_eq_right_inv
  rw [calibrationB, matSqrt_inv hm]
  calc
    (matSqrt (matGeomMean b SStar))⁻¹ * b *
          (matSqrt (matGeomMean b SStar))⁻¹ *
        (matSqrt (matGeomMean b SStar) * b⁻¹ *
          matSqrt (matGeomMean b SStar)) =
        (matSqrt (matGeomMean b SStar))⁻¹ * b *
          ((matSqrt (matGeomMean b SStar))⁻¹ *
            matSqrt (matGeomMean b SStar)) * b⁻¹ *
          matSqrt (matGeomMean b SStar) := by
      noncomm_ring
    _ = (matSqrt (matGeomMean b SStar))⁻¹ * (b * b⁻¹) *
          matSqrt (matGeomMean b SStar) := by
      rw [Matrix.nonsing_inv_mul _ hmUnit]
      noncomm_ring
    _ = 1 := by
      rw [Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hb),
        Matrix.mul_one]
      exact Matrix.nonsing_inv_mul _ hmUnit

/-- The Riccati conjugation: the calibrated `S₊`-energy of the `p`-load is the
inverse normalized block. -/
theorem metric_conj_sStar {b SStar : Mat d} (hb : b.PosDef)
    (hStar : SStar.PosDef) :
    matSqrt (matGeomMean b SStar)⁻¹ * SStar *
        matSqrt (matGeomMean b SStar)⁻¹ =
      (calibrationB b SStar)⁻¹ := by
  have hm : (matGeomMean b SStar).PosDef := posDef_matGeomMean hb hStar
  have hmUnit : IsUnit (matSqrt (matGeomMean b SStar)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt hm)
  have hroot : matSqrt (matGeomMean b SStar) * matSqrt (matGeomMean b SStar) =
      matGeomMean b SStar := (matSqrt_spec hm.posSemidef).2
  have hric : matGeomMean b SStar * b⁻¹ * matGeomMean b SStar = SStar :=
    matGeomMean_riccati hb hStar
  have hcancel₁ : (matSqrt (matGeomMean b SStar))⁻¹ * matGeomMean b SStar =
      matSqrt (matGeomMean b SStar) := by
    calc
      (matSqrt (matGeomMean b SStar))⁻¹ * matGeomMean b SStar =
          (matSqrt (matGeomMean b SStar))⁻¹ *
            (matSqrt (matGeomMean b SStar) * matSqrt (matGeomMean b SStar)) := by
        rw [hroot]
      _ = ((matSqrt (matGeomMean b SStar))⁻¹ * matSqrt (matGeomMean b SStar)) *
            matSqrt (matGeomMean b SStar) := by
        rw [Matrix.mul_assoc]
      _ = matSqrt (matGeomMean b SStar) := by
        rw [Matrix.nonsing_inv_mul _ hmUnit, Matrix.one_mul]
  have hcancel₂ : matGeomMean b SStar * (matSqrt (matGeomMean b SStar))⁻¹ =
      matSqrt (matGeomMean b SStar) := by
    calc
      matGeomMean b SStar * (matSqrt (matGeomMean b SStar))⁻¹ =
          matSqrt (matGeomMean b SStar) * matSqrt (matGeomMean b SStar) *
            (matSqrt (matGeomMean b SStar))⁻¹ := by
        rw [hroot]
      _ = matSqrt (matGeomMean b SStar) *
            (matSqrt (matGeomMean b SStar) *
              (matSqrt (matGeomMean b SStar))⁻¹) := by
        rw [Matrix.mul_assoc]
      _ = matSqrt (matGeomMean b SStar) := by
        rw [Matrix.mul_nonsing_inv _ hmUnit, Matrix.mul_one]
  rw [calibrationB_inv hb hStar]
  calc
    matSqrt (matGeomMean b SStar)⁻¹ * SStar *
        matSqrt (matGeomMean b SStar)⁻¹ =
        matSqrt (matGeomMean b SStar)⁻¹ *
          (matGeomMean b SStar * b⁻¹ * matGeomMean b SStar) *
            matSqrt (matGeomMean b SStar)⁻¹ := by
      rw [hric]
    _ = (matSqrt (matGeomMean b SStar))⁻¹ *
          (matGeomMean b SStar * b⁻¹ * matGeomMean b SStar) *
            (matSqrt (matGeomMean b SStar))⁻¹ := by
      rw [matSqrt_inv hm]
    _ = ((matSqrt (matGeomMean b SStar))⁻¹ * matGeomMean b SStar) * b⁻¹ *
          (matGeomMean b SStar * (matSqrt (matGeomMean b SStar))⁻¹) := by
      noncomm_ring
    _ = matSqrt (matGeomMean b SStar) * b⁻¹ *
          matSqrt (matGeomMean b SStar) := by
      rw [hcancel₁, hcancel₂]

/-- The mirrored Riccati conjugation: the calibrated `S₊⁻¹`-energy of the
`r`-load is the normalized block itself. -/
theorem metric_conj_sStarInv {b SStar : Mat d} (hb : b.PosDef)
    (hStar : SStar.PosDef) :
    matSqrt (matGeomMean b SStar) * SStar⁻¹ *
        matSqrt (matGeomMean b SStar) =
      calibrationB b SStar := by
  have hm : (matGeomMean b SStar).PosDef := posDef_matGeomMean hb hStar
  have hmUnit : IsUnit (matGeomMean b SStar).det := isUnit_det_of_posDef hm
  have hrootUnit : IsUnit (matSqrt (matGeomMean b SStar)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt hm)
  have hroot : matSqrt (matGeomMean b SStar) * matSqrt (matGeomMean b SStar) =
      matGeomMean b SStar := (matSqrt_spec hm.posSemidef).2
  have hric : matGeomMean b SStar * b⁻¹ * matGeomMean b SStar = SStar :=
    matGeomMean_riccati hb hStar
  have hStarInv : SStar⁻¹ =
      (matGeomMean b SStar)⁻¹ * b * (matGeomMean b SStar)⁻¹ := by
    calc
      SStar⁻¹ = (matGeomMean b SStar * b⁻¹ * matGeomMean b SStar)⁻¹ := by
        rw [hric]
      _ = (matGeomMean b SStar)⁻¹ * (matGeomMean b SStar * b⁻¹)⁻¹ := by
        rw [Matrix.mul_inv_rev]
      _ = (matGeomMean b SStar)⁻¹ * ((b⁻¹)⁻¹ * (matGeomMean b SStar)⁻¹) := by
        rw [Matrix.mul_inv_rev]
      _ = (matGeomMean b SStar)⁻¹ * b * (matGeomMean b SStar)⁻¹ := by
        rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hb),
          Matrix.mul_assoc]
  have hcancel₁ : matSqrt (matGeomMean b SStar) * (matGeomMean b SStar)⁻¹ =
      (matSqrt (matGeomMean b SStar))⁻¹ := by
    calc
      matSqrt (matGeomMean b SStar) * (matGeomMean b SStar)⁻¹ =
          matSqrt (matGeomMean b SStar) *
            (matSqrt (matGeomMean b SStar) * matSqrt (matGeomMean b SStar))⁻¹ := by
        rw [hroot]
      _ = matSqrt (matGeomMean b SStar) *
            ((matSqrt (matGeomMean b SStar))⁻¹ *
              (matSqrt (matGeomMean b SStar))⁻¹) := by
        rw [Matrix.mul_inv_rev]
      _ = (matSqrt (matGeomMean b SStar) *
            (matSqrt (matGeomMean b SStar))⁻¹) *
              (matSqrt (matGeomMean b SStar))⁻¹ := by
        rw [Matrix.mul_assoc]
      _ = (matSqrt (matGeomMean b SStar))⁻¹ := by
        rw [Matrix.mul_nonsing_inv _ hrootUnit, Matrix.one_mul]
  have hcancel₂ : (matGeomMean b SStar)⁻¹ * matSqrt (matGeomMean b SStar) =
      (matSqrt (matGeomMean b SStar))⁻¹ := by
    calc
      (matGeomMean b SStar)⁻¹ * matSqrt (matGeomMean b SStar) =
          (matSqrt (matGeomMean b SStar) * matSqrt (matGeomMean b SStar))⁻¹ *
            matSqrt (matGeomMean b SStar) := by
        rw [hroot]
      _ = (matSqrt (matGeomMean b SStar))⁻¹ *
            ((matSqrt (matGeomMean b SStar))⁻¹ *
              matSqrt (matGeomMean b SStar)) := by
        rw [Matrix.mul_inv_rev, Matrix.mul_assoc]
      _ = (matSqrt (matGeomMean b SStar))⁻¹ := by
        rw [Matrix.nonsing_inv_mul _ hrootUnit, Matrix.mul_one]
  calc
    matSqrt (matGeomMean b SStar) * SStar⁻¹ *
        matSqrt (matGeomMean b SStar) =
        matSqrt (matGeomMean b SStar) *
          ((matGeomMean b SStar)⁻¹ * b * (matGeomMean b SStar)⁻¹) *
            matSqrt (matGeomMean b SStar) := by
      rw [← hStarInv]
    _ = (matSqrt (matGeomMean b SStar) * (matGeomMean b SStar)⁻¹) * b *
          ((matGeomMean b SStar)⁻¹ * matSqrt (matGeomMean b SStar)) := by
      noncomm_ring
    _ = (matSqrt (matGeomMean b SStar))⁻¹ * b *
          (matSqrt (matGeomMean b SStar))⁻¹ := by
      rw [hcancel₁, hcancel₂]
    _ = calibrationB b SStar := by
      rw [calibrationB, matSqrt_inv hm]

/-- The metric lies above the lower Schur datum. -/
theorem sStar_le_metric {b SStar : Mat d} (hb : b.PosDef)
    (hStar : SStar.PosDef) (hbStar : SStar ≤ b) :
    SStar ≤ matGeomMean b SStar := by
  have h2 : matGeomMean SStar SStar ≤ matGeomMean b SStar :=
    matGeomMean_mono hStar hb hStar hStar hbStar le_rfl
  rw [matGeomMean_self hStar] at h2
  exact h2

/-- The metric lies below the corrected block. -/
theorem metric_le_b {b SStar : Mat d} (hb : b.PosDef)
    (hStar : SStar.PosDef) (hbStar : SStar ≤ b) :
    matGeomMean b SStar ≤ b := by
  have h2 : matGeomMean b SStar ≤ matGeomMean b b :=
    matGeomMean_mono hb hb hStar hb le_rfl hbStar
  rw [matGeomMean_self hb] at h2
  exact h2

/-- The normalized corrected block dominates the identity. -/
theorem one_le_calibrationB {b SStar : Mat d} (hb : b.PosDef)
    (hStar : SStar.PosDef) (hbStar : SStar ≤ b) :
    (1 : Mat d) ≤ calibrationB b SStar := by
  have hm : (matGeomMean b SStar).PosDef := posDef_matGeomMean hb hStar
  have hmUnit : IsUnit (matSqrt (matGeomMean b SStar)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt hm)
  have hroot : matSqrt (matGeomMean b SStar) * matSqrt (matGeomMean b SStar) =
      matGeomMean b SStar := (matSqrt_spec hm.posSemidef).2
  have hle := conj_le_conj (matSqrt (matGeomMean b SStar)⁻¹)
    (metric_le_b hb hStar hbStar)
  have hherm : (matSqrt (matGeomMean b SStar)⁻¹)ᴴ =
      matSqrt (matGeomMean b SStar)⁻¹ :=
    conjTranspose_matSqrt hm.inv.posSemidef
  rw [hherm] at hle
  have hcancel : (matSqrt (matGeomMean b SStar))⁻¹ * matGeomMean b SStar =
      matSqrt (matGeomMean b SStar) := by
    calc
      (matSqrt (matGeomMean b SStar))⁻¹ * matGeomMean b SStar =
          (matSqrt (matGeomMean b SStar))⁻¹ *
            (matSqrt (matGeomMean b SStar) * matSqrt (matGeomMean b SStar)) := by
        rw [hroot]
      _ = ((matSqrt (matGeomMean b SStar))⁻¹ * matSqrt (matGeomMean b SStar)) *
            matSqrt (matGeomMean b SStar) := by
        rw [Matrix.mul_assoc]
      _ = matSqrt (matGeomMean b SStar) := by
        rw [Matrix.nonsing_inv_mul _ hmUnit, Matrix.one_mul]
  have hone : matSqrt (matGeomMean b SStar)⁻¹ * matGeomMean b SStar *
      matSqrt (matGeomMean b SStar)⁻¹ = 1 := by
    rw [matSqrt_inv hm, hcancel]
    exact Matrix.mul_nonsing_inv _ hmUnit
  calc
    (1 : Mat d) = matSqrt (matGeomMean b SStar)⁻¹ * matGeomMean b SStar *
        matSqrt (matGeomMean b SStar)⁻¹ := hone.symm
    _ ≤ matSqrt (matGeomMean b SStar)⁻¹ * b *
        matSqrt (matGeomMean b SStar)⁻¹ := hle
    _ = calibrationB b SStar := rfl

/-- The inverse normalized corrected block is below the identity. -/
theorem calibrationB_inv_le_one {b SStar : Mat d} (hb : b.PosDef)
    (hStar : SStar.PosDef) (hbStar : SStar ≤ b) :
    (calibrationB b SStar)⁻¹ ≤ (1 : Mat d) := by
  have hB := calibrationB_posDef hb hStar
  have hinvone : (1 : Mat d)⁻¹ = 1 :=
    Matrix.inv_eq_right_inv (by rw [Matrix.one_mul])
  have h := HCPolySupport.HighContrast.inv_le_inv_of_le
    Matrix.PosDef.one hB (one_le_calibrationB hb hStar hbStar)
  rwa [hinvone] at h

/-! ## Calibrated loads -/

/-- The calibrated loads pair to the unit. -/
theorem calibration_pair {b SStar : Mat d} (hb : b.PosDef)
    (hStar : SStar.PosDef) (e : Vec d) :
    (matSqrt (matGeomMean b SStar)⁻¹ *ᵥ e) ⬝ᵥ
      (matSqrt (matGeomMean b SStar) *ᵥ e) = e ⬝ᵥ e := by
  have hm : (matGeomMean b SStar).PosDef := posDef_matGeomMean hb hStar
  have hherm : (matSqrt (matGeomMean b SStar)⁻¹)ᴴ =
      matSqrt (matGeomMean b SStar)⁻¹ :=
    conjTranspose_matSqrt hm.inv.posSemidef
  rw [mulVec_dotProduct_symm hherm, Matrix.mulVec_mulVec,
    matSqrt_inv_mul_matSqrt hm, Matrix.one_mulVec]

/-- The `S₊`-energy of the `p`-load is the `B⁻¹`-quadratic. -/
theorem calibration_energy_p {b SStar : Mat d} (hb : b.PosDef)
    (hStar : SStar.PosDef) (e : Vec d) :
    (matSqrt (matGeomMean b SStar)⁻¹ *ᵥ e) ⬝ᵥ SStar *ᵥ
        (matSqrt (matGeomMean b SStar)⁻¹ *ᵥ e) =
      e ⬝ᵥ (calibrationB b SStar)⁻¹ *ᵥ e := by
  have hm : (matGeomMean b SStar).PosDef := posDef_matGeomMean hb hStar
  have hherm : (matSqrt (matGeomMean b SStar)⁻¹)ᴴ =
      matSqrt (matGeomMean b SStar)⁻¹ :=
    conjTranspose_matSqrt hm.inv.posSemidef
  have hquad := Initialization.quad_conj (matSqrt (matGeomMean b SStar)⁻¹) SStar e
  rw [hherm] at hquad
  rw [← hquad, metric_conj_sStar hb hStar]

/-- The `S₊⁻¹`-energy of the `r`-load is the `B`-quadratic. -/
theorem calibration_energy_r {b SStar : Mat d} (hb : b.PosDef)
    (hStar : SStar.PosDef) (e : Vec d) :
    (matSqrt (matGeomMean b SStar) *ᵥ e) ⬝ᵥ SStar⁻¹ *ᵥ
        (matSqrt (matGeomMean b SStar) *ᵥ e) =
      e ⬝ᵥ calibrationB b SStar *ᵥ e := by
  have hm : (matGeomMean b SStar).PosDef := posDef_matGeomMean hb hStar
  have hherm : (matSqrt (matGeomMean b SStar))ᴴ =
      matSqrt (matGeomMean b SStar) :=
    conjTranspose_matSqrt hm.posSemidef
  have hquad := Initialization.quad_conj (matSqrt (matGeomMean b SStar)) SStar⁻¹ e
  rw [hherm] at hquad
  rw [← hquad, metric_conj_sStarInv hb hStar]

/-! ## Square-root conjugations and metric Cauchy–Schwarz -/

/-- The inverse root conjugation of a positive matrix is the identity. -/
theorem matSqrt_inv_conj_self {A : Mat d} (hA : A.PosDef) :
    matSqrt A⁻¹ * A * matSqrt A⁻¹ = 1 := by
  have hroot : matSqrt A * matSqrt A = A := (matSqrt_spec hA.posSemidef).2
  have hUnit : IsUnit (matSqrt A).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt hA)
  have hcancel : (matSqrt A)⁻¹ * A = matSqrt A := by
    calc
      (matSqrt A)⁻¹ * A = (matSqrt A)⁻¹ * (matSqrt A * matSqrt A) := by
        rw [hroot]
      _ = ((matSqrt A)⁻¹ * matSqrt A) * matSqrt A := by
        rw [Matrix.mul_assoc]
      _ = matSqrt A := by
        rw [Matrix.nonsing_inv_mul _ hUnit, Matrix.one_mul]
  rw [matSqrt_inv hA, hcancel]
  exact Matrix.mul_nonsing_inv _ hUnit

/-- Cauchy–Schwarz in a positive metric. -/
theorem dotProduct_sq_le_quad_mul_quad {M : Mat d} (hM : M.PosDef)
    (x y : Vec d) :
    (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ M *ᵥ x) * (y ⬝ᵥ M⁻¹ *ᵥ y) := by
  have hMsymm : Mᴴ = M := hM.isHermitian
  have hMinvM : M *ᵥ (M⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_det_of_posDef hM), Matrix.one_mulVec]
  have ha : 0 ≤ x ⬝ᵥ M *ᵥ x := by
    have := hM.posSemidef.dotProduct_mulVec_nonneg x
    simpa using this
  have hc : 0 ≤ y ⬝ᵥ M⁻¹ *ᵥ y := by
    have := hM.inv.posSemidef.dotProduct_mulVec_nonneg y
    simpa using this
  have hf : ∀ t : ℝ,
      0 ≤ t ^ 2 * (x ⬝ᵥ M *ᵥ x) - 2 * t * (x ⬝ᵥ y) + y ⬝ᵥ M⁻¹ *ᵥ y := by
    intro t
    have hquad : 0 ≤ (t • x - M⁻¹ *ᵥ y) ⬝ᵥ M *ᵥ (t • x - M⁻¹ *ᵥ y) := by
      have := hM.posSemidef.dotProduct_mulVec_nonneg (t • x - M⁻¹ *ᵥ y)
      simpa using this
    have hswap : (M⁻¹ *ᵥ y) ⬝ᵥ M *ᵥ x = x ⬝ᵥ y := by
      calc
        (M⁻¹ *ᵥ y) ⬝ᵥ M *ᵥ x = x ⬝ᵥ M *ᵥ (M⁻¹ *ᵥ y) := by
          rw [dotProduct_comm, mulVec_dotProduct_symm hMsymm]
        _ = x ⬝ᵥ y := by rw [hMinvM]
    have hswap₂ : x ⬝ᵥ M *ᵥ (M⁻¹ *ᵥ y) = x ⬝ᵥ y := by
      rw [hMinvM]
    have hyy : (M⁻¹ *ᵥ y) ⬝ᵥ M *ᵥ (M⁻¹ *ᵥ y) = y ⬝ᵥ M⁻¹ *ᵥ y := by
      rw [hMinvM, dotProduct_comm]
    have hexpand : (t • x - M⁻¹ *ᵥ y) ⬝ᵥ M *ᵥ (t • x - M⁻¹ *ᵥ y) =
        t ^ 2 * (x ⬝ᵥ M *ᵥ x) - 2 * t * (x ⬝ᵥ y) + y ⬝ᵥ M⁻¹ *ᵥ y := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
        sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      rw [hswap, hswap₂, hyy]
      ring
    rw [hexpand] at hquad
    exact hquad
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · by_cases hb : x ⬝ᵥ y = 0
    · rw [hb]
      have : (0 : ℝ) ^ 2 = 0 * (y ⬝ᵥ M⁻¹ *ᵥ y) := by ring
      rw [this, ← ha0]
    · exfalso
      have hft := hf ((y ⬝ᵥ M⁻¹ *ᵥ y + 1) / (2 * (x ⬝ᵥ y)))
      rw [← ha0] at hft
      have hb2 : (2 : ℝ) * (x ⬝ᵥ y) ≠ 0 := by
        intro h
        exact hb (by linarith only [h])
      rw [mul_zero] at hft
      have hcalc : (y ⬝ᵥ M⁻¹ *ᵥ y + 1) / (2 * (x ⬝ᵥ y)) *
          (2 * (x ⬝ᵥ y)) = y ⬝ᵥ M⁻¹ *ᵥ y + 1 :=
        div_mul_cancel₀ _ hb2
      nlinarith only [hft, hcalc]
  · have hft := hf ((x ⬝ᵥ y) / (x ⬝ᵥ M *ᵥ x))
    have hcancel : (x ⬝ᵥ y) / (x ⬝ᵥ M *ᵥ x) * (x ⬝ᵥ M *ᵥ x) = x ⬝ᵥ y :=
      div_mul_cancel₀ _ (ne_of_gt hapos)
    nlinarith only [hft, hcancel, hapos]

end

end HCPolySupport.HighContrast.Quenched
