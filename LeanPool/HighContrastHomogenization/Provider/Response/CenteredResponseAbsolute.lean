/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseTrace

/-!
# High-contrast homogenization: Provider.Response.CenteredResponseAbsolute

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The absolute centered-response bound

Each centered response at a linearly generated load is a quadratic form in the
generating vector.  This gives boundedness on the Euclidean unit sphere and
allows the trace estimate to be enlarged to the sum of the two absolute
responses.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory Set

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem dotProduct_two_mulVec (A B : Mat d) (e : Vec d) :
    (A *ᵥ e) ⬝ᵥ (B *ᵥ e) = e ⬝ᵥ (Aᴴ * B) *ᵥ e := by
  rw [dotProduct_mulVec_pair A B e e, conjTranspose_eq_transpose']

private theorem centeredResponse_linear_loads_eq_quadratic
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d} (hStar : SStar.PosDef)
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) (Pmat Qmat : Mat d) (e : Vec d) :
    centeredResponse P U (Pmat *ᵥ e) (Qmat *ᵥ e) =
      e ⬝ᵥ
        ((1 / 2 : ℝ) •
            ((Qmat + K * Pmat)ᴴ *
              (SStar⁻¹ * K * SStar⁻¹) * (Qmat + K * Pmat)) +
          (1 / 2 : ℝ) •
            ((SStar⁻¹ * S * Pmat)ᴴ * (Qmat + K * Pmat)) -
          (1 / 2 : ℝ) • (Pmatᴴ * Qmat)) *ᵥ e := by
  rw [centeredResponse_eq_schur U hint hStar hE]
  let W : Mat d := Qmat + K * Pmat
  have hw : Qmat *ᵥ e + K *ᵥ Pmat *ᵥ e =
      W *ᵥ e := by
    rw [Matrix.add_mulVec, Matrix.mulVec_mulVec]
  rw [hw, Matrix.mulVec_mulVec]
  have hquad :
      (W *ᵥ e) ⬝ᵥ
          ((SStar⁻¹ * K * SStar⁻¹) * W) *ᵥ e =
        e ⬝ᵥ (Wᴴ * (SStar⁻¹ * K * SStar⁻¹) * W) *ᵥ e := by
    rw [← Matrix.mulVec_mulVec]
    exact (Initialization.quad_conj W (SStar⁻¹ * K * SStar⁻¹) e).symm
  rw [hquad]
  have hlin :
      ((SStar⁻¹ * S) *ᵥ (Pmat *ᵥ e)) ⬝ᵥ (W *ᵥ e) =
        e ⬝ᵥ ((SStar⁻¹ * S * Pmat)ᴴ * W) *ᵥ e := by
    rw [Matrix.mulVec_mulVec,
      dotProduct_two_mulVec (SStar⁻¹ * S * Pmat) W e]
  rw [hlin, dotProduct_two_mulVec Pmat Qmat e]
  change _ = e ⬝ᵥ
    ((1 / 2 : ℝ) • (Wᴴ * (SStar⁻¹ * K * SStar⁻¹) * W) +
      (1 / 2 : ℝ) • ((SStar⁻¹ * S * Pmat)ᴴ * W) -
      (1 / 2 : ℝ) • (Pmatᴴ * Qmat)) *ᵥ e
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]

private theorem centeredAdjointResponse_linear_loads_eq_quadratic
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d} (hStar : SStar.PosDef)
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) (Pmat Qmat : Mat d) (e : Vec d) :
    centeredAdjointResponse P U (Pmat *ᵥ e) (Qmat *ᵥ e) =
      e ⬝ᵥ
        (-(1 / 2 : ℝ) •
            ((Qmat - K * Pmat)ᴴ *
              (SStar⁻¹ * K * SStar⁻¹) * (Qmat - K * Pmat)) +
          (1 / 2 : ℝ) •
            ((SStar⁻¹ * S * Pmat)ᴴ * (Qmat - K * Pmat)) -
          (1 / 2 : ℝ) • (Pmatᴴ * Qmat)) *ᵥ e := by
  rw [centeredAdjointResponse_eq_schur U hint hStar hE]
  let W : Mat d := Qmat - K * Pmat
  have hw : Qmat *ᵥ e - K *ᵥ Pmat *ᵥ e =
      W *ᵥ e := by
    rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec]
  rw [hw, Matrix.mulVec_mulVec]
  have hquad :
      (W *ᵥ e) ⬝ᵥ
          ((SStar⁻¹ * K * SStar⁻¹) * W) *ᵥ e =
        e ⬝ᵥ (Wᴴ * (SStar⁻¹ * K * SStar⁻¹) * W) *ᵥ e := by
    rw [← Matrix.mulVec_mulVec]
    exact (Initialization.quad_conj W (SStar⁻¹ * K * SStar⁻¹) e).symm
  rw [hquad]
  have hlin :
      ((SStar⁻¹ * S) *ᵥ (Pmat *ᵥ e)) ⬝ᵥ (W *ᵥ e) =
        e ⬝ᵥ ((SStar⁻¹ * S * Pmat)ᴴ * W) *ᵥ e := by
    rw [Matrix.mulVec_mulVec,
      dotProduct_two_mulVec (SStar⁻¹ * S * Pmat) W e]
  rw [hlin, dotProduct_two_mulVec Pmat Qmat e]
  change _ = e ⬝ᵥ
    (-(1 / 2 : ℝ) • (Wᴴ * (SStar⁻¹ * K * SStar⁻¹) * W) +
      (1 / 2 : ℝ) • ((SStar⁻¹ * S * Pmat)ᴴ * W) -
      (1 / 2 : ℝ) • (Pmatᴴ * Qmat)) *ᵥ e
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]

private theorem abs_quadratic_le_norm (A : Mat d) {e : Vec d}
    (he : e ⬝ᵥ e = 1) : |e ⬝ᵥ A *ᵥ e| ≤ ‖A‖ := by
  rw [abs_le]
  constructor
  · have hneg := dotProduct_mulVec_le_norm_mul (-A) e
    rw [Matrix.neg_mulVec, dotProduct_neg, norm_neg, he, mul_one] at hneg
    linarith only [hneg]
  · have hpos := dotProduct_mulVec_le_norm_mul A e
    rw [he, mul_one] at hpos
    exact hpos

/-- The sum of the absolute primal and adjoint responses on the response unit
sphere is bounded above. -/
theorem bddAbove_absolute_centeredResponses
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d} (hStar : SStar.PosDef)
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) :
    BddAbove
      ((fun e : Vec d =>
          |centeredResponse P U (centeredResponseLoadP S SStar K e)
            (centeredResponseLoadQ S SStar K e -
              responseSkew K *ᵥ centeredResponseLoadP S SStar K e)| +
          |centeredAdjointResponse P U (centeredResponseLoadP S SStar K e)
            (centeredResponseLoadQ S SStar K e +
              responseSkew K *ᵥ centeredResponseLoadP S SStar K e)|) ''
        {e : Vec d | e ⬝ᵥ e = 1}) := by
  let m : Mat d := centeredResponseMetric S SStar K
  let Pmat : Mat d := matSqrt m⁻¹
  let Qmat : Mat d := matSqrt m
  let h : Mat d := responseSkew K
  let Qminus : Mat d := Qmat - h * Pmat
  let Qplus : Mat d := Qmat + h * Pmat
  let Apr : Mat d :=
    (1 / 2 : ℝ) •
        ((Qminus + K * Pmat)ᴴ *
          (SStar⁻¹ * K * SStar⁻¹) * (Qminus + K * Pmat)) +
      (1 / 2 : ℝ) •
        ((SStar⁻¹ * S * Pmat)ᴴ * (Qminus + K * Pmat)) -
      (1 / 2 : ℝ) • (Pmatᴴ * Qminus)
  let Aadj : Mat d :=
    -(1 / 2 : ℝ) •
        ((Qplus - K * Pmat)ᴴ *
          (SStar⁻¹ * K * SStar⁻¹) * (Qplus - K * Pmat)) +
      (1 / 2 : ℝ) •
        ((SStar⁻¹ * S * Pmat)ᴴ * (Qplus - K * Pmat)) -
      (1 / 2 : ℝ) • (Pmatᴴ * Qplus)
  have hpr (e : Vec d) :
      centeredResponse P U (Pmat *ᵥ e) (Qminus *ᵥ e) =
        e ⬝ᵥ Apr *ᵥ e := by
    exact centeredResponse_linear_loads_eq_quadratic U hint hStar hE Pmat Qminus e
  have hadj (e : Vec d) :
      centeredAdjointResponse P U (Pmat *ᵥ e) (Qplus *ᵥ e) =
        e ⬝ᵥ Aadj *ᵥ e := by
    exact centeredAdjointResponse_linear_loads_eq_quadratic U hint hStar hE Pmat Qplus e
  refine ⟨‖Apr‖ + ‖Aadj‖, ?_⟩
  intro x hx
  rcases hx with ⟨e, he, rfl⟩
  change e ⬝ᵥ e = 1 at he
  change
    |centeredResponse P U (Pmat *ᵥ e)
        (Qmat *ᵥ e - h *ᵥ Pmat *ᵥ e)| +
      |centeredAdjointResponse P U (Pmat *ᵥ e)
        (Qmat *ᵥ e + h *ᵥ Pmat *ᵥ e)| ≤ _
  have hminus : Qmat *ᵥ e - h *ᵥ Pmat *ᵥ e = Qminus *ᵥ e := by
    simp only [Qminus, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
  have hplus : Qmat *ᵥ e + h *ᵥ Pmat *ᵥ e = Qplus *ᵥ e := by
    simp only [Qplus, Matrix.add_mulVec, Matrix.mulVec_mulVec]
  rw [hminus, hplus, hpr, hadj]
  exact add_le_add (abs_quadratic_le_norm Apr he)
    (abs_quadratic_le_norm Aadj he)

end

end HCPolySupport.HighContrast.Response
