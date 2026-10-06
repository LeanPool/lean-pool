/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseSchur

/-!
# High-contrast homogenization: Provider.Response.CenteredResponseFormulas

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Centered response formulas

The centered primal and adjoint responses have explicit formulas in the Schur
coordinates of the annealed coarse block.  Adding them at the two shifted
loads gives the nonsymmetric polarization identity used by the response
estimate.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

private theorem quadratic_conjTranspose (A : Mat d) (x : Vec d) :
    x ⬝ᵥ Aᴴ *ᵥ x = x ⬝ᵥ A *ᵥ x := by
  rw [conjTranspose_eq_transpose', Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, dotProduct_comm, Matrix.transpose_transpose]

private theorem dotProduct_mulVec_conjTranspose (A : Mat d) (x y : Vec d) :
    x ⬝ᵥ A *ᵥ y = y ⬝ᵥ Aᴴ *ᵥ x := by
  rw [conjTranspose_eq_transpose', Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, dotProduct_comm]

private theorem nonsymmetric_polarization (A : Mat d) (q w : Vec d) :
    (1 / 2 : ℝ) * ((q + w) ⬝ᵥ A *ᵥ (q + w)) -
        (1 / 2 : ℝ) * ((q - w) ⬝ᵥ A *ᵥ (q - w)) =
      w ⬝ᵥ (A + Aᴴ) *ᵥ q := by
  have hcross := dotProduct_mulVec_conjTranspose A q w
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct,
    sub_dotProduct, dotProduct_add, dotProduct_sub, Matrix.add_mulVec, hcross]
  ring

private theorem primal_centering_expansion {S SStar : Mat d}
    (hStar : SStar.PosDef) (K : Mat d) (p q : Vec d) :
    (-p + SStar⁻¹ *ᵥ (q + K *ᵥ p)) ⬝ᵥ
        ((1 - Kᴴ * SStar⁻¹) *ᵥ q -
          (S + Kᴴ * SStar⁻¹ * K) *ᵥ p) =
      p ⬝ᵥ S *ᵥ p +
        (q + K *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (q + K *ᵥ p) -
        (q + K *ᵥ p) ⬝ᵥ
          (SStar⁻¹ * K * SStar⁻¹) *ᵥ (q + K *ᵥ p) -
        ((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ (q + K *ᵥ p) - p ⬝ᵥ q := by
  let w : Vec d := q + K *ᵥ p
  have hw : q = w - K *ᵥ p := by
    simp only [w]
    abel
  have hrow :
      (1 - Kᴴ * SStar⁻¹) *ᵥ q -
          (S + Kᴴ * SStar⁻¹ * K) *ᵥ p =
        w - K *ᵥ p - Kᴴ *ᵥ (SStar⁻¹ *ᵥ w) - S *ᵥ p := by
    simp only [w, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.add_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    abel
  have hT : (SStar⁻¹)ᵀ = SStar⁻¹ := by
    rw [← conjTranspose_eq_transpose']
    exact hStar.inv.isHermitian
  have hcrossK :
      p ⬝ᵥ Kᴴ *ᵥ (SStar⁻¹ *ᵥ w) =
        (K *ᵥ p) ⬝ᵥ (SStar⁻¹ *ᵥ w) := by
    rw [dotProduct_mulVec_pair K SStar⁻¹ p w,
      conjTranspose_eq_transpose', Matrix.mulVec_mulVec]
  have hquadK :
      (SStar⁻¹ *ᵥ w) ⬝ᵥ Kᴴ *ᵥ (SStar⁻¹ *ᵥ w) =
        w ⬝ᵥ (SStar⁻¹ * K * SStar⁻¹) *ᵥ w := by
    rw [Matrix.mulVec_mulVec,
      dotProduct_mulVec_pair SStar⁻¹ (Kᴴ * SStar⁻¹) w w, hT]
    have hm : SStar⁻¹ * (Kᴴ * SStar⁻¹) =
        (SStar⁻¹ * K * SStar⁻¹)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        hStar.inv.isHermitian]
    rw [hm, quadratic_conjTranspose]
  have hcrossS :
      (SStar⁻¹ *ᵥ w) ⬝ᵥ (S *ᵥ p) =
        ((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ w := by
    rw [dotProduct_mulVec_pair SStar⁻¹ S w p, hT,
      dotProduct_comm]
  have hcrossK' :
      p ⬝ᵥ (Kᴴ * SStar⁻¹) *ᵥ w =
        (K *ᵥ p) ⬝ᵥ (SStar⁻¹ *ᵥ w) := by
    rw [← Matrix.mulVec_mulVec]
    exact hcrossK
  have hquadK' :
      (SStar⁻¹ *ᵥ w) ⬝ᵥ (Kᴴ * SStar⁻¹) *ᵥ w =
        w ⬝ᵥ (SStar⁻¹ * K * SStar⁻¹) *ᵥ w := by
    rw [← Matrix.mulVec_mulVec]
    exact hquadK
  rw [show q + K *ᵥ p = w by rfl, hrow]
  simp only [add_dotProduct, dotProduct_sub, neg_dotProduct,
    Matrix.mulVec_mulVec]
  rw [dotProduct_comm (SStar⁻¹ *ᵥ w) w, hcrossK',
    dotProduct_comm (SStar⁻¹ *ᵥ w) (K *ᵥ p), hquadK', hcrossS]
  rw [hw]
  simp only [dotProduct_sub]
  ring

/-- The corrected centered primal response formula. -/
theorem centeredResponse_eq_schur {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d} (hStar : SStar.PosDef)
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) (p q : Vec d) :
    centeredResponse P U p q =
      (1 / 2 : ℝ) *
          ((q + K *ᵥ p) ⬝ᵥ
            (SStar⁻¹ * K * SStar⁻¹) *ᵥ (q + K *ᵥ p)) +
        (1 / 2 : ℝ) *
          (((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ (q + K *ᵥ p)) -
        (1 / 2 : ℝ) * (p ⬝ᵥ q) := by
  rw [centeredResponse, annealed_responseJ_schur U hint hE p q]
  have hmeans := annealed_optimizer_means_schur U hint hE p q
  have hgrad := congrArg Prod.fst hmeans
  have hflux := congrArg Prod.snd hmeans
  simp only at hgrad hflux
  rw [hgrad, hflux]
  have hcenter := primal_centering_expansion (S := S) hStar K p q
  change
    (1 / 2 : ℝ) * (p ⬝ᵥ S *ᵥ p) +
          (1 / 2 : ℝ) *
            ((q + K *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (q + K *ᵥ p)) -
        p ⬝ᵥ q -
      (1 / 2 : ℝ) *
        ((-p + SStar⁻¹ *ᵥ (q + K *ᵥ p)) ⬝ᵥ
          ((1 - Kᴴ * SStar⁻¹) *ᵥ q -
            (S + Kᴴ * SStar⁻¹ * K) *ᵥ p)) = _
  rw [hcenter]
  ring

/-- The corrected centered adjoint response formula.  Its leading term has
the opposite sign because coefficient transposition sends `K` to `-K`. -/
theorem centeredAdjointResponse_eq_schur {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d} (hStar : SStar.PosDef)
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) (p q : Vec d) :
    centeredAdjointResponse P U p q =
      -(1 / 2 : ℝ) *
          ((q - K *ᵥ p) ⬝ᵥ
            (SStar⁻¹ * K * SStar⁻¹) *ᵥ (q - K *ᵥ p)) +
        (1 / 2 : ℝ) *
          (((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ (q - K *ᵥ p)) -
        (1 / 2 : ℝ) * (p ⬝ᵥ q) := by
  rw [centeredAdjointResponse,
    annealed_adjoint_responseJ_schur U hint hE p q]
  have hmeans := annealed_adjoint_optimizer_means_schur U hint hE p q
  have hgrad := congrArg Prod.fst hmeans
  have hflux := congrArg Prod.snd hmeans
  simp only at hgrad hflux
  rw [hgrad, hflux]
  have hcenter := primal_centering_expansion (S := S) hStar (-K) p q
  simp only [Matrix.neg_mulVec, Matrix.conjTranspose_neg, neg_neg,
    Matrix.neg_mul, Matrix.mul_neg] at hcenter
  have hcenter' :
      (-p + SStar⁻¹ *ᵥ (q - K *ᵥ p)) ⬝ᵥ
          ((1 + Kᴴ * SStar⁻¹) *ᵥ q -
            (S + Kᴴ * SStar⁻¹ * K) *ᵥ p) =
        p ⬝ᵥ S *ᵥ p +
          (q - K *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (q - K *ᵥ p) +
          (q - K *ᵥ p) ⬝ᵥ
            (SStar⁻¹ * K * SStar⁻¹) *ᵥ (q - K *ᵥ p) -
          ((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ (q - K *ᵥ p) - p ⬝ᵥ q := by
    simpa only [sub_eq_add_neg, neg_neg, dotProduct_neg] using hcenter
  change
    (1 / 2 : ℝ) * (p ⬝ᵥ S *ᵥ p) +
          (1 / 2 : ℝ) *
            ((q - K *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ (q - K *ᵥ p)) -
        p ⬝ᵥ q -
      (1 / 2 : ℝ) *
        ((-p + SStar⁻¹ *ᵥ (q - K *ᵥ p)) ⬝ᵥ
          ((1 + Kᴴ * SStar⁻¹) *ᵥ q -
            (S + Kᴴ * SStar⁻¹ * K) *ᵥ p)) = _
  rw [hcenter']
  ring

/-- Adding the primal and adjoint formulas at opposite load shifts gives the
corrected nonsymmetric polarization identity. -/
theorem centeredResponse_add_adjoint_eq_schur
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) (p q r : Vec d) :
    centeredResponse P U p (q - r) +
        centeredAdjointResponse P U p (q + r) =
      p ⬝ᵥ (S * SStar⁻¹ - 1) *ᵥ q +
        (K *ᵥ p - r) ⬝ᵥ
          (SStar⁻¹ * (K + Kᴴ) * SStar⁻¹) *ᵥ q := by
  rw [centeredResponse_eq_schur U hint hStar hE p (q - r),
    centeredAdjointResponse_eq_schur U hint hStar hE p (q + r)]
  let w : Vec d := K *ᵥ p - r
  have hw₁ : q - r + K *ᵥ p = q + w := by
    simp only [w]
    abel
  have hw₂ : q + r - K *ᵥ p = q - w := by
    simp only [w]
    abel
  rw [hw₁, hw₂]
  let A : Mat d := SStar⁻¹ * K * SStar⁻¹
  have hquad := nonsymmetric_polarization A q w
  have hT : (SStar⁻¹)ᴴ = SStar⁻¹ := hStar.inv.isHermitian
  have hA : A + Aᴴ = SStar⁻¹ * (K + Kᴴ) * SStar⁻¹ := by
    simp only [A, Matrix.conjTranspose_mul, hT]
    noncomm_ring
  rw [hA] at hquad
  have hquad' :
      (1 / 2 : ℝ) *
          ((q + w) ⬝ᵥ
            (SStar⁻¹ * K * SStar⁻¹) *ᵥ (q + w)) -
        (1 / 2 : ℝ) *
          ((q - w) ⬝ᵥ
            (SStar⁻¹ * K * SStar⁻¹) *ᵥ (q - w)) =
        w ⬝ᵥ (SStar⁻¹ * (K + Kᴴ) * SStar⁻¹) *ᵥ q := by
    simpa only [A] using hquad
  have hlinear :
      ((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ q =
        p ⬝ᵥ (S * SStar⁻¹) *ᵥ q := by
    rw [dotProduct_comm, dotProduct_mulVec_conjTranspose (SStar⁻¹ * S) q p,
      Matrix.conjTranspose_mul, hS.isHermitian, hT]
  have hlinear' :
      p ⬝ᵥ (S * SStar⁻¹ - 1) *ᵥ q =
        ((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ q - p ⬝ᵥ q := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hlinear]
  have hLplus :
      ((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ (q + w) =
        ((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ q +
          ((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ w := dotProduct_add _ _ _
  have hLminus :
      ((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ (q - w) =
        ((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ q -
          ((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ w := dotProduct_sub _ _ _
  have hpminus : p ⬝ᵥ (q - r) = p ⬝ᵥ q - p ⬝ᵥ r := dotProduct_sub _ _ _
  have hpplus : p ⬝ᵥ (q + r) = p ⬝ᵥ q + p ⬝ᵥ r := dotProduct_add _ _ _
  change
    (1 / 2 : ℝ) *
          ((q + w) ⬝ᵥ
            (SStar⁻¹ * K * SStar⁻¹) *ᵥ (q + w)) +
        (1 / 2 : ℝ) * (((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ (q + w)) -
        (1 / 2 : ℝ) * (p ⬝ᵥ (q - r)) +
      (-(1 / 2 : ℝ) *
            ((q - w) ⬝ᵥ
              (SStar⁻¹ * K * SStar⁻¹) *ᵥ (q - w)) +
          (1 / 2 : ℝ) * (((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ (q - w)) -
          (1 / 2 : ℝ) * (p ⬝ᵥ (q + r))) =
      p ⬝ᵥ (S * SStar⁻¹ - 1) *ᵥ q +
        w ⬝ᵥ (SStar⁻¹ * (K + Kᴴ) * SStar⁻¹) *ᵥ q
  rw [hLplus, hLminus, hpminus, hpplus]
  linear_combination hquad' - hlinear'

end

end HCPolySupport.HighContrast.Response
