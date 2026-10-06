/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewSolenoidal
public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationQuadratic
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm
public import LeanPool.HighContrastHomogenization.Support.Probability.RegCoeffField.EllipticSet

/-!
# High-contrast homogenization: Provider.Response.ConstantSkewCoefficient

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Constant-skew recentering of coefficient samples

Subtracting a constant skew matrix leaves the coercive quadratic form
unchanged.  Its action on vectors remains bounded by a finite-dimensional
matrix norm, so the recentered field is again a member of the qualitative
coefficient space.
-/

namespace HCPolySupport.HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

namespace Response

/-- An upper ellipticity constant after subtracting a constant skew matrix. -/
@[expose]
def skewShiftUpper (lam Lam : ℝ) (g : Mat d) : ℝ :=
  2 * (Lam ^ 2 + Book.Ch02.matrixFrobeniusNormSq g) / lam

theorem isSkewMat_neg {g : Mat d} (hg : IsSkewMat g) :
    IsSkewMat (-g) := by
  rw [IsSkewMat] at hg ⊢
  ext i j
  have hij := congrFun (congrFun hg i) j
  simp only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply] at hij ⊢
  linarith only [hij]

theorem le_skewShiftUpper {lam Lam : ℝ} (hlam : 0 < lam)
    (hle : lam ≤ Lam) (g : Mat d) :
    lam ≤ skewShiftUpper lam Lam g := by
  have hgNorm0 : 0 ≤ Book.Ch02.matrixFrobeniusNormSq g :=
    Book.Ch02.matrixFrobeniusNormSq_nonneg g
  unfold skewShiftUpper
  rw [le_div_iff₀ hlam]
  have hsquare : lam * lam ≤ Lam * Lam :=
    mul_self_le_mul_self hlam.le hle
  nlinarith only [hsquare, hgNorm0]

private theorem vecDot_sub_skew (A g : Mat d) (hg : IsSkewMat g)
    (x : Vec d) :
    vecDot x (matVecMul (A - g) x) = vecDot x (matVecMul A x) := by
  have hgstar : Matrix.conjTranspose g = -g := by
    rwa [conjTranspose_eq_transpose']
  have hmul : matVecMul (A - g) x = matVecMul A x - matVecMul g x := by
    funext i
    simp only [matVecMul, Matrix.sub_apply, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hmul]
  have hdot :
      vecDot x (matVecMul A x - matVecMul g x) =
        vecDot x (matVecMul A x) - vecDot x (matVecMul g x) := by
    simp only [vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hzero : vecDot x (matVecMul g x) = 0 := by
    simpa [matVecMul] using! dotProduct_mulVec_of_skew hgstar x
  rw [hdot, hzero, sub_zero]

/-- Uniform ellipticity is preserved when a constant skew matrix is
subtracted. -/
theorem isEllipticMatrix_sub_skew {lam Lam : ℝ} {A g : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (hg : IsSkewMat g) :
    IsEllipticMatrix lam (skewShiftUpper lam Lam g) (A - g) := by
  have hlam : 0 < lam := hA.1
  have hle : lam ≤ Lam := hA.2.1
  have hgNorm0 : 0 ≤ Book.Ch02.matrixFrobeniusNormSq g :=
    Book.Ch02.matrixFrobeniusNormSq_nonneg g
  have hupperNonneg : 0 ≤ skewShiftUpper lam Lam g := by
    unfold skewShiftUpper
    positivity
  have hleUpper : lam ≤ skewShiftUpper lam Lam g :=
    le_skewShiftUpper hlam hle g
  rw [isEllipticMatrix_iff_isEllipticEntryLU]
  refine ⟨hlam, hleUpper, ?_, ?_⟩
  · intro x
    rw [vecDot_sub_skew A g hg x]
    exact hA.2.2.1 x
  · intro x
    have hsub :
        vecNormSq (matVecMul (A - g) x) ≤
          2 * (vecNormSq (matVecMul A x) + vecNormSq (matVecMul g x)) := by
      have hmul : matVecMul (A - g) x = matVecMul A x - matVecMul g x := by
        funext i
        simp only [matVecMul, Matrix.sub_apply, Pi.sub_apply]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hmul]
      exact vecNormSq_sub_le (matVecMul A x) (matVecMul g x)
    have hAbound := vecNormSq_matVecMul_le_of_isEllipticMatrix hA x
    have hgbound :=
      Book.Ch02.vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq g x
    have hnorm :
        vecNormSq (matVecMul (A - g) x) ≤
          2 * (Lam ^ 2 + Book.Ch02.matrixFrobeniusNormSq g) * vecNormSq x := by
      calc
        vecNormSq (matVecMul (A - g) x) ≤
            2 * (vecNormSq (matVecMul A x) + vecNormSq (matVecMul g x)) := hsub
        _ ≤ 2 * (Lam ^ 2 * vecNormSq x +
              Book.Ch02.matrixFrobeniusNormSq g * vecNormSq x) := by
            gcongr
        _ = 2 * (Lam ^ 2 + Book.Ch02.matrixFrobeniusNormSq g) * vecNormSq x := by
            ring
    have hlower := hA.2.2.1 x
    rw [← vecDot_sub_skew A g hg x] at hlower
    calc
      vecNormSq (matVecMul (A - g) x) ≤
          2 * (Lam ^ 2 + Book.Ch02.matrixFrobeniusNormSq g) * vecNormSq x := hnorm
      _ = skewShiftUpper lam Lam g * (lam * vecNormSq x) := by
          unfold skewShiftUpper
          field_simp [hlam.ne']
      _ ≤ skewShiftUpper lam Lam g *
          vecDot x (matVecMul (A - g) x) :=
        mul_le_mul_of_nonneg_left hlower hupperNonneg

end Response

namespace CoeffSpace

/-- Recenter a coefficient sample by subtracting a constant skew matrix. -/
@[expose]
def subSkew (a : CoeffSpace d) (g : Mat d) (hg : IsSkewMat g) :
    CoeffSpace d where
  val := AEEqFun.mk (fun x ↦ (a.1 x : Mat d) - g)
    (a.1.stronglyMeasurable.sub stronglyMeasurable_const).aestronglyMeasurable
  property := by
    intro R hR
    obtain ⟨lam, Lam, hlam, hle, hEll⟩ := a.2 R hR
    refine ⟨lam, Response.skewShiftUpper lam Lam g, hlam,
      Response.le_skewShiftUpper hlam hle g, ?_⟩
    filter_upwards [hEll,
      AEEqFun.coeFn_mk (fun x ↦ (a.1 x : Mat d) - g)
        (a.1.stronglyMeasurable.sub stronglyMeasurable_const).aestronglyMeasurable]
      with x hx hshift hxb
    rw [hshift]
    exact Response.isEllipticMatrix_sub_skew (hx hxb) hg

/-- The recentered quotient sample has the expected pointwise representative
almost everywhere. -/
theorem subSkew_ae (a : CoeffSpace d) (g : Mat d) (hg : IsSkewMat g) :
    (⇑(a.subSkew g hg).1 : CoeffField d) =ᵐ[volume]
      fun x ↦ (a.1 x : Mat d) - g := by
  unfold subSkew
  exact AEEqFun.coeFn_mk _ _

/-- On a Chapter 2 domain, recentering is represented by pointwise subtraction
of the same constant skew matrix. -/
theorem coeffOn_subSkew_ae (a : CoeffSpace d) (U : Book.Ch02.Domain d)
    (g : Mat d) (hg : IsSkewMat g) :
    ((a.subSkew g hg).coeffOn U).toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x ↦ (a.coeffOn U).toCoeffField x - g :=
  ae_restrict_of_ae (subSkew_ae a g hg)

/-- Transposition reverses the sign of a constant-skew recentering. -/
theorem transpose_subSkew (a : CoeffSpace d) (g : Mat d) (hg : IsSkewMat g) :
    (a.subSkew g hg).transpose =
      a.transpose.subSkew (-g) (Response.isSkewMat_neg hg) := by
  apply Subtype.ext
  apply AEEqFun.ext
  filter_upwards [transpose_ae (a.subSkew g hg), subSkew_ae a g hg,
    subSkew_ae a.transpose (-g) (Response.isSkewMat_neg hg), transpose_ae a]
    with x hleft ha hright hat
  rw [hleft, ha, hright, hat]
  ext i j
  have hji : g j i = -g i j := by
    have hij := congrFun (congrFun hg i) j
    simpa [IsSkewMat, matTranspose, Matrix.transpose_apply,
      Matrix.neg_apply] using hij
  simp only [matTranspose, Matrix.transpose_apply, Matrix.sub_apply,
    Matrix.neg_apply]
  rw [hji]

end CoeffSpace

end

end HCPolySupport.HighContrast
