/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedWeakProductResponse

/-!
# High-contrast homogenization: Provider.Response.AdaptedWeakProductAnnealed

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Annealed weak-product bounds for adapted responses

The samplewise affine weak-product estimate is specialized to the separately
centered primal and adjoint response profiles.  Integrating these literal
physical cutoff terms gives the weak components used by the response estimate.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- One primal sample's physical cutoff product is bounded by its squared
normalized profile weak root. -/
theorem ofReal_abs_adaptedPreYoungCutoff_primalSample_le
    {l t : ℤ} {m0 : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid l (roundedGrid l m0))
    (P : Measure (CoeffSpace d)) (sample : CoeffSpace d → CoeffSpace d)
    (p r : Vec d) (a : CoeffSpace d) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid
    let center := profilePrimalCenter P hq t sample p r
    ENNReal.ofReal |Book.Ch02.average (adaptedDomain hq t) (fun x ↦
      adaptedPreYoungCutoff (roundedGrid l m0) hq t x * ((1 / 2 : ℝ) *
        vecDot
          ((centeredResponseOptimizer (adaptedDomain hq t)
            (sample a) p r).toH1.grad x - center.1)
          (matVecMul (((sample a).coeffOn
              (adaptedDomain hq t)).toCoeffField x)
            ((centeredResponseOptimizer (adaptedDomain hq t)
              (sample a) p r).toH1.grad x) - center.2)))| ≤
      ENNReal.ofReal
        (1 + divCurlDimensionCoeff d * adaptedCutoffDerivativeCoeff d *
          ((51 / 50 : ℝ) * (d : ℝ) ^ 2)) *
        profilePrimalWeakRoot m0 hq t sample p r center a ^ (2 : ℕ) := by
  simpa only [profilePrimalWeakRoot] using
    ofReal_abs_adaptedResponseCutoff_le_weakRoot_sq hm0 hgrid
      (sample a) p r
        (profilePrimalCenter P (Recurrence.posDef_of_isRoundedGrid hgrid) t sample p r)

/-- One adjoint sample obeys the same weak-product bound, with its independently
centered transposed-coefficient optimizer and adjoint weak root. -/
theorem ofReal_abs_adaptedPreYoungCutoff_adjointSample_le
    {l t : ℤ} {m0 : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid l (roundedGrid l m0))
    (P : Measure (CoeffSpace d)) (sample : CoeffSpace d → CoeffSpace d)
    (p r : Vec d) (a : CoeffSpace d) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid
    let center := profileAdjointCenter P hq t sample p r
    ENNReal.ofReal |Book.Ch02.average (adaptedDomain hq t) (fun x ↦
      adaptedPreYoungCutoff (roundedGrid l m0) hq t x * ((1 / 2 : ℝ) *
        vecDot
          ((centeredAdjointOptimizer (adaptedDomain hq t)
            (sample a) p r).toH1.grad x - center.1)
          (matVecMul (((sample a).transpose.coeffOn
              (adaptedDomain hq t)).toCoeffField x)
            ((centeredAdjointOptimizer (adaptedDomain hq t)
              (sample a) p r).toH1.grad x) - center.2)))| ≤
      ENNReal.ofReal
        (1 + divCurlDimensionCoeff d * adaptedCutoffDerivativeCoeff d *
          ((51 / 50 : ℝ) * (d : ℝ) ^ 2)) *
        profileAdjointWeakRoot m0 hq t sample p r center a ^ (2 : ℕ) := by
  simpa only [profileAdjointWeakRoot, diagonalWeakAdjointState,
    centeredAdjointOptimizer] using
    ofReal_abs_adaptedResponseCutoff_le_weakRoot_sq hm0 hgrid
      (sample a).transpose p r
        (profileAdjointCenter P (Recurrence.posDef_of_isRoundedGrid hgrid) t sample p r)

/-- The expectation of the literal primal cutoff product is controlled by the
primal weak quantity, with the rounded-grid distortion already absorbed. -/
theorem ofReal_abs_integral_adaptedPreYoungCutoff_primal_le
    {l t : ℤ} {m0 : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid l (roundedGrid l m0))
    (P : Measure (CoeffSpace d)) (sample : CoeffSpace d → CoeffSpace d)
    (p r : Vec d) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid
    let center := profilePrimalCenter P hq t sample p r
    ENNReal.ofReal |∫ a, Book.Ch02.average (adaptedDomain hq t) (fun x ↦
      adaptedPreYoungCutoff (roundedGrid l m0) hq t x * ((1 / 2 : ℝ) *
        vecDot
          ((centeredResponseOptimizer (adaptedDomain hq t)
            (sample a) p r).toH1.grad x - center.1)
          (matVecMul (((sample a).coeffOn
              (adaptedDomain hq t)).toCoeffField x)
            ((centeredResponseOptimizer (adaptedDomain hq t)
              (sample a) p r).toH1.grad x) - center.2))) ∂P| ≤
      ENNReal.ofReal
        (1 + divCurlDimensionCoeff d * adaptedCutoffDerivativeCoeff d *
          ((51 / 50 : ℝ) * (d : ℝ) ^ 2)) *
        profilePrimalWeakQuantity P m0 hq t sample p r := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  apply ofReal_abs_integral_le_mul_profilePrimalWeakQuantity
  filter_upwards [] with a
  exact ofReal_abs_adaptedPreYoungCutoff_primalSample_le hm0 hgrid
    P sample p r a

/-- The corresponding adjoint expectation is controlled by the independently
centered adjoint weak quantity. -/
theorem ofReal_abs_integral_adaptedPreYoungCutoff_adjoint_le
    {l t : ℤ} {m0 : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid l (roundedGrid l m0))
    (P : Measure (CoeffSpace d)) (sample : CoeffSpace d → CoeffSpace d)
    (p r : Vec d) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid
    let center := profileAdjointCenter P hq t sample p r
    ENNReal.ofReal |∫ a, Book.Ch02.average (adaptedDomain hq t) (fun x ↦
      adaptedPreYoungCutoff (roundedGrid l m0) hq t x * ((1 / 2 : ℝ) *
        vecDot
          ((centeredAdjointOptimizer (adaptedDomain hq t)
            (sample a) p r).toH1.grad x - center.1)
          (matVecMul (((sample a).transpose.coeffOn
              (adaptedDomain hq t)).toCoeffField x)
            ((centeredAdjointOptimizer (adaptedDomain hq t)
              (sample a) p r).toH1.grad x) - center.2))) ∂P| ≤
      ENNReal.ofReal
        (1 + divCurlDimensionCoeff d * adaptedCutoffDerivativeCoeff d *
          ((51 / 50 : ℝ) * (d : ℝ) ^ 2)) *
        profileAdjointWeakQuantity P m0 hq t sample p r := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  apply ofReal_abs_integral_le_mul_profileAdjointWeakQuantity
  filter_upwards [] with a
  exact ofReal_abs_adaptedPreYoungCutoff_adjointSample_le hm0 hgrid
    P sample p r a

end

end HCPolySupport.HighContrast.Response
