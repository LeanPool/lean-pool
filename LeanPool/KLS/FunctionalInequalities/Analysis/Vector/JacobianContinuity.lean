/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Vector.Jacobian
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Continuity and measurability of the volume factors

Mathlib proves the algebraic theory of
`LinearMap.normDet` but **not** its continuity in the operator, so the right-hand side of the area
formula is not yet known to be an integral of a measurable function.  This module supplies that.

`normDet A` is the square root of the determinant of the Gram operator `Aᵀ A`, and each step of
that description is continuous: the adjoint is a linear isometry, composition is continuous, the
determinant of a continuous linear endomorphism is continuous, and so is the square root.  The
measurability of the integrand then follows from `measurable_fderiv`, which needs **no**
differentiability hypothesis on the function.

The same argument applies verbatim to `coareaJacobian`, whose integrand the codimension-`m` coarea
formula will need on the other side.

**No area formula and no coarea formula are proved here.**
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Analysis

variable {H V W : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- `normDet` is the square root of the Gram determinant, in continuous-linear-map form. -/
theorem normDet_eq_sqrt_det (A : H →L[ℝ] V) :
    LinearMap.normDet (A : H →ₗ[ℝ] V)
      = Real.sqrt ((ContinuousLinearMap.adjoint A ∘L A).det) := by
  rw [← Real.sqrt_sq (LinearMap.normDet_nonneg (A : H →ₗ[ℝ] V))]
  congr 1
  exact_mod_cast ContinuousLinearMap.normDet_sq A

/-- The Gram operator depends continuously on the map. -/
theorem continuous_adjoint_comp :
    Continuous (fun A : H →L[ℝ] V => ContinuousLinearMap.adjoint A ∘L A) := by
  have hadj : Continuous (fun A : H →L[ℝ] V => (ContinuousLinearMap.adjoint A : V →L[ℝ] H)) :=
    (ContinuousLinearMap.adjoint : (H →L[ℝ] V) ≃ₗᵢ⋆[ℝ] (V →L[ℝ] H)).continuous
  exact (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := H) (F := V) (G := H)).continuous.comp
    (hadj.prodMk continuous_id)

/-- The area-formula volume factor is continuous in the differential. -/
theorem continuous_normDet :
    Continuous (fun A : H →L[ℝ] V => LinearMap.normDet (A : H →ₗ[ℝ] V)) := by
  simp only [normDet_eq_sqrt_det]
  exact Real.continuous_sqrt.comp
    (ContinuousLinearMap.continuous_det.comp continuous_adjoint_comp)

variable [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace V] [BorelSpace V] in
/-- The integrand of the area formula is measurable, for an **arbitrary** function.  No
differentiability hypothesis is needed: `fderiv` is measurable unconditionally and is zero where the
function is not differentiable. -/
theorem measurable_normDet_fderiv (g : H → V) :
    Measurable (fun y : H => LinearMap.normDet ((fderiv ℝ g y : H →ₗ[ℝ] V))) :=
  continuous_normDet.measurable.comp (measurable_fderiv ℝ g)

/-! ### The same for the coarea side -/

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V] in
/-- The coarea Jacobian is continuous in the differential. -/
theorem continuous_coareaJacobian :
    Continuous (fun L : V →L[ℝ] W => coareaJacobian L) := by
  have h : (fun L : V →L[ℝ] W => coareaJacobian L)
      = fun L : V →L[ℝ] W => LinearMap.normDet ((ContinuousLinearMap.adjoint L : W →ₗ[ℝ] V)) := by
    funext L
    rfl
  rw [h]
  exact continuous_normDet.comp
    (ContinuousLinearMap.adjoint : (V →L[ℝ] W) ≃ₗᵢ⋆[ℝ] (W →L[ℝ] V)).continuous

omit [MeasurableSpace H] [BorelSpace H] in
/-- The integrand of the codimension-`m` coarea formula is measurable, for an arbitrary function. -/
theorem measurable_coareaJacobian_fderiv [MeasurableSpace W] [BorelSpace W] (u : V → W) :
    Measurable (fun x : V => coareaJacobian (fderiv ℝ u x)) :=
  continuous_coareaJacobian.measurable.comp (measurable_fderiv ℝ u)

end FunctionalInequalities.Analysis
