/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledLocalizationAssembly
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRateBearingCommonAffineGoodScaleEvent

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ScheduledLocalizationRowSupply

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The scheduled localization hypothesis from a ruled Whitney row supply

The scheduled localization clause consumes the scheduled localization
hypothesis: on the gauge-reduced domain it asks for a ruled scheduled
localization package together
with the two normalized Whitney row-energy caps of the corrector difference and
of the flux defect.

This module discharges every part of that demand which does not require a new
estimate — the gauge-reduced geometry, the elliptic source representative, the
Hardy coefficient, the distortion factor, the boundary energy, and the whole
package assembly — and isolates what remains as a single named supply,
`ScheduledLocalizationRowSupply`, stated at exactly the scheduled spelling.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory Set
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The residual supply -/

/-! ## Package assembly with the two rows retained -/

private theorem isEllipticFieldOn_of_pointwise_representative
    {lam Lam : ℝ} {f : CoeffField d} {U : Set (Vec d)} (hf : Measurable f)
    (hell : ∀ x ∈ U, IsEllipticMatrix lam Lam (f x)) (hU : MeasurableSet U) :
    IsEllipticFieldOn lam Lam U f := by
  classical
  refine ⟨?_, hell⟩
  refine measurable_pi_iff.2 fun i ↦ measurable_pi_iff.2 fun j ↦ ?_
  exact Measurable.ite hU
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hf))
    measurable_const

/-- The physical flux difference of an a.e. uniformly elliptic coefficient is
square integrable on a bounded convex domain. -/
theorem memVectorL2_physical_flux_difference
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (aSource : Source.AKL.Field d) (haSource : AEUniformlyEllipticField aSource)
    (aPhysical : CoeffField d)
    (haeSource : (⇑aSource : CoeffField d) =ᵐ[volume] aPhysical)
    (u h : H1Function U) :
    MemVectorL2 U (fun y ↦ matVecMul (aPhysical y) (u.grad y) - h.grad y) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hfMeasurable, hfElliptic, haSourceF⟩ :=
    exists_pointwise_elliptic_representative haSource hU.isBoundedDomain.isBounded
  have hfPhysical : f =ᵐ[volume] aPhysical := haSourceF.symm.trans haeSource
  have hfFlux : MemVectorL2 U (fun y ↦ matVecMul (f y) (u.grad y)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (isEllipticFieldOn_of_pointwise_representative
        hfMeasurable hfElliptic hU.isOpen.measurableSet)
      u.grad_memVectorL2
  have hPhysicalFlux : MemVectorL2 U
      (fun y ↦ matVecMul (aPhysical y) (u.grad y)) := by
    apply MemLp.ae_eq _ hfFlux
    filter_upwards [ae_restrict_of_ae hfPhysical] with y hy
    rw [hy]
  exact hPhysicalFlux.sub h.grad_memVectorL2

end

end HighContrast
end HCPolySupport
