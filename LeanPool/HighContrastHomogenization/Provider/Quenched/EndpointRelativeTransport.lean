/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.PhysicalScaleTransport
public import LeanPool.HighContrastHomogenization.Provider.Quenched.TriadicRebasedDagger

/-!
# High-contrast homogenization: Provider.Quenched.EndpointRelativeTransport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Endpoint-relative coefficient transport

The physical-scale coefficient used by the quenched row is the same quotient
pullback as the coefficient-space triadic dilation used to define the rebased
law.  This identifies endpoint-relative tail estimates under the mapped law
with their pullbacks to the original law.
-/

namespace HCPolySupport.HighContrast.Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The two quotient-level realizations of triadic coefficient dilation agree. -/
theorem physical_scale_coeff_eq_triadicDilation (N : ℕ) (a : CoeffSpace d) :
    physical_scale_coeff N a = CoeffSpace.triadicDilation N a := by
  apply Subtype.ext
  apply AEEqFun.ext
  filter_upwards [physical_scale_coeff_ae N a,
    CoeffSpace.triadicDilation_ae N a] with x hphysical hdilation
  rw [hphysical, hdilation]
  rfl

/-- The source in endpoint units evaluates to the restored source divided by
the endpoint dilation factor. -/
theorem triadicRebasedSource_physical_scale_coeff (N : ℕ)
    (S : CoeffSpace d → ℝ) (a : CoeffSpace d) :
    triadicRebasedSource N S (physical_scale_coeff N a) =
      S a / (3 : ℝ) ^ N := by
  rw [physical_scale_coeff_eq_triadicDilation,
    triadicRebasedSource_triadicDilation]

/-- A measurable strict upper-tail event under the endpoint-rebased law is
exactly its physical-coefficient pullback under the original law. -/
theorem measureReal_triadicRebasedLaw_upperTailEvent
    (N : ℕ) {P : Measure (CoeffSpace d)} {F : CoeffSpace d → ℝ}
    (hF : Measurable F) (t : ℝ) :
    (triadicRebasedLaw N P).real {a | t < F a} =
      P.real {a | t < F (physical_scale_coeff N a)} := by
  rw [triadicRebasedLaw]
  change (Measure.map (CoeffSpace.triadicDilation N) P).real
      (F ⁻¹' Set.Ioi t) =
    P.real ((fun a => F (physical_scale_coeff N a)) ⁻¹' Set.Ioi t)
  rw [
    map_measureReal_apply (CoeffSpace.measurable_triadicDilation N)
      (hF measurableSet_Ioi)]
  congr 1
  ext a
  simp only [Set.mem_preimage,
    physical_scale_coeff_eq_triadicDilation]

end

end HCPolySupport.HighContrast.Quenched
