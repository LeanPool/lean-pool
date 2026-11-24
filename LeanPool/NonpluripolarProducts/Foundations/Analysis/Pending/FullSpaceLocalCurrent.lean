/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.FullSpaceRegularPatch
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.FullSpaceLowDimDensity

/-!
# Local smooth representative of a full-space current

This is the local analytic half of the full-space mass comparison.  On an
open coordinate patch where an admissible potential is represented by a smooth
real function `g`, and `ρ` is a smooth local potential for the perturbed
representative, the actual coordinate current is literally `ddᶜ (g + ρ)`.

The result is deliberately pointwise.  A later module applies it on each
closed regular parameter ball, combines it with the full-dimensional
biholomorphism, and then transports the resulting smooth measure through
`Patch.pushMeasure`.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped ContDiff Topology

namespace SGPT.Foundations.Analysis.Pending.FullSpaceLocalCurrent

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}

/-- On a pole-free smooth coordinate neighborhood, the coordinate current of
an admissible presentation is the `ddᶜ` of the ordinary corrected potential.
The two hypotheses on `g` are the literal local output of
`SmoothOffPoleSet`; they are not a mass-comparison assumption. -/
theorem coordinateCurrentForm_eq_smoothDDC_corrected
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (e : ComplexChart n M) {U : Set (ComplexModel n)} {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential (perturbedRepresentative p).val e U rho)
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hpot : EqOn (chartFunction p.potential e) (fun y => (g y : EReal)) U)
    {z : ComplexModel n} (hz : z ∈ U) :
    coordinateCurrentForm p e z = smoothDDC (fun y => g y + rho y) z := by
  have hreal : (fun y => (p.potential (e.val.symm y)).toReal) =ᶠ[𝓝 z] g := by
    filter_upwards [hrho.1.mem_nhds hz] with y hy
    change (chartFunction p.potential e y).toReal = g y
    rw [hpot hy, EReal.toReal_coe]
  rw [coordinateCurrentForm, ← hrho.2.2.2 hz, smoothDDC_congr hreal,
    smoothDDC_add hrho.1 hg hrho.2.2.1 hz]
  ac_rfl

end SGPT.Foundations.Analysis.Pending.FullSpaceLocalCurrent
