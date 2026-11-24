/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.FullSpaceClosedBallTransport
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.FullSpaceLocalCurrent
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.FullSpaceLowDimDensity

/-!
# A smooth current on one full-space regular closed ball

For a full-dimensional regular patch, this module connects three already
verified interfaces on one compact parameter piece:

* the low-dimensional exterior-power formula for `patchDensity`,
* the pointwise identity `T = ddᶜ (g + ρ)` off the poles, and
* the Jacobian transport formula for the corresponding smooth measure.

The result is deliberately a *single-piece* statement.  It neither identifies
the resulting smooth measure with an arbitrary global non-pluripolar measure
nor sums a finite regular-patch family.  Those later steps require the separate
local-patch/gauge and localization arguments.  All current and smoothness
data here are ordinary local witnesses, rather than an assumed mass bound.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace Metric
open scoped ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.FullSpaceLowDimClosedBall

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.AdmissibleCurrentFormPositivity
  FirstPass.MongeAmpere
open FullSpaceRegularPatch FullSpaceClosedBallDomains FullSpaceClosedBallTransport
  FullSpaceLocalCurrent FullSpaceLowDimDensity BedfordTaylor

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}

/-- On a full-space regular patch of complex dimension one, the actual
parameter density is the smooth density of the pulled-back corrected local
potential.  The proof uses the verified dimension-one exterior-power identity
and the holomorphic `ddᶜ` chain rule; it makes no ambient-mass assertion. -/
theorem patchDensity_eq_smoothDensity_corrected_of_dim_eq_one
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential (perturbedRepresentative p).val
      (complexChartAt (n := n) P.center) U rho)
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hpot : EqOn (chartFunction p.potential (complexChartAt (n := n) P.center))
      (fun y => (g y : EReal)) U)
    {w : ComplexModel n} (hw : w ∈ regularParameterDomain P U) (hn : n = 1) :
    patchDensity p P w =
      smoothDensity (fun x => g (fullSpaceCoordinateParametrization P x) +
        rho (fullSpaceCoordinateParametrization P x)) w := by
  let hbio := fullSpaceCoordinateParametrization_isBiholomorphic P
  have hwA : w ∈ fullParameterDomain P :=
    (mem_regularParameterDomain_iff P U w).mp hw |>.1
  have hwU : P.coordinateParametrization w ∈ U :=
    (mem_regularParameterDomain_iff P U w).mp hw |>.2
  have hsub : (regularParameterDomain P U : Set (ComplexModel n)) ⊆
      (fullParameterDomain P : Set (ComplexModel n)) := fun x hx =>
    (mem_regularParameterDomain_iff P U x).mp hx |>.1
  have hmap : MapsTo (fullSpaceCoordinateParametrization P)
      (regularParameterDomain P U : Set (ComplexModel n))
      (regularPotentialDomain P U : Set (ComplexModel n)) := by
    intro x hx
    obtain ⟨hxA, hxU⟩ := (mem_regularParameterDomain_iff P U x).mp hx
    exact ⟨hxU, hbio.mapsTo hxA⟩
  have hF : ContDiffOn ℂ ∞ (fullSpaceCoordinateParametrization P)
      (regularParameterDomain P U : Set (ComplexModel n)) := hbio.holo.mono hsub
  have hF_eq : fullSpaceCoordinateParametrization P = P.coordinateParametrization := rfl
  have hcorrected : ContDiffOn ℝ ∞ (fun y => g y + rho y)
      (regularPotentialDomain P U : Set (ComplexModel n)) :=
    (hg.add hrho.2.2.1).mono fun _ hy => hy.1
  have hpull : ContDiffOn ℝ ∞
      (fun x => g (fullSpaceCoordinateParametrization P x) +
        rho (fullSpaceCoordinateParametrization P x))
      (regularParameterDomain P U : Set (ComplexModel n)) :=
    hcorrected.comp (hF.restrict_scalars ℝ) hmap
  have htwo : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hw_nhds : (regularParameterDomain P U : Set (ComplexModel n)) ∈ nhds w :=
    (regularParameterDomain P U).isOpen.mem_nhds hw
  have hpull2 : ContDiffAt ℝ 2
      (fun x => g (fullSpaceCoordinateParametrization P x) +
        rho (fullSpaceCoordinateParametrization P x)) w :=
    ((hpull w hw).contDiffAt hw_nhds).of_le htwo
  have hcurrent : coordinateCurrentForm p (complexChartAt (n := n) P.center)
      (fullSpaceCoordinateParametrization P w) =
      smoothDDC (fun y => g y + rho y) (fullSpaceCoordinateParametrization P w) := by
    simpa only [fullSpaceCoordinateParametrization_apply] using
      (coordinateCurrentForm_eq_smoothDDC_corrected p
        (complexChartAt (n := n) P.center) hrho hg hpot hwU)
  have hddc : smoothDDC
      (fun x => g (fullSpaceCoordinateParametrization P x) +
        rho (fullSpaceCoordinateParametrization P x)) w =
      (smoothDDC (fun y => g y + rho y) (fullSpaceCoordinateParametrization P
        w)).compContinuousLinearMap
        (fderiv ℝ (fullSpaceCoordinateParametrization P) w) :=
    FirstPass.HolomorphicDDC.smoothDDC_comp
      (regularParameterDomain P U).isOpen (regularPotentialDomain P U).isOpen hF
      hcorrected hmap hw
  have hVone : (fullSpaceSubvariety V hcarrier hdim).dim = 1 := by
    simpa only [fullSpaceSubvariety] using hn
  calc
    patchDensity p P w =
        normalizedTopPowerDensity
          ((coordinateCurrentForm p (complexChartAt (n := n) P.center)
            (fullSpaceCoordinateParametrization P w)).compContinuousLinearMap
            (fderiv ℝ (fullSpaceCoordinateParametrization P) w)) := by
          rw [hF_eq]
          exact patchDensity_eq_normalizedTopPowerDensity_of_dim_eq_one p P w hVone
    _ = normalizedTopPowerDensity
          ((smoothDDC (fun y => g y + rho y)
            (fullSpaceCoordinateParametrization P w)).compContinuousLinearMap
            (fderiv ℝ (fullSpaceCoordinateParametrization P) w)) := by rw [hcurrent]
    _ = normalizedTopPowerDensity
          (smoothDDC (fun x => g (fullSpaceCoordinateParametrization P x) +
            rho (fullSpaceCoordinateParametrization P x)) w) :=
      congrArg normalizedTopPowerDensity hddc.symm
    _ = smoothDensity (fun x => g (fullSpaceCoordinateParametrization P x) +
      rho (fullSpaceCoordinateParametrization P x)) w :=
      normalizedTopPowerDensity_smoothDDC hpull2

/-- In complex dimension two, the same local density identification holds on
a pole-free coordinate neighbourhood.  The pole-free premise is a literal
property of the chosen local neighbourhood, used only to invoke the existing
dimension-two `(1,1)` certificate. -/
theorem patchDensity_eq_smoothDensity_corrected_of_dim_eq_two
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential (perturbedRepresentative p).val
      (complexChartAt (n := n) P.center) U rho)
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hpot : EqOn (chartFunction p.potential (complexChartAt (n := n) P.center))
      (fun y => (g y : EReal)) U)
    (hnoPole : ∀ z ∈ U, (complexChartAt (n := n) P.center).val.symm z ∉
      poleSet p.potential)
    {w : ComplexModel n} (hw : w ∈ regularParameterDomain P U) (hn : n = 2) :
    patchDensity p P w =
      smoothDensity (fun x => g (fullSpaceCoordinateParametrization P x) +
        rho (fullSpaceCoordinateParametrization P x)) w := by
  let hbio := fullSpaceCoordinateParametrization_isBiholomorphic P
  have hwA : w ∈ fullParameterDomain P :=
    (mem_regularParameterDomain_iff P U w).mp hw |>.1
  have hwU : P.coordinateParametrization w ∈ U :=
    (mem_regularParameterDomain_iff P U w).mp hw |>.2
  have hsub : (regularParameterDomain P U : Set (ComplexModel n)) ⊆
      (fullParameterDomain P : Set (ComplexModel n)) := fun x hx =>
    (mem_regularParameterDomain_iff P U x).mp hx |>.1
  have hmap : MapsTo (fullSpaceCoordinateParametrization P)
      (regularParameterDomain P U : Set (ComplexModel n))
      (regularPotentialDomain P U : Set (ComplexModel n)) := by
    intro x hx
    obtain ⟨hxA, hxU⟩ := (mem_regularParameterDomain_iff P U x).mp hx
    exact ⟨hxU, hbio.mapsTo hxA⟩
  have hF : ContDiffOn ℂ ∞ (fullSpaceCoordinateParametrization P)
      (regularParameterDomain P U : Set (ComplexModel n)) := hbio.holo.mono hsub
  have hF_eq : fullSpaceCoordinateParametrization P = P.coordinateParametrization := rfl
  have hcorrected : ContDiffOn ℝ ∞ (fun y => g y + rho y)
      (regularPotentialDomain P U : Set (ComplexModel n)) :=
    (hg.add hrho.2.2.1).mono fun _ hy => hy.1
  have hpull : ContDiffOn ℝ ∞
      (fun x => g (fullSpaceCoordinateParametrization P x) +
        rho (fullSpaceCoordinateParametrization P x))
      (regularParameterDomain P U : Set (ComplexModel n)) :=
    hcorrected.comp (hF.restrict_scalars ℝ) hmap
  have htwo : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hw_nhds : (regularParameterDomain P U : Set (ComplexModel n)) ∈ nhds w :=
    (regularParameterDomain P U).isOpen.mem_nhds hw
  have hpull2 : ContDiffAt ℝ 2
      (fun x => g (fullSpaceCoordinateParametrization P x) +
        rho (fullSpaceCoordinateParametrization P x)) w :=
    ((hpull w hw).contDiffAt hw_nhds).of_le htwo
  have hcurrent : coordinateCurrentForm p (complexChartAt (n := n) P.center)
      (fullSpaceCoordinateParametrization P w) =
      smoothDDC (fun y => g y + rho y) (fullSpaceCoordinateParametrization P w) := by
    simpa only [fullSpaceCoordinateParametrization_apply] using
      (coordinateCurrentForm_eq_smoothDDC_corrected p
        (complexChartAt (n := n) P.center) hrho hg hpot hwU)
  have hddc : smoothDDC
      (fun x => g (fullSpaceCoordinateParametrization P x) +
        rho (fullSpaceCoordinateParametrization P x)) w =
      (smoothDDC (fun y => g y + rho y) (fullSpaceCoordinateParametrization P
        w)).compContinuousLinearMap
        (fderiv ℝ (fullSpaceCoordinateParametrization P) w) :=
    FirstPass.HolomorphicDDC.smoothDDC_comp
      (regularParameterDomain P U).isOpen (regularPotentialDomain P U).isOpen hF
      hcorrected hmap hw
  have hVtwo : (fullSpaceSubvariety V hcarrier hdim).dim = 2 := by
    simpa only [fullSpaceSubvariety] using hn
  calc
    patchDensity p P w =
        normalizedTopPowerDensity
          ((coordinateCurrentForm p (complexChartAt (n := n) P.center)
            (fullSpaceCoordinateParametrization P w)).compContinuousLinearMap
            (fderiv ℝ (fullSpaceCoordinateParametrization P) w)) := by
          rw [hF_eq]
          exact patchDensity_eq_normalizedTopPowerDensity_of_dim_eq_two p P w hVtwo hwA
            (hnoPole _ hwU)
    _ = normalizedTopPowerDensity
          ((smoothDDC (fun y => g y + rho y)
            (fullSpaceCoordinateParametrization P w)).compContinuousLinearMap
            (fderiv ℝ (fullSpaceCoordinateParametrization P) w)) := by rw [hcurrent]
    _ = normalizedTopPowerDensity
          (smoothDDC (fun x => g (fullSpaceCoordinateParametrization P x) +
            rho (fullSpaceCoordinateParametrization P x)) w) :=
      congrArg normalizedTopPowerDensity hddc.symm
    _ = smoothDensity (fun x => g (fullSpaceCoordinateParametrization P x) +
      rho (fullSpaceCoordinateParametrization P x)) w :=
      normalizedTopPowerDensity_smoothDDC hpull2

/-- A compact parameter piece in complex dimension one has exactly the smooth
mass of its coordinate image.  This is the requested single-piece bridge from
the actual restricted-mass density to a genuine smooth measure. -/
theorem lintegral_patchDensity_eq_smoothMeasure_coordinateImage_of_dim_eq_one
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential (perturbedRepresentative p).val
      (complexChartAt (n := n) P.center) U rho)
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hpot : EqOn (chartFunction p.potential (complexChartAt (n := n) P.center))
      (fun y => (g y : EReal)) U)
    {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKU : K ⊆ (regularParameterDomain P U : Set (ComplexModel n)))
    (hsmooth : IsSmoothPshOn (regularPotentialDomain P U) (fun y => g y + rho y))
    (hn : n = 1) :
    ∫⁻ w in K, ENNReal.ofReal (patchDensity p P w) ∂volume =
      smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
        (fullSpaceCoordinateParametrization P '' K) := by
  calc
    ∫⁻ w in K, ENNReal.ofReal (patchDensity p P w) ∂volume =
        ∫⁻ w in K, ENNReal.ofReal
          (smoothDensity (fun x => g (fullSpaceCoordinateParametrization P x) +
            rho (fullSpaceCoordinateParametrization P x)) w) ∂volume := by
      refine setLIntegral_congr_fun hK.measurableSet fun w hw => ?_
      rw [patchDensity_eq_smoothDensity_corrected_of_dim_eq_one p P U hrho hg hpot
        (hKU hw) hn]
    _ = smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
          (fullSpaceCoordinateParametrization P '' K) :=
      (smoothMeasure_coordinateImage_eq_lintegral_smoothDensity_comp P U hK hKU hsmooth).symm

/-- The dimension-two version of the single compact-piece bridge.  Its only
extra input is the explicit pole-free certificate for the local chart domain. -/
theorem lintegral_patchDensity_eq_smoothMeasure_coordinateImage_of_dim_eq_two
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential (perturbedRepresentative p).val
      (complexChartAt (n := n) P.center) U rho)
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hpot : EqOn (chartFunction p.potential (complexChartAt (n := n) P.center))
      (fun y => (g y : EReal)) U)
    (hnoPole : ∀ z ∈ U, (complexChartAt (n := n) P.center).val.symm z ∉
      poleSet p.potential)
    {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKU : K ⊆ (regularParameterDomain P U : Set (ComplexModel n)))
    (hsmooth : IsSmoothPshOn (regularPotentialDomain P U) (fun y => g y + rho y))
    (hn : n = 2) :
    ∫⁻ w in K, ENNReal.ofReal (patchDensity p P w) ∂volume =
      smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
        (fullSpaceCoordinateParametrization P '' K) := by
  calc
    ∫⁻ w in K, ENNReal.ofReal (patchDensity p P w) ∂volume =
        ∫⁻ w in K, ENNReal.ofReal
          (smoothDensity (fun x => g (fullSpaceCoordinateParametrization P x) +
            rho (fullSpaceCoordinateParametrization P x)) w) ∂volume := by
      refine setLIntegral_congr_fun hK.measurableSet fun w hw => ?_
      rw [patchDensity_eq_smoothDensity_corrected_of_dim_eq_two p P U hrho hg hpot hnoPole
        (hKU hw) hn]
    _ = smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
          (fullSpaceCoordinateParametrization P '' K) :=
      (smoothMeasure_coordinateImage_eq_lintegral_smoothDensity_comp P U hK hKU hsmooth).symm

/-- A closed parameter ball contained in the regular-potential intersection
is the promised concrete compact piece in complex dimension one. -/
theorem closedBall_lintegral_patchDensity_eq_smoothMeasure_coordinateImage_of_dim_eq_one
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential (perturbedRepresentative p).val
      (complexChartAt (n := n) P.center) U rho)
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hpot : EqOn (chartFunction p.potential (complexChartAt (n := n) P.center))
      (fun y => (g y : EReal)) U)
    (w : ComplexModel n) {r : ℝ}
    (hball : closedBall w r ⊆ (regularParameterDomain P U : Set (ComplexModel n)))
    (hsmooth : IsSmoothPshOn (regularPotentialDomain P U) (fun y => g y + rho y))
    (hn : n = 1) :
    ∫⁻ x in closedBall w r, ENNReal.ofReal (patchDensity p P x) ∂volume =
      smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
        (fullSpaceCoordinateParametrization P '' closedBall w r) :=
  lintegral_patchDensity_eq_smoothMeasure_coordinateImage_of_dim_eq_one p P U hrho hg hpot
    (isCompact_closedBall w r) hball hsmooth hn

/-- A pole-free closed parameter ball has the analogous exact smooth-mass
identity in complex dimension two. -/
theorem closedBall_lintegral_patchDensity_eq_smoothMeasure_coordinateImage_of_dim_eq_two
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential (perturbedRepresentative p).val
      (complexChartAt (n := n) P.center) U rho)
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hpot : EqOn (chartFunction p.potential (complexChartAt (n := n) P.center))
      (fun y => (g y : EReal)) U)
    (hnoPole : ∀ z ∈ U, (complexChartAt (n := n) P.center).val.symm z ∉
      poleSet p.potential)
    (w : ComplexModel n) {r : ℝ}
    (hball : closedBall w r ⊆ (regularParameterDomain P U : Set (ComplexModel n)))
    (hsmooth : IsSmoothPshOn (regularPotentialDomain P U) (fun y => g y + rho y))
    (hn : n = 2) :
    ∫⁻ x in closedBall w r, ENNReal.ofReal (patchDensity p P x) ∂volume =
      smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
        (fullSpaceCoordinateParametrization P '' closedBall w r) :=
  lintegral_patchDensity_eq_smoothMeasure_coordinateImage_of_dim_eq_two p P U hrho hg hpot
    hnoPole (isCompact_closedBall w r) hball hsmooth hn

end SGPT.Foundations.Analysis.Pending.FullSpaceLowDimClosedBall
