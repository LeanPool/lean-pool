/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.FullSpaceLowDimClosedBall
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalNonPluripolar
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalNonPluripolarDensity

/-!
# A full-space chart patch carries the local smooth mass to the global measure

This module proves the measure-theoretic step left open by the closed-ball
Jacobian calculation.  On a relatively compact pole-free coordinate open set
inside one *concrete* `Patch`, the global mixed non-pluripolar measure equals
the local smooth density measure on inverse-chart images.  The proof follows
the actual definitions: restrict the global measure to the patch, evaluate the
patch pushforward, and invoke stabilization of the truncation-limit measure.

The final theorem combines this with the verified dimension-one closed-ball
identity.  It is intentionally one-piece only; no assertion about a finite
regular-patch family or the total `acTopMass` is made here.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped ContDiff ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.FullSpacePatchMeasure

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.AdmissibleCurrentFormPositivity
  FirstPass.MongeAmpere FirstPass.MixedMongeAmpere FirstPass.MixedNonPluripolar
  FirstPass.GlobalPotentialPatches
open GlobalNonPluripolar LocalNonPluripolarDensity FullSpaceRegularPatch
  FullSpaceClosedBallDomains FullSpaceClosedBallTransport FullSpaceLowDimClosedBall
  BedfordTaylor MixedNonPluripolar

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Restricting the global measure to one concrete patch, followed by the
literal `Patch.pushMeasure` evaluation, identifies an inverse-chart image with
the smooth mixed measure obtained from the stabilized truncation limit. -/
theorem globalMixedMeasure_coordinate_inverse_image_eq_smoothMixedMeasure
    {theta : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (theta i).val (u i))
    (Q : Patch theta u) (W : Opens (ComplexModel n)) (hWQ : W ≤ Q.domain)
    (k : ℕ) (hW : RelativelyCompactIn W Q.domain)
    (hWk : (W : Set (ComplexModel n)) ⊆ commonStrictLocus Q.domain Q.corrected k)
    (hsm : IsSmoothMixedPshOn W (fun i z => (Q.corrected i z).toReal))
    {S : Set (ComplexModel n)} (hSW : S ⊆ W) :
    globalMixedMeasure theta u hu (Q.chart.val.symm '' S) =
      smoothMixedMeasure W (fun i z => (Q.corrected i z).toReal) hsm S := by
  have hSQ : S ⊆ Q.domain := hSW.trans hWQ
  have hsource : Q.chart.val.symm '' S ⊆ (Q.source : Set M) := by
    rintro x ⟨z, hz, rfl⟩
    exact Q.map_target (hSQ hz)
  have hpreimage : (Q.domain : Set (ComplexModel n)) ∩
      Q.chart.val.symm ⁻¹' (Q.chart.val.symm '' S) = S := by
    ext z
    constructor
    · rintro ⟨hzD, y, hyS, hy⟩
      have hyD : y ∈ Q.domain := hSQ hyS
      have hzy : z = y := by
        calc
          z = Q.chart.val (Q.chart.val.symm z) :=
            (Q.chart.val.right_inv (Q.domain_le_target hzD)).symm
          _ = Q.chart.val (Q.chart.val.symm y) := congrArg Q.chart.val hy.symm
          _ = y := Q.chart.val.right_inv (Q.domain_le_target hyD)
      exact hzy.symm ▸ hyS
    · intro hz
      exact ⟨hSQ hz, ⟨z, hz, rfl⟩⟩
  have hpatch : patchMeasure Q (Q.chart.val.symm '' S) =
      mixedTruncationLimitMeasure Q.domain Q.corrected Q.plurisubharmonic S := by
    rw [patchMeasure, Q.pushMeasure_apply, hpreimage]
  have hrestrict :
      mixedTruncationLimitMeasure Q.domain Q.corrected Q.plurisubharmonic S =
        (mixedTruncationLimitMeasure Q.domain Q.corrected Q.plurisubharmonic).restrict
          (W : Set (ComplexModel n)) S := by
    symm
    rw [Measure.restrict_apply' W.isOpen.measurableSet,
      inter_eq_self_of_subset_left hSW]
  have hlocal := mixedTruncationLimitMeasure_restrict_smooth_of_original
    Q.plurisubharmonic k hW hWk hsm
  calc
    globalMixedMeasure theta u hu (Q.chart.val.symm '' S) =
        (globalMixedMeasure theta u hu).restrict (Q.source : Set M)
          (Q.chart.val.symm '' S) := by
      symm
      rw [Measure.restrict_apply' Q.source.isOpen.measurableSet,
        inter_eq_self_of_subset_left hsource]
    _ = patchMeasure Q (Q.chart.val.symm '' S) :=
      congrArg (fun mu : Measure M => mu (Q.chart.val.symm '' S))
        (globalMixedMeasure_restrict_patch hu Q)
    _ = mixedTruncationLimitMeasure Q.domain Q.corrected Q.plurisubharmonic S := hpatch
    _ = (mixedTruncationLimitMeasure Q.domain Q.corrected Q.plurisubharmonic).restrict
          (W : Set (ComplexModel n)) S := hrestrict
    _ = smoothMixedMeasure W (fun i z => (Q.corrected i z).toReal) hsm S :=
      congrArg (fun mu : Measure (ComplexModel n) => mu S) hlocal

/-- The diagonal specialization turns the stabilized mixed density into the
ordinary smooth Monge--Ampère measure.  Equality of the corrected patch
potentials with `f` is explicit local gauge data, not a comparison of masses. -/
theorem globalMixedMeasure_coordinate_inverse_image_eq_smoothMeasure_of_diagonal
    {theta : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : ThetaPlurisubharmonic theta.val u)
    (Q : Patch (fun _ : Fin n => theta) (fun _ => u))
    (W : Opens (ComplexModel n)) (hWQ : W ≤ Q.domain)
    (k : ℕ) (hW : RelativelyCompactIn W Q.domain)
    (hWk : (W : Set (ComplexModel n)) ⊆ commonStrictLocus Q.domain Q.corrected k)
    {f : ComplexModel n → ℝ} (hf : IsSmoothPshOn W f)
    (hcorrected : ∀ i, EqOn (fun z => (Q.corrected i z).toReal) f W)
    {S : Set (ComplexModel n)} (hSW : S ⊆ W) :
    globalMixedMeasure (fun _ : Fin n => theta) (fun _ => u) (fun _ => hu)
        (Q.chart.val.symm '' S) = smoothMeasure W f hf S := by
  let hdiag : IsSmoothMixedPshOn W (fun _ : Fin n => f) :=
    IsSmoothMixedPshOn.diagonal hf
  let hpatch : IsSmoothMixedPshOn W (fun i z => (Q.corrected i z).toReal) :=
    isSmoothMixedPshOn_of_eqOn hdiag hcorrected
  calc
    globalMixedMeasure (fun _ : Fin n => theta) (fun _ => u) (fun _ => hu)
        (Q.chart.val.symm '' S) =
        smoothMixedMeasure W (fun i z => (Q.corrected i z).toReal) hpatch S :=
      globalMixedMeasure_coordinate_inverse_image_eq_smoothMixedMeasure (fun _ => hu)
        Q W hWQ k hW hWk hpatch hSW
    _ = smoothMixedMeasure W (fun _ : Fin n => f) hdiag S :=
      congrArg (fun mu : Measure (ComplexModel n) => mu S)
        (smoothMixedMeasure_eq_of_eqOn hpatch hdiag hcorrected)
    _ = smoothMeasure W f hf S :=
      congrArg (fun mu : Measure (ComplexModel n) => mu S)
        (smoothMixedMeasure_diagonal W f hf hdiag)

variable {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}

/-- One full-space closed ball in complex dimension one is measured exactly by
the global diagonal non-pluripolar measure of a concrete compatible patch.
The patch compatibility is entirely local: it identifies the real corrected
potential and supplies a precompact strict truncation neighbourhood around the
coordinate image. -/
theorem closedBall_lintegral_patchDensity_eq_globalMixedMeasure_of_dim_eq_one
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
    (hn : n = 1)
    (Q : Patch (fun _ : Fin n => perturbedRepresentative p) (fun _ => p.potential))
    (hchart : Q.chart = complexChartAt (n := n) P.center)
    (W : Opens (ComplexModel n)) (hWD : W ≤ regularPotentialDomain P U)
    (hWQ : W ≤ Q.domain) (k : ℕ) (hW : RelativelyCompactIn W Q.domain)
    (hWk : (W : Set (ComplexModel n)) ⊆ commonStrictLocus Q.domain Q.corrected k)
    (hcorrected : ∀ i, EqOn (fun z => (Q.corrected i z).toReal)
      (fun z => g z + rho z) W)
    (himage : fullSpaceCoordinateParametrization P '' closedBall w r ⊆ W) :
    ∫⁻ x in closedBall w r, ENNReal.ofReal (patchDensity p P x) ∂volume =
      globalMixedMeasure (fun _ : Fin n => perturbedRepresentative p) (fun _ => p.potential)
        (fun _ => p.potential_psh.1)
          ((complexChartAt (n := n) P.center).val.symm ''
            (fullSpaceCoordinateParametrization P '' closedBall w r)) := by
  have hsmoothW : IsSmoothPshOn W (fun y => g y + rho y) :=
    ⟨hsmooth.1.mono hWD, hsmooth.2.1.mono hWD,
      fun z hz => hsmooth.2.2 z (hWD hz)⟩
  have hsmooth_restrict :
      smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
        (fullSpaceCoordinateParametrization P '' closedBall w r) =
      smoothMeasure W (fun y => g y + rho y) hsmoothW
        (fullSpaceCoordinateParametrization P '' closedBall w r) := by
    symm
    calc
      smoothMeasure W (fun y => g y + rho y) hsmoothW
          (fullSpaceCoordinateParametrization P '' closedBall w r) =
        (smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth).restrict
          (W : Set (ComplexModel n))
          (fullSpaceCoordinateParametrization P '' closedBall w r) :=
        congrArg (fun mu : Measure (ComplexModel n) =>
          mu (fullSpaceCoordinateParametrization P '' closedBall w r))
          (smoothMeasure_restrict hWD (fun y => g y + rho y) hsmooth hsmoothW).symm
      _ = smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
          (fullSpaceCoordinateParametrization P '' closedBall w r) := by
        rw [Measure.restrict_apply' W.isOpen.measurableSet,
          inter_eq_self_of_subset_left himage]
  calc
    ∫⁻ x in closedBall w r, ENNReal.ofReal (patchDensity p P x) ∂volume =
        smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
          (fullSpaceCoordinateParametrization P '' closedBall w r) :=
      closedBall_lintegral_patchDensity_eq_smoothMeasure_coordinateImage_of_dim_eq_one
        p P U hrho hg hpot w hball hsmooth hn
    _ = smoothMeasure W (fun y => g y + rho y) hsmoothW
          (fullSpaceCoordinateParametrization P '' closedBall w r) := hsmooth_restrict
    _ = globalMixedMeasure (fun _ : Fin n => perturbedRepresentative p) (fun _ => p.potential)
          (fun _ => p.potential_psh.1)
          ((complexChartAt (n := n) P.center).val.symm ''
            (fullSpaceCoordinateParametrization P '' closedBall w r)) := by
      simpa only [hchart, perturbedRepresentative] using
        (globalMixedMeasure_coordinate_inverse_image_eq_smoothMeasure_of_diagonal
          p.potential_psh.1 Q W hWQ k hW hWk hsmoothW hcorrected himage).symm

end SGPT.Foundations.Analysis.Pending.FullSpacePatchMeasure
