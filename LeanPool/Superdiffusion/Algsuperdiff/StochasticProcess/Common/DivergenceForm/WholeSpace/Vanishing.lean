/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Continuity
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.LocalizedTailData
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry

/-!
# Vanishing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Vanishing at infinity of the analytic minimal resolvent

The uniform Agmon tail estimate is applied to the zero-trace solution on
each cube.  Its bound is independent of the cube, so it passes to the
pointwise supremum.  Compactly supported data are handled first; arbitrary
`C₀` data follow by uniform approximation and resolvent stability.
-/

namespace DivergenceFormProcess.Form

open CompactlySupported Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess.Semigroup
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal ZeroAtInfty RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- A fixed `H¹₀` representative of the local resolvent of a bounded datum. -/
def cubeDatumResolventH10 (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    H10Function (wholeSpaceCube d m) :=
  Classical.choose (ZeroTraceSobolev.exists_h10Function
    (isOpenBoundedConvexDomain_wholeSpaceCube d m)
    (alphaShiftedSolution A.a mu.property A.hnu
      (A.cubeEllipticity m)
      (boundedMeasurableToScalarL2
        (isOpenBoundedConvexDomain_wholeSpaceCube d m)
        (hf.comp measurable_subtype_coe) (fun y => hfD y))))

theorem cubeDatumResolventH10_value (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    (A.cubeDatumResolventH10 mu hf hfD m).toH1Function.toScalarL2 =
      alphaShiftedResolvent A.a mu.property A.hnu
        (A.cubeEllipticity m)
        (boundedMeasurableToScalarL2
          (isOpenBoundedConvexDomain_wholeSpaceCube d m)
          (hf.comp measurable_subtype_coe) (fun y => hfD y)) := by
  simpa only [alphaShiftedResolvent_apply] using!
    (Classical.choose_spec (ZeroTraceSobolev.exists_h10Function
      (isOpenBoundedConvexDomain_wholeSpaceCube d m)
      (alphaShiftedSolution A.a mu.property A.hnu
        (A.cubeEllipticity m)
        (boundedMeasurableToScalarL2
          (isOpenBoundedConvexDomain_wholeSpaceCube d m)
          (hf.comp measurable_subtype_coe) (fun y => hfD y))))).1

/-- The chosen local representative solves the scalar shifted equation with
the canonical `L²` representative of the datum. -/
theorem cubeDatumResolventH10_isScalarForcedWeakSolution
    (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    let F := boundedMeasurableToScalarL2
      (isOpenBoundedConvexDomain_wholeSpaceCube d m)
      (hf.comp measurable_subtype_coe) (fun y => hfD y)
    IsScalarForcedWeakSolution A.a (wholeSpaceCube d m)
      (fun y => F y - (mu : ℝ) *
        (A.cubeDatumResolventH10 mu hf hfD m).toH1Function.toFun y)
      (A.cubeDatumResolventH10 mu hf hfD m).toH1Function := by
  dsimp only
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  let F : ScalarL2 (wholeSpaceCube d m) :=
    boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
      (fun y => hfD y)
  let z : H10Function (wholeSpaceCube d m) := A.cubeDatumResolventH10 mu hf hfD m
  have hzclass : ZeroTraceSobolev.ofH10Function z =
      alphaShiftedSolution A.a mu.property A.hnu
        (A.cubeEllipticity m) F := by
    apply ZeroTraceSobolev.ext
    · simpa only [ZeroTraceSobolev.toL2_ofH10Function, z, F] using!
        A.cubeDatumResolventH10_value mu hf hfD m
    · exact (Classical.choose_spec (ZeroTraceSobolev.exists_h10Function hU
        (alphaShiftedSolution A.a mu.property A.hnu
          (A.cubeEllipticity m) F))).2
  apply isScalarForcedWeakSolution_sub_alpha_mul_of_isAlphaShiftedWeakSolution z
  rw [hzclass]
  exact alphaShiftedSolution_isAlphaShiftedWeakSolution A.a mu.property
    A.hnu (A.cubeEllipticity m) F

/-- A normalized nonnegative datum that vanishes on a ball satisfies the
localized split-skew tail.  All rough and divergence constants are read on
that ball; the upper ellipticity constant of the exhaustion cube does not
enter the conclusion. -/
theorem mul_toReal_analyticMinimalResolvent_le_localizedTail
    (L : WholeSpaceLocalizedSplitData A) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, |f x| ≤ 1)
    {x : Vec d} {r : ℝ} (hr : 0 < r)
    (hzero : ∀ y ∈ euclideanBall x r, f y = 0) :
    (mu : ℝ) * (A.analyticMinimalResolvent mu f hf hf1 x).toReal ≤
      L.tail mu x r := by
  obtain ⟨N, hN⟩ := exists_euclideanBall_subset_wholeSpaceCube x hr
  have htail : ∀ k, (mu : ℝ) *
      |A.analyticCubeResolvent mu f hf hf1 (k + N) x| ≤ L.tail mu x r := by
    intro k
    let m := k + N
    let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
    let F : ScalarL2 (wholeSpaceCube d m) :=
      boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
        (fun y ↦ hf1 y)
    let z : H10Function (wholeSpaceCube d m) :=
      A.cubeDatumResolventH10 mu hf hf1 m
    have hNm : N ≤ m := Nat.le_add_left N k
    have hball : euclideanBall x r ⊆ wholeSpaceCube d m :=
      hN.trans (wholeSpaceCube_mono hNm)
    have hFM : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d m), |F y| ≤ 1 := by
      simpa only [F, hU, abs_one] using
        abs_boundedMeasurableToScalarL2_le hU
          (hf.comp measurable_subtype_coe) (fun y ↦ hf1 y)
    have hresBound := abs_alpha_mul_alphaShiftedResolvent_le_ae A.a hU
      mu.property A.hnu (A.cubeEllipticity m) F 1 (by norm_num) hFM
    have hzcoe := z.toH1Function.coeFn_toScalarL2
    have hzvalue : z.toH1Function.toScalarL2 =
        alphaShiftedResolvent A.a mu.property A.hnu
          (A.cubeEllipticity m) F := by
      simpa only [z, F, hU] using A.cubeDatumResolventH10_value mu hf hf1 m
    have hMbound : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d m),
        |z.toH1Function.toFun y| ≤ 1 / (mu : ℝ) := by
      filter_upwards [hresBound, hzcoe] with y hb hz
      rw [← hz, hzvalue]
      rw [abs_mul, abs_of_pos mu.property] at hb
      exact (le_div_iff₀ mu.property).2 (by simpa only [mul_comm] using hb)
    have hFcoe := boundedMeasurableToScalarL2_coeFn hU
      (hf.comp measurable_subtype_coe) (fun y ↦ hf1 y)
    have hgzero : ∀ᵐ y ∂volume, y ∈ euclideanBall x r → F y = 0 := by
      have hae := (ae_restrict_iff' hU.isOpen.measurableSet).mp hFcoe
      filter_upwards [hae] with y hy hyball
      rw [hy (hball hyball), domainExtension_of_mem (hball hyball)]
      exact hzero y hyball
    let r₀ := L.clippedFreezingRadius x r
    have hr₀ : 0 < r₀ := L.clippedFreezingRadius_pos x hr
    have hr₀r : r₀ ≤ r / 2 := L.clippedFreezingRadius_le_half x r
    have hsmallBall : euclideanBall x (r₀ / 2) ⊆ wholeSpaceCube d m :=
      (Algsuperdiff.Section4.Provider.Schauder.euclideanBall_mono
        (by positivity : 0 ≤ r₀ / 2)
        (show r₀ / 2 ≤ r by
          calc
            r₀ / 2 ≤ (r / 2) / 2 := by gcongr
            _ ≤ r := by linarith only [hr])).trans hball
    have hrepCont :=
      (A.continuousOn_analyticCubeResolvent mu hf hf1 m).mono hsmallBall
    have hrepAe : A.analyticCubeResolvent mu f hf hf1 m =ᵐ[
        volume.restrict (euclideanBall x (r₀ / 2))]
        z.toH1Function.toFun := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsmallBall
          (A.analyticCubeResolvent_ae mu hf hf1 m),
        ae_restrict_of_ae_restrict_of_subset hsmallBall hzcoe] with y ha hz
      rw [ha, ← hz, hzvalue]
    simpa only [WholeSpaceLocalizedSplitData.tail, r₀] using
      (Decay.resolventTail_localized_representative hU.isOpen
        hU.isBoundedDomain A.hd L.holderExponent_mem L.delta_nonneg L.delta_le
        A.hnu (L.roughBound_nonneg x r hr.le)
        (L.smoothDivBound_nonneg x r hr.le) mu.property A.hameas
        (L.roughEllipticity m) L.split L.ksSkew L.klSkew L.klContDiff
        (by simpa only [z, F, hU] using
          A.cubeDatumResolventH10_isScalarForcedWeakSolution mu hf hf1 m)
        hMbound hr hr₀ hr₀r hball (L.roughBound_spec x r hr.le)
        (L.smoothDivBound_spec x r hr.le) (L.smallContrast_clipped x hr)
        hgzero hrepCont hrepAe)
  have hnonneg : ∀ m, 0 ≤ A.analyticCubeResolvent mu f hf hf1 m x :=
    fun m ↦ A.analyticCubeResolvent_nonneg mu hf hf0 hf1 m x
  have hsupTail : (mu : ℝ) * (⨆ k,
      A.analyticCubeResolvent mu f hf hf1 (k + N) x) ≤ L.tail mu x r := by
    have hdiv : (⨆ k, A.analyticCubeResolvent mu f hf hf1 (k + N) x) ≤
        L.tail mu x r / (mu : ℝ) := by
      refine ciSup_le fun k ↦ (le_div_iff₀ mu.property).2 ?_
      simpa only [abs_of_nonneg (hnonneg (k + N)), mul_comm] using htail k
    calc
      (mu : ℝ) * (⨆ k, A.analyticCubeResolvent mu f hf hf1 (k + N) x) ≤
          (mu : ℝ) * (L.tail mu x r / (mu : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv mu.property.le
      _ = L.tail mu x r := by
        rw [← mul_div_assoc,
          mul_div_cancel_left₀ _ (ne_of_gt (show 0 < (mu : ℝ) from mu.property))]
  have hshift := ciSup_nat_add_of_monotone
    (A.monotone_analyticCubeResolvent mu hf hf0 hf1 x)
    (by
      refine ⟨1 / (mu : ℝ), ?_⟩
      rintro y ⟨m, rfl⟩
      exact (le_abs_self _).trans
        (A.abs_analyticCubeResolvent_le mu hf (by norm_num) hf1 m x)) N
  rw [hshift] at hsupTail
  have ht := A.tendsto_analyticCubeResolvent mu hf hf0 (by norm_num) hf1 x
  have hlim := tendsto_nhds_unique
    (tendsto_atTop_ciSup (A.monotone_analyticCubeResolvent mu hf hf0 hf1 x)
      (by
        refine ⟨1 / (mu : ℝ), ?_⟩
        rintro y ⟨m, rfl⟩
        exact (le_abs_self _).trans
          (A.abs_analyticCubeResolvent_le mu hf (by norm_num) hf1 m x))) ht
  rwa [hlim] at hsupTail

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
