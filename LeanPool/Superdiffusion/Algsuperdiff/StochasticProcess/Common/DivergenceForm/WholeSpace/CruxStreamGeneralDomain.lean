/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamEquality

/-!
# CruxStreamGeneralDomain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# S-free crux comparison on bounded part domains

The localized stream tail works on any bounded part domain after embedding it
in a centered exhaustion cube.  This extends the stream crux equality from the
centered cubes to every open bounded convex part domain.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Algsuperdiff.Section5.Field
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal RealInnerProductSpace ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- A vanishing-error exterior-penalization interchange on a bounded part
domain. -/
theorem iInf_toReal_analyticPenalizedResolvent_le_of_isRepresentative_of_error
    {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) (v : ℕ)
    (hVcube : V ⊆ wholeSpaceCube d v) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hD : 0 < D) (hfD : ∀ x, |f x| ≤ D)
    {u : Vec d → ℝ} (hucont : ContinuousOn u V)
    (hurep : u =ᵐ[volumeMeasureOn V] ZeroTraceSobolev.toL2
      (alphaShiftedSolution A.a mu.property A.hnu (partEllipticity A hV)
        (partDatumL2 hV hf hfD)))
    {x : Vec d} (hx : x ∈ V) (error : ℕ → ℝ)
    (herror : Tendsto error atTop (nhds 0))
    (hcompare : ∀ᶠ n in atTop,
      (A.analyticPenalizedResolvent hV.isOpen n mu f hf hfD x).toReal ≤
        A.analyticPenalizedCubeResolvent hV.isOpen n mu f hf hfD (v + 1) x +
          error n) :
    (⨅ n : ℕ, (A.analyticPenalizedResolvent hV.isOpen n mu f hf hfD x).toReal) ≤
      u x := by
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d (v + 1)
  have hVU : V ⊆ wholeSpaceCube d (v + 1) :=
    hVcube.trans (wholeSpaceCube_subset_succ d v)
  let F : ScalarL2 (wholeSpaceCube d (v + 1)) :=
    boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe) (fun y => hfD y)
  have hF0 : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d (v + 1)), 0 ≤ F y := by
    filter_upwards [boundedMeasurableToScalarL2_wholeSpaceCube_ae_eq hf hfD
      (v + 1)] with y hy
    rw [hy]
    exact hf0 y
  have hFD : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d (v + 1)), |F y| ≤ D := by
    filter_upwards [boundedMeasurableToScalarL2_wholeSpaceCube_ae_eq hf hfD
      (v + 1)] with y hy
    rw [hy]
    exact hfD y
  have hregPen : HasLocalHolderPenalizedResolvents A.a hU hV.isOpen A.hnu
      (A.cubeEllipticity (v + 1)) (1 / 2 : ℝ) A.nu⁻¹ :=
    hasLocalHolderPenalizedResolvents_continuousCoeff A.hd A.a hU hV.isOpen
      hVU A.hnu A.hsymm (A.skewContinuousOnCube (v + 1)) A.hnu
      (A.cubeEllipticity (v + 1))
  have hregV : HasContinuousShiftedResolvents A.a A.hnu
      ((A.cubeEllipticity (v + 1)).mono hV.isOpen.measurableSet hVU) :=
    hasContinuousShiftedResolvents_mono_continuousCoeff A.hd A.a hV hVU A.hnu
      A.hsymm (A.skewContinuousOnCube (v + 1)) A.hnu (A.cubeEllipticity (v + 1))
  obtain ⟨rep, limit, hrepcont, hlimitcont, hrepae, hlimitae, -, htend, -⟩ :=
    exists_penalization_everywhere_limit_reg A.a hV ⟨x, hx⟩ hU hVU mu.property
      A.hnu (A.cubeEllipticity (v + 1)) (by norm_num) hregPen hregV F hF0
      hD.le hFD
  have hqeq := wholeSpacePenalizationPotential_ae_eq_penalizationPotential
    hU.isOpen.measurableSet (V := V) (U := wholeSpaceCube d (v + 1))
  have hrepEq : ∀ n, Set.EqOn
      (A.analyticPenalizedCubeResolvent hV.isOpen n mu f hf hfD (v + 1))
      (rep n) V := by
    intro n
    have hop := potentialResolvent_eq_of_ae_eq_potential A.a mu.property A.hnu
      (A.cubeEllipticity (v + 1)) (wholeSpacePenalizationPotential V n)
      (penalizationPotential (wholeSpaceCube d (v + 1)) V n)
      (wholeSpacePenalizationPotential_isBounded hV.isOpen n (v + 1))
      (penalizationPotential_isBoundedNonnegative hU.isOpen.measurableSet
        hV.isOpen.measurableSet n) (hqeq n)
    have hana := A.analyticPenalizedCubeResolvent_ae hV.isOpen n mu hf hfD (v + 1)
    rw [hop] at hana
    have hpen : A.analyticPenalizedCubeResolvent hV.isOpen n mu f hf hfD
        (v + 1) =ᵐ[volumeMeasureOn (wholeSpaceCube d (v + 1))]
        penalizedResolvent A.a hU.isOpen hV.isOpen mu.property A.hnu
          (A.cubeEllipticity (v + 1)) n F := by
      simpa only [F, hU, penalizedResolvent] using hana
    refine eqOn_of_continuousOn_of_ae_eq hV.isOpen
      ((A.continuousOn_analyticPenalizedCubeResolvent hV.isOpen n mu hf hfD
        (v + 1)).mono hVU) (hrepcont n) ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hVU hpen, hrepae n]
      with y hy hz
    rw [hy, hz]
  have hlimitEq : Set.EqOn limit u V := by
    have hrestrict := restrictScalarL2ToPart_boundedMeasurableToScalarL2 hV hU
      hVU hf hfD
    rw [hrestrict] at hlimitae
    refine eqOn_of_continuousOn_of_ae_eq hV.isOpen hlimitcont hucont ?_
    filter_upwards [hlimitae, hurep] with y hy hz
    rw [hy, hz]
    exact congrArg (fun w ↦ ZeroTraceSobolev.toL2 w y)
      (alphaShiftedSolution_congr_ellipticity A.a mu.property A.hnu A.hnu
        ((A.cubeEllipticity (v + 1)).mono hV.isOpen.measurableSet hVU)
        (partEllipticity A hV) (partDatumL2 hV hf hfD))
  have hinner : Tendsto (fun n ↦
      A.analyticPenalizedCubeResolvent hV.isOpen n mu f hf hfD (v + 1) x)
      atTop (nhds (u x)) := by
    have h := htend x hx
    rw [hlimitEq hx] at h
    exact h.congr' (Filter.Eventually.of_forall fun n ↦ (hrepEq n hx).symm)
  have hrhs := hinner.add herror
  have hbdd : BddBelow (Set.range fun n : ℕ ↦
      (A.analyticPenalizedResolvent hV.isOpen n mu f hf hfD x).toReal) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact ENNReal.toReal_nonneg
  have hle : ∀ᶠ n in atTop,
      (⨅ j : ℕ, (A.analyticPenalizedResolvent hV.isOpen j mu f hf hfD x
        ).toReal) ≤ A.analyticPenalizedCubeResolvent hV.isOpen n mu f hf hfD
          (v + 1) x + error n := by
    filter_upwards [hcompare] with n hn
    exact (ciInf_le hbdd n).trans hn
  have hlim := le_of_tendsto_of_tendsto tendsto_const_nhds hrhs hle
  simpa only [add_zero] using hlim

end WholeSpaceAnalyticData

namespace WholeSpaceBarrierData

variable {M : ABKModel d} {omega : FullSample d M.gamma}
  (P : WholeSpaceBarrierData (streamWholeSpaceAnalyticData M omega))

/-- The localized stream tail gives the penalization upper bound on every
bounded part domain. -/
theorem iInf_toReal_analyticPenalizedResolvent_le_utilde_stream {D : ℝ}
    (hD : 0 < D) (hfD : ∀ y, |P.f y| ≤ D) {x : Vec d} (hx : x ∈ P.V) :
    (⨅ n : ℕ, ((streamWholeSpaceAnalyticData M omega).analyticPenalizedResolvent
      P.hV.isOpen n P.lam P.f P.hf hfD x).toReal) ≤ P.utilde x := by
  let A := streamWholeSpaceAnalyticData M omega
  let v := partCubeIndex P.hV
  let error : ℕ → ℝ := fun n ↦ D *
    (streamFixedCollarTailProfile M omega v (Real.sqrt ((P.lam : ℝ) + n)) /
      (P.lam : ℝ))
  have hsupp : ∀ᵐ y ∂volume, y ∉ P.V → P.f y = 0 := by
    filter_upwards [P.hfV] with y hy hynot
    rw [hy, Set.indicator_of_notMem hynot]
  let g : Vec d → ℝ := fun y => D⁻¹ * P.f y
  have hg : Measurable g := P.hf.const_smul D⁻¹
  have hg0 : ∀ y, 0 ≤ g y := fun y =>
    mul_nonneg (inv_nonneg.mpr hD.le) (P.hf0 y)
  have hg1 : ∀ y, |g y| ≤ 1 := by
    intro y
    rw [show g y = D⁻¹ * P.f y by rfl, abs_mul, abs_of_pos (inv_pos.mpr hD)]
    calc
      D⁻¹ * |P.f y| ≤ D⁻¹ * D :=
        mul_le_mul_of_nonneg_left (hfD y) (inv_nonneg.mpr hD.le)
      _ = 1 := inv_mul_cancel₀ hD.ne'
  have hgsupp : ∀ᵐ y ∂volume, y ∉ P.V → g y = 0 := by
    filter_upwards [hsupp] with y hy hynot
    rw [show g y = D⁻¹ * P.f y by rfl, hy hynot, mul_zero]
  have hscaleRes : ∀ n : ℕ,
      (A.analyticPenalizedResolvent P.hV.isOpen n P.lam P.f P.hf hfD x).toReal =
        D * (A.analyticPenalizedResolvent P.hV.isOpen n P.lam g hg hg1 x).toReal := by
    intro n
    have h := A.toReal_analyticPenalizedResolvent_smul P.hV.isOpen n P.lam
      hD.le hg hg0 (by norm_num : (0 : ℝ) ≤ 1) hg1 x
    simpa only [g, ← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul, mul_one] using h
  have hscaleCube : ∀ n : ℕ,
      A.analyticPenalizedCubeResolvent P.hV.isOpen n P.lam P.f P.hf hfD
          (v + 1) x =
        D * A.analyticPenalizedCubeResolvent P.hV.isOpen n P.lam g hg hg1
          (v + 1) x := by
    intro n
    have h := A.analyticPenalizedCubeResolvent_smul P.hV.isOpen n P.lam D hg hg1
      (fun y => by
        rw [abs_mul, abs_of_pos hD]
        exact mul_le_mul_of_nonneg_left (hg1 y) hD.le) (v + 1) x
    simpa only [g, ← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul, mul_one,
      abs_of_pos hD] using h
  have hmassTop : Tendsto (fun n : ℕ ↦ (P.lam : ℝ) + n) atTop atTop := by
    have h := tendsto_atTop_add_const_right atTop (P.lam : ℝ)
      tendsto_natCast_atTop_atTop
    exact h.congr' (Filter.Eventually.of_forall fun n ↦ by simp only [add_comm])
  have hsqrtTop : Tendsto (fun n : ℕ ↦ Real.sqrt ((P.lam : ℝ) + n))
      atTop atTop := by
    simpa only [← Real.sqrt_eq_rpow, Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hmassTop
  have htail := (tendsto_streamFixedCollarTailProfile_atTop M omega v).comp hsqrtTop
  have herror : Tendsto error atTop (nhds 0) := by
    simpa only [error, zero_div, mul_zero, Function.comp_def] using
      (htail.div_const (P.lam : ℝ)).const_mul D
  have hsqrtEventually : ∀ᶠ n : ℕ in atTop,
      1 < Real.sqrt ((P.lam : ℝ) + n) :=
    hsqrtTop.eventually (eventually_gt_atTop 1)
  refine A.iInf_toReal_analyticPenalizedResolvent_le_of_isRepresentative_of_error
    P.hV v (subset_wholeSpaceCube_partCubeIndex P.hV) P.lam P.hf P.hf0 hD hfD
    P.hutildeCont.continuousOn P.hutildeRep hx error herror ?_
  filter_upwards [hsqrtEventually] with n hn
  have hnorm :=
    Algsuperdiff.Section5.Field.toReal_streamAnalyticPenalizedResolvent_le_next_add_fixedCollarTail_of_subset
      M omega P.hV.isOpen v (subset_wholeSpaceCube_partCubeIndex P.hV) n P.lam
      hg hg0 hg1 hgsupp hn (subset_wholeSpaceCube_partCubeIndex P.hV hx)
  rw [hscaleRes n, hscaleCube n]
  calc
    D * (A.analyticPenalizedResolvent P.hV.isOpen n P.lam g hg hg1 x).toReal ≤
        D * (A.analyticPenalizedCubeResolvent P.hV.isOpen n P.lam g hg hg1
          (v + 1) x + streamFixedCollarTailProfile M omega v
            (Real.sqrt ((P.lam : ℝ) + n)) / (P.lam : ℝ)) :=
      mul_le_mul_of_nonneg_left hnorm hD.le
    _ = D * A.analyticPenalizedCubeResolvent P.hV.isOpen n P.lam g hg hg1
          (v + 1) x + error n := by ring

/-- S-free upper comparison on every bounded part domain. -/
theorem killedResolvent_le_partResolvent_stream_general
    (R : PositiveC0ContractiveResolvent (Vec d)) (hreg : R.OnePointRegular)
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : (streamWholeSpaceAnalyticData M omega
      ).KernelResolventIdentifiesAnalyticMinimal R)
    {x : Vec d} (hx : x ∈ P.V) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' P.V)
        (OnePoint.isOpen_image_coe.mpr P.hV.isOpen) (P.lam : ℝ)
        (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun y => ENNReal.ofReal (P.f y))) (x : OnePoint (Vec d)) ≤
      ENNReal.ofReal (P.utilde x) := by
  have hD : (0 : ℝ) < max P.D 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hfD : ∀ y, |P.f y| ≤ max P.D 1 := fun y =>
    (P.hfD y).trans (le_max_left _ _)
  exact P.killedResolvent_le_ofReal_of_iInf_le R hreg hcons hid hD.le hfD
    (P.iInf_toReal_analyticPenalizedResolvent_le_utilde_stream hD hfD hx)

/-- **S-free crux equality on every open bounded convex part domain.** -/
theorem killedResolvent_eq_partResolvent_stream_general
    (R : PositiveC0ContractiveResolvent (Vec d)) (hreg : R.OnePointRegular)
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : (streamWholeSpaceAnalyticData M omega
      ).KernelResolventIdentifiesAnalyticMinimal R)
    (hT : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
      R.toContractiveResolvent.operator mu g =
        ((streamWholeSpaceC0BarrierData M omega).resolvent
          ).toContractiveResolvent.operator mu g)
    {x : Vec d} (hx : x ∈ P.V) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' P.V)
        (OnePoint.isOpen_image_coe.mpr P.hV.isOpen) (P.lam : ℝ)
        (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun y => ENNReal.ofReal (P.f y))) (x : OnePoint (Vec d)) =
      ENNReal.ofReal (P.utilde x) := by
  let _ := hreg.metricSpace
  let _ := hreg.completeSpace
  exact le_antisymm (P.killedResolvent_le_partResolvent_stream_general
    R hreg hcons hid hx) (P.killedResolvent_ge_partResolvent_wholeSpace_of_c0Barrier
      (streamWholeSpaceC0BarrierData M omega) R hreg hid (fun _ _ => hT _ _) hx)

end WholeSpaceBarrierData

end

end DivergenceFormProcess.Form
