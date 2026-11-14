/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamPenalization

/-!
# CruxStreamInterchange

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Localized-tail penalization interchange for the stream field

The generic lemma isolates the compact-domain penalization limit from the
coefficient-dependent tail estimate.  The stream specialization supplies the
fixed-collar log-subexponential profile proved from localized split-skew data.
No whole-space small-contrast datum occurs in this module.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open MarkovProcess.Semigroup
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- A coefficient-generic interchange lemma: any eventually valid next-cube
comparison whose scalar error tends to zero yields the desired infimum bound. -/
theorem iInf_toReal_analyticPenalizedResolvent_le_cube_of_eventually_error
    (v : ℕ) (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, |f x| ≤ 1)
    {x : Vec d} (hx : x ∈ wholeSpaceCube d v)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (hcompare : ∀ᶠ n in atTop,
      (A.analyticPenalizedResolvent
        (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen
        n mu f hf hf1 x).toReal ≤
      A.analyticPenalizedCubeResolvent
        (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen
        n mu f hf hf1 (v + 1) x + error n) :
    (⨅ n : ℕ, (A.analyticPenalizedResolvent
      (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen
      n mu f hf hf1 x).toReal) ≤
      A.analyticCubeResolvent mu f hf hf1 v x := by
  let hV := isOpenBoundedConvexDomain_wholeSpaceCube d v
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d (v + 1)
  let F : ScalarL2 (wholeSpaceCube d (v + 1)) :=
    boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
      (fun y ↦ hf1 y)
  have hF0 : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d (v + 1)), 0 ≤ F y := by
    filter_upwards [boundedMeasurableToScalarL2_wholeSpaceCube_ae_eq hf hf1
      (v + 1)] with y hy
    rw [hy]
    exact hf0 y
  have hF1 : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d (v + 1)), |F y| ≤ 1 := by
    filter_upwards [boundedMeasurableToScalarL2_wholeSpaceCube_ae_eq hf hf1
      (v + 1)] with y hy
    rw [hy]
    exact hf1 y
  have hregPen : HasLocalHolderPenalizedResolvents A.a hU hV.isOpen A.hnu
      (A.cubeEllipticity (v + 1)) (1 / 2 : ℝ) A.nu⁻¹ :=
    hasLocalHolderPenalizedResolvents_continuousCoeff A.hd A.a
      hU hV.isOpen (wholeSpaceCube_subset_succ d v) A.hnu A.hsymm
      (A.skewContinuousOnCube (v + 1)) A.hnu (A.cubeEllipticity (v + 1))
  have hregV : HasContinuousShiftedResolvents A.a A.hnu
      (A.cubeEllipticity v) :=
    hasContinuousShiftedResolvents_continuousCoeff A.hd A.a hV
      A.hnu A.hsymm (A.skewContinuousOnCube v) A.hnu (A.cubeEllipticity v)
  obtain ⟨rep, limit, hrepcont, hlimitcont, hrepae, hlimitae, -, htend, -⟩ :=
    exists_penalization_everywhere_limit_reg A.a hV
      (by
        refine ⟨0, mem_wholeSpaceCube_iff.2 fun i ↦ ?_⟩
        have hp := pow_pos (by norm_num : (0 : ℝ) < 3) v
        simpa only [Pi.zero_apply] using ⟨neg_neg_of_pos hp, hp⟩) hU
      (wholeSpaceCube_subset_succ d v) mu.property A.hnu
      (A.cubeEllipticity (v + 1)) (by norm_num) hregPen hregV F hF0
      (by norm_num) hF1
  have hqeq := wholeSpacePenalizationPotential_ae_eq_penalizationPotential
    hU.isOpen.measurableSet (V := wholeSpaceCube d v)
    (U := wholeSpaceCube d (v + 1))
  have hrepEq : ∀ n, Set.EqOn
      (A.analyticPenalizedCubeResolvent hV.isOpen n mu f hf hf1 (v + 1))
      (rep n) (wholeSpaceCube d v) := by
    intro n
    have hop := potentialResolvent_eq_of_ae_eq_potential A.a mu.property A.hnu
      (A.cubeEllipticity (v + 1))
      (wholeSpacePenalizationPotential (wholeSpaceCube d v) n)
      (penalizationPotential (wholeSpaceCube d (v + 1))
        (wholeSpaceCube d v) n)
      (wholeSpacePenalizationPotential_isBounded hV.isOpen n (v + 1))
      (penalizationPotential_isBoundedNonnegative hU.isOpen.measurableSet
        hV.isOpen.measurableSet n) (hqeq n)
    have hana := A.analyticPenalizedCubeResolvent_ae hV.isOpen n mu hf hf1
      (v + 1)
    rw [hop] at hana
    have hpen : A.analyticPenalizedCubeResolvent hV.isOpen n mu f hf hf1
        (v + 1) =ᵐ[volumeMeasureOn (wholeSpaceCube d (v + 1))]
        penalizedResolvent A.a hU.isOpen hV.isOpen mu.property A.hnu
          (A.cubeEllipticity (v + 1)) n F := by
      simpa only [F, hU, hV, penalizedResolvent] using hana
    refine eqOn_of_continuousOn_of_ae_eq hV.isOpen
      ((A.continuousOn_analyticPenalizedCubeResolvent hV.isOpen n mu hf hf1
        (v + 1)).mono (wholeSpaceCube_subset_succ d v))
      (hrepcont n) ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (wholeSpaceCube_subset_succ d v) hpen, hrepae n] with y hy hz
    rw [hy, hz]
  have hlimitEq : Set.EqOn limit
      (A.analyticCubeResolvent mu f hf hf1 v) (wholeSpaceCube d v) := by
    have hrestrict := restrict_boundedMeasurableToScalarL2_succ hf hf1 v
    rw [hrestrict] at hlimitae
    have hana := A.analyticCubeResolvent_ae mu hf hf1 v
    refine eqOn_of_continuousOn_of_ae_eq hV.isOpen hlimitcont
      (A.continuousOn_analyticCubeResolvent mu hf hf1 v) ?_
    filter_upwards [hlimitae, hana] with y hy hz
    exact hy.trans hz.symm
  have hinner : Tendsto (fun n ↦
      A.analyticPenalizedCubeResolvent hV.isOpen n mu f hf hf1 (v + 1) x)
      atTop (nhds (A.analyticCubeResolvent mu f hf hf1 v x)) := by
    have h := htend x hx
    rw [hlimitEq hx] at h
    exact h.congr' (Filter.Eventually.of_forall fun n ↦ (hrepEq n hx).symm)
  have hrhs := hinner.add herror
  have hbdd : BddBelow (Set.range fun n : ℕ ↦
      (A.analyticPenalizedResolvent hV.isOpen n mu f hf hf1 x).toReal) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact ENNReal.toReal_nonneg
  have hle : ∀ᶠ n in atTop,
      (⨅ j : ℕ, (A.analyticPenalizedResolvent hV.isOpen j mu f hf hf1 x).toReal) ≤
        A.analyticPenalizedCubeResolvent hV.isOpen n mu f hf hf1 (v + 1) x +
          error n := by
    filter_upwards [hcompare] with n hn
    exact (ciInf_le hbdd n).trans hn
  have hlim := le_of_tendsto_of_tendsto tendsto_const_nhds hrhs hle
  simpa only [add_zero, hV] using hlim

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Filter HCPolySupport MeasureTheory Set Topology
open DivergenceFormProcess.Form MarkovProcess.Semigroup
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The normalized stream-field penalization interchange.  Fixed-collar
localized tails replace the unavailable global small-contrast estimate. -/
theorem iInf_toReal_streamAnalyticPenalizedResolvent_le_cube
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (v : ℕ) (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, |f x| ≤ 1)
    (hfsupp : ∀ᵐ x ∂volume, x ∉ wholeSpaceCube d v → f x = 0)
    {x : Vec d} (hx : x ∈ wholeSpaceCube d v) :
    (⨅ n : ℕ, ((streamWholeSpaceAnalyticData M omega).analyticPenalizedResolvent
      (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen
      n mu f hf hf1 x).toReal) ≤
      (streamWholeSpaceAnalyticData M omega).analyticCubeResolvent
        mu f hf hf1 v x := by
  let A := streamWholeSpaceAnalyticData M omega
  let error : ℕ → ℝ := fun n ↦
    streamFixedCollarTailProfile M omega v (Real.sqrt ((mu : ℝ) + n)) /
      (mu : ℝ)
  have hmassTop : Tendsto (fun n : ℕ ↦ (mu : ℝ) + n) atTop atTop := by
    have h := tendsto_atTop_add_const_right atTop (mu : ℝ)
      tendsto_natCast_atTop_atTop
    exact h.congr' (Filter.Eventually.of_forall fun n ↦ by simp only [add_comm])
  have hsqrtTop : Tendsto (fun n : ℕ ↦ Real.sqrt ((mu : ℝ) + n))
      atTop atTop := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hmassTop
    simpa only [← Real.sqrt_eq_rpow] using! h
  have htail : Tendsto (fun n : ℕ ↦
      streamFixedCollarTailProfile M omega v (Real.sqrt ((mu : ℝ) + n)))
      atTop (nhds 0) :=
    (tendsto_streamFixedCollarTailProfile_atTop M omega v).comp hsqrtTop
  have herror : Tendsto error atTop (nhds 0) := by
    simpa only [error, zero_div] using htail.div_const (mu : ℝ)
  have hsqrtEventually : ∀ᶠ n : ℕ in atTop,
      1 < Real.sqrt ((mu : ℝ) + n) :=
    hsqrtTop.eventually (eventually_gt_atTop 1)
  have hcompare : ∀ᶠ n : ℕ in atTop,
      (A.analyticPenalizedResolvent
        (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen
        n mu f hf hf1 x).toReal ≤
      A.analyticPenalizedCubeResolvent
        (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen
        n mu f hf hf1 (v + 1) x + error n := by
    filter_upwards [hsqrtEventually] with n hn
    exact toReal_streamAnalyticPenalizedResolvent_le_next_add_fixedCollarTail_of_subset
      M omega (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen v subset_rfl
      n mu hf hf0 hf1 hfsupp hn hx
  exact A.iInf_toReal_analyticPenalizedResolvent_le_cube_of_eventually_error
    v mu hf hf0 hf1 hx error herror hcompare

/-- The bounded stream-field penalization interchange, obtained by positive
normalization. -/
theorem iInf_toReal_streamAnalyticPenalizedResolvent_le_cube_of_bound
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (v : ℕ) (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hD : 0 < D)
    (hfD : ∀ x, |f x| ≤ D)
    (hfsupp : ∀ᵐ x ∂volume, x ∉ wholeSpaceCube d v → f x = 0)
    {x : Vec d} (hx : x ∈ wholeSpaceCube d v) :
    (⨅ n : ℕ, ((streamWholeSpaceAnalyticData M omega).analyticPenalizedResolvent
      (isOpenBoundedConvexDomain_wholeSpaceCube d v).isOpen
      n mu f hf hfD x).toReal) ≤
      (streamWholeSpaceAnalyticData M omega).analyticCubeResolvent
        mu f hf hfD v x := by
  let A := streamWholeSpaceAnalyticData M omega
  let g : Vec d → ℝ := fun y ↦ D⁻¹ * f y
  have hg : Measurable g := hf.const_smul D⁻¹
  have hg0 : ∀ y, 0 ≤ g y := fun y ↦
    mul_nonneg (inv_nonneg.2 hD.le) (hf0 y)
  have hg1 : ∀ y, |g y| ≤ 1 := by
    intro y
    change |D⁻¹ * f y| ≤ 1
    rw [abs_mul, abs_of_pos (inv_pos.2 hD)]
    calc
      D⁻¹ * |f y| ≤ D⁻¹ * D :=
        mul_le_mul_of_nonneg_left (hfD y) (inv_nonneg.2 hD.le)
      _ = 1 := inv_mul_cancel₀ hD.ne'
  have hgsupp : ∀ᵐ y ∂volume, y ∉ wholeSpaceCube d v → g y = 0 := by
    filter_upwards [hfsupp] with y hy
    intro hyV
    change D⁻¹ * f y = 0
    rw [hy hyV, mul_zero]
  have hnormalized := iInf_toReal_streamAnalyticPenalizedResolvent_le_cube
    M omega v mu hg hg0 hg1 hgsupp hx
  let hV := isOpenBoundedConvexDomain_wholeSpaceCube d v
  have hscalePen : ∀ n : ℕ,
      (A.analyticPenalizedResolvent hV.isOpen n mu f hf hfD x).toReal =
        D * (A.analyticPenalizedResolvent hV.isOpen n mu g hg hg1 x).toReal := by
    intro n
    have h := A.toReal_analyticPenalizedResolvent_smul hV.isOpen n mu hD.le
      hg hg0 (by norm_num : (0 : ℝ) ≤ 1) hg1 x
    simpa only [g, ← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul,
      mul_one] using h
  have hscaleCube : A.analyticCubeResolvent mu f hf hfD v x =
      D * A.analyticCubeResolvent mu g hg hg1 v x := by
    have h := A.analyticCubeResolvent_smul mu D hg hg1
      (fun y ↦ by
        rw [abs_mul, abs_of_pos hD]
        exact mul_le_mul_of_nonneg_left (hg1 y) hD.le) v x
    simpa only [g, ← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul,
      mul_one, abs_of_pos hD] using h
  have hbdd : BddBelow (Set.range fun n : ℕ ↦
      (A.analyticPenalizedResolvent hV.isOpen n mu g hg hg1 x).toReal) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact ENNReal.toReal_nonneg
  calc
    (⨅ n : ℕ, (A.analyticPenalizedResolvent hV.isOpen n mu f hf hfD x).toReal) =
        ⨅ n : ℕ, D *
          (A.analyticPenalizedResolvent hV.isOpen n mu g hg hg1 x).toReal := by
            apply iInf_congr
            exact hscalePen
    _ = D * (⨅ n : ℕ,
          (A.analyticPenalizedResolvent hV.isOpen n mu g hg hg1 x).toReal) :=
      (by
        simpa only [smul_eq_mul] using!
          ((OrderIso.smulRight hD).map_ciInf hbdd).symm)
    _ ≤ D * A.analyticCubeResolvent mu g hg hg1 v x :=
      mul_le_mul_of_nonneg_left hnormalized hD.le
    _ = A.analyticCubeResolvent mu f hf hfD v x := hscaleCube.symm

end

end Algsuperdiff.Section5.Field
