/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PositiveDistributionMeasure
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Pending uniqueness for measures representing distributions

This file supplies the uniqueness statement omitted from the first-pass
positive-distribution measure construction.  It is formulated for arbitrary
regular locally finite measures on an open subset of a finite-dimensional real
vector space and uses smooth-test separation of Radon--Nikodym densities.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set TopologicalSpace
open scoped CompactlySupported Distributions Manifold

namespace SGPT.Foundations.Analysis.Pending

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens E}

/-- Regular locally finite measures on an open set are determined by their
integrals against ambient smooth test functions supported in that open set. -/
theorem Measure.eq_of_testFunction_integral_eq
    (μ ν : Measure Ω) [μ.Regular] [ν.Regular]
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (h : ∀ φ : 𝓓(Ω, ℝ), (∫ x : Ω, φ x ∂μ) = ∫ x : Ω, φ x ∂ν) :
    μ = ν := by
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let ξ : Measure Ω := μ + ν
  have hμξ : μ ≪ ξ := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hνξ : ν ≪ ξ := Measure.AbsolutelyContinuous.rfl.add_right' μ
  have hfμ : LocallyIntegrable (fun x : Ω => (μ.rnDeriv ξ x).toReal) ξ := by
    rw [locallyIntegrable_iff]
    intro K hK
    exact Measure.integrableOn_toReal_rnDeriv
      hK.measure_ne_top
  have hfν : LocallyIntegrable (fun x : Ω => (ν.rnDeriv ξ x).toReal) ξ := by
    rw [locallyIntegrable_iff]
    intro K hK
    exact Measure.integrableOn_toReal_rnDeriv
      hK.measure_ne_top
  have haeReal :
      (fun x : Ω => (μ.rnDeriv ξ x).toReal) =ᵐ[ξ]
        fun x : Ω => (ν.rnDeriv ξ x).toReal := by
    apply ae_eq_of_integral_contMDiff_smul_eq 𝓘(ℝ, E) hfμ hfν
    intro g hgdiff hgsupp
    let ĝ : E → ℝ := Subtype.val.extend g 0
    have hĝdiff := (hgdiff.extend_zero hgsupp).contDiff
    have hĝsupp : HasCompactSupport ĝ := hgsupp.extend_zero continuous_subtype_val
    have hĝΩ : tsupport ĝ ⊆ Ω :=
      (hgsupp.tsupport_extend_zero_subset continuous_subtype_val).trans
        (Subtype.coe_image_subset _ _)
    let φ : 𝓓(Ω, ℝ) := ⟨ĝ, hĝdiff, hĝsupp, hĝΩ⟩
    calc
      (∫ x : Ω, g x • (μ.rnDeriv ξ x).toReal ∂ξ) =
          ∫ x : Ω, (μ.rnDeriv ξ x).toReal * g x ∂ξ := by
            congr 1
            funext x
            simp [mul_comm]
      _ = ∫ x : Ω, g x ∂μ := integral_toReal_rnDeriv_mul hμξ
      _ = ∫ x : Ω, φ x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp [φ, ĝ]
      _ = ∫ x : Ω, φ x ∂ν := h φ
      _ = ∫ x : Ω, g x ∂ν := by
        apply integral_congr_ae
        filter_upwards with x
        simp [φ, ĝ]
      _ = ∫ x : Ω, (ν.rnDeriv ξ x).toReal * g x ∂ξ :=
        (integral_toReal_rnDeriv_mul hνξ).symm
      _ = ∫ x : Ω, g x • (ν.rnDeriv ξ x).toReal ∂ξ := by
        congr 1
        funext x
        simp [mul_comm]
  have hae : μ.rnDeriv ξ =ᵐ[ξ] ν.rnDeriv ξ := by
    filter_upwards [haeReal, Measure.rnDeriv_ne_top μ ξ,
      Measure.rnDeriv_ne_top ν ξ] with x hx hμtop hνtop
    exact (ENNReal.toReal_eq_toReal_iff' hμtop hνtop).mp hx
  calc
    μ = ξ.withDensity (μ.rnDeriv ξ) :=
      (Measure.withDensity_rnDeriv_eq μ ξ hμξ).symm
    _ = ξ.withDensity (ν.rnDeriv ξ) := withDensity_congr_ae hae
    _ = ν := Measure.withDensity_rnDeriv_eq ν ξ hνξ

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A locally integrable real density has locally finite positive-part
measure.  This is the local-finiteness input needed when a signed density is
split into its positive and negative parts. -/
theorem Measure.isLocallyFiniteMeasure_withDensity_ofReal
    (mu : Measure Ω) [SigmaFinite mu]
    {f : Ω → ℝ} (hf : LocallyIntegrable f mu) :
    IsLocallyFiniteMeasure (mu.withDensity fun x => ENNReal.ofReal (f x)) := by
  constructor
  intro x
  obtain ⟨s, hs, hfs⟩ := hf x
  refine ⟨s, hs, ?_⟩
  rw [withDensity_apply']
  exact hfs.setLIntegral_lt_top

/-- A finite sum of locally finite measures is locally finite. -/
theorem Measure.isLocallyFiniteMeasure_add
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (mu nu : Measure X) [IsLocallyFiniteMeasure mu]
    [IsLocallyFiniteMeasure nu] : IsLocallyFiniteMeasure (mu + nu) := by
  constructor
  intro x
  obtain ⟨s, hs, hmus⟩ := mu.finiteAt_nhds x
  obtain ⟨t, ht, hnut⟩ := nu.finiteAt_nhds x
  refine ⟨s ∩ t, Filter.inter_mem hs ht, ?_⟩
  simp only [FunLike.coe_add, Pi.add_apply]
  exact ENNReal.add_lt_top.mpr
    ⟨(measure_mono inter_subset_left).trans_lt hmus,
      (measure_mono inter_subset_right).trans_lt hnut⟩

/-- A finset sum of locally finite measures is locally finite. -/
theorem Measure.isLocallyFiniteMeasure_finset_sum
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (s : Finset ι) (mu : ι → Measure X)
    (hmu : ∀ i ∈ s, IsLocallyFiniteMeasure (mu i)) :
    IsLocallyFiniteMeasure (∑ i ∈ s, mu i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      infer_instance
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      let _ : IsLocallyFiniteMeasure (mu a) := hmu a (Finset.mem_insert_self a s)
      let _ : IsLocallyFiniteMeasure (∑ i ∈ s, mu i) :=
        ih fun i hi => hmu i (Finset.mem_insert_of_mem hi)
      exact Measure.isLocallyFiniteMeasure_add _ _

/-- A measure sum over a finite type preserves local finiteness. -/
theorem Measure.isLocallyFiniteMeasure_sum_finite
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [Finite ι]
    (mu : ι → Measure X) (hmu : ∀ i, IsLocallyFiniteMeasure (mu i)) :
    IsLocallyFiniteMeasure (Measure.sum mu) := by
  let := Fintype.ofFinite ι
  rw [Measure.sum_fintype]
  exact Measure.isLocallyFiniteMeasure_finset_sum Finset.univ mu
    (fun i _ => hmu i)

/-- If a locally integrable density induces a positive distribution, then it
is nonnegative almost everywhere.  The proof compares its positive-part
measure with the Riesz measure of the distribution; uniqueness forces the
negative-part measure to vanish. -/
theorem ae_nonneg_of_positiveDistribution_integral
    {T : 𝓓'(Ω, ℝ)} (hT : PositiveDistribution T)
    (mu : Measure Ω) [IsLocallyFiniteMeasure mu]
    {f : Ω → ℝ} (hfmeas : Measurable f) (hf : LocallyIntegrable f mu)
    (hrep : ∀ φ : 𝓓(Ω, ℝ), T φ = ∫ x : Ω, φ x * f x ∂mu) :
    ∀ᵐ x ∂mu, 0 ≤ f x := by
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let rhoPos : Measure Ω := mu.withDensity fun x => ENNReal.ofReal (f x)
  let rhoNeg : Measure Ω := mu.withDensity fun x => ENNReal.ofReal (-f x)
  let _ : IsLocallyFiniteMeasure rhoPos :=
    Measure.isLocallyFiniteMeasure_withDensity_ofReal mu hf
  let _ : IsLocallyFiniteMeasure rhoNeg :=
    Measure.isLocallyFiniteMeasure_withDensity_ofReal mu hf.neg
  obtain ⟨nu, hnuReg, hnuLoc, hnu⟩ := hT.exists_regular_measure
  let _ : nu.Regular := hnuReg
  let _ : IsLocallyFiniteMeasure nu := hnuLoc
  let _ : IsLocallyFiniteMeasure (nu + rhoNeg) :=
    Measure.isLocallyFiniteMeasure_add nu rhoNeg
  have hmeasure : rhoPos = nu + rhoNeg := by
    apply Measure.eq_of_testFunction_integral_eq
    intro φ
    let g₀ : C_c(Ω, ℝ) := testFunctionToCompactlySupportedLM Ω φ
    let g : Ω → ℝ := g₀
    have hgcont : Continuous g := g₀.continuous
    have hgsupp : HasCompactSupport g := g₀.hasCompactSupport
    have hg_apply (x : Ω) : g x = φ x := by
      simp [g, g₀]
    have hfAbs : LocallyIntegrable (fun x => |f x|) mu := by
      intro x
      simpa [Real.norm_eq_abs] using (hf x).norm
    have hfNegPart : LocallyIntegrable (fun x => max (-f x) 0) mu := by
      apply hfAbs.mono
      · exact (hfmeas.neg.max measurable_const).aestronglyMeasurable
      · filter_upwards with x
        have hxnonneg : 0 ≤ max (-f x) 0 := le_max_right _ _
        simpa only [Real.norm_eq_abs, abs_abs, abs_of_nonneg hxnonneg] using
          max_le (neg_le_abs (f x)) (abs_nonneg (f x))
    have hfg : Integrable (fun x => f x * g x) mu := by
      simpa [smul_eq_mul] using
        hf.integrable_smul_right_of_hasCompactSupport hgcont hgsupp
    have hnegfg : Integrable (fun x => max (-f x) 0 * g x) mu := by
      simpa [smul_eq_mul] using
        hfNegPart.integrable_smul_right_of_hasCompactSupport hgcont hgsupp
    have hgnu : Integrable g nu := hgcont.integrable_of_hasCompactSupport hgsupp
    have hgrhoNeg : Integrable g rhoNeg :=
      hgcont.integrable_of_hasCompactSupport hgsupp
    have hposIntegral :
        (∫ x, g x ∂rhoPos) =
          ∫ x, f x * g x + max (-f x) 0 * g x ∂mu := by
      rw [integral_withDensity_eq_integral_toReal_smul₀
        hfmeas.ennreal_ofReal.aemeasurable
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) g]
      apply integral_congr_ae
      filter_upwards with x
      simp only [ENNReal.toReal_ofReal', smul_eq_mul]
      rcases le_total 0 (f x) with hx | hx
      · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
      · simp [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
    have hnegIntegral :
        (∫ x, g x ∂rhoNeg) = ∫ x, max (-f x) 0 * g x ∂mu := by
      change (∫ x, g x ∂(mu.withDensity fun x => ENNReal.ofReal ((-f) x))) =
        ∫ x, max (-f x) 0 * g x ∂mu
      rw [integral_withDensity_eq_integral_toReal_smul₀
        hfmeas.neg.ennreal_ofReal.aemeasurable
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) g]
      apply integral_congr_ae
      filter_upwards with x
      simp [ENNReal.toReal_ofReal', smul_eq_mul]
    calc
      ∫ x, φ x ∂rhoPos = ∫ x, g x ∂rhoPos := rfl
      _ = (∫ x, f x * g x ∂mu) +
          ∫ x, max (-f x) 0 * g x ∂mu := by
        rw [hposIntegral, integral_add hfg hnegfg]
      _ = T φ + ∫ x, g x ∂rhoNeg := by
        rw [hnegIntegral]
        congr 1
        simpa only [hg_apply, mul_comm] using (hrep φ).symm
      _ = (∫ x, g x ∂nu) + ∫ x, g x ∂rhoNeg := by
        congr 1
        simpa only [hg_apply] using (hnu φ).symm
      _ = ∫ x, g x ∂(nu + rhoNeg) :=
        (MeasureTheory.integral_add_measure hgnu hgrhoNeg).symm
      _ = ∫ x, φ x ∂(nu + rhoNeg) := rfl
  have hrhoNeg_le : rhoNeg ≤ rhoPos := by
    rw [hmeasure]
    exact Measure.le_add_left le_rfl
  have hrhoNeg_ac : rhoNeg ≪ rhoPos :=
    Measure.absolutelyContinuous_of_le hrhoNeg_le
  have hrhoNeg_sing : rhoNeg ⟂ₘ rhoPos := by
    exact (withDensity_ofReal_mutuallySingular (μ := mu) hfmeas).symm
  have hrhoNeg_zero : rhoNeg = 0 :=
    Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular
      hrhoNeg_ac hrhoNeg_sing
  have hzero : (fun x => ENNReal.ofReal (-f x)) =ᵐ[mu] 0 :=
    (withDensity_eq_zero_iff
      hfmeas.neg.ennreal_ofReal.aemeasurable).mp hrhoNeg_zero
  filter_upwards [hzero] with x hx
  exact neg_nonpos.mp (ENNReal.ofReal_eq_zero.mp hx)

end SGPT.Foundations.Analysis.Pending
