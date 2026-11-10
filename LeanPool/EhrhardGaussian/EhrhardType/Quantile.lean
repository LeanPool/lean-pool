/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.EhrhardType.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite quantiles with strict distribution functions

For a real probability law and `p ∈ (0,1)`, the infimum of thresholds with strict-CDF
value greater than `p` is finite. The strict inverse identity below includes atoms and
is the identity needed by the LX26 Lemma 2.5 construction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace EhrhardGaussian.EhrhardType

/-- The strict CDF of an arbitrary real probability measure is the left limit of its CDF. -/
theorem strictCDF_eq_leftLim_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) :
    μ.real (Iio a) = Function.leftLim (cdf μ) a := by
  have hnonneg : 0 ≤ Function.leftLim (cdf μ) a :=
    (cdf_nonneg μ (a - 1)).trans ((monotone_cdf μ).le_leftLim (by linarith))
  have h := (cdf μ).measure_Iio (tendsto_cdf_atBot μ) a
  rw [measure_cdf, sub_zero] at h
  rw [Measure.real, h, ENNReal.toReal_ofReal hnonneg]

/-- If a strict-CDF value exceeds `p`, it already exceeds it at a smaller threshold. -/
theorem exists_lt_strictCDF_gt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p a : ℝ} (ha : p < μ.real (Iio a)) :
    ∃ b < a, p < μ.real (Iio b) := by
  rw [strictCDF_eq_leftLim_cdf] at ha
  have h := ((monotone_cdf μ).tendsto_leftLim a).eventually (eventually_gt_nhds ha)
  obtain ⟨b, hb, hba⟩ := (h.and self_mem_nhdsWithin).exists
  obtain ⟨c, hbc, hca⟩ := exists_between hba
  refine ⟨c, hca, hb.trans_le ?_⟩
  rw [cdf_eq_real]
  exact measureReal_mono (Iic_subset_Iio.mpr hbc)

/-- The set defining a finite quantile is nonempty when `p < 1`. -/
theorem nonempty_strictCDF_gt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℝ} (hp : p < 1) : {a | p < μ.real (Iio a)}.Nonempty := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds hp)).exists
  refine ⟨a + 1, ha.trans_le ?_⟩
  rw [cdf_eq_real]
  exact measureReal_mono (Iic_subset_Iio.mpr (by linarith))

/-- The set defining a finite quantile is bounded below when `0 < p`. -/
theorem bddBelow_strictCDF_gt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℝ} (hp : 0 < p) : BddBelow {a | p < μ.real (Iio a)} := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually (eventually_lt_nhds hp)).exists
  refine ⟨a, ?_⟩
  intro b hb
  by_contra hab
  have hle : μ.real (Iio b) ≤ cdf μ a := by
    rw [cdf_eq_real]
    exact measureReal_mono (Iio_subset_Iic (le_of_not_ge hab))
  exact (hb.trans_le hle).not_ge ha.le

/-- The atom-compatible quantile of a real probability law, on its finite probability domain. -/
noncomputable def quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : Ioo (0 : ℝ) 1) : ℝ :=
  sInf {a | p.val < μ.real (Iio a)}

/-- Exact strict inverse identity, valid even at a lower-endpoint atom. -/
theorem quantile_lt_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : Ioo (0 : ℝ) 1) (a : ℝ) :
    quantile μ p < a ↔ p.val < μ.real (Iio a) := by
  rw [quantile, csInf_lt_iff (bddBelow_strictCDF_gt μ p.property.1)
    (nonempty_strictCDF_gt μ p.property.2)]
  constructor
  · rintro ⟨b, hb, hba⟩
    exact hb.trans_le (measureReal_mono (Iio_subset_Iio hba.le))
  · intro ha
    obtain ⟨b, hba, hb⟩ := exists_lt_strictCDF_gt μ ha
    exact ⟨b, hb, hba⟩

/-- Uniqueness from the strict inverse property, with no arbitrary choice of representative. -/
theorem quantile_unique (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : Ioo (0 : ℝ) 1) {q : ℝ}
    (hq : ∀ a, q < a ↔ p.val < μ.real (Iio a)) : q = quantile μ p := by
  exact eq_of_forall_gt_iff fun a => (hq a).trans (quantile_lt_iff μ p a).symm

/-- Increasing the probability increases its quantile. -/
theorem monotone_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Monotone (quantile μ) := by
  intro p q hpq
  apply le_of_forall_gt_imp_ge_of_dense
  intro a hqa
  exact ((quantile_lt_iff μ p a).mpr
    (lt_of_le_of_lt hpq ((quantile_lt_iff μ q a).mp hqa))).le

/-- The transport used in LX26: sample a finite quantile at the standard Gaussian CDF. -/
noncomputable def gaussianQuantileTransport (μ : Measure ℝ) [IsProbabilityMeasure μ] (z : ℝ) : ℝ :=
  quantile μ ⟨cdf (gaussianReal 0 1) z, standardGaussian_cdf_mem_Ioo z⟩

/-- The Gaussian quantile transport is monotone. -/
theorem monotone_gaussianQuantileTransport (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Monotone (gaussianQuantileTransport μ) := by
  intro x y hxy
  exact monotone_quantile μ ((monotone_cdf (gaussianReal 0 1)) hxy)

/-- The Gaussian quantile transport is measurable. -/
theorem measurable_gaussianQuantileTransport (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (gaussianQuantileTransport μ) :=
  (monotone_gaussianQuantileTransport μ).measurable

/-- The transport has the strict-sublevel characterization used in the source proof. -/
theorem gaussianQuantileTransport_lt_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (z a : ℝ) :
    gaussianQuantileTransport μ z < a ↔ cdf (gaussianReal 0 1) z < μ.real (Iio a) :=
  quantile_lt_iff μ _ a

/-- The normal-CDF quantile construction realizes the original law, including its atoms. -/
theorem map_gaussianQuantileTransport (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (gaussianReal 0 1).map (gaussianQuantileTransport μ) = μ := by
  have hstrict : ∀ a : ℝ,
      ((gaussianReal 0 1).map (gaussianQuantileTransport μ)) (Iio a) = μ (Iio a) := by
    intro a
    rw [Measure.map_apply (measurable_gaussianQuantileTransport μ) measurableSet_Iio]
    have hpre : gaussianQuantileTransport μ ⁻¹' Iio a =
        {z | cdf (gaussianReal 0 1) z < μ.real (Iio a)} := by
      ext z
      exact gaussianQuantileTransport_lt_iff μ z a
    rw [hpre]
    by_cases hzero : μ.real (Iio a) = 0
    · have hempty : {z | cdf (gaussianReal 0 1) z < μ.real (Iio a)} = ∅ := by
        ext z
        simp only [mem_ofPred_eq, hzero, not_lt.mpr (cdf_nonneg _ _), mem_empty_iff_false]
      rw [hempty, measure_empty]
      exact ((measureReal_eq_zero_iff (measure_ne_top μ _)).mp hzero).symm
    by_cases hone : μ.real (Iio a) = 1
    · have huniv : {z | cdf (gaussianReal 0 1) z < μ.real (Iio a)} = univ := by
        ext z
        simp only [mem_ofPred_eq, hone, (standardGaussian_cdf_mem_Ioo z).2, mem_univ]
      rw [huniv, measure_univ]
      exact ((ENNReal.toReal_eq_one_iff _).mp hone).symm
    have hp : μ.real (Iio a) ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne measureReal_nonneg (Ne.symm hzero),
        lt_of_le_of_ne measureReal_le_one hone⟩
    obtain ⟨b, hb, _⟩ := existsUnique_standardGaussian_quantile hp
    have hinterval : {z | cdf (gaussianReal 0 1) z < μ.real (Iio a)} = Iio b := by
      ext z
      rw [mem_ofPred_eq, ← hb, strictMono_standardGaussian_cdf.lt_iff_lt]
      rfl
    rw [hinterval]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    exact (strictCDF_standardGaussian b).trans hb
  apply Measure.ext_of_Ici
  intro a
  rw [← compl_Iio, measure_compl measurableSet_Iio (measure_ne_top _ _),
    measure_compl measurableSet_Iio (measure_ne_top _ _), hstrict, measure_univ, measure_univ]

end EhrhardGaussian.EhrhardType
