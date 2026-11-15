/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

public import LeanPool.Copula.Distribution.ProbabilityIntegralTransform
import LeanPool.Copula.CDF.Continuity
import LeanPool.Copula.CDF.Extensionality
public import LeanPool.Copula.CDF

/-! # Sklar's theorem with continuous marginals

The copula is the joint law of the marginal CDF transforms. Equality of
lower-orthant probabilities is proved almost everywhere, allowing flat CDFs.
-/

public section

open MeasureTheory Set Filter
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- A coordinate law of a probability measure on real vectors. -/
@[expose]
noncomputable def marginal (μ : ProbabilityMeasure (Fin d → ℝ)) (i : Fin d) : Measure ℝ :=
  μ.toMeasure.map (fun x => x i)

instance (μ : ProbabilityMeasure (Fin d → ℝ)) (i : Fin d) : IsProbabilityMeasure (marginal μ i) :=
  inferInstanceAs (IsProbabilityMeasure (μ.toMeasure.map (fun x => x i)))

/-- Apply each marginal CDF to its own coordinate. -/
@[expose]
noncomputable def marginalTransform (μ : ProbabilityMeasure (Fin d → ℝ)) (x : Fin d → ℝ)
    (i : Fin d) : I := cdfUnit (marginal μ i) (x i)

theorem measurable_marginalTransform (μ : ProbabilityMeasure (Fin d → ℝ)) :
    Measurable (marginalTransform μ) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_cdfUnit (marginal μ i)).comp (measurable_pi_apply i)

theorem map_marginalTransform_eval (μ : ProbabilityMeasure (Fin d → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) (i : Fin d) :
    μ.toMeasure.map (fun x => marginalTransform μ x i) = volume := by
  calc
    _ = (marginal μ i).map (cdfUnit (marginal μ i)) :=
      (Measure.map_map (measurable_cdfUnit _) (measurable_pi_apply i)).symm
    _ = volume := map_cdfUnit _ (hc i)

/-- The copula of a real random vector with continuous marginal CDFs. -/
@[expose]
noncomputable def ofContinuousMarginals (μ : ProbabilityMeasure (Fin d → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) : Copula d :=
  ofMap μ (marginalTransform μ) (measurable_marginalTransform μ)
    (map_marginalTransform_eval μ hc)

/-- The distribution factorization in Sklar's theorem. -/
@[expose]
def IsSklarCopula (μ : ProbabilityMeasure (Fin d → ℝ)) (C : Copula d) : Prop :=
  ∀ x, C.cdf (marginalTransform μ x) = μ.toMeasure.real (Iic x)

theorem isSklarCopula_ofContinuousMarginals (μ : ProbabilityMeasure (Fin d → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) :
    IsSklarCopula μ (ofContinuousMarginals μ hc) := by
  intro x
  rw [cdf, ofContinuousMarginals, toMeasure_ofMap,
    map_measureReal_apply (measurable_marginalTransform μ) measurableSet_Iic]
  have heq (i : Fin d) : {z : Fin d → ℝ | z i ≤ x i} =ᵐ[μ.toMeasure]
      {z | marginalTransform μ z i ≤ marginalTransform μ x i} := by
    apply ae_eq_of_subset_of_measure_ge
    · intro z hz
      exact ProbabilityTheory.monotone_cdf (marginal μ i) hz
    · have hleft : μ.toMeasure {z | z i ≤ x i} =
          ENNReal.ofReal (ProbabilityTheory.cdf (marginal μ i) (x i)) := by
        rw [ProbabilityTheory.ofReal_cdf]
        exact (Measure.map_apply (measurable_pi_apply i) measurableSet_Iic).symm
      have hright : μ.toMeasure {z | marginalTransform μ z i ≤ marginalTransform μ x i} =
          ENNReal.ofReal (ProbabilityTheory.cdf (marginal μ i) (x i)) := by
        have hm : Measurable (fun z => marginalTransform μ z i) :=
          (measurable_pi_apply i).comp (measurable_marginalTransform μ)
        change μ.toMeasure ((fun z => marginalTransform μ z i) ⁻¹'
          Iic (marginalTransform μ x i)) = _
        rw [← Measure.map_apply hm measurableSet_Iic, map_marginalTransform_eval μ hc,
          unitInterval.volume_Iic]
        rfl
      rw [hleft, hright]
    · exact (measurableSet_le (measurable_pi_apply i) measurable_const).nullMeasurableSet
    · exact measure_ne_top _ _
  apply measureReal_congr
  apply Filter.Eventually.set_eq
  filter_upwards [ae_all_iff.mpr (fun i => (heq i).mem_iff)] with z hz
  change (∀ i, marginalTransform μ z i ≤ marginalTransform μ x i) ↔ ∀ i, z i ≤ x i
  exact forall_congr' (fun i => (hz i).symm)

/-- Factorizations agree on the product of marginal CDF ranges, even with atoms. -/
theorem IsSklarCopula.cdf_eq_on_ranges {μ : ProbabilityMeasure (Fin d → ℝ)} {C D : Copula d}
    (hC : IsSklarCopula μ C) (hD : IsSklarCopula μ D) (u : Fin d → I)
    (hu : ∀ i, u i ∈ Set.range (cdfUnit (marginal μ i))) : C.cdf u = D.cdf u := by
  choose x hx using hu
  have hux : marginalTransform μ x = u := funext hx
  rw [← hux, hC x, hD x]

private theorem denseRange_cdfUnit (μ : Measure ℝ) (hc : Continuous (ProbabilityTheory.cdf μ)) :
    DenseRange (cdfUnit μ) := by
  have hd : Dense (Ioo (0 : I) 1) := by
    rw [dense_iff_closure_eq, closure_Ioo (zero_ne_one : (0 : I) ≠ 1)]
    ext u
    simp [unitInterval.le_one']
  apply hd.mono
  intro u hu
  obtain ⟨x, hx⟩ := exists_cdf_eq_of_continuous μ hc
    (show 0 < (u : ℝ) from hu.1) (show (u : ℝ) < 1 from hu.2)
  exact ⟨x, Subtype.ext hx⟩

/-- Continuous marginals make the Sklar copula unique on the entire unit cube. -/
theorem IsSklarCopula.unique {μ : ProbabilityMeasure (Fin d → ℝ)}
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {C D : Copula d}
    (hC : IsSklarCopula μ C) (hD : IsSklarCopula μ D) : C = D := by
  apply cdf_injective
  have hd : DenseRange (marginalTransform μ) :=
    DenseRange.piMap (fun i => denseRange_cdfUnit (marginal μ i) (hc i))
  apply hd.equalizer C.continuous_cdf D.continuous_cdf
  funext x
  exact (hC x).trans (hD x).symm

/-- Existence and uniqueness in Sklar's theorem for continuous marginal CDFs. -/
theorem existsUnique_sklarCopula_of_continuous (μ : ProbabilityMeasure (Fin d → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) :
    ∃! C : Copula d, IsSklarCopula μ C := by
  refine ⟨ofContinuousMarginals μ hc, isSklarCopula_ofContinuousMarginals μ hc, ?_⟩
  intro C hC
  exact hC.unique hc (isSklarCopula_ofContinuousMarginals μ hc)

end ProbabilityTheory.Copula
