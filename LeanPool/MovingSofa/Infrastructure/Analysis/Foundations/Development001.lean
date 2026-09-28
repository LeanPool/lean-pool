/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Moving sofa: related mathematical developments

* `Analysis.Foundations.Development001`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Analysis.BoundedDensity`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Bounded Density
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace MovingSofa

theorem boundedDensity_of_domination (a b : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (q : ℝ → ℝ) (hq : Measurable q)
    (hq_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ q t)
    (hq_bound : ∃ C : ℝ, ∀ t ∈ Set.Icc a b, q t ≤ C)
    (hdom : ∀ E : Set ℝ, MeasurableSet E →
      μ E ≤ ENNReal.ofReal (∫ t in E, q t ∂volume.restrict (Set.Icc a b))) :
    ∃ r : ℝ → ℝ, Measurable r ∧ Integrable r (volume.restrict (Set.Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), 0 ≤ r t ∧ r t ≤ q t) ∧
      μ = (volume.restrict (Set.Icc a b)).withDensity (fun t ↦ ENNReal.ofReal (r t)) ∧
      (∃ C : ℝ, ∀ᵐ t ∂volume.restrict (Set.Icc a b), |r t| ≤ C) := by
  classical
  obtain ⟨C, hC⟩ := hq_bound
  let lam : Measure ℝ := volume.restrict (Set.Icc a b)
  let nu : Measure ℝ := lam.withDensity (fun t ↦ ENNReal.ofReal (q t))
  have hq_ae : 0 ≤ᵐ[lam] q := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hq_nonneg t ht
  have hq_bound_ae : ∀ᵐ t ∂lam, ‖q t‖ ≤ max C 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hq_nonneg t ht)]
    exact le_max_of_le_left (hC t ht)
  have hq_int : Integrable q lam := by
    exact Measure.integrableOn_of_bounded (μ := volume)
      (s := Set.Icc a b) (M := max C 0) (by simp) hq.aestronglyMeasurable hq_bound_ae
  have hν_apply : ∀ E : Set ℝ, MeasurableSet E →
      nu E = ENNReal.ofReal (∫ t in E, q t ∂lam) := by
    intro E hE
    change (lam.withDensity (fun t ↦ ENNReal.ofReal (q t))) E = _
    rw [withDensity_apply _ hE]
    exact (ofReal_integral_eq_lintegral_ofReal
      (μ := lam.restrict E) hq_int.integrableOn
      (ae_restrict_of_ae hq_ae)).symm
  have hμν : μ ≤ nu := by
    rw [Measure.le_iff]
    intro E hE
    rw [hν_apply E hE]
    exact hdom E hE
  have hνlam : nu.AbsolutelyContinuous lam :=
    withDensity_absolutelyContinuous lam _
  have hμlam : μ.AbsolutelyContinuous lam :=
    (Measure.absolutelyContinuous_of_le hμν).trans hνlam
  let r : ℝ → ℝ := fun t ↦ (μ.rnDeriv lam t).toReal
  have hr_meas : Measurable r := by
    exact (Measure.measurable_rnDeriv μ lam).ennreal_toReal
  have hr_int : Integrable r lam := by
    simpa [r] using
      (Measure.integrableOn_toReal_rnDeriv
        (μ := μ) (ν := lam) (s := Set.univ) (by simp))
  have hr_eq : lam.withDensity (fun t ↦ μ.rnDeriv lam t) = μ :=
    Measure.withDensity_rnDeriv_eq μ lam hμlam
  have hr_le_q_enn : μ.rnDeriv lam ≤ᵐ[lam] (fun t ↦ ENNReal.ofReal (q t)) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (Measure.measurable_rnDeriv μ lam)
    intro E hE hEfin
    rw [Measure.setLIntegral_rnDeriv hμlam E]
    calc
      μ E ≤ nu E := hμν E
      _ = ∫⁻ t in E, ENNReal.ofReal (q t) ∂lam := by
        exact withDensity_apply' _ _
  have hr_bounds : ∀ᵐ t ∂lam, 0 ≤ r t ∧ r t ≤ q t := by
    filter_upwards [hr_le_q_enn, Measure.rnDeriv_ne_top μ lam,
      ae_restrict_mem measurableSet_Icc] with t hle htop ht
    constructor
    · exact ENNReal.toReal_nonneg
    · have hto := (ENNReal.toReal_le_toReal htop ENNReal.ofReal_ne_top).mpr hle
      simpa [r, ENNReal.toReal_ofReal (hq_nonneg t ht)] using hto
  have hfun : (fun t ↦ ENNReal.ofReal (r t)) =ᵐ[lam] μ.rnDeriv lam := by
    filter_upwards [Measure.rnDeriv_ne_top μ lam] with t htop
    simpa [r] using ENNReal.ofReal_toReal htop
  have hr_eq' : lam.withDensity (fun t ↦ ENNReal.ofReal (r t)) = μ := by
    rw [← hr_eq]
    exact withDensity_congr_ae hfun
  have hr_bound : ∃ K : ℝ, ∀ᵐ t ∂lam, |r t| ≤ K := by
    refine ⟨max C 0, ?_⟩
    filter_upwards [hr_bounds, ae_restrict_mem measurableSet_Icc] with t ⟨h₀, hq⟩ ht
    rw [abs_of_nonneg h₀]
    exact hq.trans ((hC t ht).trans (le_max_left _ _))
  refine ⟨r, hr_meas, hr_int, hr_bounds, ?_, hr_bound⟩
  simpa [lam] using hr_eq'.symm

/-- A finite measure carried by `Set.Icc a b` and dominated on that interval by the integral of
a bounded, almost everywhere strongly measurable nonnegative function `f` has an integrable real
density with respect to the Lebesgue measure on `Set.Icc a b`, and that density is bounded above
by `f` almost everywhere. -/
theorem exists_density_le_of_domination {a b : ℝ} (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ (Set.Icc a b)ᶜ = 0) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b)))
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    {M : ℝ} (hf_bound : ∀ t ∈ Set.Icc a b, f t ≤ M)
    (hdom : ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Icc a b →
      μ E ≤ ENNReal.ofReal (∫ t in E, f t)) :
    ∃ r : ℝ → ℝ, Measurable r ∧ IntegrableOn r (Set.Icc a b) volume ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), 0 ≤ r t ∧ r t ≤ f t) ∧
      μ = (volume.restrict (Set.Icc a b)).withDensity (fun t ↦ ENNReal.ofReal (r t)) := by
  classical
  obtain ⟨g, hg, hgf⟩ := hf
  set q : ℝ → ℝ := fun t ↦ max 0 (min M (g t)) with hq
  have hq_meas : Measurable q := measurable_const.max (measurable_const.min hg.measurable)
  have hq_nonneg : ∀ t, 0 ≤ q t := fun t ↦ le_max_left _ _
  have hq_bound : ∀ t, q t ≤ max M 0 := fun t ↦
    max_le (le_max_right M 0) ((min_le_left _ _).trans (le_max_left _ _))
  have hqf : f =ᵐ[volume.restrict (Set.Icc a b)] q := by
    filter_upwards [hgf, ae_restrict_mem measurableSet_Icc] with t hgt ht
    simp only [hq, ← hgt, min_eq_right (hf_bound t ht), max_eq_right (hf_nonneg t ht)]
  have hdom' : ∀ E : Set ℝ, MeasurableSet E →
      μ E ≤ ENNReal.ofReal (∫ t in E, q t ∂volume.restrict (Set.Icc a b)) := by
    intro E hE
    have hnull : μ (E \ Set.Icc a b) = 0 := measure_mono_null (fun x hx ↦ hx.2) hμ
    have hEsub : μ E ≤ μ (E ∩ Set.Icc a b) :=
      calc μ E ≤ μ (E ∩ Set.Icc a b) + μ (E \ Set.Icc a b) := measure_le_inter_add_sdiff μ E _
        _ = μ (E ∩ Set.Icc a b) := by rw [hnull, add_zero]
    refine hEsub.trans ((hdom _ (hE.inter measurableSet_Icc) Set.inter_subset_right).trans ?_)
    rw [Measure.restrict_restrict hE]
    exact le_of_eq (congrArg ENNReal.ofReal (integral_congr_ae
      (ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right hqf)))
  obtain ⟨r, hr_meas, hr_int, hr_bounds, hr_eq, -⟩ :=
    boundedDensity_of_domination a b μ q hq_meas (fun t _ ↦ hq_nonneg t)
      ⟨max M 0, fun t _ ↦ hq_bound t⟩ hdom'
  refine ⟨r, hr_meas, hr_int, ?_, hr_eq⟩
  filter_upwards [hr_bounds, hqf] with t ht htq
  exact ⟨ht.1, htq ▸ ht.2⟩

/-- A finite measure carried by `Set.Icc a b` and dominated on that interval by the integral of
a bounded, almost everywhere strongly measurable nonnegative function has a measurable
`ℝ≥0`-valued density with respect to the Lebesgue measure on `Set.Icc a b`. -/
theorem exists_nnreal_density_of_domination {a b : ℝ} (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ (Set.Icc a b)ᶜ = 0) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b)))
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    {M : ℝ} (hf_bound : ∀ t ∈ Set.Icc a b, f t ≤ M)
    (hdom : ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Icc a b →
      μ E ≤ ENNReal.ofReal (∫ t in E, f t)) :
    ∃ r : ℝ → ℝ≥0, Measurable r ∧
      μ = (volume.restrict (Set.Icc a b)).withDensity (fun t ↦ (r t : ℝ≥0∞)) := by
  obtain ⟨r, hr_meas, -, -, hr_eq⟩ :=
    exists_density_le_of_domination μ hμ f hf hf_nonneg hf_bound hdom
  exact ⟨fun t ↦ (r t).toNNReal, hr_meas.real_toNNReal, hr_eq⟩

end MovingSofa

end

end

end

end

end

end
