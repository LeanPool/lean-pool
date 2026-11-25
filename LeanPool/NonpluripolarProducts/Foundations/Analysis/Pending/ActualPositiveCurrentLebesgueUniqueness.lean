/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentLebesgue

/-! # Actual positive-current sum and Lebesgue uniqueness

The trace and bounded coefficient densities are constructed from the
actual currents, rather than supplied as decomposition certificates.
-/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualPositiveCurrentLebesgueUniqueness
open FirstPass StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  LocalBedfordTaylorLocality

variable {n q : ℕ} {U : Opens (ComplexModel n)}

/-- Addition of actual positive currents adds their constructed trace
measures, including the empty open domain and arbitrary dimension. -/
theorem traceMeasure_add {D R : LocalProductCurrent n U q}
    (hD : IsPositive D) (hR : IsPositive R) :
    (hD.add hR).traceMeasure = hD.traceMeasure + hR.traceMeasure := by
  apply eq_of_forall_testFunction_integral_eq
    (hD.add hR).traceMeasure_compl
  · rw [add_apply, hD.traceMeasure_compl, hR.traceMeasure_compl, add_zero]
  · exact fun K hK hKU => (hD.add hR).traceMeasure_lt_top hK hKU
  · intro K hK hKU
    rw [add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hD.traceMeasure_lt_top hK hKU,
      hR.traceMeasure_lt_top hK hKU⟩
  · intro φ
    have hi (S : LocalProductCurrent n U q) (hS : IsPositive S) :
        Integrable φ hS.traceMeasure := by
      simpa only [mul_one] using
        hS.integrable_mul_of_bounded φ.continuous φ.hasCompactSupport φ.tsupport_subset
          (measurable_const.aestronglyMeasurable : AEStronglyMeasurable
            (fun _ : ComplexModel n => (1 : ℝ)) hS.traceMeasure)
          ⟨1, by intros; simp⟩
    rw [integral_add_measure (hi D hD) (hi R hR),
      (hD.add hR).integral_traceMeasure, hD.integral_traceMeasure,
      hR.integral_traceMeasure, LinearMap.add_apply, _root_.add_apply]

/-- Actual coefficient-density uniqueness identifies both parts of a
positive sum from the natural singular/AC component traces. -/
theorem parts_of_singular_add_absolutelyContinuous
    {D R : LocalProductCurrent n U q} (hD : IsPositive D) (hR : IsPositive R)
    (hDs : hD.traceMeasure ⟂ₘ volume) (hRa : hR.traceMeasure ≪ volume) :
    sgPart (hD.add hR) = D ∧ acPart (hD.add hR) = R := by
  classical
  let hT := hD.add hR
  have hσ : hT.traceMeasure = hD.traceMeasure + hR.traceMeasure := traceMeasure_add hD hR
  have hDsCopy := hDs
  obtain ⟨S, hSm, hDS, hVS⟩ := hDsCopy
  let A := Sᶜ
  have hAm : MeasurableSet A := hSm.compl
  have hDAc : hD.traceMeasure Aᶜ = 0 := by simpa only [A, compl_compl] using hDS
  have hRA : hR.traceMeasure A = 0 := hRa hVS
  have hAD : ∀ᵐ x ∂hD.traceMeasure, x ∈ A := by
    simpa only [mem_compl_iff, not_not] using measure_eq_zero_iff_ae_notMem.mp hDAc
  have hAR : ∀ᵐ x ∂hR.traceMeasure, x ∉ A := measure_eq_zero_iff_ae_notMem.mp hRA
  let w (γ : formSpan n q) (x : ComplexModel n) : ℝ :=
    if x ∈ A then densityForm hD x γ else densityForm hR x γ
  have hwm (γ : formSpan n q) : Measurable (w γ) :=
    Measurable.ite hAm (measurable_densityForm hD γ) (measurable_densityForm hR γ)
  have hwb (γ : formSpan n q) : ∃ C : ℝ, ∀ x, |w γ x| ≤ C := by
    obtain ⟨CD, _, hCD⟩ := exists_abs_densityForm_le hD γ
    obtain ⟨CR, _, hCR⟩ := exists_abs_densityForm_le hR γ
    refine ⟨max CD CR, fun x => ?_⟩
    by_cases hx : x ∈ A
    · change |if x ∈ A then _ else _| ≤ _
      rw [ite_eq_left hx]
      exact (hCD x).trans (le_max_left _ _)
    · change |if x ∈ A then _ else _| ≤ _
      rw [ite_eq_right hx]
      exact (hCR x).trans (le_max_right _ _)
  have hwD (γ : formSpan n q) : w γ =ᵐ[hD.traceMeasure] fun x => densityForm hD x γ :=
    hAD.mono fun x hx => ite_eq_left hx
  have hwR (γ : formSpan n q) : w γ =ᵐ[hR.traceMeasure] fun x => densityForm hR x γ :=
    hAR.mono fun x hx => ite_eq_right hx
  have hwi (γ : formSpan n q) (φ : 𝓓(U, ℝ)) (L : LocalProductCurrent n U q)
      (hL : IsPositive L) : Integrable (fun x => φ x * w γ x) hL.traceMeasure := by
    obtain ⟨C, hC⟩ := hwb γ
    exact hL.integrable_mul_of_bounded φ.continuous φ.hasCompactSupport φ.tsupport_subset
      (hwm γ).aestronglyMeasurable ⟨C, fun x _ => hC x⟩
  have hdens (γ : formSpan n q) :
      (fun x => densityForm hT x γ) =ᵐ[hT.traceMeasure] w γ := by
    obtain ⟨C, _, hC⟩ := exists_abs_densityForm_le hT γ
    apply hT.ae_eq_of_forall_integral_eq (measurable_densityForm hT γ)
      (hwm γ) ⟨C, hC⟩ (hwb γ)
    intro φ
    rw [← apply_eq_integral_densityForm hT, hσ,
      integral_add_measure (hwi γ φ D hD) (hwi γ φ R hR),
      LinearMap.add_apply, _root_.add_apply]
    congr 1
    · rw [apply_eq_integral_densityForm hD]
      exact integral_congr_ae ((hwD γ).mono fun x hx =>
        congrArg (fun t : ℝ => φ x * t) hx.symm)
    · rw [apply_eq_integral_densityForm hR]
      exact integral_congr_ae ((hwR γ).mono fun x hx =>
        congrArg (fun t : ℝ => φ x * t) hx.symm)
  have hDle : hD.traceMeasure ≤ hT.traceMeasure := by
    rw [hσ]
    exact Measure.le_add_right le_rfl
  have hsgμ : sgMeasure hT = hD.traceMeasure := by
    change hT.traceMeasure.singularPart volume = _
    rw [hσ, Measure.singularPart_add, Measure.singularPart_eq_self.mpr hDs,
      Measure.singularPart_eq_zero_of_ac hRa, add_zero]
  have hpart : ofMeasure hT hD.traceMeasure hDle = D := by
    ext γ φ
    rw [ofMeasure_apply, apply_eq_integral_densityForm hD]
    refine integral_congr_ae ?_
    filter_upwards [(Measure.absolutelyContinuous_of_le hDle).ae_le (hdens γ), hwD γ]
      with x hx hxD
    rw [hx, hxD]
  have hsg : sgPart hT = D :=
    (ofMeasure_congr hT (sgMeasure_le hT) hDle hsgμ).trans hpart
  refine ⟨hsg, ?_⟩
  have hsum := sgPart_add_acPart hT
  rw [hsg] at hsum
  exact add_left_cancel hsum

end SGPT.Foundations.Analysis.Pending.ActualPositiveCurrentLebesgueUniqueness
