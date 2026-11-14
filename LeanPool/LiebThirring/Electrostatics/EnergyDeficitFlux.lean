/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitFluxExtension
public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitLimits
import LeanPool.LiebThirring.Electrostatics.SlicingDivergence

/-!
# The exterior cutoff calculation from compact-field flux

The whole exterior lies outside every ball contained in the cell.

A genuine face belongs to the exterior of either incident open cell.
-/

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology ContDiff

namespace LiebThirring

/-- The whole exterior lies outside every ball contained in the cell. -/
theorem norm_ge_on_voronoiExterior {M : ℕ} (R : Fin M → Position) (k : Fin M)
    (a : ℝ) (hball : ball (R k) a ⊆ voronoiCell R k) {x : Position}
    (hx : x ∈ (voronoiCell R k)ᶜ) : a ≤ ‖x - R k‖ := by
  apply le_of_not_gt
  intro h
  exact hx (hball (by simpa only [mem_ball, dist_eq_norm] using h))

/-- A genuine face belongs to the exterior of either incident open cell. -/
theorem voronoiFace_subset_exterior {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) {k l : Fin M} (hkl : k ≠ l) :
    voronoiFace R k l ⊆ (voronoiCell R k)ᶜ := by
  intro y hy
  apply exterior_halfSpace_subset_compl_voronoiCell R hR hkl
  exact ((mem_bisectorPlane_iff_normal R hR hkl y).mp hy.2.1).ge

/-- Exact normal value of the inverse-square gradient on a bisector face. -/
theorem inner_exteriorInverseSquareField_on_face {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) {k l : Fin M} (hkl : k ≠ l) {y : Position}
    (hy : y ∈ voronoiFace R k l) :
    inner ℝ (bisectorNormal R k l) (exteriorInverseSquareField (R k) y) =
      -2 * (nuclearHalfDistance R k l / ‖y - R k‖ ^ 4) := by
  have he := (mem_bisectorPlane_iff_normal R hR hkl y).mp hy.2.1
  rw [exteriorInverseSquareField, inner_smul_right, he]
  simp only [nuclearHalfDistance, div_eq_mul_inv, inv_pow, ← pow_mul]
  ring

/-- Integrability of a cutoff multiplied by any integrable density. -/
theorem integrable_exteriorFluxCutoff_mul (μ : Measure Position) (c : Position) (T : ℝ)
    (f : Position → ℝ) (hf : Integrable f μ) :
    Integrable (fun x => exteriorFluxCutoff c T x * f x) μ := by
  apply hf.bdd_mul (c := 1) ((contDiff_exteriorFluxCutoff c
    T).continuous.measurable.aestronglyMeasurable)
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (show 0 ≤ exteriorFluxCutoff c T x from exteriorFluxBump.nonneg)]
    exact exteriorFluxBump.le_one)

/-- Integrability of the derivative defect multiplied by any integrable density. -/
theorem integrable_exteriorFluxDefect_mul (μ : Measure Position) (c : Position) (T : ℝ)
    (f : Position → ℝ) (hf : Integrable f μ) :
    Integrable (fun x => exteriorFluxDefect (T⁻¹ • (x - c)) * f x) μ := by
  obtain ⟨C, hC⟩ := exteriorFluxDefect_bounded
  have hm : Continuous (fun x : Position => exteriorFluxDefect (T⁻¹ • (x - c))) :=
    continuous_exteriorFluxDefect.comp
      ((continuous_const : Continuous (fun _ : Position => T⁻¹)).smul
        (continuous_id.sub continuous_const))
  exact hf.bdd_mul hm.measurable.aestronglyMeasurable (Eventually.of_forall (fun x => hC _))

/-- Exact truncated balance, conditional only on compact C¹ flux. -/
theorem integral_voronoiExterior_cutoff_of_compact_flux {M : ℕ}
    (R : Fin M → Position) (hR : Function.Injective R) (hM : 2 ≤ M) (k : Fin M)
    (hFlux : ∀ V : Position → Position, ContDiff ℝ 1 V → HasCompactSupport V →
      (∫ x in (voronoiCell R k)ᶜ, positionDivergence V x) =
        -(∑ l : {l : Fin M // l ≠ k}, ∫ y in voronoiFace R k l.val,
          inner ℝ (bisectorNormal R k l.val) (V y)
            ∂bisectorSurfaceMeasure R hR k l.val l.property.symm)) (T : ℝ) (hT : 0 < T) :
    (∫ x in (voronoiCell R k)ᶜ, exteriorFluxCutoff (R k) T x * (1 / ‖x - R k‖ ^ 4)) -
      (∫ x in (voronoiCell R k)ᶜ,
        exteriorFluxDefect (T⁻¹ • (x - R k)) * (1 / ‖x - R k‖ ^ 4)) =
      ∑ l : {l : Fin M // l ≠ k}, ∫ y in voronoiFace R k l.val,
        exteriorFluxCutoff (R k) T y * (nuclearHalfDistance R k l.val / ‖y - R k‖ ^ 4)
          ∂bisectorSurfaceMeasure R hR k l.val l.property.symm := by
  let a := (nearestOtherNucleusDistance R k).toReal / 2
  have ha : 0 < a := half_pos (nearestOtherNucleusDistance_toReal_pos R hR hM k)
  have hball : ball (R k) a ⊆ voronoiCell R k := ball_nearestOther_half_subset_voronoiCell R hM k
  have hr {x : Position} (hx : x ∈ (voronoiCell R k)ᶜ) : a / 2 < ‖x - R k‖ := by
    have hb := norm_ge_on_voronoiExterior R k a hball hx
    linarith
  have hdiv {x : Position} (hx : x ∈ (voronoiCell R k)ᶜ) :
      positionDivergence (exteriorFluxExtendedField (R k) a T ha) x =
      2 * (exteriorFluxCutoff (R k) T x * (1 / ‖x - R k‖ ^ 4) -
        exteriorFluxDefect (T⁻¹ • (x - R k)) * (1 / ‖x - R k‖ ^ 4)) := by
    rw [positionDivergence_exteriorFluxExtendedField _ _ _ _ ha (hr hx)]
    ring
  have hnormal (l : {l : Fin M // l ≠ k}) {y : Position} (hy : y ∈ voronoiFace R k l.val) :
      inner ℝ (bisectorNormal R k l.val) (exteriorFluxExtendedField (R k) a T ha y) =
      -2 * (exteriorFluxCutoff (R k) T y * (nuclearHalfDistance R k l.val / ‖y - R k‖ ^ 4)) := by
    rw [exteriorFluxExtendedField_eq _ _ _ _ ha
      (hr (voronoiFace_subset_exterior R hR l.property.symm hy)).le,
      inner_smul_right, inner_exteriorInverseSquareField_on_face R hR l.property.symm hy]
    ring
  have hf := integrableOn_inverse_fourth_voronoiExterior R hR hM k
  have hχ := integrable_exteriorFluxCutoff_mul _ (R k) T _ hf
  have hδ := integrable_exteriorFluxDefect_mul _ (R k) T _ hf
  have he := hFlux (exteriorFluxExtendedField (R k) a T ha)
    ((contDiff_exteriorFluxExtendedField (R k) a T ha).of_le (by simp))
    (hasCompactSupport_exteriorFluxExtendedField (R k) a T ha hT)
  rw [setIntegral_congr_fun (isOpen_voronoiCell R k).measurableSet.compl (fun x hx => hdiv hx),
    integral_const_mul, integral_sub hχ hδ] at he
  have hb : (∑ l : {l : Fin M // l ≠ k}, ∫ y in voronoiFace R k l.val,
        inner ℝ (bisectorNormal R k l.val) (exteriorFluxExtendedField (R k) a T ha y)
          ∂bisectorSurfaceMeasure R hR k l.val l.property.symm) =
      -2 * (∑ l : {l : Fin M // l ≠ k}, ∫ y in voronoiFace R k l.val,
        exteriorFluxCutoff (R k) T y * (nuclearHalfDistance R k l.val / ‖y - R k‖ ^ 4)
          ∂bisectorSurfaceMeasure R hR k l.val l.property.symm) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [setIntegral_congr_fun (measurableSet_voronoiFace R k l.val) (fun y hy => hnormal l hy),
      integral_const_mul]
  rw [hb] at he
  linarith only [he]

/-- The full real exterior identity after the proved cutoff passage from compact C¹ flux. -/
theorem integral_voronoiExterior_inverse_fourth_of_compact_flux {M : ℕ}
    (R : Fin M → Position) (hR : Function.Injective R) (hM : 2 ≤ M) (k : Fin M)
    (hFlux : ∀ V : Position → Position, ContDiff ℝ 1 V → HasCompactSupport V →
      (∫ x in (voronoiCell R k)ᶜ, positionDivergence V x) =
        -(∑ l : {l : Fin M // l ≠ k}, ∫ y in voronoiFace R k l.val,
          inner ℝ (bisectorNormal R k l.val) (V y)
            ∂bisectorSurfaceMeasure R hR k l.val l.property.symm)) :
    (∫ x in (voronoiCell R k)ᶜ, 1 / ‖x - R k‖ ^ 4) =
      ∑ l : {l : Fin M // l ≠ k}, ∫ y in voronoiFace R k l.val,
        nuclearHalfDistance R k l.val / ‖y - R k‖ ^ 4
          ∂bisectorSurfaceMeasure R hR k l.val l.property.symm := by
  have hleft := (tendsto_integral_cutoff_voronoiExterior R hR hM k).sub
    (tendsto_integral_defect_voronoiExterior R hR hM k)
  simp only [sub_zero] at hleft
  have hright := tendsto_finsetSum Finset.univ (fun (l : {l : Fin M // l ≠ k}) _ =>
    tendsto_integral_cutoff_voronoiFace R hR k l.val l.property.symm)
  have heq : (fun T : ℝ =>
      (∫ x in (voronoiCell R k)ᶜ, exteriorFluxCutoff (R k) T x * (1 / ‖x - R k‖ ^ 4)) -
      (∫ x in (voronoiCell R k)ᶜ,
        exteriorFluxDefect (T⁻¹ • (x - R k)) * (1 / ‖x - R k‖ ^ 4))) =ᶠ[atTop]
      (fun T => ∑ l : {l : Fin M // l ≠ k}, ∫ y in voronoiFace R k l.val,
        exteriorFluxCutoff (R k) T y * (nuclearHalfDistance R k l.val / ‖y - R k‖ ^ 4)
          ∂bisectorSurfaceMeasure R hR k l.val l.property.symm) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact integral_voronoiExterior_cutoff_of_compact_flux R hR hM k hFlux T hT
  exact tendsto_nhds_unique (hleft.congr' heq) hright

/-- The full extended nonnegative exterior identity from a compact C¹ flux identity. -/
theorem lintegral_voronoiExterior_inverse_fourth_of_compact_flux {M : ℕ}
    (R : Fin M → Position) (hR : Function.Injective R) (hM : 2 ≤ M) (k : Fin M)
    (hFlux : ∀ V : Position → Position, ContDiff ℝ 1 V → HasCompactSupport V →
      (∫ x in (voronoiCell R k)ᶜ, positionDivergence V x) =
        -(∑ l : {l : Fin M // l ≠ k}, ∫ y in voronoiFace R k l.val,
          inner ℝ (bisectorNormal R k l.val) (V y)
            ∂bisectorSurfaceMeasure R hR k l.val l.property.symm)) :
    (∫⁻ x in (voronoiCell R k)ᶜ, ENNReal.ofReal ((‖x - R k‖ ^ 4)⁻¹)) =
      ∑ l : {l : Fin M // l ≠ k}, ∫⁻ y in voronoiFace R k l.val,
        ENNReal.ofReal (nuclearHalfDistance R k l.val / ‖y - R k‖ ^ 4)
          ∂bisectorSurfaceMeasure R hR k l.val l.property.symm := by
  have hi := integrableOn_inverse_fourth_voronoiExterior R hR hM k
  have hn : ∀ᵐ x ∂(volume.restrict (voronoiCell R k)ᶜ), 0 ≤ 1 / ‖x - R k‖ ^ 4 :=
    Eventually.of_forall (fun x => by positivity)
  simp_rw [← one_div]
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    integral_voronoiExterior_inverse_fourth_of_compact_flux R hR hM k hFlux,
    ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro l _
    apply ofReal_integral_eq_lintegral_ofReal
      (integrableOn_voronoiFace_inverse_fourth_flux R hR k l.val l.property.symm)
    exact Eventually.of_forall (fun y => div_nonneg
      (nuclearHalfDistance_pos R hR l.property.symm).le (pow_nonneg (norm_nonneg _) _))
  · intro l _
    apply integral_nonneg
    intro y
    exact div_nonneg (nuclearHalfDistance_pos R hR l.property.symm).le (pow_nonneg (norm_nonneg _)
      _)

end LiebThirring

end
