/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.SlicingDirectional
public import LeanPool.LiebThirring.Electrostatics.PlaneFormula
import all LeanPool.LiebThirring.Electrostatics.FaceMeasureGeometry

/-!
# Directional integration over a Voronoi cell

Fubini and the planar projection formula turn the almost-everywhere scalar
line identity into the cell integration-by-parts formula.
-/

public section

open Set MeasureTheory

namespace LiebThirring

theorem integrable_compact_bisectorSurfaceMeasure {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (k l : Fin M) (hkl : k ≠ l)
    (g : Position → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable g (bisectorSurfaceMeasure R hR k l hkl) := by
  obtain ⟨a, ha⟩ : ∃ a, bisectorNormal R k l a ≠ 0 := by
    by_contra! hz
    have hn : bisectorNormal R k l = 0 := by ext a; exact hz a
    have he := norm_bisectorNormal R hR hkl
    rw [hn, norm_zero] at he
    exact zero_ne_one he
  rw [bisectorSurfaceMeasure, integrable_planeMeasure_projection_iff _ _
    (norm_bisectorNormal R hR hkl) a ha]
  exact (hg.comp (isClosedEmbedding_planeGraph _ _ a ha).continuous).integrable_of_hasCompactSupport
    (hgc.comp_isClosedEmbedding (isClosedEmbedding_planeGraph _ _ a ha))

theorem integrable_coordinateFaceTerm {M : ℕ} (R : Fin M → Position)
    (k l : Fin M) (a : Fin 3) (g : Position → ℝ)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (coordinateFaceTerm R k l a g) := by
  classical
  unfold coordinateFaceTerm
  split_ifs with ha
  · let G := planeGraph (bisectorNormal R k l) (midpoint ℝ (R k) (R l)) a ha
    have hc := isClosedEmbedding_planeGraph (bisectorNormal R k l)
      (midpoint ℝ (R k) (R l)) a ha
    have hi : Integrable (g ∘ G) := (hg.comp hc.continuous).integrable_of_hasCompactSupport
      (hgc.comp_isClosedEmbedding hc)
    have he (q : Planar) : (voronoiFace R k l).indicator g (G q) =
        (G ⁻¹' voronoiFace R k l).indicator (g ∘ G) q := by
      by_cases hq : G q ∈ voronoiFace R k l
      · rw [indicator_of_mem hq, indicator_of_mem (s := G ⁻¹' voronoiFace R k l) hq]; rfl
      · rw [indicator_of_notMem hq, indicator_of_notMem (s := G ⁻¹' voronoiFace R k l) hq]
    change Integrable (fun q => _ * (voronoiFace R k l).indicator g (G q))
    simp_rw [he]
    exact (hi.indicator ((measurableSet_voronoiFace R k l).preimage
      hc.continuous.measurable)).const_mul _
  · exact integrable_zero _ _ _

theorem integral_coordinateFaceTerm {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (k l : Fin M) (hkl : k ≠ l)
    (a : Fin 3) (g : Position → ℝ) :
    (∫ q, coordinateFaceTerm R k l a g q) =
      bisectorNormal R k l a * ∫ x in voronoiFace R k l, g x
        ∂bisectorSurfaceMeasure R hR k l hkl := by
  classical
  by_cases ha : bisectorNormal R k l a ≠ 0
  · simp only [coordinateFaceTerm, dite_eq_left ha]
    rw [integral_const_mul, ← integral_indicator (measurableSet_voronoiFace R k l),
      bisectorSurfaceMeasure, integral_planeMeasure_projection _ _
        (norm_bisectorNormal R hR hkl) a ha]
    simp only [div_eq_mul_inv, mul_assoc]
  · have he : coordinateFaceTerm R k l a g = fun _ => 0 := by
      funext q
      exact dite_eq_right ha
    rw [he, integral_zero, not_ne_iff.mp ha, zero_mul]

theorem voronoiCell_compact_directional_integral {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (k : Fin M) (a : Fin 3) (g : Position → ℝ)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    (∫ x in voronoiCell R k, fderiv ℝ g x (EuclideanSpace.basisFun (Fin 3) ℝ a)) =
      ∑ l : {l : Fin M // l ≠ k}, bisectorNormal R k l.val a *
        ∫ x in voronoiFace R k l.val, g x
          ∂bisectorSurfaceMeasure R hR k l.val l.property.symm := by
  classical
  let D := fun x => fderiv ℝ g x (EuclideanSpace.basisFun (Fin 3) ℝ a)
  have hi : Integrable D :=
    ((hg.continuous_fderiv (by decide)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hgc.fderiv_apply ℝ _)
  let C := voronoiCell R k
  have hC := (isOpen_voronoiCell R k).measurableSet
  rw [← integral_indicator hC, integral_coordinateLines a _ (hi.indicator hC)]
  have he (q : Planar) : (fun t => C.indicator D (coordinateLine a q t)) =
      {t | coordinateLine a q t ∈ C}.indicator (fun t => D (coordinateLine a q t)) := by
    ext t
    by_cases ht : coordinateLine a q t ∈ C
    · rw [indicator_of_mem ht,
        indicator_of_mem (s := {t | coordinateLine a q t ∈ C}) ht]
    · rw [indicator_of_notMem ht,
        indicator_of_notMem (s := {t | coordinateLine a q t ∈ C}) ht]
  have hs : (∫ q : Planar, ∫ t, C.indicator D (coordinateLine a q t)) =
      ∫ q : Planar, ∑ l : {l : Fin M // l ≠ k}, coordinateFaceTerm R k l.val a g q := by
    apply integral_congr_ae
    filter_upwards [ae_notMem_slicingExceptionalSet R hR a] with q hq
    rw [he q]
    have hpre : MeasurableSet {t | coordinateLine a q t ∈ C} :=
      ((isOpen_voronoiCell R k).preimage (isClosedEmbedding_coordinateLine a
        q).continuous).measurableSet
    exact (integral_indicator hpre).trans
      (integral_coordinateLine_voronoiCell R hR k a q hq g hg hgc)
  rw [hs, integral_finsetSum _ (fun l _ => integrable_coordinateFaceTerm R k l.val a g
    hg.continuous hgc)]
  exact Finset.sum_congr rfl (fun l _ => integral_coordinateFaceTerm R hR k l.val l.property.symm a
    g)

end LiebThirring

end
