/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WeightedSourceMomentVectors
public import LeanPool.VacuumBellSeparation.FreeField.SourceTranslationEquivalence
public import LeanPool.VacuumBellSeparation.FreeField.SpatialLocalizedMomentSeries

/-!
# Weighted original-source moments about an arbitrary spatial center

The region and its literal test functions are translated, while the
physical unitary transports the original reserve exactly. The constants
are independent of the center and the region.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian Gaussian.HilbertComplexification
open scoped BigOperators

theorem exists_centered_weightedSource_moment_vectors {b : ℝ}
    (hb : 1 / 2 ≤ b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℝ) (hm : 0 < m) (T : ℝ) (_ : 0 < T)
        (a : EuclideanSpace ℝ (Fin 3)) (W : Set (EuclideanSpace ℝ (Fin 3))),
        W ⊆ Metric.ball a T → ∀ α : Fin 3 → ℕ,
          ∃ u v : ComplexSourceHilbert hm W,
            ‖u‖ ≤ C * T / (1 + m * T) * Real.exp (sourceMomentLambda b * m * T) *
              (sourceMomentBase b * T) ^ (∑ j, α j) ∧
            ‖v‖ ≤ C * T ^ 2 / (1 + m * T) ^ 2 * Real.exp (sourceMomentLambda b * m * T) *
              (sourceMomentBase b * T) ^ (∑ j, α j) ∧
            (∀ x : SourceTestSpace hm W,
              inner ℂ (ofReal (x : SourceHilbert hm W)) ((sourceReserve hm W ^ b) u) =
                (centeredSpatialTestMoment a x.1.1 α : ℂ)) ∧
            (∀ x : SourceTestSpace hm W,
              inner ℂ (ofReal (x : SourceHilbert hm W)) ((sourceReserve hm W ^ b) v) =
                (centeredSpatialTestMoment a x.1.2 α : ℂ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_weightedSource_moment_vectors hb hb1
  refine ⟨C, hC, ?_⟩
  intro m hm T hT a W hW α
  let U : Set (EuclideanSpace ℝ (Fin 3)) := {x | x + a ∈ W}
  have hUW : ∀ x ∈ U, x + a ∈ W := fun _ hx => hx
  have hWU : ∀ x ∈ W, x - a ∈ U := by
    intro x hx
    simpa only [U, Set.mem_ofPred_eq, sub_add_cancel] using hx
  have hU : U ⊆ Metric.ball 0 T := by
    intro x hx
    have h := hW hx
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using h
  obtain ⟨u, v, hu, hv, hueq, hveq⟩ := hbound m hm T hT U hU α
  let e := complexSourceSpatialTranslation hm a hUW hWU
  have hb0 : 0 ≤ b := by linarith
  have heq (y : SourceTestSpace hm W) :
      translatedSourceTest hm a hUW
        (translatedSourceTest hm (-a)
          (fun x hx => by simpa only [sub_eq_add_neg] using hWU x hx) y) = y := by
    apply Subtype.ext
    change timeZeroTranslate a (timeZeroTranslate (-a) y.1) = y.1
    simpa only [neg_neg] using timeZeroTranslate_neg_cancel (-a) y.1
  have hpair (w : ComplexSourceHilbert hm U) (y : SourceTestSpace hm W) :
      inner ℂ (ofReal (y : SourceHilbert hm W)) ((sourceReserve hm W ^ b) (e w)) =
        inner ℂ (ofReal
          (translatedSourceTest hm (-a)
            (fun x hx => by simpa only [sub_eq_add_neg] using hWU x hx) y : SourceHilbert hm U))
          ((sourceReserve hm U ^ b) w) := by
    let x := translatedSourceTest hm (-a)
      (fun x hx => by simpa only [sub_eq_add_neg] using hWU x hx) y
    have hex : e (ofReal (x : SourceHilbert hm U)) = ofReal (y : SourceHilbert hm W) := by
      rw [complexSourceSpatialTranslation_test, heq]
    rw [← hex, sourceReserve_rpow_spatialTranslation hm a hUW hWU hb0, e.inner_map_map]
  refine ⟨e u, e v, (e.norm_map u).le.trans hu, (e.norm_map v).le.trans hv, ?_, ?_⟩
  · intro y
    rw [hpair, hueq]
    rfl
  · intro y
    rw [hpair, hveq]
    rfl

end VacuumBellSeparation
