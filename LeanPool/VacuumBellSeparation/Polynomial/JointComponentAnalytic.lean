/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Polynomial.JointComponentApproximation
public import Mathlib.Analysis.Analytic.Polynomial

/-! # Actual analyticity on each of the four labelled component neighborhoods -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian MvPolynomial

theorem jointShift_analyticAt (z : Fin 6 → ℂ) :
    AnalyticAt ℂ (fun w : Fin 6 → ℂ => fun j => w j + jointMidpointShift j) z := by
  apply AnalyticAt.pi
  intro j
  simpa only [Pi.add_def, ContinuousLinearMap.proj_apply] using
    ((ContinuousLinearMap.proj j : (Fin 6 → ℂ) →L[ℂ] ℂ).analyticAt z).add
      (analyticAt_const (𝕜 := ℂ) (x := z) (v := jointMidpointShift j))

theorem jointSwap_analyticAt (z : Fin 6 → ℂ) :
    AnalyticAt ℂ (fun w : Fin 6 → ℂ => w ∘ swapSpatialSix) z := by
  apply AnalyticAt.pi
  intro j
  exact (ContinuousLinearMap.proj (swapSpatialSix j) : (Fin 6 → ℂ) →L[ℂ] ℂ).analyticAt z

theorem jointOrientedComponentKernel_analyticAt {δ : ℝ} (hδ : δ ≤ 1 / 100)
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), AnalyticAt ℂ F z)
    (a b : Bool) (z : Fin 6 → ℂ) (hz : InJointComponent a b δ z) :
    AnalyticAt ℂ (jointOrientedComponentKernel F a b) z := by
  by_cases hd : a = false ∧ b = true
  · rcases hd with ⟨rfl, rfl⟩
    have ha := (hF _ (fun j => (hz.desired_shift j).trans hδ)).comp
      (f := fun w : Fin 6 → ℂ => fun j => w j + jointMidpointShift j)
      (jointShift_analyticAt z)
    change AnalyticAt ℂ (fun w : Fin 6 → ℂ =>
      if false = false ∧ true = true then F (fun j => w j + jointMidpointShift j) else 0) z
    simpa only [Function.comp_def, and_self, ↓reduceIte] using ha
  · change AnalyticAt ℂ (fun w : Fin 6 → ℂ =>
      if a = false ∧ b = true then F (fun j => w j + jointMidpointShift j) else 0) z
    simpa only [ite_eq_right hd] using
      (analyticAt_const (𝕜 := ℂ) (x := z) (v := (0 : ℂ)))

theorem jointComponentKernel_analyticAt {δ : ℝ} (hδ : δ ≤ 1 / 100)
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), AnalyticAt ℂ F z)
    (a b : Bool) (z : Fin 6 → ℂ) (hz : InJointComponent a b δ z) :
    AnalyticAt ℂ (jointComponentKernel F a b) z := by
  have hswap :=
    (jointOrientedComponentKernel_analyticAt hδ F hF b a (z ∘ swapSpatialSix) hz.swap).comp
      (f := fun w : Fin 6 → ℂ => w ∘ swapSpatialSix) (jointSwap_analyticAt z)
  change AnalyticAt ℂ (fun w : Fin 6 → ℂ =>
    -(jointOrientedComponentKernel F a b w +
      jointOrientedComponentKernel F b a (w ∘ swapSpatialSix))) z
  simpa only [Pi.add_def, Pi.neg_def, Function.comp_def] using
    ((jointOrientedComponentKernel_analyticAt hδ F hF a b z hz).add hswap).neg

theorem jointMidpointPolynomial_analyticAt (F : (Fin 6 → ℂ) → ℂ) (n : ℕ)
    (z : Fin 6 → ℂ) :
    AnalyticAt ℂ (fun w => eval w (jointMidpointPolynomial F n)) z :=
  (AnalyticOnNhd.eval_continuousLinearMap
    (ContinuousLinearMap.id ℂ (Fin 6 → ℂ)) (jointMidpointPolynomial F n)) z (Set.mem_univ z)

end VacuumBellSeparation
