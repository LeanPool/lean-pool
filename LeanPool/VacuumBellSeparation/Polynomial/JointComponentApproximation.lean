/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Polynomial.JointComponentGeometry

/-!
# Actual polynomial errors on all four complex joint-region components

The target is the negative cross kernel and its transpose, with zero on
both same-region components. The bounds use the actual selector-weighted
Taylor polynomial and a universal geometric constant independent of mass.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian MvPolynomial

/-- An oriented cross kernel, extended by zero to the other labelled components. -/
def jointOrientedComponentKernel (F : (Fin 6 → ℂ) → ℂ) (a b : Bool)
    (z : Fin 6 → ℂ) : ℂ :=
  if a = false ∧ b = true then F (fun j => z j + jointMidpointShift j) else 0

/-- The literal product-minus-joint sign on the two cross components. -/
def jointComponentKernel (F : (Fin 6 → ℂ) → ℂ) (a b : Bool)
    (z : Fin 6 → ℂ) : ℂ :=
  -(jointOrientedComponentKernel F a b z +
    jointOrientedComponentKernel F b a (z ∘ swapSpatialSix))

theorem jointOriented_desired_geometric {M δ : ℝ} (hM : 0 ≤ M)
    (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / 200)
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), DifferentiableAt ℂ F z)
    (hbound : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), ‖F z‖ ≤ M)
    (n : ℕ) (z : Fin 6 → ℂ) (hz : InJointComponent false true δ z) :
    ‖F (fun j => z j + jointMidpointShift j) - eval z (jointMidpointOriented F n)‖ ≤
      584 * M * (26214400 * δ) ^ n := by
  rw [eval_jointMidpointOriented]
  have h := selectedCauchyTaylor_desired_error (n := n) (R := 1 / 100)
    (by norm_num) hδ (by linarith) (by linarith) hM F hF hbound
    (z 0 + 1 / 2) (1 / 2 - z 3) (fun j => z j + jointMidpointShift j)
    (by simpa using hz.left) (by simpa using hz.right) hz.desired_shift
  have hsq : δ ^ 2 ≤ δ := by nlinarith
  have h₁ : (2 * (δ / (1 / 100))) ^ n ≤ (26214400 * δ) ^ n := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have h₂ : (8 * δ) ^ (2 * n) ≤ (26214400 * δ) ^ n := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  calc
    _ ≤ M * (576 * (2 * (δ / (1 / 100))) ^ n + 8 * (8 * δ) ^ (2 * n)) := h
    _ ≤ M * (576 * (26214400 * δ) ^ n + 8 * (26214400 * δ) ^ n) := by gcongr
    _ = _ := by ring

theorem jointOriented_wrong_geometric {M δ : ℝ} (hM : 0 ≤ M)
    (hδ : 0 ≤ δ) (hsmall : δ ≤ 1)
    (F : (Fin 6 → ℂ) → ℂ)
    (hbound : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), ‖F z‖ ≤ M)
    (n : ℕ) (a b : Bool) (z : Fin 6 → ℂ) (hz : InJointComponent a b δ z)
    (hwrong : ¬ (a = false ∧ b = true)) :
    ‖eval z (jointMidpointOriented F n)‖ ≤ 64 * M * (26214400 * δ) ^ n := by
  rw [eval_jointMidpointOriented]
  have hb := hz.selector_bounds hsmall
  have h := selectedCauchyTaylor_wrong_component (n := n) (R := 1 / 100) (r := 2)
    (by norm_num) hM F hbound
    (z 0 + 1 / 2) (1 / 2 - z 3) (fun j => z j + jointMidpointShift j)
    hb.1 hb.2 (hz.wrong_selector hwrong)
    (fun j => (hz.shift_bound j).trans (by linarith))
  have hsq : δ ^ 2 ≤ δ := by nlinarith
  have hbase : (256 * δ) ^ 2 * (2 * max 1 (2 / (1 / 100 : ℝ))) ≤
      26214400 * δ := by
    norm_num
    nlinarith
  exact h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hbase n) (by positivity))

theorem jointOriented_component_error {M δ : ℝ} (hM : 0 ≤ M)
    (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / 200)
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), DifferentiableAt ℂ F z)
    (hbound : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), ‖F z‖ ≤ M)
    (n : ℕ) (a b : Bool) (z : Fin 6 → ℂ) (hz : InJointComponent a b δ z) :
    ‖jointOrientedComponentKernel F a b z - eval z (jointMidpointOriented F n)‖ ≤
      584 * M * (26214400 * δ) ^ n := by
  by_cases hd : a = false ∧ b = true
  · rcases hd with ⟨rfl, rfl⟩
    simpa only [jointOrientedComponentKernel, and_self, ↓reduceIte] using
      jointOriented_desired_geometric hM hδ hsmall F hF hbound n z hz
  · rw [jointOrientedComponentKernel, ite_eq_right hd, zero_sub, norm_neg]
    exact (jointOriented_wrong_geometric hM hδ (by linarith) F hbound n a b z hz hd).trans
      (by gcongr; norm_num)

/-- Uniform approximation on the two cross and the two same-region components. -/
theorem jointMidpointPolynomial_component_error {M δ : ℝ} (hM : 0 ≤ M)
    (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / 200)
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), DifferentiableAt ℂ F z)
    (hbound : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), ‖F z‖ ≤ M)
    (n : ℕ) (a b : Bool) (z : Fin 6 → ℂ) (hz : InJointComponent a b δ z) :
    ‖jointComponentKernel F a b z - eval z (jointMidpointPolynomial F n)‖ ≤
      1168 * M * (26214400 * δ) ^ n := by
  have h₁ := jointOriented_component_error hM hδ hsmall F hF hbound n a b z hz
  have h₂ := jointOriented_component_error hM hδ hsmall F hF hbound n b a
    (z ∘ swapSpatialSix) hz.swap
  simp only [jointComponentKernel, jointMidpointPolynomial, map_neg, map_add, eval_rename]
  have he : -(jointOrientedComponentKernel F a b z +
        jointOrientedComponentKernel F b a (z ∘ swapSpatialSix)) -
      -(eval z (jointMidpointOriented F n) +
        eval (z ∘ swapSpatialSix) (jointMidpointOriented F n)) =
      -((jointOrientedComponentKernel F a b z - eval z (jointMidpointOriented F n)) +
        (jointOrientedComponentKernel F b a (z ∘ swapSpatialSix) -
          eval (z ∘ swapSpatialSix) (jointMidpointOriented F n))) := by ring
  rw [he, norm_neg]
  exact (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

end VacuumBellSeparation
