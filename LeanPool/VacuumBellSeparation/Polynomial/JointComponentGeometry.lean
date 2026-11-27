/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Polynomial.JointMidpointPolynomial

/-!
# The four genuine joint-region components in midpoint coordinates

The Boolean labels select the original balls centred at zero and at the
separation vector. Coordinate errors are measured in the complex supremum
norm, allowing later physical complex neighborhoods of all four components.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

/-- The two centres after subtracting the midpoint and dividing by separation. -/
def jointComponentCenter (a b : Bool) (j : Fin 6) : ℂ :=
  if j = 0 then (if a then 1 / 2 else -(1 / 2))
  else if j = 3 then (if b then 1 / 2 else -(1 / 2)) else 0

/-- In joint component given by `∀ j, ‖z j - jointComponentCenter a b j‖ ≤ δ`. -/
def InJointComponent (a b : Bool) (δ : ℝ) (z : Fin 6 → ℂ) : Prop :=
  ∀ j, ‖z j - jointComponentCenter a b j‖ ≤ δ

@[simp] theorem jointComponentCenter_swap (a b : Bool) (j : Fin 6) :
    jointComponentCenter a b (swapSpatialSix j) = jointComponentCenter b a j := by
  have hs0 : swapSpatialSix 0 = 3 := rfl
  have hs1 : swapSpatialSix 1 = 4 := rfl
  have hs2 : swapSpatialSix 2 = 5 := rfl
  have hs3 : swapSpatialSix 3 = 0 := rfl
  have hs4 : swapSpatialSix 4 = 1 := rfl
  have hs5 : swapSpatialSix 5 = 2 := rfl
  fin_cases j <;> simp [jointComponentCenter, hs0, hs1, hs2, hs3, hs4, hs5]

theorem InJointComponent.swap {a b : Bool} {δ : ℝ} {z : Fin 6 → ℂ}
    (hz : InJointComponent a b δ z) : InJointComponent b a δ (z ∘ swapSpatialSix) := by
  intro j
  simpa only [Function.comp_apply, jointComponentCenter_swap] using hz (swapSpatialSix j)

theorem InJointComponent.left {a b : Bool} {δ : ℝ} {z : Fin 6 → ℂ}
    (hz : InJointComponent a b δ z) :
    ‖(z 0 + 1 / 2) - (if a then 1 else 0)‖ ≤ δ := by
  have he : (z 0 + 1 / 2) - (if a then 1 else 0) =
      z 0 - jointComponentCenter a b 0 := by
    (cases a <;> simp [jointComponentCenter]); ring
  rw [he]
  exact hz 0

theorem InJointComponent.right {a b : Bool} {δ : ℝ} {z : Fin 6 → ℂ}
    (hz : InJointComponent a b δ z) :
    ‖(1 / 2 - z 3) - (if b then 0 else 1)‖ ≤ δ := by
  have h := hz 3
  cases b
  · change ‖(1 / 2 - z 3) - 1‖ ≤ δ
    have he : (1 / 2 - z 3) - 1 = -(z 3 + 1 / 2) := by ring
    rw [he, norm_neg]
    simpa [jointComponentCenter] using h
  · change ‖(1 / 2 - z 3) - 0‖ ≤ δ
    have he : (1 / 2 - z 3) - 0 = -(z 3 - 1 / 2) := by ring
    rw [he, norm_neg]
    simpa [jointComponentCenter] using h

theorem InJointComponent.shift_bound {a b : Bool} {δ : ℝ} {z : Fin 6 → ℂ}
    (hz : InJointComponent a b δ z) (j : Fin 6) :
    ‖z j + jointMidpointShift j‖ ≤ δ + 1 := by
  have hc : ‖jointComponentCenter a b j + jointMidpointShift j‖ ≤ (1 : ℝ) := by
    fin_cases j <;> cases a <;> cases b <;>
      norm_num [jointComponentCenter, jointMidpointShift]
  calc
    _ = ‖(z j - jointComponentCenter a b j) +
        (jointComponentCenter a b j + jointMidpointShift j)‖ := by congr 1; ring
    _ ≤ ‖z j - jointComponentCenter a b j‖ +
        ‖jointComponentCenter a b j + jointMidpointShift j‖ := norm_add_le _ _
    _ ≤ δ + 1 := add_le_add (hz j) hc

theorem InJointComponent.desired_shift {δ : ℝ} {z : Fin 6 → ℂ}
    (hz : InJointComponent false true δ z) (j : Fin 6) :
    ‖z j + jointMidpointShift j‖ ≤ δ := by
  have hc : jointComponentCenter false true j = -jointMidpointShift j := by
    fin_cases j <;> norm_num [jointComponentCenter, jointMidpointShift]
  simpa only [hc, sub_neg_eq_add] using hz j

theorem InJointComponent.selector_bounds {a b : Bool} {δ : ℝ} {z : Fin 6 → ℂ}
    (hz : InJointComponent a b δ z) (hδ : δ ≤ 1) :
    ‖z 0 + 1 / 2‖ ≤ 2 ∧ ‖1 / 2 - z 3‖ ≤ 2 := by
  constructor
  · have he : (z 0 + 1 / 2) =
        ((z 0 + 1 / 2) - (if a then 1 else 0)) + (if a then 1 else 0) := by ring
    rw [he]
    have hc : ‖(if a then 1 else 0 : ℂ)‖ ≤ (1 : ℝ) := by cases a <;> norm_num
    exact (norm_add_le _ _).trans ((add_le_add hz.left hc).trans (by linarith))
  · have he : (1 / 2 - z 3) =
        ((1 / 2 - z 3) - (if b then 0 else 1)) + (if b then 0 else 1) := by ring
    rw [he]
    have hc : ‖(if b then 0 else 1 : ℂ)‖ ≤ (1 : ℝ) := by cases b <;> norm_num
    exact (norm_add_le _ _).trans ((add_le_add hz.right hc).trans (by linarith))

theorem InJointComponent.wrong_selector {a b : Bool} {δ : ℝ} {z : Fin 6 → ℂ}
    (hz : InJointComponent a b δ z) (hwrong : ¬ (a = false ∧ b = true)) :
    ‖1 - (z 0 + 1 / 2)‖ ≤ δ ∨ ‖1 - (1 / 2 - z 3)‖ ≤ δ := by
  cases a
  · cases b
    · right
      simpa only [Bool.false_eq_true, ↓reduceIte, norm_sub_rev] using hz.right
    · exact (hwrong ⟨rfl, rfl⟩).elim
  · left
    simpa only [↓reduceIte, norm_sub_rev] using hz.left

end VacuumBellSeparation
