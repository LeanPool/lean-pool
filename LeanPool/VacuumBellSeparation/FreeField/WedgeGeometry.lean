/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Lorentz

/-!
# The actual left wedges and their containing geometry

The ambient product norm on Spacetime is not its Euclidean four-norm.
The latter is defined explicitly here, preserving the square-root-two
constant in the manuscript's containing-wedge estimate.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace

/-- Left wedge with membership specified by `{x | ⟪e₁, x.2⟫_ℝ + |x.1| < ℓ}`. -/
def leftWedge (ℓ : ℝ) : Set Spacetime :=
  {x | ⟪e₁, x.2⟫_ℝ + |x.1| < ℓ}

/-- Left wedge time zero with membership specified by `{x | ⟪e₁, x⟫_ℝ < ℓ}`. -/
def leftWedgeTimeZero (ℓ : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | ⟪e₁, x⟫_ℝ < ℓ}

/-- Spacetime Euclidean norm given by `Real.sqrt (x.1 ^ 2 + ‖x.2‖ ^ 2)`. -/
noncomputable def spacetimeEuclideanNorm (x : Spacetime) : ℝ :=
  Real.sqrt (x.1 ^ 2 + ‖x.2‖ ^ 2)

theorem mem_leftWedge_iff (ℓ : ℝ) (x : Spacetime) :
    x ∈ leftWedge ℓ ↔ ⟪e₁, x.2⟫_ℝ + x.1 < ℓ ∧ ⟪e₁, x.2⟫_ℝ - x.1 < ℓ := by
  change ⟪e₁, x.2⟫_ℝ + |x.1| < ℓ ↔ _
  constructor
  · intro h
    constructor <;> linarith [le_abs_self x.1, neg_abs_le x.1]
  · rintro ⟨hp, hm⟩
    by_cases hx : 0 ≤ x.1
    · rwa [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      linarith

theorem mem_leftWedge_zero_time (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    (0, x) ∈ leftWedge ℓ ↔ x ∈ leftWedgeTimeZero ℓ := by
  simp only [leftWedge, leftWedgeTimeZero, Set.mem_ofPred_eq, abs_zero, add_zero]

theorem boost_light_coordinate_plus (η : ℝ) (x : Spacetime) :
    ⟪e₁, (boost η x).2⟫_ℝ + (boost η x).1 =
      Real.exp η * (⟪e₁, x.2⟫_ℝ + x.1) := by
  rw [boost_apply, boostCLM_apply, inner_e₁_add_smul, ← Real.cosh_add_sinh]
  ring

theorem boost_light_coordinate_minus (η : ℝ) (x : Spacetime) :
    ⟪e₁, (boost η x).2⟫_ℝ - (boost η x).1 =
      Real.exp (-η) * (⟪e₁, x.2⟫_ℝ - x.1) := by
  rw [boost_apply, boostCLM_apply, inner_e₁_add_smul, ← Real.cosh_sub_sinh]
  ring

theorem boost_mem_leftWedge_zero_iff (η : ℝ) (x : Spacetime) :
    boost η x ∈ leftWedge 0 ↔ x ∈ leftWedge 0 := by
  rw [mem_leftWedge_iff, mem_leftWedge_iff, boost_light_coordinate_plus,
    boost_light_coordinate_minus]
  simp only [mul_neg_iff, Real.exp_pos, true_and,
    not_lt_of_ge (Real.exp_pos η).le, not_lt_of_ge (Real.exp_pos (-η)).le,
    false_and, or_false]

theorem leftWedge_eq_translate (ℓ : ℝ) :
    leftWedge ℓ = (fun x : Spacetime => x + (0, ℓ • e₁)) '' leftWedge 0 := by
  ext x
  constructor
  · intro hx
    refine ⟨x - (0, ℓ • e₁), ?_, sub_add_cancel _ _⟩
    change ⟪e₁, x.2 - ℓ • e₁⟫_ℝ + |x.1 - 0| < 0
    rw [inner_sub_right, real_inner_smul_right, inner_e₁_self, mul_one, sub_zero]
    change ⟪e₁, x.2⟫_ℝ + |x.1| < ℓ at hx
    linarith
  · rintro ⟨y, hy, rfl⟩
    change ⟪e₁, y.2 + ℓ • e₁⟫_ℝ + |y.1 + 0| < ℓ
    rw [inner_e₁_add_smul, add_zero]
    change ⟪e₁, y.2⟫_ℝ + |y.1| < 0 at hy
    linarith

theorem spacetimeEuclideanNorm_nonneg (x : Spacetime) : 0 ≤ spacetimeEuclideanNorm x :=
  Real.sqrt_nonneg _

theorem spacetimeEuclideanNorm_le_time_add_space (x : Spacetime) :
    spacetimeEuclideanNorm x ≤ |x.1| + ‖x.2‖ := by
  calc
    spacetimeEuclideanNorm x ≤ Real.sqrt ((|x.1| + ‖x.2‖) ^ 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith [sq_abs x.1, mul_nonneg (abs_nonneg x.1) (norm_nonneg x.2)]
    _ = |x.1| + ‖x.2‖ := Real.sqrt_sq (add_nonneg (abs_nonneg _) (norm_nonneg _))

theorem wedge_coordinate_le_euclidean (x : Spacetime) :
    ⟪e₁, x.2⟫_ℝ + |x.1| ≤ Real.sqrt 2 * spacetimeEuclideanNorm x := by
  have hcoord : ⟪e₁, x.2⟫_ℝ ≤ ‖x.2‖ :=
    (le_abs_self _).trans (abs_inner_e₁_le _)
  calc
    ⟪e₁, x.2⟫_ℝ + |x.1| ≤ |x.1| + ‖x.2‖ := by linarith
    _ = Real.sqrt ((|x.1| + ‖x.2‖) ^ 2) :=
      (Real.sqrt_sq (add_nonneg (abs_nonneg _) (norm_nonneg _))).symm
    _ ≤ Real.sqrt (2 * (x.1 ^ 2 + ‖x.2‖ ^ 2)) := by
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg (|x.1| - ‖x.2‖), sq_abs x.1]
    _ = Real.sqrt 2 * spacetimeEuclideanNorm x := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rfl

theorem spacetimeEuclideanNorm_lt_of_mem_doubleCone {R : ℝ} {x : Spacetime}
    (hx : x ∈ doubleCone 0 R) : spacetimeEuclideanNorm x < R := by
  have hx' : |x.1| + ‖x.2‖ < R := by simpa only [doubleCone, Set.mem_ofPred_eq,
    Prod.fst_zero, Prod.snd_zero, sub_zero] using hx
  exact (spacetimeEuclideanNorm_le_time_add_space x).trans_lt hx'

/-- The source's containing-wedge estimate with an explicit true Euclidean
bound on the transformed point. -/
theorem mem_leftWedge_of_euclidean_bound {x : Spacetime} {r ℓ : ℝ}
    (hx : spacetimeEuclideanNorm x ≤ r) (hℓ : Real.sqrt 2 * r < ℓ) : x ∈ leftWedge ℓ :=
  (wedge_coordinate_le_euclidean x).trans_lt
    ((mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg 2)).trans_lt hℓ)

theorem doubleCone_subset_leftWedge {R ℓ : ℝ}
    (hℓ : Real.sqrt 2 * R ≤ ℓ) : doubleCone 0 R ⊆ leftWedge ℓ := by
  intro x hx
  have hnorm := spacetimeEuclideanNorm_lt_of_mem_doubleCone hx
  exact (wedge_coordinate_le_euclidean x).trans_lt
    ((mul_lt_mul_of_pos_left hnorm (Real.sqrt_pos.mpr (by norm_num))).trans_le hℓ)

end VacuumBellSeparation
