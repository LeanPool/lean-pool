/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.C19PlaneWave

/-!
# C19 Fourier symbol from the native geometry

The moments and low-momentum symbol follow from the canonical C19 bond geometry.
-/

@[expose] public section

namespace LeanDirac.V2

noncomputable section
open BigOperators Complex

/-- The C19 face and edge weights expressed as integers for exact moment sums. -/
def c19IntegerWeight (direction : C19Neighbor) : ℤ :=
  if direction.val < 6 then 2 else 1

theorem c19_weight_is_integer_weight (direction : C19Neighbor) :
    c19Weight direction = (c19IntegerWeight direction : ℝ) := by
  unfold c19Weight c19IntegerWeight
  split <;> norm_num

/-- The weighted first stencil moment measures its response to the coordinate-linear
part of an affine lattice field. -/
def c19FirstMoment (axis : Fin 3) : ℤ :=
  ∑ direction, c19IntegerWeight direction * c19Coord axis direction

/-- The weighted cross moment of two coordinate directions of the stencil. -/
def c19SecondMoment (axis other : Fin 3) : ℤ :=
  ∑ direction, c19IntegerWeight direction *
    c19Coord axis direction * c19Coord other direction

/-- The C19 weighted first-difference stencil annihilates coordinate-linear fields. -/
theorem c19_first_moment_zero (axis : Fin 3) :
    c19FirstMoment axis = 0 := by
  fin_cases axis <;> decide

theorem c19_second_moment_isotropic (axis other : Fin 3) :
    c19SecondMoment axis other = if axis = other then 12 else 0 := by
  fin_cases axis <;> fin_cases other <;> decide

/-- The exact Fourier symbol of the weighted C19 difference operator. -/
def c19TransportSymbol (momentum : LatticeMomentum) : ℝ :=
  ∑ direction,
    c19Weight direction *
      Complex.normSq (1 - c19Character momentum direction)

theorem c19_transport_symbol_nonnegative (momentum : LatticeMomentum) :
    0 ≤ c19TransportSymbol momentum := by
  unfold c19TransportSymbol
  exact Finset.sum_nonneg (fun direction _ =>
    mul_nonneg (le_of_lt (c19_weight_positive direction))
      (Complex.normSq_nonneg _))

theorem c19_character_zero (direction : C19Neighbor) :
    c19Character (fun _ => 0) direction = 1 := by
  simp [c19Character, c19PhaseAngle]

theorem c19_transport_symbol_zero :
    c19TransportSymbol (fun _ => 0) = 0 := by
  simp [c19TransportSymbol, c19_character_zero]

/-- The propagation scale obtained from the isotropic second moment of the stencil. -/
def c19ContinuumSpeed : ℝ := Real.sqrt 12

theorem c19_continuum_speed_square : c19ContinuumSpeed ^ 2 = 12 := by
  norm_num [c19ContinuumSpeed]

/-- The physical momentum along an axis, scaled by the C19 propagation speed. -/
def c19ScaledMomentum (momentum : LatticeMomentum) (axis : Fin 3) : ℝ :=
  c19ContinuumSpeed * momentum axis

theorem normSq_one_sub_exp_I (angle : ℝ) :
    Complex.normSq
        (1 - Complex.exp (Complex.I * (angle : ℂ))) =
      2 * (1 - Real.cos angle) := by
  rw [mul_comm, Complex.exp_ofReal_mul_I]
  rw [Complex.normSq_apply]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  nlinarith [Real.sin_sq_add_cos_sq angle]

/-- The quadratic approximation of the C19 transport symbol at zero momentum. -/
def c19QuadraticSymbol (momentum : LatticeMomentum) : ℝ :=
  12 * (momentum 0 ^ 2 + momentum 1 ^ 2 + momentum 2 ^ 2)

theorem c19_quadratic_symbol_eq_scaled_momentum (momentum : LatticeMomentum) :
    c19QuadraticSymbol momentum = c19ScaledMomentum momentum 0 ^ 2 +
      c19ScaledMomentum momentum 1 ^ 2 + c19ScaledMomentum momentum 2 ^ 2 := by
  simp only [c19QuadraticSymbol, c19ScaledMomentum, mul_pow, c19_continuum_speed_square]
  ring

/-- Contract the C19 phase with one stencil coordinate using the isotropic moment. -/
theorem c19_linear_axis_moment
    (momentum : LatticeMomentum) (axis : Fin 3) :
    ∑ direction : C19Neighbor,
        c19Weight direction * (c19Coord axis direction : ℝ) *
          c19PhaseAngle momentum direction =
      12 * momentum axis := by
  have hmoment (first second : Fin 3) :
      (∑ direction : C19Neighbor,
        c19Weight direction * (c19Coord first direction : ℝ) *
          (c19Coord second direction : ℝ)) =
        (c19SecondMoment first second : ℝ) := by
    simp_rw [c19_weight_is_integer_weight]
    exact_mod_cast rfl
  unfold c19PhaseAngle
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ x : Fin 3, ∑ direction : C19Neighbor,
      c19Weight direction * (c19Coord axis direction : ℝ) *
        (momentum x * (c19Coord x direction : ℝ))) =
        ∑ x : Fin 3, momentum x *
          (∑ direction : C19Neighbor,
            c19Weight direction * (c19Coord axis direction : ℝ) *
              (c19Coord x direction : ℝ)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro direction _
      ring
    _ = ∑ x : Fin 3, momentum x * c19SecondMoment axis x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hmoment]
    _ = 12 * momentum axis := by
      simp [c19_second_moment_isotropic]
      ring

theorem c19_quadratic_symbol_is_phase_square_sum
    (momentum : LatticeMomentum) :
    c19QuadraticSymbol momentum =
      ∑ direction,
        c19Weight direction * c19PhaseAngle momentum direction ^ 2 := by
  symm
  simp only [pow_two]
  calc
    (∑ d : C19Neighbor, c19Weight d * (c19PhaseAngle momentum d * c19PhaseAngle momentum d)) =
        ∑ d : C19Neighbor, ∑ axis : Fin 3, momentum axis *
          (c19Weight d * (c19Coord axis d : ℝ) * c19PhaseAngle momentum d) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [show c19Weight d * (c19PhaseAngle momentum d * c19PhaseAngle momentum d) =
        c19PhaseAngle momentum d * (c19Weight d * c19PhaseAngle momentum d) by ring]
      nth_rw 1 [c19PhaseAngle]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun axis _ ↦ by ring
    _ = ∑ axis : Fin 3, momentum axis * (12 * momentum axis) := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, c19_linear_axis_moment]
    _ = c19QuadraticSymbol momentum := by
      simp only [Fin.sum_univ_three, c19QuadraticSymbol]
      ring

/-- The exact difference between the lattice symbol and its quadratic approximation. -/
def c19SpatialRemainder (momentum : LatticeMomentum) : ℝ :=
  c19TransportSymbol momentum - c19QuadraticSymbol momentum

theorem c19_spatial_remainder_is_bond_error_sum
    (momentum : LatticeMomentum) :
    c19SpatialRemainder momentum =
      ∑ direction, c19Weight direction *
        (2 * (1 - Real.cos (c19PhaseAngle momentum direction)) -
          c19PhaseAngle momentum direction ^ 2) := by
  rw [c19SpatialRemainder, c19_quadratic_symbol_is_phase_square_sum]
  unfold c19TransportSymbol
  simp_rw [c19Character, normSq_one_sub_exp_I]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro direction _
  ring

/-- Each C19 offset has at most two unit coordinates. -/
private theorem c19_offset_abs_sum_le_two (direction : C19Neighbor) :
    ∑ axis : Fin 3, |(c19Coord axis direction : ℝ)| ≤ 2 := by
  have count : ∀ d : C19Neighbor, (∑ axis : Fin 3, (c19Coord axis d).natAbs) ≤ 2 := by
    -- This finite check counts the occupied coordinates of each stencil offset.
    decide
  have absCast (n : ℤ) : (n.natAbs : ℝ) = |(n : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have castCount : (∑ axis : Fin 3, ((c19Coord axis direction).natAbs : ℝ)) ≤ 2 := by
    exact_mod_cast count direction
  simpa only [absCast] using castCount

theorem c19_phase_angle_abs_le_two_mul
    (momentum : LatticeMomentum) (radius : ℝ) (hradius : 0 ≤ radius)
    (hmomentum : ∀ axis, |momentum axis| ≤ radius)
    (direction : C19Neighbor) :
    |c19PhaseAngle momentum direction| ≤ 2 * radius := by
  unfold c19PhaseAngle
  calc
    |∑ axis : Fin 3, momentum axis * (c19Coord axis direction : ℝ)| ≤
        ∑ axis : Fin 3, |momentum axis * (c19Coord axis direction : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ axis : Fin 3, radius * |(c19Coord axis direction : ℝ)| := by
      refine Finset.sum_le_sum fun axis _ ↦ ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hmomentum axis) (abs_nonneg _)
    _ = radius * ∑ axis : Fin 3, |(c19Coord axis direction : ℝ)| :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * radius := by
      rw [mul_comm 2 radius]
      exact mul_le_mul_of_nonneg_left (c19_offset_abs_sum_le_two direction) hradius

theorem cosine_phase_error_bound
    (angle radius : ℝ) (_hradius : 0 ≤ radius)
    (hangle : |angle| ≤ 2 * radius) (hsmall : 2 * radius ≤ 1) :
    |2 * (1 - Real.cos angle) - angle ^ 2| ≤ (5/3 : ℝ) * radius ^ 4 := by
  have hunit : |angle| ≤ 1 := hangle.trans hsmall
  have hcos := Real.cos_bound hunit
  have hpow : |angle|^4 ≤ (2 * radius) ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg angle) hangle 4
  calc
    |2 * (1 - Real.cos angle) - angle ^ 2| =
        2 * |Real.cos angle - (1 - angle ^ 2 / 2)| := by
          rw [show 2 * (1 - Real.cos angle) - angle ^ 2 =
            -2 * (Real.cos angle - (1 - angle ^ 2 / 2)) by ring]
          simp
    _ ≤ 2 * (|angle|^4 * (5/96 : ℝ)) := by nlinarith
    _ ≤ 2 * ((2 * radius) ^ 4 * (5/96 : ℝ)) := by nlinarith
    _ = (5/3 : ℝ) * radius ^ 4 := by ring

theorem c19_spatial_remainder_bound
    (momentum : LatticeMomentum) (radius : ℝ) (hradius : 0 ≤ radius)
    (hmomentum : ∀ axis, |momentum axis| ≤ radius)
    (hsmall : 2 * radius ≤ 1) :
    |c19SpatialRemainder momentum| ≤ 40 * radius ^ 4 := by
  rw [c19_spatial_remainder_is_bond_error_sum]
  calc
    |∑ direction, c19Weight direction *
        (2 * (1 - Real.cos (c19PhaseAngle momentum direction)) -
          c19PhaseAngle momentum direction ^ 2)| ≤
      ∑ direction, |c19Weight direction *
        (2 * (1 - Real.cos (c19PhaseAngle momentum direction)) -
          c19PhaseAngle momentum direction ^ 2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ direction, c19Weight direction * ((5/3 : ℝ) * radius ^ 4) := by
      apply Finset.sum_le_sum
      intro direction _
      rw [abs_mul, abs_of_pos (c19_weight_positive direction)]
      exact mul_le_mul_of_nonneg_left
        (cosine_phase_error_bound
          (c19PhaseAngle momentum direction) radius hradius
          (c19_phase_angle_abs_le_two_mul momentum radius hradius
            hmomentum direction) hsmall)
        (le_of_lt (c19_weight_positive direction))
    _ = 40 * radius ^ 4 := by
      have hweights : ∑ direction, c19Weight direction = 24 := by
        norm_num [c19Weight, Fin.sum_univ_succ]
      rw [← Finset.sum_mul, hweights]
      ring

theorem c19_symbol_exact_quadratic_plus_remainder
    (momentum : LatticeMomentum) :
    c19TransportSymbol momentum =
      c19QuadraticSymbol momentum + c19SpatialRemainder momentum := by
  simp [c19SpatialRemainder]

theorem c19_spatial_remainder_zero_at_origin :
    c19SpatialRemainder (fun _ => 0) = 0 := by
  simp [c19SpatialRemainder, c19QuadraticSymbol,
    c19_transport_symbol_zero]

end
end LeanDirac.V2
