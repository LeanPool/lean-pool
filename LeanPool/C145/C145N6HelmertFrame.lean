/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145N6ResponseLine

/-!
# The Helmert eigenframe of the six-vertex source.
-/

@[expose] public section
noncomputable section
namespace C145N6Frame
open scoped BigOperators

/-- The six-column integer Helmert array before column normalization. -/
def helmert : Fin 6 → Fin 6 → ℝ :=
  !![1,1,1,1,1,1; 1,-1,1,1,1,1; 1,0,-2,1,1,1;
     1,0,0,-3,1,1; 1,0,0,0,-4,1; 1,0,0,0,0,-5]
/-- The squared lengths of the unnormalized Helmert columns. -/
def gramWeight : Fin 6 → ℝ := ![6,2,6,12,20,30]
/-- The integer numerators of the signed port's projections on the Helmert columns. -/
def numerator : Fin 6 → ℝ := ![119,79,119,119,119,119]
/-- The explicit six-vertex port with two nonzero vertex entries. -/
def port : Fin 6 → ℝ := ![99 / 101,20 / 101,0,0,0,0]
/-- The Helmert array normalized by the square roots of its Gram weights. -/
def frame (v i : Fin 6) : ℝ := helmert v i / Real.sqrt (gramWeight i)
/-- The modal overlap of the port with one normalized Helmert column. -/
def overlap (i : Fin 6) : ℝ := numerator i / (101 * Real.sqrt (gramWeight i))
/-- The contribution of a single modal overlap to a vertex coordinate. -/
def feature (v i : Fin 6) : ℝ := helmert v i * numerator i / (101 * gramWeight i)

theorem gramWeight_pos (i : Fin 6) : 0 < gramWeight i := by
  fin_cases i <;> norm_num [gramWeight]
theorem sqrtWeight_ne (i : Fin 6) : Real.sqrt (gramWeight i) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.2 (gramWeight_pos i))
theorem sqrtWeight_sq (i : Fin 6) : Real.sqrt (gramWeight i) ^ 2 = gramWeight i :=
  Real.sq_sqrt (le_of_lt (gramWeight_pos i))
theorem helmert_gram (i j : Fin 6) :
    (∑ v, helmert v i * helmert v j) = if i = j then gramWeight i else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [helmert, gramWeight, Fin.sum_univ_succ]

theorem frame_orthonormal : C145PhysicalFrame.ColumnOrthonormal frame := by
  intro i j
  have hh : (∑ v, frame v i * frame v j) =
      (∑ v, helmert v i * helmert v j) / (Real.sqrt (gramWeight i) * Real.sqrt (gramWeight j)) := by
    simp only [frame, div_mul_div_comm, Finset.sum_div]
  rw [hh, helmert_gram]
  split_ifs with he
  · subst j
    rw [← pow_two, sqrtWeight_sq]
    exact div_self (ne_of_gt (gramWeight_pos i))
  · simp

theorem frame_ground (v : Fin 6) : frame v 0 = 1 / Real.sqrt 6 := by
  fin_cases v <;> simp [frame, helmert, gramWeight]
theorem raw_port_projection (i : Fin 6) :
    (∑ v, helmert v i * port v) = numerator i / 101 := by
  fin_cases i <;> norm_num [helmert, port, numerator, Fin.sum_univ_succ]
theorem overlap_actual_projection (i : Fin 6) :
    overlap i = ∑ v, frame v i * port v := by
  have h : (∑ v, frame v i * port v) = (∑ v, helmert v i * port v) / Real.sqrt (gramWeight i) := by
    simp only [frame, div_mul_eq_mul_div, Finset.sum_div]
  rw [h, raw_port_projection]
  simp only [overlap, div_div]
theorem overlap_nonzero (i : Fin 6) : overlap i ≠ 0 := by
  apply div_ne_zero
  · fin_cases i <;> norm_num [numerator]
  · exact mul_ne_zero (by norm_num) (sqrtWeight_ne i)
theorem port_normalized : (∑ v, port v ^ 2) = 1 := by
  norm_num [port, Fin.sum_univ_succ]
theorem overlap_square (i : Fin 6) : overlap i ^ 2 = C145N6Literal.overlapSquare i := by
  simp only [overlap, div_pow, mul_pow, sqrtWeight_sq]
  fin_cases i <;> norm_num [numerator, gramWeight, C145N6Literal.overlapSquare]
theorem overlap_frame_feature (v i : Fin 6) : overlap i * frame v i = feature v i := by
  unfold overlap frame feature
  field_simp [sqrtWeight_ne i, ne_of_gt (gramWeight_pos i)]
  rw [sqrtWeight_sq]
  ring
end C145N6Frame

end
