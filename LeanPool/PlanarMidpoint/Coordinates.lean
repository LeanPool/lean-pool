/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.Basic
public import LeanPool.PlanarMidpoint.Algebra
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Exact coordinate semantics of the fourth-order obstruction. -/

@[expose] public section
namespace PlanarMidpoint

/-- The eight entries of a linear map from planar vectors to cubic coefficients. -/
abbrev DerivativeArray := Fin 8 → ℝ

/-- The columns of a cubic derivative in the fixed Euclidean basis. -/
def derivativeArray (J : E →L[ℝ] Coeff) : DerivativeArray :=
  ![J (vec 1 0) 0, J (vec 1 0) 1, J (vec 1 0) 2, J (vec 1 0) 3,
    J (vec 0 1) 0, J (vec 0 1) 1, J (vec 0 1) 2, J (vec 0 1) 3]

/-- Evaluation of a derivative represented by its eight coordinate entries. -/
def arrayApply (z : DerivativeArray) (h : E) : Coeff :=
  ![z 0 * h 0 + z 4 * h 1, z 1 * h 0 + z 5 * h 1,
    z 2 * h 0 + z 6 * h 1, z 3 * h 0 + z 7 * h 1]

theorem vec_decomp (h : E) : h = h 0 • vec 1 0 + h 1 • vec 0 1 := by
  apply vec_ext <;> simp [vec]

theorem arrayApply_derivativeArray (J : E →L[ℝ] Coeff) (h : E) :
    arrayApply (derivativeArray J) h = J h := by
  have he : J h = h 0 • J (vec 1 0) + h 1 • J (vec 0 1) := by
    conv_lhs => rw [vec_decomp h]
    simp only [map_add, map_smul]
  rw [he]
  ext i
  fin_cases i <;> simp [arrayApply, derivativeArray] <;> ring

theorem derivativeArray_eq_zero_iff (J : E →L[ℝ] Coeff) :
    derivativeArray J = 0 ↔ J = 0 := by
  constructor
  · intro h
    ext v i
    rw [← arrayApply_derivativeArray J v, h]
    fin_cases i <;> simp [arrayApply]
  · rintro rfl
    simp [derivativeArray]

/-- The midpoint obstruction expressed through coordinate derivative data. -/
def arrayObstruction (c : Coeff) (z : DerivativeArray) (h : E) : E :=
  2 • K c h (K (arrayApply z h) h h) + 5 • K (arrayApply z (K c h h)) h h - 4 • K (arrayApply z h)
      h (K c h h)

theorem arrayObstruction_derivativeArray (c : Coeff) (J : E →L[ℝ] Coeff) (h : E) :
    arrayObstruction c (derivativeArray J) h = obstruction c J h := by
  simp [arrayObstruction, obstruction, arrayApply_derivativeArray]

/-- The ten scalar coefficients of the two homogeneous quartic obstruction components. -/
def rows (c : Coeff) (z : DerivativeArray) : Fin 10 → ℝ :=
  ![3 * (c 0) * z 0 - 2 * (c 1) * z 1 + 5 * (c 1) * z 4,
    4 * (c 1) * z 0 + 8 * (c 1) * z 5 + z 1 * (10 * (c 0) - 6 * (c 2)) + z 4 * (-2 * (c 0) + 10 *
        (c 2)),
    2 * (c 1) * z 3 + 5 * (c 1) * z 6 + (c 2) * z 0 + 14 * (c 2) * z 5 + z 1 * (16 * (c 1) - 4 *
        (c 3)) + z 2 * (7 * (c 0) - 4 * (c 2)) + z 4 * (-6 * (c 1) + 5 * (c 3)),
    2 * (c 1) * z 7 + 6 * (c 2) * z 1 + 2 * (c 2) * z 3 - 4 * (c 2) * z 4 + z 2 * (12 * (c 1) - 4
        * (c 3)) + z 5 * (-4 * (c 1) + 6 * (c 3)) + z 6 * (2 * (c 0) + 6 * (c 2)),
    5 * (c 2) * z 2 - 4 * (c 2) * z 5 + 2 * (c 2) * z 7 + z 6 * (2 * (c 1) + (c 3)),
    2 * (c 1) * z 0 - 4 * (c 1) * z 2 + 5 * (c 1) * z 5 + z 1 * ((c 0) + 2 * (c 2)),
    -4 * (c 1) * z 3 + 2 * (c 1) * z 4 + 6 * (c 1) * z 6 + 2 * (c 2) * z 0 + z 1 * (6 * (c 1) + 2
        * (c 3)) + z 2 * (6 * (c 0) - 4 * (c 2)) + z 5 * (-4 * (c 0) + 12 * (c 2)),
    14 * (c 1) * z 2 + (c 1) * z 7 + 5 * (c 2) * z 1 + 2 * (c 2) * z 4 + z 3 * (5 * (c 0) - 6 * (c
        2)) + z 5 * (-4 * (c 1) + 7 * (c 3)) + z 6 * (-4 * (c 0) + 16 * (c 2)),
    8 * (c 2) * z 2 + 4 * (c 2) * z 7 + z 3 * (10 * (c 1) - 2 * (c 3)) + z 6 * (-6 * (c 1) + 10 *
        (c 3)),
    5 * (c 2) * z 3 - 2 * (c 2) * z 6 + 3 * (c 3) * z 7]

theorem kernel_iff_rows (c : Coeff) (z : DerivativeArray) :
    Algebra.Kernel (c 0) (c 1) (c 2) (c 3) z ↔ ∀ i, rows c z i = 0 := by
  simp [Algebra.Kernel, rows, Fin.forall_fin_succ]

theorem arrayObstruction_component_0 (c : Coeff) (z : DerivativeArray) (h : E) :
    arrayObstruction c z h 0 = rows c z 0 * h 0 ^ 4 * h 1 ^ 0 + rows c z 1 * h 0 ^ 3 * h 1 ^ 1 +
        rows c z 2 * h 0 ^ 2 * h 1 ^ 2 + rows c z 3 * h 0 ^ 1 * h 1 ^ 3 + rows c z 4 * h 0 ^ 0 * h
        1 ^ 4 := by
  simp [arrayObstruction, K, arrayApply, rows]
  ring

theorem arrayObstruction_component_1 (c : Coeff) (z : DerivativeArray) (h : E) :
    arrayObstruction c z h 1 = rows c z 5 * h 0 ^ 4 * h 1 ^ 0 + rows c z 6 * h 0 ^ 3 * h 1 ^ 1 +
        rows c z 7 * h 0 ^ 2 * h 1 ^ 2 + rows c z 8 * h 0 ^ 1 * h 1 ^ 3 + rows c z 9 * h 0 ^ 0 * h
        1 ^ 4 := by
  simp [arrayObstruction, K, arrayApply, rows]
  ring

theorem quartic_coefficients_zero (a b c d e : ℝ)
    (h : ∀ j : Fin 5, a * (j : ℝ) ^ 4 + b * (j : ℝ) ^ 3 + c * (j : ℝ) ^ 2 + d * (j : ℝ) + e = 0) :
        a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  norm_num at h0 h1 h2 h3 h4
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Five samples determine whether the coordinate obstruction vanishes identically. -/
theorem kernel_of_five_arrayObstruction_zero (c : Coeff) (z : DerivativeArray)
    (htest : ∀ j : Fin 5, arrayObstruction c z (vec (j : ℝ) 1) = 0) :
    Algebra.Kernel (c 0) (c 1) (c 2) (c 3) z := by
  apply (kernel_iff_rows c z).mpr
  have h0 : ∀ j : Fin 5,
      rows c z 0 * (j : ℝ) ^ 4 + rows c z 1 * (j : ℝ) ^ 3 + rows c z 2 * (j : ℝ) ^ 2 + rows c z
          3 * (j : ℝ) + rows c z 4 = 0 := by
    intro j
    simpa [arrayObstruction_component_0, vec] using
      congrArg (fun v : E => v 0) (htest j)
  have h1 : ∀ j : Fin 5,
      rows c z 5 * (j : ℝ) ^ 4 + rows c z 6 * (j : ℝ) ^ 3 + rows c z 7 * (j : ℝ) ^ 2 + rows c z
          8 * (j : ℝ) + rows c z 9 = 0 := by
    intro j
    simpa [arrayObstruction_component_1, vec] using
      congrArg (fun v : E => v 1) (htest j)
  have hs0 := quartic_coefficients_zero _ _ _ _ _ h0
  have hs1 := quartic_coefficients_zero _ _ _ _ _ h1
  obtain ⟨h0, h1, h2, h3, h4⟩ := hs0
  obtain ⟨h5, h6, h7, h8, h9⟩ := hs1
  intro i
  fin_cases i <;> assumption

theorem kernel_iff_arrayObstruction_zero (c : Coeff) (z : DerivativeArray) :
    Algebra.Kernel (c 0) (c 1) (c 2) (c 3) z ↔ ∀ h, arrayObstruction c z h = 0 := by
  constructor
  · intro hk h
    have hz := (kernel_iff_rows c z).mp hk
    apply vec_ext
    · simp [arrayObstruction_component_0, hz]
    · simp [arrayObstruction_component_1, hz]
  · intro hz
    exact kernel_of_five_arrayObstruction_zero c z (fun j ↦ hz (vec (j : ℝ) 1))

theorem kernel_of_obstruction_zero (c : Coeff) (J : E →L[ℝ] Coeff)
    (h : ∀ v, obstruction c J v = 0) :
    Algebra.Kernel (c 0) (c 1) (c 2) (c 3) (derivativeArray J) := by
  apply (kernel_iff_arrayObstruction_zero c (derivativeArray J)).mpr
  simpa [arrayObstruction_derivativeArray] using h

end PlanarMidpoint
