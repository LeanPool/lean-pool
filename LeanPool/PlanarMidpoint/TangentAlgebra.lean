/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.Algebra
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum

/-!
# Exact tangent-kernel certificates

Linear polynomial combinations of the ten obstruction rows isolate every
coordinate of a tangent to either exceptional graph.
-/

@[expose] public section

namespace PlanarMidpoint


/-- The derivative array of a pure-cube tangent, with denominators cleared. -/
def qTangentArray (s t : ℝ) (w : Fin 4 → ℝ) : Fin 8 → ℝ :=
  ![(s ^ 4 + 3 * s ^ 2 * t ^ 2) * w 0 + (-2 * s ^ 3 * t) * w 1,
    (2 * s * t ^ 3) * w 0 + (s ^ 4 - s ^ 2 * t ^ 2) * w 1,
    (-s ^ 2 * t ^ 2 + t ^ 4) * w 0 + (2 * s ^ 3 * t) * w 1,
    (-2 * s * t ^ 3) * w 0 + (3 * s ^ 2 * t ^ 2 + t ^ 4) * w 1,
    (s ^ 4 + 3 * s ^ 2 * t ^ 2) * w 2 + (-2 * s ^ 3 * t) * w 3,
    (2 * s * t ^ 3) * w 2 + (s ^ 4 - s ^ 2 * t ^ 2) * w 3,
    (-s ^ 2 * t ^ 2 + t ^ 4) * w 2 + (2 * s ^ 3 * t) * w 3,
    (-2 * s * t ^ 3) * w 2 + (3 * s ^ 2 * t ^ 2 + t ^ 4) * w 3]

theorem q_tangent_kernel (s t : ℝ) (w : Fin 4 → ℝ)
    (hρ : s ^ 2 + t ^ 2 ≠ 0)
    (h : Algebra.Kernel (s ^ 3) (s ^ 2 * t) (s * t ^ 2) (t ^ 3) (qTangentArray s t w)) :
    w = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  norm_num [qTangentArray] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hw0 : (s ^ 2 + t ^ 2) ^ 4 * w 0 = 0 := by
    have he : 36 * ((s ^ 2 + t ^ 2) ^ 4 * w 0) = 0 := by
      linear_combination (12 * s) * h0 + (84 * t) * h1 + (-18 * s) * h2 + (-9 * t) * h3 + (252 *
          s) * h4 + (-204 * t) * h5 + (28 * t) * h7 + (-93 * s) * h8
    linarith only [he]
  have hw1 : (s ^ 2 + t ^ 2) ^ 4 * w 1 = 0 := by
    have he : 36 * ((s ^ 2 + t ^ 2) ^ 4 * w 1) = 0 := by
      linear_combination (-24 * t) * h0 + (88 * t) * h2 + (-93 * s) * h3 + (180 * t) * h4 + (36 *
          s) * h5 + (-111 * t) * h6 + (52 * s) * h7 + (-18 * t) * h8 + (-96 * s) * h9
    linarith only [he]
  have hw2 : (s ^ 2 + t ^ 2) ^ 4 * w 2 = 0 := by
    have he : 36 * ((s ^ 2 + t ^ 2) ^ 4 * w 2) = 0 := by
      linear_combination (-96 * t) * h0 + (-18 * s) * h1 + (52 * t) * h2 + (-111 * s) * h3 + (36 *
          t) * h4 + (180 * s) * h5 + (-93 * t) * h6 + (88 * s) * h7 + (-24 * s) * h9
    linarith only [he]
  have hw3 : (s ^ 2 + t ^ 2) ^ 4 * w 3 = 0 := by
    have he : 36 * ((s ^ 2 + t ^ 2) ^ 4 * w 3) = 0 := by
      linear_combination (-93 * t) * h1 + (28 * s) * h2 + (-204 * s) * h4 + (252 * t) * h5 + (-9 *
          s) * h6 + (-18 * t) * h7 + (84 * s) * h8 + (12 * t) * h9
    linarith only [he]
  ext i
  fin_cases i
  · exact (mul_eq_zero.mp hw0).resolve_left (pow_ne_zero 4 hρ)
  · exact (mul_eq_zero.mp hw1).resolve_left (pow_ne_zero 4 hρ)
  · exact (mul_eq_zero.mp hw2).resolve_left (pow_ne_zero 4 hρ)
  · exact (mul_eq_zero.mp hw3).resolve_left (pow_ne_zero 4 hρ)

/-- The derivative array of a second-graph tangent, with denominators cleared. -/
def rTangentArray (s t : ℝ) (w : Fin 4 → ℝ) : Fin 8 → ℝ :=
  ![(-3 * s ^ 2 * t ^ 2 + 3 * t ^ 4) * w 0 + (6 * s ^ 3 * t) * w 1,
    (-6 * s * t ^ 3) * w 0 + (-2 * s ^ 4 + 5 * s ^ 2 * t ^ 2 + t ^ 4) * w 1,
    (s ^ 4 + 5 * s ^ 2 * t ^ 2 - 2 * t ^ 4) * w 0 + (-6 * s ^ 3 * t) * w 1,
    (6 * s * t ^ 3) * w 0 + (3 * s ^ 4 - 3 * s ^ 2 * t ^ 2) * w 1,
    (-3 * s ^ 2 * t ^ 2 + 3 * t ^ 4) * w 2 + (6 * s ^ 3 * t) * w 3,
    (-6 * s * t ^ 3) * w 2 + (-2 * s ^ 4 + 5 * s ^ 2 * t ^ 2 + t ^ 4) * w 3,
    (s ^ 4 + 5 * s ^ 2 * t ^ 2 - 2 * t ^ 4) * w 2 + (-6 * s ^ 3 * t) * w 3,
    (6 * s * t ^ 3) * w 2 + (3 * s ^ 4 - 3 * s ^ 2 * t ^ 2) * w 3]

theorem r_tangent_kernel (s t : ℝ) (w : Fin 4 → ℝ)
    (hρ : s ^ 2 + t ^ 2 ≠ 0)
    (h : Algebra.Kernel (3 * s * t ^ 2) (-2 * s ^ 2 * t + t ^ 3) (s ^ 3 - 2 * s * t ^ 2) (3 * s ^
        2 * t) (rTangentArray s t w)) :
    w = 0 := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  norm_num [rTangentArray] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hw0 : (s ^ 2 + t ^ 2) ^ 4 * w 0 = 0 := by
    have he : 349236 * ((s ^ 2 + t ^ 2) ^ 4 * w 0) = 0 := by
      linear_combination (198044 * s) * h0 + (-14059 * t) * h1 + (108436 * s) * h2 + (82684 * t) *
          h3 + (65600 * s) * h4 + (28576 * t) * h5 + (-79741 * s) * h6 + (-75082 * t) * h7 +
          (17002 * s) * h8 + (-92096 * t) * h9
    linarith only [he]
  have hw1 : (s ^ 2 + t ^ 2) ^ 4 * w 1 = 0 := by
    have he : 843660 * ((s ^ 2 + t ^ 2) ^ 4 * w 1) = 0 := by
      linear_combination (378568 * t) * h0 + (-25705 * s) * h1 + (33086 * t) * h2 + (208000 * s) *
          h3 + (754768 * t) * h4 + (425152 * s) * h5 + (178570 * t) * h6 + (-57166 * s) * h7 +
          (-55135 * t) * h8 + (166672 * s) * h9
    linarith only [he]
  have hw2 : (s ^ 2 + t ^ 2) ^ 4 * w 2 = 0 := by
    have he : 843660 * ((s ^ 2 + t ^ 2) ^ 4 * w 2) = 0 := by
      linear_combination (166672 * t) * h0 + (-55135 * s) * h1 + (-57166 * t) * h2 + (178570 * s)
          * h3 + (425152 * t) * h4 + (754768 * s) * h5 + (208000 * t) * h6 + (33086 * s) * h7 +
          (-25705 * t) * h8 + (378568 * s) * h9
    linarith only [he]
  have hw3 : (s ^ 2 + t ^ 2) ^ 4 * w 3 = 0 := by
    have he : 349236 * ((s ^ 2 + t ^ 2) ^ 4 * w 3) = 0 := by
      linear_combination (-92096 * s) * h0 + (17002 * t) * h1 + (-75082 * s) * h2 + (-79741 * t) *
          h3 + (28576 * s) * h4 + (65600 * t) * h5 + (82684 * s) * h6 + (108436 * t) * h7 +
          (-14059 * s) * h8 + (198044 * t) * h9
    linarith only [he]
  ext i
  fin_cases i
  · exact (mul_eq_zero.mp hw0).resolve_left (pow_ne_zero 4 hρ)
  · exact (mul_eq_zero.mp hw1).resolve_left (pow_ne_zero 4 hρ)
  · exact (mul_eq_zero.mp hw2).resolve_left (pow_ne_zero 4 hρ)
  · exact (mul_eq_zero.mp hw3).resolve_left (pow_ne_zero 4 hρ)

end PlanarMidpoint
