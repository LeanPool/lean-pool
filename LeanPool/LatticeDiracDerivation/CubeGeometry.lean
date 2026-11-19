/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/CubeGeometry.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.C19Geometry

/-! Explicit eight-corner tetrahedral geometry used by the prepared state. -/

@[expose] public section

namespace LeanDirac

noncomputable section
open BigOperators Complex

abbrev CubeCorner := Fin 8

def tetraA : ℝ := 1 / Real.sqrt 3
def tetraB : ℝ := Real.sqrt 2 / Real.sqrt 3
def omega : ℂ := (-1/2 : ℝ) + (Real.sqrt 3 / 2 : ℝ) * I
def omegaBar : ℂ := (-1/2 : ℝ) - (Real.sqrt 3 / 2 : ℝ) * I

def c3Of (x y z : ℂ) : C3
  | 0 => x | 1 => y | _ => z

def tetraRay0 : C3 := c3Of 1 0 0
def tetraRay1 : C3 := c3Of tetraA tetraB 0
def tetraRay2 : C3 := c3Of tetraA (tetraB * omega) 0
def tetraRay3 : C3 := c3Of tetraA (tetraB * omegaBar) 0
def c3Neg (u : C3) : C3 := fun component => -u component

def tetraCorner (corner : CubeCorner) : C3 :=
  match corner.val with
  | 0 => tetraRay0 | 1 => tetraRay1
  | 2 => tetraRay2 | 3 => tetraRay3
  | 4 => c3Neg tetraRay3 | 5 => c3Neg tetraRay2
  | 6 => c3Neg tetraRay1 | _ => c3Neg tetraRay0

def overlap (u v : C3) : ℂ :=
  ⟨(∑ component : Fin 3,
      ((u component).re * (v component).re +
        (u component).im * (v component).im)),
    (∑ component : Fin 3,
      ((u component).re * (v component).im -
        (u component).im * (v component).re))⟩

def faceProduct (a b c d : CubeCorner) : ℂ :=
  overlap (tetraCorner a) (tetraCorner b) *
    overlap (tetraCorner b) (tetraCorner c) *
    overlap (tetraCorner c) (tetraCorner d) *
    overlap (tetraCorner d) (tetraCorner a)

theorem sqrt_three_ne_zero : Real.sqrt 3 ≠ 0 := by positivity
theorem sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
theorem sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
theorem sqrt_three_pow_four : (Real.sqrt 3) ^ 4 = 9 := by
  calc
    (Real.sqrt 3) ^ 4 = ((Real.sqrt 3) ^ 2) ^ 2 := by ring
    _ = 9 := by rw [sqrt_three_sq]; norm_num
theorem sqrt_three_pow_five : (Real.sqrt 3) ^ 5 = 9 * Real.sqrt 3 := by
  calc
    (Real.sqrt 3) ^ 5 = (Real.sqrt 3) ^ 4 * Real.sqrt 3 := by ring
    _ = 9 * Real.sqrt 3 := by rw [sqrt_three_pow_four]
theorem sqrt_three_pow_six : (Real.sqrt 3) ^ 6 = 27 := by
  calc
    (Real.sqrt 3) ^ 6 = ((Real.sqrt 3) ^ 2) ^ 3 := by ring
    _ = 27 := by rw [sqrt_three_sq]; norm_num
theorem sqrt_three_pow_eight : (Real.sqrt 3) ^ 8 = 81 := by
  calc
    (Real.sqrt 3) ^ 8 = ((Real.sqrt 3) ^ 4) ^ 2 := by ring
    _ = 81 := by rw [sqrt_three_pow_four]; norm_num
theorem sqrt_two_pow_four : (Real.sqrt 2) ^ 4 = 4 := by
  calc
    (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
    _ = 4 := by rw [sqrt_two_sq]; norm_num

theorem tetra_corner_density_one (corner : CubeCorner) :
    density (tetraCorner corner) = 1 := by
  fin_cases corner <;>
    simp [density, Fin.sum_univ_succ, tetraCorner, tetraRay0,
      tetraRay1, tetraRay2, tetraRay3, c3Of, c3Neg, omega, omegaBar,
      tetraA, tetraB, Complex.normSq] <;>
    field_simp [sqrt_three_ne_zero] <;> ring_nf <;>
    nlinarith [sqrt_three_sq, sqrt_two_sq, sqrt_three_pow_four,
      sqrt_three_pow_five, sqrt_three_pow_six, sqrt_three_pow_eight,
      sqrt_two_pow_four]

theorem overlap_eq_sum (u v : C3) :
    overlap u v = ∑ component, star (u component) * v component := by
  apply Complex.ext
  · simp [overlap, Complex.re_sum, Complex.mul_re]
  · simp only [overlap, Complex.im_sum, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem overlap_neg_left (u v : C3) : overlap (c3Neg u) v = -overlap u v := by
  simp [overlap_eq_sum, c3Neg, Finset.sum_neg_distrib]

theorem overlap_neg_right (u v : C3) : overlap u (c3Neg v) = -overlap u v := by
  simp [overlap_eq_sum, c3Neg, Finset.sum_neg_distrib]

theorem overlap_swap (u v : C3) : overlap v u = star (overlap u v) := by
  simp [overlap_eq_sum, star_sum, mul_comm]

theorem tetraA_sq : tetraA ^ 2 = 1 / 3 := by
  rw [tetraA, div_pow, sqrt_three_sq]
  norm_num

theorem tetraA_pow_four : tetraA ^ 4 = 1 / 9 := by
  rw [show tetraA ^ 4 = (tetraA ^ 2) ^ 2 by ring, tetraA_sq]
  norm_num

/-- Every pair of distinct tetrahedral rays has overlap `tetraA` times a fourth root
of unity. -/
theorem overlap_tetra_rays :
    overlap tetraRay0 tetraRay1 = (tetraA : ℂ) ∧
    overlap tetraRay0 tetraRay2 = (tetraA : ℂ) ∧
    overlap tetraRay0 tetraRay3 = (tetraA : ℂ) ∧
    overlap tetraRay1 tetraRay2 = (tetraA : ℂ) * I ∧
    overlap tetraRay1 tetraRay3 = -((tetraA : ℂ) * I) ∧
    overlap tetraRay2 tetraRay3 = (tetraA : ℂ) * I := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply Complex.ext <;>
    simp [overlap, Fin.sum_univ_succ, tetraRay0, tetraRay1, tetraRay2, tetraRay3,
      c3Of, omega, omegaBar, tetraA, tetraB] <;>
    field_simp [sqrt_three_ne_zero] <;> ring_nf <;>
    nlinarith [sqrt_three_sq, sqrt_two_sq, sqrt_three_pow_four]

theorem tetra_corner_values :
    tetraCorner 0 = tetraRay0 ∧ tetraCorner 1 = tetraRay1 ∧
    tetraCorner 2 = tetraRay2 ∧ tetraCorner 3 = tetraRay3 ∧
    tetraCorner 4 = c3Neg tetraRay3 ∧ tetraCorner 5 = c3Neg tetraRay2 ∧
    tetraCorner 6 = c3Neg tetraRay1 ∧ tetraCorner 7 = c3Neg tetraRay0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem all_face_products_negative :
    faceProduct 0 2 3 1 = (-1/9 : ℂ) ∧
    faceProduct 4 6 7 5 = (-1/9 : ℂ) ∧
    faceProduct 0 4 5 1 = (-1/9 : ℂ) ∧
    faceProduct 2 6 7 3 = (-1/9 : ℂ) ∧
    faceProduct 0 4 6 2 = (-1/9 : ℂ) ∧
    faceProduct 1 5 7 3 = (-1/9 : ℂ) := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := overlap_tetra_rays
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := tetra_corner_values
  have h4 : ((tetraA : ℂ)) ^ 4 = 1 / 9 := by
    rw [← Complex.ofReal_pow, tetraA_pow_four]
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [faceProduct, c0, c1, c2, c3, c4, c5, c6, c7, overlap_neg_left,
      overlap_neg_right] <;>
    simp only [overlap_swap tetraRay0 tetraRay1, overlap_swap tetraRay0 tetraRay2,
      overlap_swap tetraRay1 tetraRay2,
      overlap_swap tetraRay1 tetraRay3, overlap_swap tetraRay2 tetraRay3,
      h01, h02, h03, h12, h13, h23, star_neg, star_mul', Complex.star_def,
      Complex.conj_ofReal, Complex.conj_I] <;>
    linear_combination (tetraA : ℂ) ^ 4 * Complex.I_sq - h4

end
end LeanDirac
