/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityDefinitions
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Flux bounds for the vorticity energy estimate

The antisymmetric transport flux is controlled by the Euclidean sizes of the
velocity and vorticity. These pointwise bounds are the algebraic input to
`lem:localized-vorticity-energy`.
-/

public section


open scoped BigOperators
open CKN.Foundation.Parabolic

namespace ESS

/-- Each coordinate of the antisymmetric vorticity flux is bounded by the
product of the Euclidean sizes of its two vector arguments. -/
theorem vorticityFlux_component_abs_le (v z : Vec3) (j i : Fin 3) :
    |v j * z i - z j * v i| ≤ 2 * vec3EuclideanNorm v * vec3EuclideanNorm z := by
  have hvj := abs_apply_le_vec3EuclideanNorm v j
  have hzi := abs_apply_le_vec3EuclideanNorm z i
  have hzj := abs_apply_le_vec3EuclideanNorm z j
  have hvi := abs_apply_le_vec3EuclideanNorm v i
  have hvn := vec3EuclideanNorm_nonneg v
  have hzn := vec3EuclideanNorm_nonneg z
  calc
    |v j * z i - z j * v i| ≤ |v j * z i| + |z j * v i| := abs_sub _ _
    _ = |v j| * |z i| + |z j| * |v i| := by rw [abs_mul, abs_mul]
    _ ≤ vec3EuclideanNorm v * vec3EuclideanNorm z +
          vec3EuclideanNorm z * vec3EuclideanNorm v := by
      exact add_le_add
        (mul_le_mul hvj hzi (abs_nonneg _) hvn)
        (mul_le_mul hzj hvi (abs_nonneg _) hzn)
    _ = 2 * vec3EuclideanNorm v * vec3EuclideanNorm z := by ring

/-- Pairing the flux with a matrix is bounded by the coordinatewise gradient
size. -/
theorem vorticityFlux_pairing_abs_le (v z : Vec3) (G : Fin 3 → Fin 3 → ℝ) :
    |∑ j : Fin 3, ∑ i : Fin 3,
      (v j * z i - z j * v i) * G i j| ≤
        (2 * vec3EuclideanNorm v * vec3EuclideanNorm z) *
          ∑ j : Fin 3, ∑ i : Fin 3, |G i j| := by
  let C : ℝ := 2 * vec3EuclideanNorm v * vec3EuclideanNorm z
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num) (vec3EuclideanNorm_nonneg v))
      (vec3EuclideanNorm_nonneg z)
  calc
    |∑ j : Fin 3, ∑ i : Fin 3,
        (v j * z i - z j * v i) * G i j| ≤
        ∑ j : Fin 3, |∑ i : Fin 3,
          (v j * z i - z j * v i) * G i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, ∑ i : Fin 3,
          |(v j * z i - z j * v i) * G i j| := by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, ∑ i : Fin 3, C * |G i j| := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      dsimp [C]
      exact mul_le_mul_of_nonneg_right
        (vorticityFlux_component_abs_le v z j i) (abs_nonneg _)
    _ = C * ∑ j : Fin 3, ∑ i : Fin 3, |G i j| := by
      dsimp [C]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]

/-- The flux pairing has the L² gradient bound used in the vorticity energy
estimate. -/
theorem vorticityFlux_pairing_l2_abs_le (v z : Vec3) (G : Fin 3 → Fin 3 → ℝ) :
    |∑ j : Fin 3, ∑ i : Fin 3,
      (v j * z i - z j * v i) * G i j| ≤
        (6 * vec3EuclideanNorm v * vec3EuclideanNorm z) *
          Real.sqrt (∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2) := by
  have hsum :
      ∑ j : Fin 3, ∑ i : Fin 3, |G i j| ≤
        3 * Real.sqrt (∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2) := by
    let A : Finset (Fin 3 × Fin 3) := Finset.univ
    have hcs := sq_sum_le_card_mul_sum_sq (s := A)
      (f := fun p : Fin 3 × Fin 3 => |G p.2 p.1|)
    have hsumProduct (f : Fin 3 × Fin 3 → ℝ) :
        (∑ p : Fin 3 × Fin 3, f p) =
          ∑ j : Fin 3, ∑ i : Fin 3, f (j, i) :=
      Fintype.sum_prod_type f
    have hsumEq :
        (∑ p : Fin 3 × Fin 3, |G p.2 p.1|) =
          ∑ j : Fin 3, ∑ i : Fin 3, |G i j| := hsumProduct _
    have hsumSqEq :
        (∑ p : Fin 3 × Fin 3, |G p.2 p.1| ^ 2) =
          ∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2 := by
      calc
        _ = ∑ p : Fin 3 × Fin 3, (G p.2 p.1) ^ 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact sq_abs _
        _ = _ := hsumProduct _
    have hcard : (A.card : ℝ) = 9 := by simp [A]
    have hsq :
        (∑ j : Fin 3, ∑ i : Fin 3, |G i j|) ^ 2 ≤
          9 * (∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2) := by
      rw [← hsumEq, ← hsumSqEq, ← hcard]
      simpa [A] using hcs
    have hsumNonneg : 0 ≤ ∑ j : Fin 3, ∑ i : Fin 3, |G i j| :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => abs_nonneg _
    have hsqNonneg : 0 ≤ ∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2 :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _
    have hroot : 0 ≤ Real.sqrt (∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2) :=
      Real.sqrt_nonneg _
    apply (sq_le_sq₀ hsumNonneg (mul_nonneg (by norm_num) hroot)).mp
    rw [mul_pow, Real.sq_sqrt hsqNonneg]
    nlinarith only [hsq]
  have hC : 0 ≤ 2 * vec3EuclideanNorm v * vec3EuclideanNorm z := by
    exact mul_nonneg (mul_nonneg (by norm_num) (vec3EuclideanNorm_nonneg v))
      (vec3EuclideanNorm_nonneg z)
  calc
    |∑ j : Fin 3, ∑ i : Fin 3,
        (v j * z i - z j * v i) * G i j| ≤
        (2 * vec3EuclideanNorm v * vec3EuclideanNorm z) *
          ∑ j : Fin 3, ∑ i : Fin 3, |G i j| :=
      vorticityFlux_pairing_abs_le v z G
    _ ≤ (2 * vec3EuclideanNorm v * vec3EuclideanNorm z) *
        (3 * Real.sqrt (∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum hC
    _ = (6 * vec3EuclideanNorm v * vec3EuclideanNorm z) *
        Real.sqrt (∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2) := by ring

/-- Cauchy--Schwarz for the matrix forcing term in the weak vorticity energy
identity. -/
theorem vorticityMatrixPairing_abs_le (F G : Fin 3 → Fin 3 → ℝ) :
    |∑ j : Fin 3, ∑ i : Fin 3, F j i * G i j| ≤
      Real.sqrt (∑ j : Fin 3, ∑ i : Fin 3, (F j i) ^ 2) *
        Real.sqrt (∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2) := by
  let f : Fin 3 × Fin 3 → ℝ := fun p => F p.1 p.2
  let g : Fin 3 × Fin 3 → ℝ := fun p => G p.2 p.1
  let A : Finset (Fin 3 × Fin 3) := Finset.univ
  have hpairFlat :
      (∑ p : Fin 3 × Fin 3, f p * g p) =
        ∑ j : Fin 3, ∑ i : Fin 3, F j i * G i j := by
    simp [f, g, Fintype.sum_prod_type]
  have hFflat :
      (∑ p : Fin 3 × Fin 3, (f p) ^ 2) =
        ∑ j : Fin 3, ∑ i : Fin 3, (F j i) ^ 2 := by
    simp [f, Fintype.sum_prod_type]
  have hGflat :
      (∑ p : Fin 3 × Fin 3, (g p) ^ 2) =
        ∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2 := by
    simp [g, Fintype.sum_prod_type]
  have hcs :
      (∑ p : Fin 3 × Fin 3, f p * g p) ^ 2 ≤
        (∑ p : Fin 3 × Fin 3, (f p) ^ 2) *
          (∑ p : Fin 3 × Fin 3, (g p) ^ 2) := by
    simpa [A] using Finset.sum_mul_sq_le_sq_mul_sq A f g
  have hFnonneg : 0 ≤ ∑ j : Fin 3, ∑ i : Fin 3, (F j i) ^ 2 :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hGnonneg : 0 ≤ ∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2 :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hrootF : 0 ≤ Real.sqrt (∑ j : Fin 3, ∑ i : Fin 3, (F j i) ^ 2) :=
    Real.sqrt_nonneg _
  have hrootG : 0 ≤ Real.sqrt (∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2) :=
    Real.sqrt_nonneg _
  have hrootSq :
      (Real.sqrt (∑ j : Fin 3, ∑ i : Fin 3, (F j i) ^ 2) *
        Real.sqrt (∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2)) ^ 2 =
          (∑ j : Fin 3, ∑ i : Fin 3, (F j i) ^ 2) *
            (∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hFnonneg, Real.sq_sqrt hGnonneg]
  have hcs' :
      (∑ j : Fin 3, ∑ i : Fin 3, F j i * G i j) ^ 2 ≤
        (∑ j : Fin 3, ∑ i : Fin 3, (F j i) ^ 2) *
          (∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2) := by
    rw [← hpairFlat, ← hFflat, ← hGflat]
    exact hcs
  have hsqAbs :
      |∑ j : Fin 3, ∑ i : Fin 3, F j i * G i j| ^ 2 ≤
        (Real.sqrt (∑ j : Fin 3, ∑ i : Fin 3, (F j i) ^ 2) *
          Real.sqrt (∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2)) ^ 2 := by
    rw [sq_abs, hrootSq]
    exact hcs'
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hrootF hrootG)).mp hsqAbs

/-- The transport and matrix terms use at most half of the gradient
dissipation after choosing the Young parameters needed for the smooth energy
estimate in `lem:localized-vorticity-energy`. -/
theorem vorticityFluxAndMatrixPairing_halfDissipation (M : ℝ)
    (v z : Vec3) (F G : Fin 3 → Fin 3 → ℝ)
    (hM : 0 ≤ M) (hv : vec3EuclideanNorm v ≤ M) :
    |∑ j : Fin 3, ∑ i : Fin 3,
      (v j * z i - z j * v i) * G i j| +
      |∑ j : Fin 3, ∑ i : Fin 3, F j i * G i j| ≤
      (1 / 2 : ℝ) * (∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2) +
        36 * M ^ 2 * (vec3EuclideanNorm z) ^ 2 +
        ∑ j : Fin 3, ∑ i : Fin 3, (F j i) ^ 2 := by
  let D : ℝ := ∑ j : Fin 3, ∑ i : Fin 3, (G i j) ^ 2
  let P : ℝ := ∑ j : Fin 3, ∑ i : Fin 3, (F j i) ^ 2
  let X : ℝ := M * vec3EuclideanNorm z
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hP : 0 ≤ P := by
    dsimp [P]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hX : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg hM (vec3EuclideanNorm_nonneg z)
  have hrootD : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hrootDsquare : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD
  have hfluxBase :
      |∑ j : Fin 3, ∑ i : Fin 3,
        (v j * z i - z j * v i) * G i j| ≤
        6 * M * vec3EuclideanNorm z * Real.sqrt D := by
    calc
      _ ≤ 6 * vec3EuclideanNorm v * vec3EuclideanNorm z * Real.sqrt D := by
        simpa [D, mul_assoc] using vorticityFlux_pairing_l2_abs_le v z G
      _ ≤ 6 * M * vec3EuclideanNorm z * Real.sqrt D := by
        have hnorm : 0 ≤ vec3EuclideanNorm z := vec3EuclideanNorm_nonneg z
        calc
          _ = 6 * (vec3EuclideanNorm v * vec3EuclideanNorm z * Real.sqrt D) := by ring
          _ ≤ 6 * (M * vec3EuclideanNorm z * Real.sqrt D) := by
            gcongr
          _ = _ := by ring
  have hfluxYoung :
      6 * M * vec3EuclideanNorm z * Real.sqrt D ≤
        (1 / 4 : ℝ) * D + 36 * M ^ 2 * (vec3EuclideanNorm z) ^ 2 := by
    have hsquare := sq_nonneg (Real.sqrt D - 12 * X)
    have hproduct : 6 * M * vec3EuclideanNorm z * Real.sqrt D =
        6 * X * Real.sqrt D := by
      dsimp [X]
      ring
    have hquadratic : 36 * M ^ 2 * (vec3EuclideanNorm z) ^ 2 = 36 * X ^ 2 := by
      dsimp [X]
      ring
    rw [hproduct, hquadratic]
    nlinarith only [hsquare, hrootDsquare]
  have hmatrixBase :
      |∑ j : Fin 3, ∑ i : Fin 3, F j i * G i j| ≤
        Real.sqrt P * Real.sqrt D := by
    simpa [P, D] using vorticityMatrixPairing_abs_le F G
  have hrootP : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
  have hrootPsquare : (Real.sqrt P) ^ 2 = P := Real.sq_sqrt hP
  have hmatrixYoung :
      Real.sqrt P * Real.sqrt D ≤ (1 / 4 : ℝ) * D + P := by
    have hsquare := sq_nonneg (Real.sqrt D / 2 - Real.sqrt P)
    nlinarith only [hsquare, hrootDsquare, hrootPsquare]
  have hsum := add_le_add (hfluxBase.trans hfluxYoung)
    (hmatrixBase.trans hmatrixYoung)
  dsimp [D, P] at hsum ⊢
  linarith only [hsum]

/-- A finite-dimensional Cauchy--Young bound for the zero-order forcing in
the smooth vorticity energy calculation. -/
theorem vorticityVectorPairing_young (g z : Vec3) :
    |∑ i : Fin 3, g i * z i| ≤
      (1 / 2 : ℝ) * (∑ i : Fin 3, (g i) ^ 2) +
        (1 / 2 : ℝ) * (∑ i : Fin 3, (z i) ^ 2) := by
  calc
    |∑ i : Fin 3, g i * z i| ≤ ∑ i : Fin 3, |g i * z i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3,
        ((1 / 2 : ℝ) * (g i) ^ 2 + (1 / 2 : ℝ) * (z i) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hsquare := sq_nonneg (|g i| - |z i|)
      have hg : |g i| ^ 2 = (g i) ^ 2 := sq_abs _
      have hz : |z i| ^ 2 = (z i) ^ 2 := sq_abs _
      rw [abs_mul]
      nlinarith only [hsquare, hg, hz]
    _ = (1 / 2 : ℝ) * (∑ i : Fin 3, (g i) ^ 2) +
        (1 / 2 : ℝ) * (∑ i : Fin 3, (z i) ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end ESS
