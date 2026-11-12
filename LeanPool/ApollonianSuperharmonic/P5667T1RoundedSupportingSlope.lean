/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.LatticeQuadraticForm
public import Mathlib.LinearAlgebra.Matrix.PosDef

-- [TABLET NODE: P5667T1RoundedSupportingSlope]

/-!
# P5667T1RoundedSupportingSlope

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5667T1RoundedSupportingSlope
    (A : Matrix (Fin 2) (Fin 2) Real) (hA : A.IsSymm)
    (hpsd : A.PosSemidef) (x : GaussianInt) :
    ∃ p : GaussianInt, ∀ y : GaussianInt,
      Int.ceil (LatticeQuadraticForm A x -
        ((abs x.re + abs x.im : Int) : Real) - 1 -
        p.re * x.re - p.im * x.im) ≤
      Int.floor (LatticeQuadraticForm A y +
          ((abs y.re + abs y.im : Int) : Real)) -
          p.re * y.re - p.im * y.im := by
-- BODY
  have q_nonneg : ∀ z, 0 ≤ LatticeQuadraticForm A z := by
    intro z
    have hz := hpsd.dotProduct_mulVec_nonneg
      (![ (z.re : Real), (z.im : Real) ] : Fin 2 → Real)
    simpa [LatticeQuadraticForm, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      using hz
  let vx : Fin 2 → Real := ![(x.re : Real), (x.im : Real)]
  let ax : Fin 2 → Real := Matrix.mulVec A vx
  let p : GaussianInt :=
    ⟨Int.floor (ax 0 + (1 / 2 : Real)),
      Int.floor (ax 1 + (1 / 2 : Real))⟩
  have round0 : |(p.re : Real) - ax 0| ≤ (1 / 2 : Real) := by
    dsimp [p]
    have h₁ := Int.floor_le (ax 0 + (1 / 2 : Real))
    have h₂ := Int.lt_floor_add_one (ax 0 + (1 / 2 : Real))
    rw [abs_le]
    constructor <;> linarith
  have round1 : |(p.im : Real) - ax 1| ≤ (1 / 2 : Real) := by
    dsimp [p]
    have h₁ := Int.floor_le (ax 1 + (1 / 2 : Real))
    have h₂ := Int.lt_floor_add_one (ax 1 + (1 / 2 : Real))
    rw [abs_le]
    constructor <;> linarith
  have qconvex : ∀ y : GaussianInt,
      LatticeQuadraticForm A x +
          (Matrix.mulVec A vx) 0 * ((y.re : Real) - x.re) +
          (Matrix.mulVec A vx) 1 * ((y.im : Real) - x.im) ≤
        LatticeQuadraticForm A y := by
    intro y
    have hy := q_nonneg (y - x)
    have hs : A 0 1 = A 1 0 := by
      exact (congrFun (congrFun hA.eq 0) 1).symm
    dsimp [LatticeQuadraticForm, vx] at hy ⊢
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hs] at hy ⊢
    nlinarith
  have lower_energy : ∀ y,
      Int.ceil (LatticeQuadraticForm A x -
        ((abs x.re + abs x.im : Int) : Real) - 1 -
        p.re * x.re - p.im * x.im) ≤
      Int.floor (LatticeQuadraticForm A y +
          ((abs y.re + abs y.im : Int) : Real)) -
          p.re * y.re - p.im * y.im := by
    intro y
    have hfloor := (Int.sub_one_lt_floor (LatticeQuadraticForm A y +
      ((abs y.re + abs y.im : Int) : Real))).le
    have hconv := qconvex y
    have hconv0 := hconv
    have hi : Int.ceil (LatticeQuadraticForm A x -
        ((abs x.re + abs x.im : Int) : Real) - 1 -
        p.re * x.re - p.im * x.im) ≤
        Int.floor (LatticeQuadraticForm A y +
          ((abs y.re + abs y.im : Int) : Real)) -
          p.re * y.re - p.im * y.im := by
      rw [Int.ceil_le]
      have hxi : (0 : Real) ≤ abs (x.re : Real) := abs_nonneg _
      have hyi : (0 : Real) ≤ abs (y.re : Real) := abs_nonneg _
      have hxm : (0 : Real) ≤ abs (x.im : Real) := abs_nonneg _
      have hym : (0 : Real) ≤ abs (y.im : Real) := abs_nonneg _
      have h0 : |((p.re : Real) - (Matrix.mulVec A vx) 0) * ((x.re : Real) - y.re)| ≤
          (1 / 2 : Real) * (abs x.re + abs y.re) := by
        have := mul_le_mul_of_nonneg_right round0 (abs_nonneg ((x.re : Real) - y.re))
        have ht : |(x.re : Real) - y.re| ≤ abs x.re + abs y.re := by
          have ht' := abs_sub_le (x.re : Real) 0 (y.re : Real)
          norm_num [Int.cast_abs, abs_sub_comm, add_comm] at ht' ⊢
          exact ht'
        have h0a : |(p.re : Real) - ax 0| * |(x.re : Real) - y.re| ≤
            (1 / 2 : Real) * (abs x.re + abs y.re) := by
          nlinarith [this]
        simpa [ax] using h0a
      have h1 : |((p.im : Real) - (Matrix.mulVec A vx) 1) * ((x.im : Real) - y.im)| ≤
          (1 / 2 : Real) * (abs x.im + abs y.im) := by
        have := mul_le_mul_of_nonneg_right round1 (abs_nonneg ((x.im : Real) - y.im))
        have ht : |(x.im : Real) - y.im| ≤ abs x.im + abs y.im := by
          have ht' := abs_sub_le (x.im : Real) 0 (y.im : Real)
          norm_num [Int.cast_abs, abs_sub_comm, add_comm] at ht' ⊢
          exact ht'
        have h1a : |(p.im : Real) - ax 1| * |(x.im : Real) - y.im| ≤
            (1 / 2 : Real) * (abs x.im + abs y.im) := by
          nlinarith [this]
        simpa [ax] using h1a
      have hxa : (0 : Real) ≤ (abs x.re + abs x.im : Int) := by
        exact_mod_cast (add_nonneg (abs_nonneg x.re) (abs_nonneg x.im))
      have hya : (0 : Real) ≤ (abs y.re + abs y.im : Int) := by
        exact_mod_cast (add_nonneg (abs_nonneg y.re) (abs_nonneg y.im))
      have herr : -(
          |((p.re : Real) - (Matrix.mulVec A vx) 0) * ((x.re : Real) - y.re)| +
          |((p.im : Real) - (Matrix.mulVec A vx) 1) * ((x.im : Real) - y.im)|) ≤
          ((p.re : Real) - (Matrix.mulVec A vx) 0) * ((x.re : Real) - y.re) +
          ((p.im : Real) - (Matrix.mulVec A vx) 1) * ((x.im : Real) - y.im) := by
        have habs := abs_add_le
          (((p.re : Real) - (Matrix.mulVec A vx) 0) * ((x.re : Real) - y.re))
          (((p.im : Real) - (Matrix.mulVec A vx) 1) * ((x.im : Real) - y.im))
        have hnon := neg_le_of_abs_le habs
        linarith
      norm_num [Int.cast_sub, Int.cast_mul] at hconv ⊢
      simp only [GaussianInt.toComplex_def] at hconv hfloor ⊢
      norm_num at hconv hfloor ⊢
      try ring_nf at hconv hfloor ⊢
      have hab :
          |((p.re : Real) - (Matrix.mulVec A vx) 0) * ((x.re : Real) - y.re)| +
          |((p.im : Real) - (Matrix.mulVec A vx) 1) * ((x.im : Real) - y.im)| ≤
          (1 / 2 : Real) * (abs x.re + abs x.im + abs y.re + abs y.im) := by
        calc
          _ ≤ (1 / 2 : Real) * (abs x.re + abs y.re) +
              (1 / 2 : Real) * (abs x.im + abs y.im) := add_le_add h0 h1
          _ = _ := by ring
      norm_num [Complex.mul_re, Complex.mul_im] at hconv hfloor ⊢
      try ring_nf at hconv hfloor ⊢
      rw [← GaussianInt.intCast_re y, ← GaussianInt.intCast_im y] at hfloor hconv ⊢
      rw [← GaussianInt.intCast_re x, ← GaussianInt.intCast_im x] at hconv ⊢
      rw [← GaussianInt.intCast_re p, ← GaussianInt.intCast_im p] at ⊢
      try ring_nf at hconv ⊢
      have hmain : LatticeQuadraticForm A x ≤
          LatticeQuadraticForm A y +
            (p.re : Real) * ((x.re : Real) - y.re) +
            (p.im : Real) * ((x.im : Real) - y.im) +
            (|((p.re : Real) - (Matrix.mulVec A vx) 0) *
                ((x.re : Real) - y.re)| +
              |((p.im : Real) - (Matrix.mulVec A vx) 1) *
                ((x.im : Real) - y.im)|) := by
        calc
          LatticeQuadraticForm A x ≤
              LatticeQuadraticForm A y +
                (Matrix.mulVec A vx) 0 * ((x.re : Real) - y.re) +
                (Matrix.mulVec A vx) 1 * ((x.im : Real) - y.im) := by
            linarith [hconv]
          _ = LatticeQuadraticForm A y +
                (p.re : Real) * ((x.re : Real) - y.re) +
                (p.im : Real) * ((x.im : Real) - y.im) -
                (((p.re : Real) - (Matrix.mulVec A vx) 0) *
                  ((x.re : Real) - y.re) +
                 ((p.im : Real) - (Matrix.mulVec A vx) 1) *
                  ((x.im : Real) - y.im)) := by ring
          _ ≤ _ := by linarith [herr]
      rw [Int.cast_abs, Int.cast_abs, Int.cast_abs, Int.cast_abs] at hab
      have hsum :
          |((p.re : Real) - (Matrix.mulVec A vx) 0) *
              ((x.re : Real) - y.re)| +
            |((p.im : Real) - (Matrix.mulVec A vx) 1) *
              ((x.im : Real) - y.im)| ≤
          |(x.re : Real)| + |(x.im : Real)| +
            |(y.re : Real)| + |(y.im : Real)| := by
        nlinarith [hab, hxi, hyi, hxm, hym]
      have hfinal : LatticeQuadraticForm A x ≤
          1 + (Int.floor (LatticeQuadraticForm A y +
            |(y.re : Real)| + |(y.im : Real)|) : Real) +
            (p.re : Real) * ((x.re : Real) - y.re) +
            (p.im : Real) * ((x.im : Real) - y.im) +
            |(x.re : Real)| + |(x.im : Real)| := by
        nlinarith [hmain, hfloor, hsum]
      have polynomial_eq :
          1 + (Int.floor (LatticeQuadraticForm A y +
            |(y.re : Real)| + |(y.im : Real)|) : Real) +
              (p.re : Real) * ((x.re : Real) - y.re) +
              (p.im : Real) * ((x.im : Real) - y.im) +
              |(x.re : Real)| + |(x.im : Real)| =
          1 - (y.re : Real) * p.re + (x.re : Real) * p.re -
            (y.im : Real) * p.im + (x.im : Real) * p.im +
              (Int.floor (LatticeQuadraticForm A y +
                |(y.re : Real)| + |(y.im : Real)|) : Real) +
              |(x.re : Real)| + |(x.im : Real)| := by ring
      rw [polynomial_eq] at hfinal
      exact hfinal
    exact_mod_cast hi
  exact ⟨p, lower_energy⟩

end ApollonianSuperharmonic

end
