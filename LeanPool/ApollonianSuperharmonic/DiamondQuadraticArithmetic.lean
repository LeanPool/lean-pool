/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.DiamondParameter
public import LeanPool.ApollonianSuperharmonic.DiamondTile
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.IntegerLatticeFunction
public import Mathlib.Init
public import Mathlib.Tactic.LinearCombination


/-!
# DiamondQuadraticArithmetic

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace DiamondQuadraticArithmetic

/-- Shared triangularScale identity for DiamondQuadraticArithmetic. -/
theorem triangularScale :
    (by
      classical
      exact
         (∀ (a : ℤ), (2 : ℤ) * (a * (a - (1 : ℤ)) / (2 : ℤ)) = a * (a - (1 :
            ℤ))) ) := by
  classical
  intro a
  rcases Int.emod_two_eq_zero_or_one a with h | h
  · have ha : a = 2*(a/2) := by omega
    rw [ha]
    rw [show 2*(a/2)*(2*(a/2)-1) = 2*((a/2)*(2*(a/2)-1)) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num : (2:Int) ≠ 0)]
  · have ha : a = 2*(a/2)+1 := by omega
    rw [ha]
    rw [show (2*(a/2)+1)*(2*(a/2)+1-1) = 2*((2*(a/2)+1)*(a/2)) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num : (2:Int) ≠ 0)]

/-- Shared squareScale identity for DiamondQuadraticArithmetic. -/
theorem squareScale :
    (by
      classical
      exact
         (∀ (a : ℤ), (4 : ℤ) * (a ^ (2 : ℕ) / (4 : ℤ)) = a ^ (2 : ℕ) - a % (2
            : ℤ)) ) := by
  classical
  intro a
  rcases Int.emod_two_eq_zero_or_one a with h | h
  · have ha : a = 2*(a/2) := by omega
    have he : a^2 = 4*(a/2)^2 := by
      conv_lhs => rw [ha]
      ring
    rw [he, Int.mul_ediv_cancel_left _ (by norm_num : (4:Int) ≠ 0), h]
    ring
  · have ha : a = 2*(a/2)+1 := by omega
    have he : a^2 = 4*((a/2)^2+a/2)+1 := by
      conv_lhs => rw [ha]
      ring
    rw [he, h]
    omega

/-- Shared quadraticScale identity for DiamondQuadraticArithmetic. -/
theorem quadraticScale :
    (by
      classical
      exact
        let Q (a b : Int) : Int :=
          (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), 2*(a*(a-1)/2) = a*(a-1)) → ((∀ (a : Int), 4*(a^2/4) = a^2-a%2) → (∀ (a :
            ℤ), ∀ (b : ℤ), (4 : ℤ) * Q a b = S a b)) ) := by
  classical
  intro Q S tri square a b
  have ht := tri (Int.natAbs a : Int)
  have hs := square (a-b)
  have ha : (Int.natAbs a : Int)^2 = a^2 := by
    rw [Int.natCast_natAbs, sq_abs]
  dsimp [Q, S]
  rw [Int.natCast_natAbs] at ht ha ⊢
  nlinarith only [ht, hs, ha]

/-- Shared evenDifference identity for DiamondQuadraticArithmetic. -/
theorem evenDifference :
    (by
      classical
      exact
         (
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        ∀ (a : ℤ), ∀ (b : ℤ), ∀ (m : ℤ), a - b = (2 : ℤ) * m → S a b = (2 : ℤ) * a ^ (2 : ℕ) - (2
            : ℤ) * |a| - (4 : ℤ) * m ^ (2 : ℕ)) ) := by
  classical
  intro S a b m h
  dsimp [S]
  rw [h, show (2*m)%2 = 0 by omega]
  ring

/-- Shared oddDifference identity for DiamondQuadraticArithmetic. -/
theorem oddDifference :
    (by
      classical
      exact
         (
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        ∀ (a : ℤ), ∀ (b : ℤ), ∀ (m : ℤ), a - b = (2 : ℤ) * m + (1 : ℤ) → S a b = (2 : ℤ) * a ^ (2
            : ℕ) - (2 : ℤ) * |a| - (4 : ℤ) * m ^ (2 : ℕ) - (4 : ℤ) * m) ) := by
  classical
  intro S a b m h
  dsimp [S]
  rw [h, show (2*m+1)%2 = 1 by omega]
  ring

/-- Shared differenceScale identity for DiamondQuadraticArithmetic. -/
theorem differenceScale :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (f : IntegerLatticeFunction),
        let Q (a b : Int) : Int :=
          (Int.natAbs a : Int)*((Int.natAbs a : Int)-1)/2-(a-b)^2/4
        let S (a b : Int) : Int := 2*a^2-2*|a|-(a-b)^2+(a-b)%2
        (∀ (a : Int), ∀ (b : Int), 4*Q a b = S a b) → ((∀ (x : GaussianInt), (x ∈
            FootprintVertices (DiamondTile K.1)) → (f x = Q x.re x.im)) → (∀ (x : GaussianInt), ∀
            (y : GaussianInt), x ∈ FootprintVertices (DiamondTile K.1) → y ∈ FootprintVertices
            (DiamondTile K.1) → (4 : ℤ) * (f y - f x) = S y.re y.im - S x.re x.im)) ) := by
  classical
  intro K f Q S scale valC x y hx hy
  rw [valC x hx, valC y hy]
  linear_combination scale y.re y.im - scale x.re x.im

end DiamondQuadraticArithmetic
end ApollonianSuperharmonic

end
