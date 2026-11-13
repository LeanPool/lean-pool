/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Positivity

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.PosDef

-- [TABLET NODE: P5630T1SymmetricMatrixPositivityCriterion]

/-!
# P5630T1SymmetricMatrixPositivityCriterion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5630T1SymmetricMatrixPositivityCriterion (s u v : Real) :
    ( (let M : Matrix (Fin 2) (Fin 2) Real := ![![s + u, v], ![v, s - u]]; M.PosSemidef) ↔
      Real.sqrt (u ^ 2 + v ^ 2) ≤ s) ∧
    ( (let M : Matrix (Fin 2) (Fin 2) Real := ![![s + u, v], ![v, s - u]]; M.PosDef) ↔
      Real.sqrt (u ^ 2 + v ^ 2) < s) := by
-- BODY
  let M : Matrix (Fin 2) (Fin 2) Real := ![![s + u, v], ![v, s - u]]
  have symmetric :
      M.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [M]
  have quadratic (a b : Real) :
      (let x : Fin 2 → Real := ![a, b]; dotProduct (fun i => x i) (M.mulVec x)) =
        (s * (a ^ 2 + b ^ 2) + u * (a ^ 2 - b ^ 2) + 2 * v * a * b) := by
    simp [M, Matrix.mulVec, dotProduct]
    ring
  constructor
  · constructor
    · intro h
      have hq (a b : Real) :
          0 ≤ s * (a ^ 2 + b ^ 2) + u * (a ^ 2 - b ^ 2) + 2 * v * a * b := by
        rw [← quadratic a b]
        simpa using (Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2 ![a, b]
      have hu := hq 1 0
      have hv := hq 0 1
      have hdet : 0 ≤ s ^ 2 - u ^ 2 - v ^ 2 := by
        by_cases hz : s + u = 0
        · have hp := hq 1 1
          have hm := hq 1 (-1)
          have huval : u = -s := by linarith [hz]
          rw [huval] at hp hm
          have hs0 : 0 ≤ s := by nlinarith [hv]
          have hzv := hq (2 * s) (-v)
          rw [huval] at hzv
          norm_num at hzv
          ring_nf at hzv
          have hsprod : s * v ^ 2 = 0 := by nlinarith [hzv]
          have hv0 : v = 0 := by
            have hprod : 0 ≤ s * v ^ 2 := mul_nonneg hs0 (sq_nonneg v)
            rcases eq_zero_or_eq_zero_of_mul_eq_zero hsprod with hs | hv
            · have hp' : 0 ≤ v := by nlinarith [hp]
              linarith
            · exact (sq_eq_zero_iff.mp hv)
          rw [hv0]
          nlinarith
        · have hp := hq v (-(s + u))
          have hsu : 0 ≤ s + u := by nlinarith
          have hsu' : 0 < s + u := lt_of_le_of_ne hsu (Ne.symm hz)
          nlinarith
      have hs : 0 ≤ s := by nlinarith
      have hsqrt : 0 ≤ Real.sqrt (u ^ 2 + v ^ 2) := Real.sqrt_nonneg _
      have hsquare : (Real.sqrt (u ^ 2 + v ^ 2)) ^ 2 = u ^ 2 + v ^ 2 :=
        Real.sq_sqrt (by positivity)
      nlinarith
    · intro h
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg symmetric ?_
      intro x
      have hx : x = ![x 0, x 1] := by
        funext i
        fin_cases i <;> rfl
      rw [hx]
      have hc :
          (u * ((x 0) ^ 2 - (x 1) ^ 2) + 2 * v * x 0 * x 1) ^ 2 ≤
            (u ^ 2 + v ^ 2) * ((x 0) ^ 2 + (x 1) ^ 2) ^ 2 := by
        nlinarith [sq_nonneg (v * ((x 0) ^ 2 - (x 1) ^ 2) -
          u * (2 * x 0 * x 1))]
      have hsquare : (Real.sqrt (u ^ 2 + v ^ 2)) ^ 2 = u ^ 2 + v ^ 2 :=
        Real.sq_sqrt (by positivity)
      have hsqrt : 0 ≤ Real.sqrt (u ^ 2 + v ^ 2) := Real.sqrt_nonneg _
      have hnorm : 0 ≤ (x 0) ^ 2 + (x 1) ^ 2 := by positivity
      have hprod : 0 ≤ (s - Real.sqrt (u ^ 2 + v ^ 2)) *
          ((x 0) ^ 2 + (x 1) ^ 2) :=
        mul_nonneg (sub_nonneg.mpr h) hnorm
      have hL : -(Real.sqrt (u ^ 2 + v ^ 2)) *
            ((x 0) ^ 2 + (x 1) ^ 2) ≤
          u * ((x 0) ^ 2 - (x 1) ^ 2) + 2 * v * x 0 * x 1 := by
        have hsq : (Real.sqrt (u ^ 2 + v ^ 2) *
            ((x 0) ^ 2 + (x 1) ^ 2)) ^ 2 =
            (u ^ 2 + v ^ 2) * ((x 0) ^ 2 + (x 1) ^ 2) ^ 2 := by
          rw [mul_pow, hsquare]
        by_contra hn
        have hlt := lt_of_not_ge hn
        have hrn : 0 ≤ Real.sqrt (u ^ 2 + v ^ 2) *
            ((x 0) ^ 2 + (x 1) ^ 2) := mul_nonneg hsqrt hnorm
        have hnl : 0 ≤ -(u * ((x 0) ^ 2 - (x 1) ^ 2) +
            2 * v * x 0 * x 1) := by linarith
        have hsq' : (Real.sqrt (u ^ 2 + v ^ 2) *
            ((x 0) ^ 2 + (x 1) ^ 2)) ^ 2 <
            (-(u * ((x 0) ^ 2 - (x 1) ^ 2) + 2 * v * x 0 * x 1)) ^ 2 := by
          apply (sq_lt_sq₀ hrn hnl).2
          linarith
        nlinarith [hsq, hsq']
      have hq : 0 ≤ s * ((x 0) ^ 2 + (x 1) ^ 2) +
          u * ((x 0) ^ 2 - (x 1) ^ 2) + 2 * v * x 0 * x 1 := by
        nlinarith [hprod]
      have hq' : 0 ≤ x 0 * ((s + u) * x 0 + v * x 1) +
          x 1 * (v * x 0 + (s - u) * x 1) := by
        nlinarith [hq]
      simpa [M, Matrix.mulVec, dotProduct, TrivialStar.star_trivial] using hq'
  · constructor
    · intro h
      have hq (a b : Real) (hne : (![a, b] : Fin 2 → Real) ≠ 0) :
          0 < s * (a ^ 2 + b ^ 2) + u * (a ^ 2 - b ^ 2) + 2 * v * a * b := by
        have hv := (Matrix.posDef_iff_dotProduct_mulVec.mp
          (by simpa [M] using h)).2 hne
        rw [← quadratic a b]
        simpa [TrivialStar.star_trivial] using hv
      have hp := hq 1 0 (by norm_num)
      have hsu : 0 < s + u := by nlinarith [hp]
      have hzv := hq v (-(s + u)) (by
        intro hz
        have hh := congrFun hz 1
        simp at hh
        nlinarith [hsu])
      have hdet : 0 < s ^ 2 - u ^ 2 - v ^ 2 := by
        nlinarith [hzv]
      have hs : 0 < s := by nlinarith [hp]
      have hsquare : (Real.sqrt (u ^ 2 + v ^ 2)) ^ 2 = u ^ 2 + v ^ 2 :=
        Real.sq_sqrt (by positivity)
      have hsqrt : 0 ≤ Real.sqrt (u ^ 2 + v ^ 2) := Real.sqrt_nonneg _
      nlinarith
    · intro h
      refine Matrix.PosDef.of_dotProduct_mulVec_pos symmetric ?_
      intro x hx
      have hcoord : x = ![x 0, x 1] := by
        funext i
        fin_cases i <;> rfl
      have hN : 0 < (x 0) ^ 2 + (x 1) ^ 2 := by
        rcases eq_or_ne (x 0) 0 with ha | ha
        · have hb : x 1 ≠ 0 := by
            intro hb
            apply hx
            rw [hcoord]
            funext i
            fin_cases i <;> simp [ha, hb]
          positivity
        · positivity
      have hsquare : (Real.sqrt (u ^ 2 + v ^ 2)) ^ 2 = u ^ 2 + v ^ 2 :=
        Real.sq_sqrt (by positivity)
      have hsqrt : 0 ≤ Real.sqrt (u ^ 2 + v ^ 2) := Real.sqrt_nonneg _
      have hprod : 0 < (s - Real.sqrt (u ^ 2 + v ^ 2)) *
          ((x 0) ^ 2 + (x 1) ^ 2) :=
        mul_pos (sub_pos.mpr h) hN
      have hc :
          (u * ((x 0) ^ 2 - (x 1) ^ 2) + 2 * v * x 0 * x 1) ^ 2 ≤
            (u ^ 2 + v ^ 2) * ((x 0) ^ 2 + (x 1) ^ 2) ^ 2 := by
        nlinarith [sq_nonneg (v * ((x 0) ^ 2 - (x 1) ^ 2) -
          u * (2 * x 0 * x 1))]
      have hL : -(Real.sqrt (u ^ 2 + v ^ 2)) *
            ((x 0) ^ 2 + (x 1) ^ 2) ≤
          u * ((x 0) ^ 2 - (x 1) ^ 2) + 2 * v * x 0 * x 1 := by
        have hsq : (Real.sqrt (u ^ 2 + v ^ 2) *
            ((x 0) ^ 2 + (x 1) ^ 2)) ^ 2 =
            (u ^ 2 + v ^ 2) * ((x 0) ^ 2 + (x 1) ^ 2) ^ 2 := by
          rw [mul_pow, hsquare]
        by_contra hn
        have hlt := lt_of_not_ge hn
        have hrn : 0 ≤ Real.sqrt (u ^ 2 + v ^ 2) *
            ((x 0) ^ 2 + (x 1) ^ 2) := mul_nonneg hsqrt (le_of_lt hN)
        have hnl : 0 ≤ -(u * ((x 0) ^ 2 - (x 1) ^ 2) +
            2 * v * x 0 * x 1) := by linarith
        have hsq' : (Real.sqrt (u ^ 2 + v ^ 2) *
            ((x 0) ^ 2 + (x 1) ^ 2)) ^ 2 <
            (-(u * ((x 0) ^ 2 - (x 1) ^ 2) + 2 * v * x 0 * x 1)) ^ 2 := by
          apply (sq_lt_sq₀ hrn hnl).2
          linarith
        nlinarith [hsq, hsq']
      have hq : 0 < s * ((x 0) ^ 2 + (x 1) ^ 2) +
          u * ((x 0) ^ 2 - (x 1) ^ 2) + 2 * v * x 0 * x 1 := by
        nlinarith [hprod]
      rw [hcoord]
      have hq' : 0 < x 0 * ((s + u) * x 0 + v * x 1) +
          x 1 * (v * x 0 + (s - u) * x 1) := by nlinarith [hq]
      simpa [M, Matrix.mulVec, dotProduct, TrivialStar.star_trivial] using hq'

end ApollonianSuperharmonic

end
