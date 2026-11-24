/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.SupportFan
public import Mathlib.Data.Fin.VecNotation
import LeanPool.ConwaySoifer.Simplified.Geometry.CoreLocalPolynomials
import Mathlib.Tactic.Positivity.Finset

/-! Explicit real support fans for the handwritten geometric point set.
The polynomial decompositions are proved by `ring`; their signs by `positivity`.
Each cone carries one fixed triple on both endpoints. No Boolean checker is used. -/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

@[expose] public section

noncomputable section
namespace ConwaySoifer.Simplified

/-- The four-point configuration used by the adaptive central-core obstruction. -/
def adaptiveCoreLocalPoint (s : ℝ) : Fin 4 → Point :=
  ![(1, 0), (1, (-1 * s)), ((((-1 / 3) * (s ^ 2)) + ((1 / 3) * s)), (((-1 / 3) * (s ^ 2)) + ((1 / 3)
      * s))), ((1 + (-1 * s)), s)]

private theorem arithmeticBound0 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    0 < cross (1, 0) ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := CoreLocalPolynomials.polynomialPositive1 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross])

private theorem arithmeticBound1 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    len (1, 0) ≤ supportNum (1, 0) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg1 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg2 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound2 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    len ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) ≤
        supportNum ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg3 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg4 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound3 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    0 < cross ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s)))
        ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := CoreLocalPolynomials.polynomialPositive2 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound4 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    len ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) ≤
        supportNum ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg3 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg4 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound5 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    len ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) ≤
        supportNum ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg5 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg6 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound6 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    0 < cross ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2))))
        ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := CoreLocalPolynomials.polynomialPositive3 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound7 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    len ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) ≤
        supportNum ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg5 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg6 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound8 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    len ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) ≤
        supportNum ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s
        ^ 2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg7 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg8 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound9 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    0 < cross ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^
        2)))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := CoreLocalPolynomials.polynomialPositive4 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound10 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    len ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) ≤
        supportNum ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s
        ^ 2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s
        3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg9 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg10 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound11 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 4) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1)
        (adaptiveCoreLocalPoint s 3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg1 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg2 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound12 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    0 < cross (1, 0) ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := CoreLocalPolynomials.polynomialPositive5 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross])

private theorem arithmeticBound13 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    len (1, 0) ≤ supportNum (1, 0) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg11 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg12 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound14 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    len ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) ≤
        supportNum ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg13 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg14 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound15 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    0 < cross ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s)))
        ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := CoreLocalPolynomials.polynomialPositive6 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound16 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    len ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) ≤
        supportNum ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg13 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg14 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound17 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    len ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) ≤
        supportNum ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg15 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg16 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound18 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    0 < cross ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2))))
        ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := CoreLocalPolynomials.polynomialPositive7 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound19 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    len ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) ≤
        supportNum ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg15 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg16 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound20 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    len ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) ≤
        supportNum ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s
        ^ 2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg17 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg18 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound21 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    0 < cross ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^
        2)))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := CoreLocalPolynomials.polynomialPositive8 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound22 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    len ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) ≤
        supportNum ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s
        ^ 2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s
        3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg19 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg20 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound23 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (3 / 8) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1)
        (adaptiveCoreLocalPoint s 3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg11 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg12 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound24 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    0 < cross (1, 0) ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := CoreLocalPolynomials.polynomialPositive9 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross])

private theorem arithmeticBound25 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    len (1, 0) ≤ supportNum (1, 0) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg21 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg22 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound26 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    len ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) ≤
        supportNum ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg23 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg24 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound27 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    0 < cross ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s)))
        ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := CoreLocalPolynomials.polynomialPositive10 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound28 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    len ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) * s))) ≤
        supportNum ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 / 3) *
        s))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg23 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg24 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound29 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    len ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) ≤
        supportNum ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg25 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg26 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound30 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    0 < cross ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2))))
        ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) :=
        by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := CoreLocalPolynomials.polynomialPositive11 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound31 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    len ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) ≤
        supportNum ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg25 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg26 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound32 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    len ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) ≤
        supportNum ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s
        ^ 2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s
        0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg27 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg28 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound33 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    0 < cross ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^
        2)))) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := CoreLocalPolynomials.polynomialPositive12 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound34 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    len ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))) ≤
        supportNum ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s
        ^ 2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s
        3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg29 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg30 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound35 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (3 / 8) ∧ 0 ≤ (7 / 16) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1)
        (adaptiveCoreLocalPoint s 3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg21 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg22 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound36 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    0 < cross (1, 0) ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := CoreLocalPolynomials.polynomialPositive13 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross])

private theorem arithmeticBound37 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    len (1, 0) ≤ supportNum (1, 0) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg31 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg32 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound38 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    len ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) ≤
        supportNum ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) (adaptiveCoreLocalPoint s 3) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg33 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg34 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound39 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    0 < cross ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2))))
        ((-1 * s), (2 * s)) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := CoreLocalPolynomials.polynomialPositive14 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound40 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    len ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^ 2)))) ≤
        supportNum ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0)
        := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg35 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg36 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound41 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    len ((-1 * s), (2 * s)) ≤ supportNum ((-1 * s), (2 * s)) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 0) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg37 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg38 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound42 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    0 < cross ((-1 * s), (2 * s)) (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := CoreLocalPolynomials.polynomialPositive15 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound43 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    len ((-1 * s), (2 * s)) ≤ supportNum ((-1 * s), (2 * s)) (adaptiveCoreLocalPoint s 2)
        (adaptiveCoreLocalPoint s 1) (adaptiveCoreLocalPoint s 3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg39 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg40 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound44 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (7 / 16) ∧ 0 ≤ (1 / 2) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (adaptiveCoreLocalPoint s 2) (adaptiveCoreLocalPoint s 1)
        (adaptiveCoreLocalPoint s 3) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := CoreLocalPolynomials.polynomialNonneg31 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := CoreLocalPolynomials.polynomialNonneg32 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [adaptiveCoreLocalPoint, supportNum, cross, rot, normSq]
      ring))

theorem adaptiveCoreLocal_obstruction {Q : EquilateralTriangle} {s : ℝ}
    (hs0 : 0 < s) (hs : s ≤ (1 / 2)) (hq : 0 < Q.side)
    (hpts : ∀ i, adaptiveCoreLocalPoint s i ∈ Q.carrier) : 1 ≤ Q.side := by
  by_cases hsplit : s ≤ (1 / 4)
  · have hl : 0 ≤ s - 0 := by
      linarith
    have hh : 0 ≤ (1 / 4) - s := by
      linarith
    have hd0 := arithmeticBound0 ⟨hs0, hl, hh⟩
    have hb0_0 := arithmeticBound1 ⟨hs0, hl, hh⟩
    have hb0_1 := arithmeticBound2 ⟨hs0, hl, hh⟩
    have hc0 : ConeBound Q (1, 0) ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2))
        + ((2 / 3) * s))) :=
      ⟨adaptiveCoreLocalPoint s 3, hpts 3, adaptiveCoreLocalPoint s 2, hpts 2,
          adaptiveCoreLocalPoint s 0, hpts 0, hb0_0, hb0_1⟩
    have hd1 := arithmeticBound3 ⟨hs0, hl, hh⟩
    have hb1_0 := arithmeticBound4 ⟨hs0, hl, hh⟩
    have hb1_1 := arithmeticBound5 ⟨hs0, hl, hh⟩
    have hc1 : ConeBound Q ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2 /
        3) * s))) ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
        2)))) :=
      ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 2, hpts 2,
          adaptiveCoreLocalPoint s 0, hpts 0, hb1_0, hb1_1⟩
    have hd2 := arithmeticBound6 ⟨hs0, hl, hh⟩
    have hb2_0 := arithmeticBound7 ⟨hs0, hl, hh⟩
    have hb2_1 := arithmeticBound8 ⟨hs0, hl, hh⟩
    have hc2 : ConeBound Q ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) *
        (s ^ 2)))) ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3) * (s
        ^ 2)))) :=
      ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
          adaptiveCoreLocalPoint s 0, hpts 0, hb2_0, hb2_1⟩
    have hd3 := arithmeticBound9 ⟨hs0, hl, hh⟩
    have hb3_0 := arithmeticBound10 ⟨hs0, hl, hh⟩
    have hb3_1 := arithmeticBound11 ⟨hs0, hl, hh⟩
    have hc3 : ConeBound Q ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 /
        3) * (s ^ 2)))) (-1, 1) :=
      ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
          adaptiveCoreLocalPoint s 3, hpts 3, hb3_0, hb3_1⟩
    have hend : SupportBound Q (-1, 1) :=
      ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
          adaptiveCoreLocalPoint s 3, hpts 3, hb3_1⟩
    apply one_le_side_of_fan hq (vs := [((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s
        ^ 2)) + ((2 / 3) * s))), ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2
        / 3) * (s ^ 2)))), ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 /
        3) * (s ^ 2)))), (-1, 1)])
    exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, hd3, hc3, by norm_num [rot, eastDir], hend⟩
  · by_cases hsplit : s ≤ (3 / 8)
    · have hl : 0 ≤ s - (1 / 4) := by
        linarith
      have hh : 0 ≤ (3 / 8) - s := by
        linarith
      have hd0 := arithmeticBound12 ⟨hs0, hl, hh⟩
      have hb0_0 := arithmeticBound13 ⟨hs0, hl, hh⟩
      have hb0_1 := arithmeticBound14 ⟨hs0, hl, hh⟩
      have hc0 : ConeBound Q (1, 0) ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^
          2)) + ((2 / 3) * s))) :=
        ⟨adaptiveCoreLocalPoint s 3, hpts 3, adaptiveCoreLocalPoint s 2, hpts 2,
            adaptiveCoreLocalPoint s 0, hpts 0, hb0_0, hb0_1⟩
      have hd1 := arithmeticBound15 ⟨hs0, hl, hh⟩
      have hb1_0 := arithmeticBound16 ⟨hs0, hl, hh⟩
      have hb1_1 := arithmeticBound17 ⟨hs0, hl, hh⟩
      have hc1 : ConeBound Q ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((2
          / 3) * s))) ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3) * (s ^
          2)))) :=
        ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 2, hpts 2,
            adaptiveCoreLocalPoint s 0, hpts 0, hb1_0, hb1_1⟩
      have hd2 := arithmeticBound18 ⟨hs0, hl, hh⟩
      have hb2_0 := arithmeticBound19 ⟨hs0, hl, hh⟩
      have hb2_1 := arithmeticBound20 ⟨hs0, hl, hh⟩
      have hc2 : ConeBound Q ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3)
          * (s ^ 2)))) ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1 / 3)
          * (s ^ 2)))) :=
        ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
            adaptiveCoreLocalPoint s 0, hpts 0, hb2_0, hb2_1⟩
      have hd3 := arithmeticBound21 ⟨hs0, hl, hh⟩
      have hb3_0 := arithmeticBound22 ⟨hs0, hl, hh⟩
      have hb3_1 := arithmeticBound23 ⟨hs0, hl, hh⟩
      have hc3 : ConeBound Q ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1
          / 3) * (s ^ 2)))) (-1, 1) :=
        ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
            adaptiveCoreLocalPoint s 3, hpts 3, hb3_0, hb3_1⟩
      have hend : SupportBound Q (-1, 1) :=
        ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
            adaptiveCoreLocalPoint s 3, hpts 3, hb3_1⟩
      apply one_le_side_of_fan hq (vs := [((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) *
          (s ^ 2)) + ((2 / 3) * s))), ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) +
          ((2 / 3) * (s ^ 2)))), ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) +
          ((1 / 3) * (s ^ 2)))), (-1, 1)])
      exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, hd3, hc3, by norm_num [rot, eastDir], hend⟩
    · by_cases hsplit : s ≤ (7 / 16)
      · have hl : 0 ≤ s - (3 / 8) := by
          linarith
        have hh : 0 ≤ (7 / 16) - s := by
          linarith
        have hd0 := arithmeticBound24 ⟨hs0, hl, hh⟩
        have hb0_0 := arithmeticBound25 ⟨hs0, hl, hh⟩
        have hb0_1 := arithmeticBound26 ⟨hs0, hl, hh⟩
        have hc0 : ConeBound Q (1, 0) ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^
            2)) + ((2 / 3) * s))) :=
          ⟨adaptiveCoreLocalPoint s 3, hpts 3, adaptiveCoreLocalPoint s 2, hpts 2,
              adaptiveCoreLocalPoint s 0, hpts 0, hb0_0, hb0_1⟩
        have hd1 := arithmeticBound27 ⟨hs0, hl, hh⟩
        have hb1_0 := arithmeticBound28 ⟨hs0, hl, hh⟩
        have hb1_1 := arithmeticBound29 ⟨hs0, hl, hh⟩
        have hc1 : ConeBound Q ((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) +
            ((2 / 3) * s))) ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 / 3)
            * (s ^ 2)))) :=
          ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 2, hpts 2,
              adaptiveCoreLocalPoint s 0, hpts 0, hb1_0, hb1_1⟩
        have hd2 := arithmeticBound30 ⟨hs0, hl, hh⟩
        have hb2_0 := arithmeticBound31 ⟨hs0, hl, hh⟩
        have hb2_1 := arithmeticBound32 ⟨hs0, hl, hh⟩
        have hc2 : ConeBound Q ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 /
            3) * (s ^ 2)))) ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) + ((1
            / 3) * (s ^ 2)))) :=
          ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
              adaptiveCoreLocalPoint s 0, hpts 0, hb2_0, hb2_1⟩
        have hd3 := arithmeticBound33 ⟨hs0, hl, hh⟩
        have hb3_0 := arithmeticBound34 ⟨hs0, hl, hh⟩
        have hb3_1 := arithmeticBound35 ⟨hs0, hl, hh⟩
        have hc3 : ConeBound Q ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) * s) +
            ((1 / 3) * (s ^ 2)))) (-1, 1) :=
          ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
              adaptiveCoreLocalPoint s 3, hpts 3, hb3_0, hb3_1⟩
        have hend : SupportBound Q (-1, 1) :=
          ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
              adaptiveCoreLocalPoint s 3, hpts 3, hb3_1⟩
        apply one_le_side_of_fan hq (vs := [((1 + ((-4 / 3) * s) + ((1 / 3) * (s ^ 2))), (((1 / 3) *
            (s ^ 2)) + ((2 / 3) * s))), ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s)
            + ((2 / 3) * (s ^ 2)))), ((-1 + ((-2 / 3) * (s ^ 2)) + ((5 / 3) * s)), (1 + ((-1 / 3) *
            s) + ((1 / 3) * (s ^ 2)))), (-1, 1)])
        exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, hd3, hc3, by norm_num [rot, eastDir], hend⟩
      · have hl : 0 ≤ s - (7 / 16) := by
          linarith
        have hh : 0 ≤ (1 / 2) - s := by
          linarith
        have hd0 := arithmeticBound36 ⟨hs0, hl, hh⟩
        have hb0_0 := arithmeticBound37 ⟨hs0, hl, hh⟩
        have hb0_1 := arithmeticBound38 ⟨hs0, hl, hh⟩
        have hc0 : ConeBound Q (1, 0) ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) +
            ((2 / 3) * (s ^ 2)))) :=
          ⟨adaptiveCoreLocalPoint s 3, hpts 3, adaptiveCoreLocalPoint s 2, hpts 2,
              adaptiveCoreLocalPoint s 0, hpts 0, hb0_0, hb0_1⟩
        have hd1 := arithmeticBound39 ⟨hs0, hl, hh⟩
        have hb1_0 := arithmeticBound40 ⟨hs0, hl, hh⟩
        have hb1_1 := arithmeticBound41 ⟨hs0, hl, hh⟩
        have hc1 : ConeBound Q ((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3) * s) + ((2 /
            3) * (s ^ 2)))) ((-1 * s), (2 * s)) :=
          ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
              adaptiveCoreLocalPoint s 0, hpts 0, hb1_0, hb1_1⟩
        have hd2 := arithmeticBound42 ⟨hs0, hl, hh⟩
        have hb2_0 := arithmeticBound43 ⟨hs0, hl, hh⟩
        have hb2_1 := arithmeticBound44 ⟨hs0, hl, hh⟩
        have hc2 : ConeBound Q ((-1 * s), (2 * s)) (-1, 1) :=
          ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
              adaptiveCoreLocalPoint s 3, hpts 3, hb2_0, hb2_1⟩
        have hend : SupportBound Q (-1, 1) :=
          ⟨adaptiveCoreLocalPoint s 2, hpts 2, adaptiveCoreLocalPoint s 1, hpts 1,
              adaptiveCoreLocalPoint s 3, hpts 3, hb2_1⟩
        apply one_le_side_of_fan hq (vs := [((((-1 / 3) * (s ^ 2)) + ((4 / 3) * s)), (1 + ((-5 / 3)
            * s) + ((2 / 3) * (s ^ 2)))), ((-1 * s), (2 * s)), (-1, 1)])
        exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, by norm_num [rot, eastDir], hend⟩

end ConwaySoifer.Simplified
