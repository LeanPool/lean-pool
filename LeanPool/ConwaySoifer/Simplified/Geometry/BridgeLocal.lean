/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.SupportFan
public import Mathlib.Data.Fin.VecNotation
import LeanPool.ConwaySoifer.Simplified.Geometry.BridgeLocalPolynomials
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

/-- The five-point configuration used to exclude an owner bridging local sections. -/
def bridgeLocalPoint (s : ℝ) : Fin 5 → Point :=
  ![((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2 / 3) * s))), ((((-2 / 3) *
      s) + ((2 / 3) * (s ^ 2))), (((-1 / 3) * (s ^ 2)) + ((1 / 3) * s))), ((((-1 / 3) * s) + ((1 /
      3) * (s ^ 2))), (((-1 / 3) * s) + ((1 / 3) * (s ^ 2)))), ((((-1 / 3) * (s ^ 2)) + ((1 / 3) *
      s)), (((-2 / 3) * s) + ((2 / 3) * (s ^ 2)))), ((1 + (-2 * s)), (2 * s))]

private theorem arithmeticBound0 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    0 < cross (1, 0) ((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) * (s ^ 2)) + ((4 / 3) *
        s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := BridgeLocalPolynomials.polynomialPositive1 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross])

private theorem arithmeticBound1 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    len (1, 0) ≤ supportNum (1, 0) (bridgeLocalPoint s 4) (bridgeLocalPoint s 2) (bridgeLocalPoint s
        4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg1 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg2 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound2 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    len ((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) * (s ^ 2)) + ((4 / 3) * s))) ≤
        supportNum ((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) * (s ^ 2)) + ((4 / 3) *
        s))) (bridgeLocalPoint s 4) (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg3 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg4 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound3 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    0 < cross ((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) * (s ^ 2)) + ((4 / 3) * s)))
        (0, (s + (-1 * (s ^ 2)))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := BridgeLocalPolynomials.polynomialPositive2 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound4 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    len ((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) * (s ^ 2)) + ((4 / 3) * s))) ≤
        supportNum ((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) * (s ^ 2)) + ((4 / 3) *
        s))) (bridgeLocalPoint s 0) (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg3 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg4 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound5 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    len (0, (s + (-1 * (s ^ 2)))) ≤ supportNum (0, (s + (-1 * (s ^ 2)))) (bridgeLocalPoint s 0)
        (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg5 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg6 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound6 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    0 < cross (0, (s + (-1 * (s ^ 2)))) ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s
        ^ 2)) + ((1 / 3) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := BridgeLocalPolynomials.polynomialPositive3 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound7 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    len (0, (s + (-1 * (s ^ 2)))) ≤ supportNum (0, (s + (-1 * (s ^ 2)))) (bridgeLocalPoint s 1)
        (bridgeLocalPoint s 3) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg7 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg8 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound8 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    len ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s))) ≤
        supportNum ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) *
        s))) (bridgeLocalPoint s 1) (bridgeLocalPoint s 3) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg9 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg10 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound9 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    0 < cross ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s)))
        ((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2 / 3) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := BridgeLocalPolynomials.polynomialPositive4 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound10 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    len ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s))) ≤
        supportNum ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) *
        s))) (bridgeLocalPoint s 1) (bridgeLocalPoint s 4) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg9 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg10 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound11 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    len ((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2 / 3) * s))) ≤
        supportNum ((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2 / 3) * s)))
        (bridgeLocalPoint s 1) (bridgeLocalPoint s 4) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg11 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg12 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound12 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    0 < cross ((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2 / 3) * s))) (-1,
        1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := BridgeLocalPolynomials.polynomialPositive5 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound13 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    len ((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2 / 3) * s))) ≤
        supportNum ((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2 / 3) * s)))
        (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg11 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg12 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound14 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - 0 ∧ 0 ≤ (1 / 6) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) (bridgeLocalPoint
        s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg1 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg2 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound15 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    0 < cross (1, 0) ((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((5 / 3) *
        s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := BridgeLocalPolynomials.polynomialPositive6 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross])

private theorem arithmeticBound16 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    len (1, 0) ≤ supportNum (1, 0) (bridgeLocalPoint s 4) (bridgeLocalPoint s 2) (bridgeLocalPoint s
        4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg13 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg14 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound17 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    len ((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((5 / 3) * s))) ≤
        supportNum ((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((5 / 3) *
        s))) (bridgeLocalPoint s 4) (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg15 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg16 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound18 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    0 < cross ((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((5 / 3) * s)))
        (0, (s + (-1 * (s ^ 2)))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := BridgeLocalPolynomials.polynomialPositive7 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound19 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    len ((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((5 / 3) * s))) ≤
        supportNum ((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((5 / 3) *
        s))) (bridgeLocalPoint s 0) (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg17 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg18 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound20 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    len (0, (s + (-1 * (s ^ 2)))) ≤ supportNum (0, (s + (-1 * (s ^ 2)))) (bridgeLocalPoint s 0)
        (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg19 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg20 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound21 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    0 < cross (0, (s + (-1 * (s ^ 2)))) ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s
        ^ 2)) + ((1 / 3) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := BridgeLocalPolynomials.polynomialPositive8 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound22 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    len (0, (s + (-1 * (s ^ 2)))) ≤ supportNum (0, (s + (-1 * (s ^ 2)))) (bridgeLocalPoint s 1)
        (bridgeLocalPoint s 3) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg21 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg22 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound23 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    len ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s))) ≤
        supportNum ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) *
        s))) (bridgeLocalPoint s 1) (bridgeLocalPoint s 3) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg23 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg24 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound24 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    0 < cross ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s)))
        ((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2 / 3) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := BridgeLocalPolynomials.polynomialPositive9 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound25 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    len ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s))) ≤
        supportNum ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) *
        s))) (bridgeLocalPoint s 1) (bridgeLocalPoint s 4) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg23 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg24 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound26 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    len ((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2 / 3) * s))) ≤
        supportNum ((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2 / 3) * s)))
        (bridgeLocalPoint s 1) (bridgeLocalPoint s 4) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg25 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg26 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound27 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    0 < cross ((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2 / 3) * s))) (-1,
        1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := BridgeLocalPolynomials.polynomialPositive10 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound28 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    len ((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2 / 3) * s))) ≤
        supportNum ((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2 / 3) * s)))
        (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg25 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg26 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound29 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 6) ∧ 0 ≤ (5 / 24) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) (bridgeLocalPoint
        s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg13 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg14 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound30 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    0 < cross (1, 0) ((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((5 / 3) *
        s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := BridgeLocalPolynomials.polynomialPositive11 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross])

private theorem arithmeticBound31 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    len (1, 0) ≤ supportNum (1, 0) (bridgeLocalPoint s 4) (bridgeLocalPoint s 2) (bridgeLocalPoint s
        4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg27 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg28 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound32 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    len ((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((5 / 3) * s))) ≤
        supportNum ((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((5 / 3) *
        s))) (bridgeLocalPoint s 4) (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg29 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg30 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound33 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    0 < cross ((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((5 / 3) * s)))
        (0, (s + (-1 * (s ^ 2)))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := BridgeLocalPolynomials.polynomialPositive12 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound34 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    len ((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((5 / 3) * s))) ≤
        supportNum ((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) + ((5 / 3) *
        s))) (bridgeLocalPoint s 0) (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg31 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg32 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound35 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    len (0, (s + (-1 * (s ^ 2)))) ≤ supportNum (0, (s + (-1 * (s ^ 2)))) (bridgeLocalPoint s 0)
        (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg33 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg34 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound36 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    0 < cross (0, (s + (-1 * (s ^ 2)))) ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s
        ^ 2)) + ((1 / 3) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := BridgeLocalPolynomials.polynomialPositive13 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound37 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    len (0, (s + (-1 * (s ^ 2)))) ≤ supportNum (0, (s + (-1 * (s ^ 2)))) (bridgeLocalPoint s 1)
        (bridgeLocalPoint s 3) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg35 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg36 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound38 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    len ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s))) ≤
        supportNum ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) *
        s))) (bridgeLocalPoint s 1) (bridgeLocalPoint s 3) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg37 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg38 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound39 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    0 < cross ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s)))
        (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := BridgeLocalPolynomials.polynomialPositive14 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound40 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    len ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s))) ≤
        supportNum ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) *
        s))) (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg39 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg40 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound41 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (5 / 24) ∧ 0 ≤ (1 / 4) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) (bridgeLocalPoint
        s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg27 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg28 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound42 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    0 < cross (1, 0) ((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) * (s ^ 2)) + ((4 / 3) *
        s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := BridgeLocalPolynomials.polynomialPositive15 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross])

private theorem arithmeticBound43 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    len (1, 0) ≤ supportNum (1, 0) (bridgeLocalPoint s 4) (bridgeLocalPoint s 2) (bridgeLocalPoint s
        4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg41 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg42 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound44 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    len ((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) * (s ^ 2)) + ((4 / 3) * s))) ≤
        supportNum ((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) * (s ^ 2)) + ((4 / 3) *
        s))) (bridgeLocalPoint s 4) (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg43 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg44 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound45 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    0 < cross ((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) * (s ^ 2)) + ((4 / 3) * s)))
        ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s))) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := BridgeLocalPolynomials.polynomialPositive16 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound46 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    len ((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) * (s ^ 2)) + ((4 / 3) * s))) ≤
        supportNum ((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) * (s ^ 2)) + ((4 / 3) *
        s))) (bridgeLocalPoint s 1) (bridgeLocalPoint s 3) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg45 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg46 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound47 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    len ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s))) ≤
        supportNum ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) *
        s))) (bridgeLocalPoint s 1) (bridgeLocalPoint s 3) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg47 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg48 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound48 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    0 < cross ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s)))
        (-1, 1) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  have hp := BridgeLocalPolynomials.polynomialPositive17 ⟨hs0, hl, hh⟩
  exact lt_of_lt_of_eq hp (by
    simp [cross]
    ring)

private theorem arithmeticBound49 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    len ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s))) ≤
        supportNum ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) *
        s))) (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) (bridgeLocalPoint s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg49 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg50 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

private theorem arithmeticBound50 {s : ℝ}
    (conditions : 0 < s ∧ 0 ≤ s - (1 / 4) ∧ 0 ≤ (1 / 3) - s) :
    len (-1, 1) ≤ supportNum (-1, 1) (bridgeLocalPoint s 2) (bridgeLocalPoint s 4) (bridgeLocalPoint
        s 4) := by
  obtain ⟨hs0, hl, hh⟩ := conditions
  apply support_of_sq
  · have hp := BridgeLocalPolynomials.polynomialNonneg41 ⟨hs0, hl, hh⟩
    exact le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot]
      ring)
  · have hp := BridgeLocalPolynomials.polynomialNonneg42 ⟨hs0, hl, hh⟩
    exact sub_nonneg.mp (le_of_le_of_eq hp (by
      simp [bridgeLocalPoint, supportNum, cross, rot, normSq]
      ring))

theorem bridgeLocal_obstruction {Q : EquilateralTriangle} {s : ℝ}
    (hs0 : 0 < s) (hs : s ≤ (1 / 3)) (hq : 0 < Q.side)
    (hpts : ∀ i, bridgeLocalPoint s i ∈ Q.carrier) : 1 ≤ Q.side := by
  by_cases hsplit : s ≤ (1 / 6)
  · have hl : 0 ≤ s - 0 := by
      linarith
    have hh : 0 ≤ (1 / 6) - s := by
      linarith
    have hd0 := arithmeticBound0 ⟨hs0, hl, hh⟩
    have hb0_0 := arithmeticBound1 ⟨hs0, hl, hh⟩
    have hb0_1 := arithmeticBound2 ⟨hs0, hl, hh⟩
    have hc0 : ConeBound Q (1, 0) ((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) * (s ^ 2))
        + ((4 / 3) * s))) :=
      ⟨bridgeLocalPoint s 4, hpts 4, bridgeLocalPoint s 2, hpts 2, bridgeLocalPoint s 4, hpts 4,
          hb0_0, hb0_1⟩
    have hd1 := arithmeticBound3 ⟨hs0, hl, hh⟩
    have hb1_0 := arithmeticBound4 ⟨hs0, hl, hh⟩
    have hb1_1 := arithmeticBound5 ⟨hs0, hl, hh⟩
    have hc1 : ConeBound Q ((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) * (s ^ 2)) + ((4
        / 3) * s))) (0, (s + (-1 * (s ^ 2)))) :=
      ⟨bridgeLocalPoint s 0, hpts 0, bridgeLocalPoint s 2, hpts 2, bridgeLocalPoint s 4, hpts 4,
          hb1_0, hb1_1⟩
    have hd2 := arithmeticBound6 ⟨hs0, hl, hh⟩
    have hb2_0 := arithmeticBound7 ⟨hs0, hl, hh⟩
    have hb2_1 := arithmeticBound8 ⟨hs0, hl, hh⟩
    have hc2 : ConeBound Q (0, (s + (-1 * (s ^ 2)))) ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 +
        ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s))) :=
      ⟨bridgeLocalPoint s 1, hpts 1, bridgeLocalPoint s 3, hpts 3, bridgeLocalPoint s 4, hpts 4,
          hb2_0, hb2_1⟩
    have hd3 := arithmeticBound9 ⟨hs0, hl, hh⟩
    have hb3_0 := arithmeticBound10 ⟨hs0, hl, hh⟩
    have hb3_1 := arithmeticBound11 ⟨hs0, hl, hh⟩
    have hc3 : ConeBound Q ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1
        / 3) * s))) ((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2 / 3) * s)))
        :=
      ⟨bridgeLocalPoint s 1, hpts 1, bridgeLocalPoint s 4, hpts 4, bridgeLocalPoint s 4, hpts 4,
          hb3_0, hb3_1⟩
    have hd4 := arithmeticBound12 ⟨hs0, hl, hh⟩
    have hb4_0 := arithmeticBound13 ⟨hs0, hl, hh⟩
    have hb4_1 := arithmeticBound14 ⟨hs0, hl, hh⟩
    have hc4 : ConeBound Q ((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2 / 3)
        * s))) (-1, 1) :=
      ⟨bridgeLocalPoint s 2, hpts 2, bridgeLocalPoint s 4, hpts 4, bridgeLocalPoint s 4, hpts 4,
          hb4_0, hb4_1⟩
    have hend : SupportBound Q (-1, 1) :=
      ⟨bridgeLocalPoint s 2, hpts 2, bridgeLocalPoint s 4, hpts 4, bridgeLocalPoint s 4, hpts 4,
          hb4_1⟩
    apply one_le_side_of_fan hq (vs := [((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) * (s
        ^ 2)) + ((4 / 3) * s))), (0, (s + (-1 * (s ^ 2)))), ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))),
        (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s))), ((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2
        / 3) * (s ^ 2)) + ((2 / 3) * s))), (-1, 1)])
    exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, hd3, hc3, hd4, hc4, by norm_num [rot, eastDir], hend⟩
  · by_cases hsplit : s ≤ (1 / 4)
    · by_cases hsplit : s ≤ (5 / 24)
      · have hl : 0 ≤ s - (1 / 6) := by
          linarith
        have hh : 0 ≤ (5 / 24) - s := by
          linarith
        have hd0 := arithmeticBound15 ⟨hs0, hl, hh⟩
        have hb0_0 := arithmeticBound16 ⟨hs0, hl, hh⟩
        have hb0_1 := arithmeticBound17 ⟨hs0, hl, hh⟩
        have hc0 : ConeBound Q (1, 0) ((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3) * (s ^
            2)) + ((5 / 3) * s))) :=
          ⟨bridgeLocalPoint s 4, hpts 4, bridgeLocalPoint s 2, hpts 2, bridgeLocalPoint s 4, hpts 4,
              hb0_0, hb0_1⟩
        have hd1 := arithmeticBound18 ⟨hs0, hl, hh⟩
        have hb1_0 := arithmeticBound19 ⟨hs0, hl, hh⟩
        have hb1_1 := arithmeticBound20 ⟨hs0, hl, hh⟩
        have hc1 : ConeBound Q ((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) +
            ((5 / 3) * s))) (0, (s + (-1 * (s ^ 2)))) :=
          ⟨bridgeLocalPoint s 0, hpts 0, bridgeLocalPoint s 2, hpts 2, bridgeLocalPoint s 4, hpts 4,
              hb1_0, hb1_1⟩
        have hd2 := arithmeticBound21 ⟨hs0, hl, hh⟩
        have hb2_0 := arithmeticBound22 ⟨hs0, hl, hh⟩
        have hb2_1 := arithmeticBound23 ⟨hs0, hl, hh⟩
        have hc2 : ConeBound Q (0, (s + (-1 * (s ^ 2)))) ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1
            + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s))) :=
          ⟨bridgeLocalPoint s 1, hpts 1, bridgeLocalPoint s 3, hpts 3, bridgeLocalPoint s 4, hpts 4,
              hb2_0, hb2_1⟩
        have hd3 := arithmeticBound24 ⟨hs0, hl, hh⟩
        have hb3_0 := arithmeticBound25 ⟨hs0, hl, hh⟩
        have hb3_1 := arithmeticBound26 ⟨hs0, hl, hh⟩
        have hc3 : ConeBound Q ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) +
            ((1 / 3) * s))) ((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2 /
            3) * s))) :=
          ⟨bridgeLocalPoint s 1, hpts 1, bridgeLocalPoint s 4, hpts 4, bridgeLocalPoint s 4, hpts 4,
              hb3_0, hb3_1⟩
        have hd4 := arithmeticBound27 ⟨hs0, hl, hh⟩
        have hb4_0 := arithmeticBound28 ⟨hs0, hl, hh⟩
        have hb4_1 := arithmeticBound29 ⟨hs0, hl, hh⟩
        have hc4 : ConeBound Q ((((-1 / 3) * s) + ((1 / 3) * (s ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2
            / 3) * s))) (-1, 1) :=
          ⟨bridgeLocalPoint s 2, hpts 2, bridgeLocalPoint s 4, hpts 4, bridgeLocalPoint s 4, hpts 4,
              hb4_0, hb4_1⟩
        have hend : SupportBound Q (-1, 1) :=
          ⟨bridgeLocalPoint s 2, hpts 2, bridgeLocalPoint s 4, hpts 4, bridgeLocalPoint s 4, hpts 4,
              hb4_1⟩
        apply one_le_side_of_fan hq (vs := [((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3)
            * (s ^ 2)) + ((5 / 3) * s))), (0, (s + (-1 * (s ^ 2)))), ((((-8 / 3) * s) + ((2 / 3) *
            (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s))), ((((-1 / 3) * s) + ((1 / 3) * (s
            ^ 2))), (((-2 / 3) * (s ^ 2)) + ((2 / 3) * s))), (-1, 1)])
        exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, hd3, hc3, hd4, hc4, by norm_num [rot, eastDir], hend⟩
      · have hl : 0 ≤ s - (5 / 24) := by
          linarith
        have hh : 0 ≤ (1 / 4) - s := by
          linarith
        have hd0 := arithmeticBound30 ⟨hs0, hl, hh⟩
        have hb0_0 := arithmeticBound31 ⟨hs0, hl, hh⟩
        have hb0_1 := arithmeticBound32 ⟨hs0, hl, hh⟩
        have hc0 : ConeBound Q (1, 0) ((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3) * (s ^
            2)) + ((5 / 3) * s))) :=
          ⟨bridgeLocalPoint s 4, hpts 4, bridgeLocalPoint s 2, hpts 2, bridgeLocalPoint s 4, hpts 4,
              hb0_0, hb0_1⟩
        have hd1 := arithmeticBound33 ⟨hs0, hl, hh⟩
        have hb1_0 := arithmeticBound34 ⟨hs0, hl, hh⟩
        have hb1_1 := arithmeticBound35 ⟨hs0, hl, hh⟩
        have hc1 : ConeBound Q ((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3) * (s ^ 2)) +
            ((5 / 3) * s))) (0, (s + (-1 * (s ^ 2)))) :=
          ⟨bridgeLocalPoint s 0, hpts 0, bridgeLocalPoint s 2, hpts 2, bridgeLocalPoint s 4, hpts 4,
              hb1_0, hb1_1⟩
        have hd2 := arithmeticBound36 ⟨hs0, hl, hh⟩
        have hb2_0 := arithmeticBound37 ⟨hs0, hl, hh⟩
        have hb2_1 := arithmeticBound38 ⟨hs0, hl, hh⟩
        have hc2 : ConeBound Q (0, (s + (-1 * (s ^ 2)))) ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1
            + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s))) :=
          ⟨bridgeLocalPoint s 1, hpts 1, bridgeLocalPoint s 3, hpts 3, bridgeLocalPoint s 4, hpts 4,
              hb2_0, hb2_1⟩
        have hd3 := arithmeticBound39 ⟨hs0, hl, hh⟩
        have hb3_0 := arithmeticBound40 ⟨hs0, hl, hh⟩
        have hb3_1 := arithmeticBound41 ⟨hs0, hl, hh⟩
        have hc3 : ConeBound Q ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) +
            ((1 / 3) * s))) (-1, 1) :=
          ⟨bridgeLocalPoint s 2, hpts 2, bridgeLocalPoint s 4, hpts 4, bridgeLocalPoint s 4, hpts 4,
              hb3_0, hb3_1⟩
        have hend : SupportBound Q (-1, 1) :=
          ⟨bridgeLocalPoint s 2, hpts 2, bridgeLocalPoint s 4, hpts 4, bridgeLocalPoint s 4, hpts 4,
              hb3_1⟩
        apply one_le_side_of_fan hq (vs := [((1 + ((-4 / 3) * s) + ((-2 / 3) * (s ^ 2))), (((1 / 3)
            * (s ^ 2)) + ((5 / 3) * s))), (0, (s + (-1 * (s ^ 2)))), ((((-8 / 3) * s) + ((2 / 3) *
            (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 / 3) * s))), (-1, 1)])
        exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, hd3, hc3, by norm_num [rot, eastDir], hend⟩
    · have hl : 0 ≤ s - (1 / 4) := by
        linarith
      have hh : 0 ≤ (1 / 3) - s := by
        linarith
      have hd0 := arithmeticBound42 ⟨hs0, hl, hh⟩
      have hb0_0 := arithmeticBound43 ⟨hs0, hl, hh⟩
      have hb0_1 := arithmeticBound44 ⟨hs0, hl, hh⟩
      have hc0 : ConeBound Q (1, 0) ((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) * (s ^
          2)) + ((4 / 3) * s))) :=
        ⟨bridgeLocalPoint s 4, hpts 4, bridgeLocalPoint s 2, hpts 2, bridgeLocalPoint s 4, hpts 4,
            hb0_0, hb0_1⟩
      have hd1 := arithmeticBound45 ⟨hs0, hl, hh⟩
      have hb1_0 := arithmeticBound46 ⟨hs0, hl, hh⟩
      have hb1_1 := arithmeticBound47 ⟨hs0, hl, hh⟩
      have hc1 : ConeBound Q ((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) * (s ^ 2)) +
          ((4 / 3) * s))) ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) + ((1 /
          3) * s))) :=
        ⟨bridgeLocalPoint s 1, hpts 1, bridgeLocalPoint s 3, hpts 3, bridgeLocalPoint s 4, hpts 4,
            hb1_0, hb1_1⟩
      have hd2 := arithmeticBound48 ⟨hs0, hl, hh⟩
      have hb2_0 := arithmeticBound49 ⟨hs0, hl, hh⟩
      have hb2_1 := arithmeticBound50 ⟨hs0, hl, hh⟩
      have hc2 : ConeBound Q ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^ 2)) +
          ((1 / 3) * s))) (-1, 1) :=
        ⟨bridgeLocalPoint s 2, hpts 2, bridgeLocalPoint s 4, hpts 4, bridgeLocalPoint s 4, hpts 4,
            hb2_0, hb2_1⟩
      have hend : SupportBound Q (-1, 1) :=
        ⟨bridgeLocalPoint s 2, hpts 2, bridgeLocalPoint s 4, hpts 4, bridgeLocalPoint s 4, hpts 4,
            hb2_1⟩
      apply one_le_side_of_fan hq (vs := [((1 + ((-5 / 3) * s) + ((-1 / 3) * (s ^ 2))), (((2 / 3) *
          (s ^ 2)) + ((4 / 3) * s))), ((((-8 / 3) * s) + ((2 / 3) * (s ^ 2))), (1 + ((-1 / 3) * (s ^
          2)) + ((1 / 3) * s))), (-1, 1)])
      exact ⟨hd0, hc0, hd1, hc1, hd2, hc2, by norm_num [rot, eastDir], hend⟩

end ConwaySoifer.Simplified
