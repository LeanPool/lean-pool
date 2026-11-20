/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

/-
Adapted from JD-Jones-ASES/persistent-sos, commit
d432ff9a67594cc0fa7a7af1913320b46d2a86db.
Original MIT notice (retained under the permission to sublicense):

MIT License

Copyright (c) 2026 JD Jones

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

module

public import LeanPool.PersistentSOS.MomentGeneral
public import LeanPool.PersistentSOS.MomentNumerator
public import LeanPool.PersistentSOS.MomentBlockFull0
public import LeanPool.PersistentSOS.MomentBlock1
public import LeanPool.PersistentSOS.MomentBlock2
public import LeanPool.PersistentSOS.MomentBlock3
public import LeanPool.PersistentSOS.MomentBlock4
public import LeanPool.PersistentSOS.MomentBlock5
public import LeanPool.PersistentSOS.MomentBlock6
public import LeanPool.PersistentSOS.MomentBlock7
public import Mathlib.Tactic.FinCases

/-!
# Explicit rational moment data

Every monomial occurrence uses one base-five exponent key. All degree-four
moments are derived from the retained rational certificate. The finite
Gram identities and coverage are proved below by kernel reduction.
-/


@[expose] public section

namespace PersistentSOS


/-- Dimensions of the eight exact moment-matrix blocks. -/
def blockSize : Fin 8 → ℕ
  | 0 => 28
  | 1 => 11
  | 2 => 11
  | 3 => 16
  | 4 => 11
  | 5 => 16
  | 6 => 16
  | 7 => 11

/-- Pairs of padded variable indices forming each quadratic monomial block. -/
def basisPair : (c : Fin 8) → Fin (blockSize c) → Fin 15 × Fin 15
  | 0 => ![(0, 0), (0, 1), (0, 6), (0, 7), (0, 8), (1, 6), (1, 7), (1, 8), (2, 2), (3, 3), (4, 4),
    (5, 5), (6, 6), (6, 7), (6, 8), (7, 7), (7, 8), (8, 8), (9, 9), (9, 14), (10, 10), (10, 13),
    (11, 11), (11, 12), (12, 12), (13, 13), (14, 14), (1, 1)]
  | 1 => ![(0, 2), (1, 2), (2, 6), (2, 7), (2, 8), (3, 9), (3, 14), (4, 10), (4, 13), (5, 11), (5,
    12)]
  | 2 => ![(0, 3), (1, 3), (2, 9), (2, 14), (3, 6), (3, 7), (3, 8), (4, 11), (4, 12), (5, 10), (5,
    13)]
  | 3 => ![(0, 9), (0, 14), (1, 9), (1, 14), (2, 3), (4, 5), (6, 9), (6, 14), (7, 9), (7, 14), (8,
    9), (8, 14), (10, 11), (10, 12), (11, 13), (12, 13)]
  | 4 => ![(0, 4), (1, 4), (2, 10), (2, 13), (3, 11), (3, 12), (4, 6), (4, 7), (4, 8), (5, 9), (5,
    14)]
  | 5 => ![(0, 10), (0, 13), (1, 10), (1, 13), (2, 4), (3, 5), (6, 10), (6, 13), (7, 10), (7, 13),
    (8, 10), (8, 13), (9, 11), (9, 12), (11, 14), (12, 14)]
  | 6 => ![(0, 11), (0, 12), (1, 11), (1, 12), (2, 5), (3, 4), (6, 11), (6, 12), (7, 11), (7, 12),
    (8, 11), (8, 12), (9, 10), (9, 13), (10, 14), (13, 14)]
  | 7 => ![(0, 5), (1, 5), (2, 11), (2, 12), (3, 10), (3, 13), (4, 9), (4, 14), (5, 6), (5, 7),
    (5, 8)]

/-- Integer moment matrices, with the common denominator kept separate. -/
def blockNumerator : (c : Fin 8) → Fin (blockSize c) → Fin (blockSize c) → ℤ
  | 0 => momentBlockFull0Stage0
  | 1 => momentBlock1Stage0
  | 2 => momentBlock2Stage0
  | 3 => momentBlock3Stage0
  | 4 => momentBlock4Stage0
  | 5 => momentBlock5Stage0
  | 6 => momentBlock6Stage0
  | 7 => momentBlock7Stage0

theorem blockNumerator_psd (c : Fin 8) : IsPSD (fun i j => (blockNumerator c i j : ℝ)) := by
  fin_cases c
  · exact momentBlockFull0Stage0_psd
  · exact momentBlock1Stage0_psd
  · exact momentBlock2Stage0_psd
  · exact momentBlock3Stage0_psd
  · exact momentBlock4Stage0_psd
  · exact momentBlock5Stage0_psd
  · exact momentBlock6Stage0_psd
  · exact momentBlock7Stage0_psd

/-- A zero index pads a monomial of degree less than two. -/
noncomputable def variableExponent (i : Fin 15) : Exponent :=
  if h : i = 0 then 0 else Finsupp.single ⟨i.val - 1, by
    have hi := i.isLt
    have hn : i.val ≠ 0 := by simpa using h
    omega⟩ 1

/-- Base-five key of a variable, with zero representing the constant monomial. -/
def variableKey (i : Fin 15) : ℕ := if i = 0 then 0 else 5 ^ (i.val - 1)

/-- Exponent vector of a quadratic monomial in the complete block basis. -/
noncomputable def momentBasis (b : (c : Fin 8) × Fin (blockSize c)) : Exponent :=
  variableExponent (basisPair b.1 b.2).1 + variableExponent (basisPair b.1 b.2).2

/-- Moment-table key of a quadratic basis monomial. -/
def basisKey (c : Fin 8) (i : Fin (blockSize c)) : ℕ :=
  variableKey (basisPair c i).1 + variableKey (basisPair c i).2

@[simp] theorem exponentKey_variableExponent (i : Fin 15) :
    exponentKey (variableExponent i) = variableKey i := by
  simp only [variableExponent, variableKey]
  split_ifs <;> simp

@[simp] theorem exponentKey_momentBasis (b : (c : Fin 8) × Fin (blockSize c)) :
    exponentKey (momentBasis b) = basisKey b.1 b.2 := by
  simp [momentBasis, basisKey]

private theorem moment_block_zero_rows : ∀ i j : Fin (blockSize 0),
    momentNumerator (basisKey 0 i + basisKey 0 j) = blockNumerator 0 i j := by
  intro i
  fin_cases i <;> decide +kernel

theorem moment_block_0 : ∀ i j : Fin (blockSize 0),
    momentNumerator (basisKey 0 i + basisKey 0 j) = blockNumerator 0 i j := by
  as_aux_lemma => exact moment_block_zero_rows

theorem moment_block_1 : ∀ i j : Fin (blockSize 1),
    momentNumerator (basisKey 1 i + basisKey 1 j) = blockNumerator 1 i j := by
  decide +kernel

theorem moment_block_2 : ∀ i j : Fin (blockSize 2),
    momentNumerator (basisKey 2 i + basisKey 2 j) = blockNumerator 2 i j := by
  decide +kernel

theorem moment_block_3 : ∀ i j : Fin (blockSize 3),
    momentNumerator (basisKey 3 i + basisKey 3 j) = blockNumerator 3 i j := by
  decide +kernel

theorem moment_block_4 : ∀ i j : Fin (blockSize 4),
    momentNumerator (basisKey 4 i + basisKey 4 j) = blockNumerator 4 i j := by
  decide +kernel

theorem moment_block_5 : ∀ i j : Fin (blockSize 5),
    momentNumerator (basisKey 5 i + basisKey 5 j) = blockNumerator 5 i j := by
  decide +kernel

theorem moment_block_6 : ∀ i j : Fin (blockSize 6),
    momentNumerator (basisKey 6 i + basisKey 6 j) = blockNumerator 6 i j := by
  decide +kernel

theorem moment_block_7 : ∀ i j : Fin (blockSize 7),
    momentNumerator (basisKey 7 i + basisKey 7 j) = blockNumerator 7 i j := by
  decide +kernel

theorem moment_block : ∀ c (i j : Fin (blockSize c)),
    momentNumerator (basisKey c i + basisKey c j) = blockNumerator c i j := by
  intro c
  fin_cases c
  · exact moment_block_0
  · exact moment_block_1
  · exact moment_block_2
  · exact moment_block_3
  · exact moment_block_4
  · exact moment_block_5
  · exact moment_block_6
  · exact moment_block_7

-- Check pairs in increasing block order. Commutativity of addition gives the
-- reverse product the same moment key.
private theorem moment_cross_ordered : ∀ c d : Fin 8, c < d →
    ∀ (i : Fin (blockSize c)) (j : Fin (blockSize d)),
    momentNumerator (basisKey c i + basisKey d j) = 0 := by
  intro c
  fin_cases c
  · -- Block 0 is the largest. Check its partners separately.
    intro d
    fin_cases d <;> decide +kernel
  all_goals decide +kernel

private theorem moment_cross_of_ne (c d : Fin 8) (h : c ≠ d)
    (i : Fin (blockSize c)) (j : Fin (blockSize d)) :
    momentNumerator (basisKey c i + basisKey d j) = 0 := by
  rcases lt_or_gt_of_ne h with hcd | hdc
  · exact moment_cross_ordered c d hcd i j
  · rw [Nat.add_comm]
    exact moment_cross_ordered d c hdc j i

theorem moment_cross_0 : ∀ d : Fin 8, 0 ≠ d → ∀ (i : Fin (blockSize 0)) (j : Fin (blockSize d)),
    momentNumerator (basisKey 0 i + basisKey d j) = 0 := by
  as_aux_lemma => exact moment_cross_of_ne 0

theorem moment_cross_1 : ∀ d : Fin 8, 1 ≠ d → ∀ (i : Fin (blockSize 1)) (j : Fin (blockSize d)),
    momentNumerator (basisKey 1 i + basisKey d j) = 0 := by
  as_aux_lemma => exact moment_cross_of_ne 1

theorem moment_cross_2 : ∀ d : Fin 8, 2 ≠ d → ∀ (i : Fin (blockSize 2)) (j : Fin (blockSize d)),
    momentNumerator (basisKey 2 i + basisKey d j) = 0 := by
  as_aux_lemma => exact moment_cross_of_ne 2

theorem moment_cross_3 : ∀ d : Fin 8, 3 ≠ d → ∀ (i : Fin (blockSize 3)) (j : Fin (blockSize d)),
    momentNumerator (basisKey 3 i + basisKey d j) = 0 := by
  as_aux_lemma => exact moment_cross_of_ne 3

theorem moment_cross_4 : ∀ d : Fin 8, 4 ≠ d → ∀ (i : Fin (blockSize 4)) (j : Fin (blockSize d)),
    momentNumerator (basisKey 4 i + basisKey d j) = 0 := by
  as_aux_lemma => exact moment_cross_of_ne 4

theorem moment_cross_5 : ∀ d : Fin 8, 5 ≠ d → ∀ (i : Fin (blockSize 5)) (j : Fin (blockSize d)),
    momentNumerator (basisKey 5 i + basisKey d j) = 0 := by
  as_aux_lemma => exact moment_cross_of_ne 5

theorem moment_cross_6 : ∀ d : Fin 8, 6 ≠ d → ∀ (i : Fin (blockSize 6)) (j : Fin (blockSize d)),
    momentNumerator (basisKey 6 i + basisKey d j) = 0 := by
  as_aux_lemma => exact moment_cross_of_ne 6

theorem moment_cross_7 : ∀ d : Fin 8, 7 ≠ d → ∀ (i : Fin (blockSize 7)) (j : Fin (blockSize d)),
    momentNumerator (basisKey 7 i + basisKey d j) = 0 := by
  as_aux_lemma => exact moment_cross_of_ne 7

theorem moment_cross : ∀ c d : Fin 8, c ≠ d → ∀ (i : Fin (blockSize c)) (j : Fin (blockSize d)),
    momentNumerator (basisKey c i + basisKey d j) = 0 := moment_cross_of_ne

theorem moment_quadratic_numerator_sum :
    (∑ i : Fin 14, momentNumerator (2 * 5 ^ i.val)) = 1000000000 := by
  decide +kernel

theorem moment_quartic_numerator_sum :
    (∑ i : Fin 14, ∑ j : Fin 14, momentNumerator (2 * 5 ^ i.val + 2 * 5 ^ j.val)) =
      1000000000 := by
  decide +kernel

end PersistentSOS
