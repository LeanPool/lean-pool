/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors, OpenAI
-/
module

public import LeanPool.MovingSofa.Development.Geometry.Foundations.AreaCertificateInputs
import Mathlib.Algebra.Order.Ring.Int
import Lean.Elab.Tactic.Omega -- shake: keep

/-!
# Area certificate replay

A nonnegative squared angle determines which two endpoint products are needed
in each Taylor step. Combining the two outward divisions gives the same
integer interval endpoints as the original recurrence.
-/

@[expose] public section

namespace MovingSofa.GerverAreaCert.AreaReplay

open SI

/-- Fast product on the area grid for a nonnegative right interval. -/
def multiply (left right : SI) : SI :=
  let lo := left.lo * (if 0 ≤ left.lo then right.lo else right.hi)
  let hi := left.hi * (if 0 ≤ left.hi then right.hi else right.lo)
  ⟨lo / M, -((-hi) / M)⟩

private theorem imin_eq (a b : ℤ) : imin a b = min a b := by
  unfold imin
  split
  next h => exact (min_eq_left h).symm
  next h => exact (min_eq_right (le_of_not_ge h)).symm

private theorem imax_eq (a b : ℤ) : imax a b = max a b := by
  unfold imax
  split
  next h => exact (max_eq_right h).symm
  next h => exact (max_eq_left (le_of_not_ge h)).symm

private theorem lower_eq (value lo hi : ℤ) (ordered : lo ≤ hi) :
    min (value * lo) (value * hi) = value * (if 0 ≤ value then lo else hi) := by
  split
  next nonnegative => exact min_eq_left (mul_le_mul_of_nonneg_left ordered nonnegative)
  next negative => exact min_eq_right (mul_le_mul_of_nonpos_left ordered (le_of_not_ge negative))

private theorem upper_eq (value lo hi : ℤ) (ordered : lo ≤ hi) :
    max (value * lo) (value * hi) = value * (if 0 ≤ value then hi else lo) := by
  split
  next nonnegative => exact max_eq_right (mul_le_mul_of_nonneg_left ordered nonnegative)
  next negative => exact max_eq_left (mul_le_mul_of_nonpos_left ordered (le_of_not_ge negative))

private theorem multiply_eq (left right : SI) (orderedLeft : left.lo ≤ left.hi)
    (orderedRight : right.lo ≤ right.hi) (nonnegative : 0 ≤ right.lo) :
    multiply left right = SI.mul left right := by
  have low := mul_le_mul_of_nonneg_right orderedLeft nonnegative
  have high := mul_le_mul_of_nonneg_right orderedLeft (nonnegative.trans orderedRight)
  simp only [multiply, SI.mul, imin_eq, imax_eq]
  rw [min_eq_left (min_le_min low high), max_eq_right (max_le_max low high),
    lower_eq _ _ _ orderedRight, upper_eq _ _ _ orderedRight]

private theorem round_ordered (low high denominator : ℤ) (ordered : low ≤ high)
    (positive : 0 < denominator) : low / denominator ≤ -((-high) / denominator) := by
  apply (Int.ediv_le_ediv positive ordered).trans
  have h₁ := Int.ediv_mul_le high positive.ne'
  have h₂ := Int.ediv_mul_le (-high) positive.ne'
  have h := add_le_add h₁ h₂
  rw [← add_mul, add_neg_cancel] at h
  have sumNonpositive := nonpos_of_mul_nonpos_left h positive
  omega

private theorem multiply_ordered (left right : SI) (orderedLeft : left.lo ≤ left.hi)
    (orderedRight : right.lo ≤ right.hi) (nonnegative : 0 ≤ right.lo) :
    (multiply left right).lo ≤ (multiply left right).hi := by
  have low := mul_le_mul_of_nonneg_right orderedLeft nonnegative
  have high := mul_le_mul_of_nonneg_right orderedLeft (nonnegative.trans orderedRight)
  apply round_ordered _ _ _ _ (by decide)
  rw [← lower_eq _ _ _ orderedRight, ← upper_eq _ _ _ orderedRight]
  exact (min_le_left _ _).trans (low.trans (le_max_left _ _))

private theorem square_nonnegative (input : SI) (nonnegative : 0 ≤ input.lo) :
    0 ≤ (multiply input input).lo := by
  simp only [multiply, ite_eq_left nonnegative]
  exact Int.ediv_nonneg (mul_self_nonneg _) (by decide)

/-- Negate and divide an interval product, combining the two outward divisions. -/
def multiplyDivideNeg (term square : SI) (divisor : ℤ) : SI :=
  let lo := term.lo * (if 0 ≤ term.lo then square.lo else square.hi)
  let hi := term.hi * (if 0 ≤ term.hi then square.hi else square.lo)
  let combined := M * divisor
  ⟨(-hi) / combined, -(lo / combined)⟩

private theorem multiplyDivideNeg_eq (term square : SI) (divisor : ℤ) :
    multiplyDivideNeg term square divisor = neg (divn (multiply term square) divisor) := by
  simp only [multiplyDivideNeg, multiply, SI.neg, SI.divn, neg_neg,
    Int.ediv_ediv_of_nonneg (by decide : 0 ≤ M)]

private theorem step_ordered (term square : SI) (denominator : ℤ) (positive : 0 < denominator)
    (termOrdered : term.lo ≤ term.hi) (squareOrdered : square.lo ≤ square.hi)
    (squareNonnegative : 0 ≤ square.lo) :
    (multiplyDivideNeg term square denominator).lo ≤
      (multiplyDivideNeg term square denominator).hi := by
  rw [multiplyDivideNeg_eq]
  simp only [SI.neg, SI.divn, neg_le_neg_iff]
  exact round_ordered _ _ _ (multiply_ordered term square termOrdered
    squareOrdered squareNonnegative) positive

/-- Taylor iteration on the area grid using the nonnegative square. -/
def iterate (square input : SI) : ℕ → SI × SI × SI × SI
  | 0 => (input, one, input, one)
  | n + 1 =>
    let state := iterate square input n
    let sine := multiplyDivideNeg state.1 square (((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ)
    let cosine := multiplyDivideNeg state.2.1 square (((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ)
    (sine, cosine, add state.2.2.1 sine, add state.2.2.2 cosine)

private theorem iterate_eq (square input : SI) (squareOrdered : square.lo ≤ square.hi)
    (squareNonnegative : 0 ≤ square.lo) (inputOrdered : input.lo ≤ input.hi) (n : ℕ) :
    iterate square input n = trigIter square input n ∧
      (iterate square input n).1.lo ≤ (iterate square input n).1.hi ∧
      (iterate square input n).2.1.lo ≤ (iterate square input n).2.1.hi := by
  induction n with
  | zero =>
    exact ⟨rfl, inputOrdered, le_rfl⟩
  | succ n ih =>
    have first : 0 < 2 * n + 1 := by omega
    have second : 0 < 2 * n + 2 := by omega
    have third : 0 < 2 * n + 3 := by omega
    have sineDenominator : 0 < (((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ) :=
      Int.natCast_pos.mpr (Nat.mul_pos second third)
    have cosineDenominator : 0 < (((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ) :=
      Int.natCast_pos.mpr (Nat.mul_pos first second)
    refine ⟨?_, step_ordered _ _ _ sineDenominator ih.2.1 squareOrdered squareNonnegative,
      step_ordered _ _ _ cosineDenominator ih.2.2 squareOrdered squareNonnegative⟩
    simp only [iterate, trigIter, multiplyDivideNeg_eq]
    rw [multiply_eq _ _ ih.2.1 squareOrdered squareNonnegative,
      multiply_eq _ _ ih.2.2 squareOrdered squareNonnegative, ih.1]

/-- Compute the same area-grid trigonometric intervals using two endpoint products. -/
def trig (input : SI) : SI × SI :=
  if 0 ≤ input.lo ∧ input.lo ≤ input.hi then
    let state := iterate (multiply input input) input 20
    (⟨state.2.2.1.lo - 1, state.2.2.1.hi + 1⟩, ⟨state.2.2.2.lo - 1, state.2.2.2.hi + 1⟩)
  else trigZ input

/-- The specialized iteration computes the original area-grid interval endpoints. -/
theorem trig_eq (input : SI) : trig input = trigZ input := by
  unfold trig
  split
  next hi =>
    have h := (iterate_eq _ _ (multiply_ordered input input hi.2 hi.2 hi.1)
      (square_nonnegative input hi.1) hi.2 20).1
    rw [h, multiply_eq _ _ hi.2 hi.2 hi.1]
    rfl
  next => rfl

/-- Evaluate the phase and contact formulas using supplied trigonometric intervals. -/
def evalFromTrig (stage : ℕ) (t : SI) (kind : ℕ) (sc : SI × SI) : SI × SI :=
  let s := sc.1
  let c := sc.2
  let data : SI × SI × SI × SI × SI × SI :=
    if stage = 1 then
      (add (add (mul a1Z c) (mul a2Z s)) (ratI (-1) 1),
        add (add (mul (neg a2Z) c) (mul a1Z s)) (ratI (-1) 2),
        add (add (mul (imul (-2) a1Z) s) (mul (imul 2 a2Z) c)) (ratI 1 2),
        add (add (mul (imul 2 a1Z) c) (mul (imul 2 a2Z) s)) (ratI (-1) 1),
        k11Z, k12Z)
    else if stage = 2 then
      let f := add (add (divn (neg (mul t t)) 4) (mul b1Z t)) b2Z
      (f, add (add (divn t 2) (neg b1Z)) (ratI (-1) 1),
        add (add (ratI 1 1) (imul 2 b1Z)) (neg t),
        add f (ratI 1 2), k21Z, k22Z)
    else if stage = 3 then
      let f := sub c1Z t
      let g := add c2Z t
      (f, g, add (ratI (-1) 1) (neg g), add (ratI 1 1) f, k31Z, k32Z)
    else if stage = 4 then
      let g := add (add (divn (neg (mul t t)) 4) (mul d1Z t)) d2Z
      (add (add (neg (divn t 2)) d1Z) (ratI (-1) 1), g,
        add (neg g) (ratI (-1) 2),
        add (add (imul 2 d1Z) (ratI (-1) 1)) (neg t), k41Z, k42Z)
    else
      (add (add (mul e1Z c) (mul e2Z s)) (ratI (-1) 2),
        add (add (mul (neg e2Z) c) (mul e1Z s)) (ratI (-1) 1),
        add (add (ratI 1 1) (mul (imul (-2) e1Z) s)) (mul (imul 2 e2Z) c),
        add (add (mul (imul 2 e1Z) c) (mul (imul 2 e2Z) s)) (ratI (-1) 2),
        k51Z, k52Z)
  let f := data.1
  let g := data.2.1
  let al := data.2.2.1
  let be := data.2.2.2.1
  let kx := data.2.2.2.2.1
  let ky := data.2.2.2.2.2
  let x0 := add (sub (mul c f) (mul s g)) kx
  let y0 := add (add (mul s f) (mul c g)) ky
  let x1 := if kind = 1 ∨ kind = 2 then sub x0 (mul al s) else x0
  let y1 := if kind = 1 ∨ kind = 2 then add y0 (mul al c) else y0
  let x2 := if kind = 1 then add x1 c else x1
  let y2 := if kind = 1 then add y1 s else y1
  let x3 := if kind = 3 ∨ kind = 4 then sub x2 (mul be c) else x2
  let y3 := if kind = 3 ∨ kind = 4 then sub y2 (mul be s) else y2
  (if kind = 3 then sub x3 s else x3, if kind = 3 then add y3 c else y3)

private theorem evalFromTrig_eq (stage : ℕ) (t : SI) (kind : ℕ) :
    evalFromTrig stage t kind (trigZ t) = evalZ stage t kind := rfl

/-- Evaluate the original contact formulas using the specialized area-grid iteration. -/
def eval (stage : ℕ) (t : SI) (kind : ℕ) : SI × SI :=
  evalFromTrig stage t kind (trig t)

private theorem eval_eq (stage : ℕ) (t : SI) (kind : ℕ) :
    eval stage t kind = evalZ stage t kind := by
  rw [eval, trig_eq, evalFromTrig_eq]

/-- An area-grid contact at a sampled stage time. -/
def contact (index kind : ℕ) : SI × SI := eval (stageOf index) (ttZ index) kind

private theorem contact_eq (index kind : ℕ) : contact index kind = contactZ index kind :=
  eval_eq _ _ _

/-- Contact at the requested fan position. -/
def fan (index : ℕ) : SI × SI := contact (fanIdx index) (fanKind index)

/-- The fan anchor contact. -/
def anchor : SI × SI := contact (5 * NN) 3

/-- Compute the original fan determinant with the specialized contact evaluations. -/
def cross (index : ℕ) : SI :=
  sub (mul (sub (fan index).1 anchor.1) (sub (fan (index + 1)).2 anchor.2))
    (mul (sub (fan index).2 anchor.2) (sub (fan (index + 1)).1 anchor.1))

/-- The specialized fan determinant has the same endpoints as the original. -/
theorem cross_eq (index : ℕ) : cross index = crossZ index := by
  simp only [cross, fan, anchor, contact_eq, crossZ, fanZ, anchorZ]

/-- Compute the original covering rectangle area using the specialized evaluations. -/
def rectangle (row column : ℕ) : ℤ :=
  let left := rowBase row column
  let right := left + 1
  let kind := rowKind row
  let leftContact := contact left kind
  let rightContact := contact right kind
  let lo := if rowFwd row then leftContact.1.lo else rightContact.1.lo
  let hi := if rowFwd row then rightContact.1.hi else leftContact.1.hi
  let height := imax (eval (stageOf right) ⟨(ttZ left).lo, (ttZ right).hi⟩ kind).2.hi
    leftContact.2.hi
  imax 0 (hi - lo) * imax 0 height

/-- The specialized computation recovers the same signed integer rectangle area. -/
theorem rectangle_eq (row column : ℕ) : rectangle row column = rectAreaZ row column := by
  simp only [rectangle, contact_eq, eval_eq, rectAreaZ, rectLoZ, rectHiZ, rectHZ]

end MovingSofa.GerverAreaCert.AreaReplay
