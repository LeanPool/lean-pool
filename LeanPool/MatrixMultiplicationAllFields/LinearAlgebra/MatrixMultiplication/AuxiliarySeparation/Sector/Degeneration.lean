/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Sector/Degeneration.lean`, by
Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; removed the ℂ-only lemma
`retained_power_rankAtMost`, which the retained proof does not need; no declaration here needs `K`
algebraically closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Basic
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Sector.Weights
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Interpolation
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# The actual three-sector polynomial degeneration

The interval weights of `SectorWeights` act by diagonal local maps on the
coefficient tensor `C(a, 3h+a-1)`. Shifting every third-leg weight by one makes
the local maps polynomial. Their restriction is exactly `X * retained +
X^2 * erased`, so the existing polynomial-restriction degeneration interface
applies with leading order one and local degree bounds `(0,1,1)`.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.Sector

open MatrixMultiplication.Foundation
open Polynomial

/-- Second-leg coordinates of the three-sector source tensor. -/
abbrev YIndex (a h : ℕ) := Fin (sourceWidth a h)
/-- Third-leg coordinates of the three-sector source tensor. -/
abbrev ZIndex (a h : ℕ) := Fin (a + sourceWidth a h - 1)

variable (K) in
open Classical in
/-- The source coefficient tensor, with its actual shared first-input space. -/
def source (a h : ℕ) : Tensor K (Fin a) (YIndex a h) (ZIndex a h) :=
  convolution K a (sourceWidth a h)

theorem source_ne_zero_iff {a h : ℕ} (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) :
    source K a h i j k ≠ 0 ↔ Support a h i.val j.val k.val := by
  classical
  simp only [source, convolution_ne_zero_iff, Support]
  constructor
  · intro heq
    exact ⟨i.isLt, j.isLt, heq.symm⟩
  · intro hs
    exact hs.2.2.symm

variable (K) in
open Classical in
/-- The weight-zero part in the original coordinate spaces. -/
def retained (a h : ℕ) : Tensor K (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if totalWeight a h i.val j.val k.val = 0 then source K a h i j k else 0

variable (K) in
open Classical in
/-- The positive-weight part, all of whose supported terms have weight one. -/
def erased (a h : ℕ) : Tensor K (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if totalWeight a h i.val j.val k.val = 1 then source K a h i j k else 0

variable (K) in
open Classical in
/-- The left retained branch, still in the common ambient coordinate spaces. -/
def leftTensor (a h : ℕ) : Tensor K (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if LeftBranch a h i.val j.val k.val then 1 else 0

variable (K) in
open Classical in
/-- The middle retained branch; its first leg is the actual shared first leg. -/
def middleTensor (a h : ℕ) : Tensor K (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if MiddleBranch a h i.val j.val k.val then 1 else 0

variable (K) in
open Classical in
/-- The right retained branch in the original coordinate spaces. -/
def rightTensor (a h : ℕ) : Tensor K (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if RightBranch a h i.val j.val k.val then 1 else 0

/-- The retained tensor is exactly the sum of the three stated branches,
with coefficient one on each and the original first-leg coordinates shared. -/
theorem retained_eq_three_branches (a h : ℕ) :
    retained K a h = leftTensor K a h + middleTensor K a h + rightTensor K a h := by
  classical
  funext i j k
  by_cases hs : Support a h i.val j.val k.val
  · have hsource : source K a h i j k = 1 := by
      exact (convolution_eq_one_iff i j k).mpr hs.2.2.symm
    have hw := retained_support_iff hs
    have hlm := leftBranch_not_middleBranch (a := a) (h := h)
      (i := i.val) (j := j.val) (k := k.val)
    have hlr := leftBranch_not_rightBranch (a := a) (h := h)
      (i := i.val) (j := j.val) (k := k.val)
    have hmr := middleBranch_not_rightBranch (a := a) (h := h)
      (i := i.val) (j := j.val) (k := k.val)
    by_cases hl : LeftBranch a h i.val j.val k.val <;>
      by_cases hm : MiddleBranch a h i.val j.val k.val <;>
      by_cases hr : RightBranch a h i.val j.val k.val
    all_goals simp_all [retained, leftTensor, middleTensor, rightTensor]
  · have hsource : source K a h i j k = 0 := by
      by_contra hz
      exact hs ((source_ne_zero_iff i j k).mp hz)
    have hl : ¬ LeftBranch a h i.val j.val k.val := fun hb => hs hb.support
    have hm : ¬ MiddleBranch a h i.val j.val k.val := fun hb => hs hb.support
    have hr : ¬ RightBranch a h i.val j.val k.val := fun hb => hs hb.support
    simp [retained, leftTensor, middleTensor, rightTensor, hsource, hl, hm, hr]

/-- Every source term belongs either to the retained tensor or the erased one. -/
theorem source_eq_retained_add_erased (a h : ℕ) :
    source K a h = retained K a h + erased K a h := by
  classical
  funext i j k
  by_cases hs : source K a h i j k = 0
  · simp [retained, erased, hs]
  · rcases totalWeight_eq_zero_or_one ((source_ne_zero_iff i j k).mp hs) with hw | hw
    all_goals simp [retained, erased, hw]

variable (K) in
open Classical in
/-- The normalized polynomial family appearing in the unshifted weights. -/
def normalizedPolynomial (a h : ℕ) :
    Tensor (Polynomial K) (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => C (retained K a h i j k) + X * C (erased K a h i j k)

variable (K) in
open Classical in
/-- The first local map fixes the common input basis. -/
def leftMap (a : ℕ) (output input : Fin a) : Polynomial K :=
  if input = output then 1 else 0

variable (K) in
open Classical in
/-- The second local map assigns weight one to the middle interval. -/
def middleMap (a h : ℕ) (output input : YIndex a h) : Polynomial K :=
  if input = output then (if MiddleY a h output.val then X else 1) else 0

variable (K) in
open Classical in
/-- Shift the third-leg weights by one, giving weight zero to the middle
interval and weight one to the two outer intervals. -/
def rightMap (a h : ℕ) (output input : ZIndex a h) : Polynomial K :=
  if input = output then (if MiddleZ a h output.val then 1 else X) else 0

variable (K) in
open Classical in
/-- One simultaneous polynomial restriction of the whole source tensor. -/
def polynomial (a h : ℕ) :
    Tensor (Polynomial K) (Fin a) (YIndex a h) (ZIndex a h) :=
  Tensor.restrict (leftMap K a) (middleMap K a h) (rightMap K a h)
    (fun i j k => C (source K a h i j k))

theorem polynomial_apply (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) :
    polynomial K a h i j k =
      (if MiddleY a h j.val then X else 1) *
      (if MiddleZ a h k.val then 1 else X) * C (source K a h i j k) := by
  classical
  simp [polynomial, Tensor.restrict, leftMap, middleMap, rightMap, ite_mul, mul_ite]

/-- The shifted polynomial restriction has precisely two possible degrees. -/
theorem polynomial_identity (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) :
    polynomial K a h i j k =
      X * C (retained K a h i j k) + X ^ 2 * C (erased K a h i j k) := by
  classical
  by_cases hs : source K a h i j k = 0
  · simp [polynomial_apply, retained, erased, hs]
  · have hsupport := (source_ne_zero_iff i j k).mp hs
    have hmiddle := middleY_of_middleZ hsupport
    by_cases hy : MiddleY a h j.val <;> by_cases hz : MiddleZ a h k.val
    all_goals
      simp_all [polynomial_apply, retained, erased, totalWeight, firstWeight,
        secondWeight, thirdWeight, pow_two]

theorem polynomial_eq_X_mul_normalized (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) :
    polynomial K a h i j k = X * normalizedPolynomial K a h i j k := by
  classical
  rw [polynomial_identity, normalizedPolynomial]
  ring

theorem polynomial_coeff (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) (n : ℕ) :
    (polynomial K a h i j k).coeff n =
      (if n = 1 then retained K a h i j k else 0) +
      (if n = 2 then erased K a h i j k else 0) := by
  classical
  rw [polynomial_identity, Polynomial.coeff_add,
    mul_comm X (C (retained K a h i j k)),
    mul_comm (X ^ 2) (C (erased K a h i j k)),
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]

theorem leftMap_degree (a : ℕ) (output input : Fin a) :
    (leftMap K a output input).degree ≤ 0 := by
  classical
  by_cases heq : input = output <;> simp [leftMap, heq]

theorem middleMap_degree (a h : ℕ) (output input : YIndex a h) :
    (middleMap K a h output input).degree ≤ 1 := by
  classical
  by_cases heq : input = output <;> by_cases hy : MiddleY a h output.val <;>
    simp [middleMap, heq, hy]

theorem rightMap_degree (a h : ℕ) (output input : ZIndex a h) :
    (rightMap K a h output input).degree ≤ 1 := by
  classical
  by_cases heq : input = output <;> by_cases hz : MiddleZ a h output.val <;>
    simp [rightMap, heq, hz]

variable (K) in
open Classical in
/-- The three-sector construction is an actual polynomial restriction
degeneration in the existing tensor API, with leading order one. -/
def restriction (a h : ℕ) :
    Tensor.PolynomialRestrictionDegeneration (source K a h) (retained K a h) 1 0 1 1 where
  leftMap := leftMap K a
  middleMap := middleMap K a h
  rightMap := rightMap K a h
  left_degree := leftMap_degree a
  middle_degree := middleMap_degree a h
  right_degree := rightMap_degree a h
  vanishes := by
    intro i j k n hn
    change (polynomial K a h i j k).coeff n = 0
    rw [polynomial_coeff]
    have hn0 : n = 0 := by omega
    simp [hn0]
  leading := by
    intro i j k
    change (polynomial K a h i j k).coeff 1 = retained K a h i j k
    simp [polynomial_coeff]

@[simp] theorem restriction_basePolynomial (a h : ℕ) :
    (restriction K a h).basePolynomial = polynomial K a h := rfl

/-- Evaluation of the normalized family has exactly the paper's form. -/
theorem normalizedPolynomial_eval (a h : ℕ) (t : K) (i : Fin a)
    (j : YIndex a h) (k : ZIndex a h) :
    (normalizedPolynomial K a h i j k).eval t =
      retained K a h i j k + t * erased K a h i j k := by
  classical
  simp only [normalizedPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

/-- At nonzero parameters, the unshifted normalized polynomial is still an
ordinary restriction: divide the first local map by the parameter. -/
theorem normalizedPolynomial_eval_restriction (a h : ℕ) (t : K) (ht : t ≠ 0) :
    (fun i j k => (normalizedPolynomial K a h i j k).eval t) =
      Tensor.restrict
        (fun output input => if input = output then t⁻¹ else 0)
        (fun output input => (middleMap K a h output input).eval t)
        (fun output input => (rightMap K a h output input).eval t)
        (source K a h) := by
  classical
  funext i j k
  have hev := congrArg (fun p : Polynomial K => p.eval t)
    (polynomial_eq_X_mul_normalized a h i j k)
  simp only [Polynomial.eval_mul, Polynomial.eval_X] at hev
  have hscaled :
      Tensor.restrict
          (fun output input => if input = output then t⁻¹ else 0)
          (fun output input => (middleMap K a h output input).eval t)
          (fun output input => (rightMap K a h output input).eval t)
          (source K a h) i j k = t⁻¹ * (polynomial K a h i j k).eval t := by
    rw [polynomial_apply]
    simp only [middleMap, rightMap, apply_ite, Polynomial.eval_zero,
      Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
    simp [Tensor.restrict, ite_mul, mul_ite, mul_assoc]
  rw [hscaled, hev, ← mul_assoc, inv_mul_cancel₀ ht, one_mul]

end MatrixMultiplication.AuxiliarySeparation.Sector

end

end MatrixMultiplicationAllFields
