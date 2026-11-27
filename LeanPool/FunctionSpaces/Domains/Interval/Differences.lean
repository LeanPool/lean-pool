/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Differences.Differences
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Analysis.Complex.Basic

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Differences of higher order

The **difference of order `r` with step `h`** of `f : ℝ → ℂ` is

`Δ_h^r f(x) = ∑_{k=0}^r (-1)^(r-k) C(r,k) f(x + k h)`   (`Interval.higherDiff_apply`),

the `r`-fold iterate `Rd.higherDiff r h f` of Mathlib's forward difference `fwdDiff h`
(`Δ_h f(x) = f(x + h) - f(x)`).
It is linear in `f` and commutes with translations (Mathlib's `fwdDiff_iter_add`,
`fwdDiff_iter_const_smul`, `fwdDiff_iter_comp_add`), and it is invariant up to sign and shift
under the reflection `x ↦ c - x`.  Its coefficients have modulus `C(r, k)`, so
`|Δ_h^r f(x)| ≤ 2^r max_k |f(x + k h)|` (`Interval.enorm_higherDiff_le_of_forall`).  Differences
of order `r` annihilate the **polynomials of degree `< r`** (`Interval.higherDiff_polynomial`),
which is why they measure smoothness of order `r`; this comes from Mathlib's
`Polynomial.fwdDiff_iter_eq_zero_of_degree_lt` (step `1`) after the change of variable `x + k h`,
which keeps the degree `< r` (`Interval.comp_affine_mem_degreeLT`).  Polynomials are elements of
Mathlib's `Polynomial.degreeLT ℂ r`, evaluated at real points.
-/

@[expose] public section

open Finset Polynomial
open Rd (higherDiff higherDiff_def)
open scoped ENNReal

namespace Interval

/-- `Δ_h^r f(x) = ∑_{k=0}^r (-1)^(r-k) C(r,k) f(x + k h)`. -/
theorem higherDiff_apply (r : ℕ) (h : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    higherDiff r h f x =
      ∑ k ∈ range (r + 1), ((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) * f (x + k * h) := by
  rw [higherDiff_def, Rd.higherDiff_apply]
  simp only [smul_eq_mul]

/-- `Δ_h^r f = ∑_{k=0}^r (-1)^(r-k) C(r,k) f(· + k h)`, as an identity of functions: a sum of
multiples of translates of `f`. -/
theorem higherDiff_eq_sum_smul (r : ℕ) (h : ℝ) (f : ℝ → ℂ) :
    higherDiff r h f =
      ∑ k ∈ range (r + 1), ((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) • fun x => f (x + k * h) := by
  funext x
  rw [higherDiff_apply, Finset.sum_apply]
  rfl

/-- `Δ_h^0 f = f`. -/
@[simp] theorem higherDiff_zero (h : ℝ) (f : ℝ → ℂ) : higherDiff 0 h f = f := rfl

/-- `Δ_h^(r+1) f(x) = Δ_h^r f(x + h) - Δ_h^r f(x)`. -/
theorem higherDiff_succ (r : ℕ) (h : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    higherDiff (r + 1) h f x = higherDiff r h f (x + h) - higherDiff r h f x := by
  rw [higherDiff, Function.iterate_succ_apply']
  rfl

/-- `Δ_h^(r+1) f = Δ_h^r (Δ_h f)`. -/
theorem higherDiff_succ' (r : ℕ) (h : ℝ) (f : ℝ → ℂ) :
    higherDiff (r + 1) h f = higherDiff r h (fwdDiff h f) := by
  rw [higherDiff, Function.iterate_succ_apply]
  rfl

/-- Differences are additive (Mathlib's `fwdDiff_iter_add`). -/
theorem higherDiff_add (r : ℕ) (h : ℝ) (f g : ℝ → ℂ) :
    higherDiff r h (f + g) = higherDiff r h f + higherDiff r h g :=
  fwdDiff_iter_add h f g r

/-- Differences commute with subtraction. -/
theorem higherDiff_sub (r : ℕ) (h : ℝ) (f g : ℝ → ℂ) :
    higherDiff r h (f - g) = higherDiff r h f - higherDiff r h g := by
  funext x
  simp only [higherDiff_apply, Pi.sub_apply, mul_sub, sum_sub_distrib]

/-- Differences are homogeneous (Mathlib's `fwdDiff_iter_const_smul`). -/
theorem higherDiff_const_mul (r : ℕ) (h : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    higherDiff r h (fun x => c * f x) = fun x => c * higherDiff r h f x :=
  fwdDiff_iter_const_smul h c f r

/-- Differences commute with translations: `Δ_h^r (f(· + c))(x) = Δ_h^r f(x + c)` (Mathlib's
`fwdDiff_iter_comp_add`). -/
theorem higherDiff_comp_add (r : ℕ) (h : ℝ) (f : ℝ → ℂ) (c x : ℝ) :
    higherDiff r h (fun y => f (y + c)) x = higherDiff r h f (x + c) :=
  fwdDiff_iter_comp_add h f c r x

/-- **Reflection**: for `g(x) = f(c - x)`, `Δ_h^r g(x) = (-1)^r Δ_h^r f(c - x - r h)`. -/
theorem higherDiff_reflect (r : ℕ) (h : ℝ) (f : ℝ → ℂ) (c x : ℝ) :
    higherDiff r h (fun y => f (c - y)) x = (-1 : ℂ) ^ r * higherDiff r h f (c - x - r * h) := by
  simp only [higherDiff_apply, mul_sum]
  rw [← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ r := Nat.lt_succ_iff.1 (mem_range.1 hk)
  rw [show r + 1 - 1 - k = r - k by omega, Nat.choose_symm hk', show r - (r - k) = k by omega]
  have hx : c - (x + ((r - k : ℕ) : ℝ) * h) = c - x - r * h + k * h := by
    rw [Nat.cast_sub hk']; ring
  rw [hx, ← Rd.neg_one_pow_mul_neg_one_pow_sub hk']
  ring

/-- **The coefficients of a difference**: `‖(-1)^(r-k) C(r, k)‖ = C(r, k)`. -/
theorem enorm_higherDiff_coeff (r k : ℕ) :
    ‖(-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)‖ₑ = (r.choose k : ℝ≥0∞) := by
  rw [eNorm_mul, eNorm_pow, eNorm_neg, eNorm_one, one_pow, one_mul, ← ofReal_norm,
    Complex.norm_natCast, ENNReal.ofReal_natCast]

/-- **Pointwise bound for differences**: if `|f(x + k h)| ≤ B` for `k ≤ r`, then
`|Δ_h^r f(x)| ≤ 2^r B`, since the coefficients `C(r, k)` add up to `2^r`. -/
theorem enorm_higherDiff_le_of_forall {r : ℕ} {h x : ℝ} {f : ℝ → ℂ} {B : ℝ≥0∞}
    (hB : ∀ k ∈ range (r + 1), ‖f (x + k * h)‖ₑ ≤ B) : ‖higherDiff r h f x‖ₑ ≤ 2 ^ r * B := by
  rw [higherDiff_apply]
  refine (eNorm_sum_le _ _).trans ?_
  calc ∑ k ∈ range (r + 1), ‖(-1 : ℂ) ^ (r - k) * (r.choose k : ℂ) * f (x + k * h)‖ₑ
      ≤ ∑ k ∈ range (r + 1), (r.choose k : ℝ≥0∞) * B :=
        sum_le_sum fun k hk => by
          rw [eNorm_mul, enorm_higherDiff_coeff]
          exact mul_le_mul_right (hB k hk) _
    _ = 2 ^ r * B := by
        rw [← sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        rfl

/-- **Affine changes of variable do not raise the degree**:
`deg P(u + v X) ≤ deg P`, since `deg (P ∘ Q) ≤ deg P · deg Q` (Mathlib's `natDegree_comp_le`). -/
theorem natDegree_comp_affine_le (P : ℂ[X]) (u v : ℂ) :
    (P.comp (C u + C v * X)).natDegree ≤ P.natDegree := by
  have h1 : (C u + C v * X).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp)))
  calc (P.comp (C u + C v * X)).natDegree ≤ P.natDegree * (C u + C v * X).natDegree :=
        natDegree_comp_le
    _ ≤ P.natDegree * 1 := Nat.mul_le_mul_left _ h1
    _ = P.natDegree := mul_one _

/-- **Affine changes of variable** keep the degree `< r`. -/
theorem comp_affine_mem_degreeLT {r : ℕ} {P : ℂ[X]} (hP : P ∈ degreeLT ℂ r) (u v : ℂ) :
    P.comp (C u + C v * X) ∈ degreeLT ℂ r := by
  rcases eq_or_ne P 0 with rfl | hP0
  · simp
  rw [mem_degreeLT] at hP ⊢
  refine degree_le_natDegree.trans_lt ?_
  exact_mod_cast (natDegree_comp_affine_le P u v).trans_lt ((natDegree_lt_iff_degree_lt hP0).2 hP)

/-- **Differences of order `r` annihilate polynomials of degree `< r`**:
`Δ_h^r P = 0` for `P ∈ degreeLT ℂ r`. -/
theorem higherDiff_polynomial {r : ℕ} {P : ℂ[X]} (hP : P ∈ degreeLT ℂ r) (h : ℝ) :
    higherDiff r h (fun x => P.eval (x : ℂ)) = 0 := by
  funext x
  rcases eq_or_ne P 0 with rfl | hP0
  · simp [higherDiff_apply]
  set Q : ℂ[X] := P.comp (C (x : ℂ) + C (h : ℂ) * X)
  have hdeg : Q.natDegree < r := (natDegree_comp_affine_le P _ _).trans_lt
    ((natDegree_lt_iff_degree_lt hP0).2 (mem_degreeLT.1 hP))
  have hzero := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg) 0
  rw [fwdDiff_iter_eq_sum_shift] at hzero
  rw [higherDiff_apply, Pi.zero_apply]
  rw [Pi.zero_apply] at hzero
  rw [← hzero]
  refine sum_congr rfl fun k _ => ?_
  rw [zsmul_eq_mul, nsmul_eq_mul, mul_one, zero_add, eval_comp]
  simp only [eval_add, eval_C, eval_mul, eval_X]
  push_cast
  ring_nf

end Interval
