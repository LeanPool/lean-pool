/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum
public import LeanPool.AaronsonAmbainis.Bridge.Algebra

/-!
# `HasDegreeLE` and polynomials of bounded total degree

`HasDegreeLE f d` holds exactly when `f` is the restriction to the cube of a real polynomial
(`MvPolynomial ι ℝ`, not necessarily multilinear) of total degree at most `d`;
this is proved for both encodings of the cube (`hasDegreeLE_iff_poly_zo`,
`hasDegreeLE_iff_poly_pm`):

* `zoPt x`: `true ↦ 1`, `false ↦ 0`   (the cube `{0,1}^n` of Conjecture 6 of arXiv:0911.0996 and
  of Theorem 1.7 of arXiv:2410.19062);
* `pmPt x`: `true ↦ -1`, `false ↦ 1`  (the cube `{1,-1}^n` in the convention of `Defs.lean`; the
  statement `ExplicitBoundPM` of `Conjecture.lean` sends `true` to `1`, see `PrintedAA.lean`).
-/

@[expose] public section

namespace AaronsonAmbainis.Bridge

open Finset MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The point of `{0,1}^ι` attached to a point of the cube (`true ↦ 1`, `false ↦ 0`). -/
noncomputable def zoPt (x : Cube ι) : ι → ℝ := fun i => if x i then 1 else 0

/-- The point of `{1,-1}^ι` attached to a point of the cube (`true ↦ -1`, `false ↦ 1`). -/
noncomputable def pmPt (x : Cube ι) : ι → ℝ := fun i => if x i then -1 else 1

omit [DecidableEq ι] in
/-- Restricting a polynomial of total degree `≤ d` along a point map whose coordinates have
degree `≤ 1` gives a function of degree `≤ d`. -/
theorem hasDegreeLE_eval {v : Cube ι → ι → ℝ} (hv : ∀ i, HasDegreeLE (fun x => v x i) 1)
    (p : MvPolynomial ι ℝ) {d : ℕ} (hp : p.totalDegree ≤ d) :
    HasDegreeLE (fun x => MvPolynomial.eval (v x) p) d := by
  classical
  have h1 : (fun x => MvPolynomial.eval (v x) p)
      = fun x => ∑ m ∈ p.support, p.coeff m * ∏ i, v x i ^ m i := by
    funext x
    exact MvPolynomial.eval_eq' (v x) p
  rw [h1]
  refine hasDegreeLE_sum _ (fun m hm => hasDegreeLE_smul _ ?_)
  have h2 : ∑ i, m i ≤ d := by
    have h3 := MvPolynomial.le_totalDegree hm
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h3
    exact h3.trans hp
  refine hasDegreeLE_mono ?_ h2
  have h4 : HasDegreeLE (fun x => ∏ i, v x i ^ m i) (∑ i, m i * 1) :=
    hasDegreeLE_prod (univ : Finset ι) (F := fun i x => v x i ^ m i) (k := fun i => m i * 1)
      (fun i _ => hasDegreeLE_pow (hv i) (m i))
  simpa only [mul_one] using h4

omit [DecidableEq ι] in
theorem hasDegreeLE_eval_zo (p : MvPolynomial ι ℝ) {d : ℕ} (hp : p.totalDegree ≤ d) :
    HasDegreeLE (fun x : Cube ι => MvPolynomial.eval (zoPt x) p) d := by
  classical
  exact hasDegreeLE_eval (v := zoPt) hasDegreeLE_zo_coord p hp

omit [DecidableEq ι] in
theorem hasDegreeLE_eval_pm (p : MvPolynomial ι ℝ) {d : ℕ} (hp : p.totalDegree ≤ d) :
    HasDegreeLE (fun x : Cube ι => MvPolynomial.eval (pmPt x) p) d := by
  classical
  exact hasDegreeLE_eval (v := pmPt) hasDegreeLE_pm_coord p hp

omit [Fintype ι] [DecidableEq ι] in
theorem totalDegree_letter (a b : ℝ) (i : ι) :
    (C a + C b * X i : MvPolynomial ι ℝ).totalDegree ≤ 1 := by
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_C]
    exact Nat.zero_le 1
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add]

omit [DecidableEq ι] in
/-- A function of degree `≤ d` is the restriction of a polynomial of total degree `≤ d` in the
coordinates `v x i`, as soon as the sign `(-1)^{x_i}` is an affine function of `v x i`. -/
theorem exists_poly_of_hasDegreeLE {v : Cube ι → ι → ℝ} {a b : ℝ}
    (hv : ∀ x i, (if x i then (-1 : ℝ) else 1) = a + b * v x i)
    {f : Cube ι → ℝ} {d : ℕ} (h : HasDegreeLE f d) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ d ∧ ∀ x, f x = MvPolynomial.eval (v x) p := by
  obtain ⟨c, hc, hf⟩ := h
  refine ⟨∑ S : Finset ι, C (c S) * ∏ i ∈ S, (C a + C b * X i), ?_, fun x => ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le (fun S _ => ?_)
    by_cases hS : d < S.card
    · rw [hc S hS, C_0, zero_mul, MvPolynomial.totalDegree_zero]
      exact Nat.zero_le d
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
      refine (Finset.sum_le_sum (fun i _ => totalDegree_letter a b i)).trans ?_
      rw [Finset.sum_const, smul_eq_mul, mul_one]
      exact not_lt.mp hS
  · rw [hf x, map_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [map_mul, MvPolynomial.eval_C, map_prod]
    congr 1
    unfold chi
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_C, MvPolynomial.eval_X]
    exact hv x i

omit [DecidableEq ι] in
/-- `HasDegreeLE f d` iff `f` is a polynomial of total degree `≤ d` in the `0/1` coordinates. -/
theorem hasDegreeLE_iff_poly_zo {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE f d ↔
      ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ d ∧ ∀ x, f x = MvPolynomial.eval (zoPt x) p := by
  classical
  constructor
  · exact exists_poly_of_hasDegreeLE (a := 1) (b := -2)
      (fun x i => by unfold zoPt; split_ifs <;> norm_num)
  · rintro ⟨p, hp, hf⟩
    have h : f = fun x => MvPolynomial.eval (zoPt x) p := funext hf
    rw [h]
    exact hasDegreeLE_eval_zo p hp

omit [DecidableEq ι] in
/-- `HasDegreeLE f d` iff `f` is a polynomial of total degree `≤ d` in the `±1` coordinates. -/
theorem hasDegreeLE_iff_poly_pm {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE f d ↔
      ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ d ∧ ∀ x, f x = MvPolynomial.eval (pmPt x) p := by
  classical
  constructor
  · exact exists_poly_of_hasDegreeLE (a := 0) (b := 1)
      (fun x i => by unfold pmPt; split_ifs <;> norm_num)
  · rintro ⟨p, hp, hf⟩
    have h : f = fun x => MvPolynomial.eval (pmPt x) p := funext hf
    rw [h]
    exact hasDegreeLE_eval_pm p hp

end AaronsonAmbainis.Bridge
