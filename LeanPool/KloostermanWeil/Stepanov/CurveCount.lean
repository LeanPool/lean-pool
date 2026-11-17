/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Counting points on a hyperelliptic curve

Relates points on `y² = f(x)` to quadratic-character sums and square/nonsquare fibers.
Compare Harcos (2015), equations (11)–(12), and Stepanov (1972).
-/

@[expose] public section

open scoped BigOperators

namespace KloostermanWeil.Stepanov

open Polynomial

/-- The finite set of affine points on `y² = f(x)`. -/
noncomputable def hyperellipticAffinePointFinset {F : Type*}
    [Field F] [Fintype F] (f : F[X]) : Finset (F × F) := by
  classical
  exact Finset.univ.filter fun z => z.2 ^ 2 = f.eval z.1

open Classical in
/-- Fiber decomposition of the affine point count. -/
theorem hyperellipticAffinePointFinset_card_fiber {F : Type*}
    [Field F] [Fintype F] (f : F[X]) :
    (hyperellipticAffinePointFinset f).card =
      ∑ x : F, (Finset.univ.filter fun y : F => y ^ 2 = f.eval x).card := by
  classical
  simp only [hyperellipticAffinePointFinset, Finset.card_filter,
    Fintype.sum_prod_type]

open Classical in
/-- The affine point count is `q + ∑ χ(f(x))`. -/
theorem hyperellipticAffinePoints_card {F : Type*}
    [Field F] [Fintype F] (hF : ringChar F ≠ 2) (f : F[X]) :
    ((hyperellipticAffinePointFinset f).card : ℤ) =
      (Fintype.card F : ℤ) + ∑ x : F, quadraticChar F (f.eval x) := by
  classical
  rw [hyperellipticAffinePointFinset_card_fiber]
  push_cast
  have hsqrt (x : F) :
      ((Finset.univ.filter fun y : F => y ^ 2 = f.eval x).card : ℤ) =
        quadraticChar F (f.eval x) + 1 := by
    simpa only [Set.toFinset_ofPred] using
      quadraticChar_card_sqrts hF (f.eval x)
  simp_rw [hsqrt]
  simp [Finset.sum_add_distrib, add_comm]

/-- Inputs on which the quadratic character has the specified integer value. -/
noncomputable def quadraticValueFinset {F : Type*}
    [Field F] [Fintype F] (f : F[X]) (a : ℤ) : Finset F := by
  classical
  exact Finset.univ.filter fun x => quadraticChar F (f.eval x) = a

open Classical in
/-- A quadratic-character sum is the number of square inputs minus the number
of nonsquare inputs. -/
theorem sum_quadraticChar_eq_card_one_sub_card_neg_one
    {F : Type*} [Field F] [Fintype F] (f : F[X]) :
    ∑ x : F, quadraticChar F (f.eval x) =
      (quadraticValueFinset f 1).card -
        (quadraticValueFinset f (-1)).card := by
  classical
  calc
    ∑ x : F, quadraticChar F (f.eval x) =
        ∑ x : F, (
          (if quadraticChar F (f.eval x) = 1 then (1 : ℤ) else 0) -
            (if quadraticChar F (f.eval x) = -1 then (1 : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rcases quadraticChar_isQuadratic F (f.eval x) with hzero | hsquare
      · simp [hzero]
      · rcases hsquare with hone | hneg
        · simp [hone]
        · simp [hneg]
    _ = (quadraticValueFinset f 1).card -
        (quadraticValueFinset f (-1)).card := by
      have hind (a : ℤ) :
          (∑ x : F, if quadraticChar F (f.eval x) = a then (1 : ℤ) else 0) =
            ((quadraticValueFinset f a).card : ℤ) := by
        simpa only [quadraticValueFinset] using
          (Finset.sum_boole (R := ℤ)
            (fun x : F => quadraticChar F (f.eval x) = a) Finset.univ)
      rw [Finset.sum_sub_distrib, hind 1, hind (-1)]

/-- Exact square-versus-nonsquare form of the affine point-count defect,
equation (12) in the Stepanov proof. -/
theorem hyperellipticAffinePoint_defect_eq
    {F : Type*} [Field F] [Fintype F]
    (hF : ringChar F ≠ 2) (f : F[X]) :
    ((hyperellipticAffinePointFinset f).card : ℤ) - Fintype.card F =
      (quadraticValueFinset f 1).card -
        (quadraticValueFinset f (-1)).card := by
  rw [hyperellipticAffinePoints_card hF f,
    sum_quadraticChar_eq_card_one_sub_card_neg_one f]
  ring

/-- Euler's criterion in the exact exponent convention used by the
Stepanov auxiliary polynomial. -/
theorem quadraticChar_eq_one_iff_pow_half
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (hqodd : Odd (Fintype.card F)) (z : F) :
    quadraticChar F z = 1 ↔
      z ^ ((Fintype.card F - 1) / 2) = 1 := by
  have hqhalf : Fintype.card F / 2 =
      (Fintype.card F - 1) / 2 := by
    obtain ⟨k, hk⟩ := hqodd
    omega
  rw [← hqhalf]
  by_cases hz : z = 0
  · subst z
    have hcard : 1 < Fintype.card F := Fintype.one_lt_card
    have he : Fintype.card F / 2 ≠ 0 :=
      (Nat.div_pos hcard (by omega)).ne'
    simp [zero_pow he]
  · rw [quadraticChar_eq_pow_of_char_ne_two hF hz]
    by_cases hp : z ^ (Fintype.card F / 2) = 1
    · simp [hp]
    · simp [hp]

/-- The nonsquare half of Euler's criterion in the Stepanov exponent
convention. -/
theorem quadraticChar_eq_neg_one_iff_pow_half
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (hqodd : Odd (Fintype.card F)) (z : F) :
    quadraticChar F z = -1 ↔
      z ^ ((Fintype.card F - 1) / 2) = -1 := by
  have hqhalf : Fintype.card F / 2 =
      (Fintype.card F - 1) / 2 := by
    obtain ⟨k, hk⟩ := hqodd
    omega
  rw [← hqhalf]
  by_cases hz : z = 0
  · subst z
    have hcard : 1 < Fintype.card F := Fintype.one_lt_card
    have he : Fintype.card F / 2 ≠ 0 :=
      (Nat.div_pos hcard (by omega)).ne'
    simp [zero_pow he]
  · rw [quadraticChar_eq_pow_of_char_ne_two hF hz]
    have hone : (1 : F) ≠ -1 :=
      (Ring.neg_one_ne_one_of_char_ne_two hF).symm
    by_cases hp : z ^ (Fintype.card F / 2) = 1
    · simp [hp, hone]
    · have hn := Or.resolve_left (FiniteField.pow_dichotomy hF hz) hp
      simp [hn, Ring.neg_one_ne_one_of_char_ne_two hF]

/-- The union of the zero-character fiber and one prescribed character
fiber, denoted `N₀ + Nₐ` in the source. -/
noncomputable def quadraticZeroOrValueFinset {F : Type*}
    [Field F] [Fintype F] (f : F[X]) (a : ℤ) : Finset F := by
  classical
  exact Finset.univ.filter fun x =>
    quadraticChar F (f.eval x) = 0 ∨ quadraticChar F (f.eval x) = a

/-- The same source fiber in the power-value convention consumed by the
Stepanov auxiliary polynomial. -/
noncomputable def stepanovValueFinset {F : Type*}
    [Field F] [Fintype F] (f : F[X]) (a : F) : Finset F := by
  classical
  exact Finset.univ.filter fun x =>
    f.eval x = 0 ∨ (f.eval x) ^ ((Fintype.card F - 1) / 2) = a

/-- The exact disjoint-cardinality decomposition `#(N₀ ∪ Nₐ)=N₀+Nₐ`. -/
theorem quadraticZeroOrValueFinset_card
    {F : Type*} [Field F] [Fintype F]
    (f : F[X]) {a : ℤ} (ha : a ≠ 0) :
    (quadraticZeroOrValueFinset f a).card =
      (quadraticValueFinset f 0).card +
        (quadraticValueFinset f a).card := by
  classical
  have hunion : quadraticZeroOrValueFinset f a =
      quadraticValueFinset f 0 ∪ quadraticValueFinset f a := by
    ext x
    simp only [quadraticZeroOrValueFinset, quadraticValueFinset,
      Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
  rw [hunion, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  · intro x hx0 hxa
    simp only [quadraticValueFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx0 hxa
    exact ha (hxa.symm.trans hx0)

/-- Euler's criterion identifies the source `N₀+N₁` fiber with the
power-value set used in equation (14). -/
theorem quadraticZeroOrOne_eq_stepanovValueFinset
    {F : Type*} [Field F] [Fintype F]
    (hF : ringChar F ≠ 2) (hqodd : Odd (Fintype.card F)) (f : F[X]) :
    quadraticZeroOrValueFinset f 1 = stepanovValueFinset f 1 := by
  classical
  ext x
  simp only [quadraticZeroOrValueFinset, stepanovValueFinset,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [quadraticChar_eq_zero_iff]
  exact or_congr Iff.rfl (quadraticChar_eq_one_iff_pow_half hF hqodd _)

/-- The analogous Euler-criterion bridge for the `N₀+N₋₁` fiber. -/
theorem quadraticZeroOrNegOne_eq_stepanovValueFinset
    {F : Type*} [Field F] [Fintype F]
    (hF : ringChar F ≠ 2) (hqodd : Odd (Fintype.card F)) (f : F[X]) :
    quadraticZeroOrValueFinset f (-1) = stepanovValueFinset f (-1) := by
  classical
  ext x
  simp only [quadraticZeroOrValueFinset, stepanovValueFinset,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [quadraticChar_eq_zero_iff]
  exact or_congr Iff.rfl
    (quadraticChar_eq_neg_one_iff_pow_half hF hqodd _)

/-- The three quadratic-character fibers partition the finite field. -/
theorem quadraticValueFinset_card_partition
    {F : Type*} [Field F] [Fintype F] (f : F[X]) :
    (quadraticValueFinset f 0).card +
      (quadraticValueFinset f 1).card +
        (quadraticValueFinset f (-1)).card = Fintype.card F := by
  classical
  let S0 := quadraticValueFinset f 0
  let S1 := quadraticValueFinset f 1
  let Sm := quadraticValueFinset f (-1)
  have h01 : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    simp only [S0, S1, quadraticValueFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx0 hx1
    omega
  have h01m : Disjoint (S0 ∪ S1) Sm := by
    rw [Finset.disjoint_left]
    intro x hx01 hxm
    simp only [Finset.mem_union] at hx01
    simp only [S0, S1, Sm, quadraticValueFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx01 hxm
    rcases hx01 with hx0 | hx1 <;> omega
  have hall : S0 ∪ S1 ∪ Sm = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    rcases quadraticChar_isQuadratic F (f.eval x) with h0 | hpm
    · left
      left
      simpa [S0, quadraticValueFinset] using h0
    · rcases hpm with h1 | hm
      · left
        right
        simpa [S1, quadraticValueFinset] using h1
      · right
        simpa [Sm, quadraticValueFinset] using hm
  rw [← Finset.card_univ, ← hall, Finset.card_union_of_disjoint h01m,
    Finset.card_union_of_disjoint h01]

end KloostermanWeil.Stepanov
