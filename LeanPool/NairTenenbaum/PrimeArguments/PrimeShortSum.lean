/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentDecomposition

/-! # The sum over prime arguments in a real interval -/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

/-- The left side of Theorem 3. -/
noncomputable def primeShortSum {k : ℕ} (Q : Fin k → ℤ[X])
    (F : ArithmeticMap k) (x y : ℝ) : ℝ :=
  ∑ p ∈ (shortInterval x y).filter Nat.Prime,
    extendArithmeticMap F (fun j => ((Q j).eval (p : ℤ)).natAbs)

theorem PolynomialSystem.primeShortSum_eq_primeIntegerSum {k r : ℕ}
    (P : PolynomialSystem k r) (F : ArithmeticMap k) {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    primeShortSum P.Q F x y =
      P.primeIntegerSum F x (⌊x⌋₊ : ℤ) (⌊x + y⌋₊ : ℤ) := by
  classical
  unfold primeIntegerSum primeShortSum
  rw [← shortInterval_natCast_image, filter_image]
  have hfilter : (shortInterval x y).filter
      (fun n : ℕ => (n : ℤ).natAbs.Prime ∧ x < ((n : ℤ).natAbs : ℝ)) =
      (shortInterval x y).filter Nat.Prime := by
    apply filter_congr
    intro n hn
    have hxn : x < (n : ℝ) := (Nat.floor_lt hx).mp (mem_Ioc.mp hn).1
    simp only [Int.natAbs_natCast, hxn, and_true]
  rw [hfilter, sum_image (fun a _ b _ h => Int.natCast_inj.mp h)]

end NairTenenbaum
