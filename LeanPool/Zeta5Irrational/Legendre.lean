/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Construction
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # The `p`-adic valuation of `S_K` (5.3)

`v_p(S_K) = 2h v_p(K!) - 12h v_p(N!) - 2 ∑_{i=1}^{h-1} v_p((2i)!) + (h-1) v_p(4)`,
where each factorial valuation is given by Legendre's formula (`multiplicity_factorial`).
-/

@[expose] public section

open Finset

namespace Zeta5Irrational

/-- `v_p(S_K)`. -/
noncomputable def vSK (n p : ℕ) : ℤ :=
  padicValRat p (S n)

lemma padicValNat_finset_prod (p : ℕ) [hp : Fact p.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) : padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  simp_rw [Nat.padicValNat_def]
  classical
    induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Nat.multiplicity_mul (hf a (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- `S_K` as a quotient of natural numbers. -/
lemma S_eq_div (n : ℕ) :
    S n =
      (((40 * n).factorial ^ (2 * (37 * n)) * 4 ^ (37 * n - 1) : ℕ) : ℚ) /
        (((3 * n).factorial ^ (12 * (37 * n)) * ∏ i ∈ Icc 1 (37 * n - 1), (2 * i).factorial ^ 2 :
            ℕ) :
          ℚ) := by
  unfold S
  push_cast
  ring

/-- **(5.3)**: the valuation of `S_K` in terms of factorial valuations. -/
theorem vS_eq {n : ℕ} (hn : 0 < n) {p : ℕ} (hp : p.Prime) :
    vSK n p =
      2 * (37 * n : ℤ) * padicValNat p (40 * n).factorial -
            12 * (37 * n : ℤ) * padicValNat p (3 * n).factorial -
          2 * ∑ i ∈ Icc 1 (37 * n - 1), (padicValNat p (2 * i).factorial : ℤ) +
        ((37 * n : ℤ) - 1) * padicValNat p 4 := by
  have := Fact.mk hp
  unfold vSK
  rw [S_eq_div]
  have hA : (((40 * n).factorial ^ (2 * (37 * n)) * 4 ^ (37 * n - 1) : ℕ) : ℚ) ≠ 0 := by
    norm_cast; positivity
  have hB :
    (((3 * n).factorial ^ (12 * (37 * n)) * ∏ i ∈ Icc 1 (37 * n - 1), (2 * i).factorial ^ 2 : ℕ) :
        ℚ) ≠
      0 := by
    norm_cast
    apply mul_ne_zero (by positivity)
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
  have hprod := padicValNat_finset_prod p (Icc 1 (37 * n - 1))
    (fun i => (2 * i).factorial ^ 2) (fun i _ => by positivity)
  simp_rw [Nat.padicValNat_def] at hprod ⊢
  rw [padicValRat.div hA hB, ← padicValRat_of_nat, ← padicValRat_of_nat,
    Nat.multiplicity_mul (by positivity) (by positivity),
    Nat.multiplicity_mul (by positivity) (Finset.prod_ne_zero_iff.mpr fun i _ => by positivity),
    Nat.multiplicity_pow, Nat.multiplicity_pow, Nat.multiplicity_pow, hprod]
  simp only [Nat.multiplicity_pow]
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ 37 * n)]
  push_cast
  simp only [Finset.mul_sum]
  ring

end Zeta5Irrational
