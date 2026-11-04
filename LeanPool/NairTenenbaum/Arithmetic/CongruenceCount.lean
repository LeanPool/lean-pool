/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Polynomials.RootCount
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.CardIntervalMod

/-! # Congruence counts in intervals

The elementary distribution estimate needed as input to the polynomial sieve:
`|#{a < n ≤ b : q ∣ Q(n)} - (b-a)ρ_Q(q)/q| ≤ ρ_Q(q)`.
No primality or squarefreeness assumption on the positive modulus is needed.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

/-- The count of one residue class differs from interval length divided by its
modulus by at most one. Integer endpoints may be negative. -/
theorem residue_count_error (a b v : ℤ) (hab : a ≤ b) {q : ℕ} (hq : 0 < q) :
    |(((Finset.Ioc a b).filter fun n => Int.ModEq (q : ℤ) n v).card : ℝ) -
      ((b : ℝ) - a) / q| ≤ 1 := by
  have h := Int.Ioc_filter_modEq_card a b (r := q) (by exact_mod_cast hq) v
  let u : ℚ := (a - v : ℤ) / (q : ℤ)
  let w : ℚ := (b - v : ℤ) / (q : ℤ)
  have hq' : (0 : ℚ) < (q : ℤ) := by exact_mod_cast hq
  have huw : u ≤ w := by
    apply div_le_div_of_nonneg_right _ hq'.le
    exact_mod_cast sub_le_sub_right hab v
  have hfloor : ⌊u⌋ ≤ ⌊w⌋ := Int.floor_mono huw
  have hfloor' : 0 ≤ ⌊((b : ℚ) - v) / (q : ℤ)⌋ - ⌊((a : ℚ) - v) / (q : ℤ)⌋ := by
    simpa only [u, w, Int.cast_sub] using sub_nonneg.mpr hfloor
  rw [max_eq_left hfloor'] at h
  have hcard : (((Finset.Ioc a b).filter fun n => Int.ModEq (q : ℤ) n v).card : ℤ) =
      ⌊w⌋ - ⌊u⌋ := by
    simpa only [u, w, Int.cast_sub] using h
  have hgap : w - u = ((b : ℚ) - a) / q := by dsimp [w, u]; push_cast; ring
  have herror : |((⌊w⌋ - ⌊u⌋ : ℤ) : ℚ) - ((b : ℚ) - a) / q| ≤ 1 := by
    have h₁ := Int.floor_le w
    have h₂ := Int.lt_floor_add_one w
    have h₃ := Int.floor_le u
    have h₄ := Int.lt_floor_add_one u
    rw [abs_le]
    push_cast
    constructor <;> linarith
  have hcard' : (((Finset.Ioc a b).filter fun n => Int.ModEq (q : ℤ) n v).card : ℝ) =
      ((⌊w⌋ - ⌊u⌋ : ℤ) : ℝ) := by exact_mod_cast hcard
  rw [hcard']
  have hreal := (Rat.cast_le (K := ℝ)).mpr herror
  push_cast at hreal ⊢
  exact hreal

/-- The roots as a finite set, for a positive modulus. -/
def residueRootSet (Q : ℤ[X]) (q : ℕ) [NeZero q] : Finset (ZMod q) :=
  Finset.univ.filter fun a => Q.eval₂ (Int.castRingHom _) a = 0

theorem residueRootSet_card (Q : ℤ[X]) (q : ℕ) [NeZero q] :
    (residueRootSet Q q).card = rootCount Q q := (rootCount_eq_card_filter Q q).symm

theorem cast_mem_residueRootSet (Q : ℤ[X]) (q : ℕ) [NeZero q] (n : ℤ) :
    (n : ZMod q) ∈ residueRootSet Q q ↔ (q : ℤ) ∣ Q.eval n := by
  simp only [residueRootSet, Finset.mem_filter, Finset.mem_univ, true_and]
  change Q.eval₂ (Int.castRingHom (ZMod q)) ((Int.castRingHom (ZMod q)) n) = 0 ↔ _
  rw [Polynomial.eval₂_at_apply]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

/-- Polynomial congruences in `(a,b]`. -/
noncomputable def polynomialCongruenceCount (Q : ℤ[X]) (q : ℕ) (a b : ℤ) : ℕ :=
  ((Finset.Ioc a b).filter fun n => (q : ℤ) ∣ Q.eval n).card

theorem polynomialCongruenceCount_eq_sum (Q : ℤ[X]) (q : ℕ) [NeZero q] (a b : ℤ) :
    polynomialCongruenceCount Q q a b =
      ∑ r ∈ residueRootSet Q q,
        ((Finset.Ioc a b).filter fun n => Int.ModEq (q : ℤ) n r.val).card := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.Ioc a b) (residueRootSet Q q)
    (fun n : ℤ => (n : ZMod q))
  simp only [cast_mem_residueRootSet] at h
  rw [polynomialCongruenceCount, ← h]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  apply Finset.filter_congr
  intro n _
  have heq := ZMod.intCast_eq_intCast_iff n (r.val : ℤ) q
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using heq

/-- The interval distribution estimate for polynomial congruences. -/
theorem polynomialCongruenceCount_error (Q : ℤ[X]) {q : ℕ} (hq : 0 < q)
    (a b : ℤ) (hab : a ≤ b) :
    |(polynomialCongruenceCount Q q a b : ℝ) -
      ((b : ℝ) - a) * rootCount Q q / q| ≤ rootCount Q q := by
  let : NeZero q := ⟨hq.ne'⟩
  let S := residueRootSet Q q
  let L : ℝ := ((b : ℝ) - a) / q
  let c : ZMod q → ℝ := fun r =>
    (((Finset.Ioc a b).filter fun n => Int.ModEq (q : ℤ) n r.val).card : ℝ)
  have hc : (polynomialCongruenceCount Q q a b : ℝ) = ∑ r ∈ S, c r := by
    rw [polynomialCongruenceCount_eq_sum, Nat.cast_sum]
  have hS : (S.card : ℝ) = rootCount Q q := by exact_mod_cast residueRootSet_card Q q
  have herr : |∑ r ∈ S, (c r - L)| ≤ S.card := by
    calc
      _ ≤ ∑ r ∈ S, |c r - L| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ S, (1 : ℝ) := Finset.sum_le_sum fun r _ => residue_count_error a b r.val hab hq
      _ = S.card := by simp
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hS] at herr
  rw [hc]
  convert herr using 2
  dsimp [L]
  ring

end NairTenenbaum
