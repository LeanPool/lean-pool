/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.FitnessLevel

/-!
Stage 110 (A1 random initialization) promotion-preparation source: exact binomial average over
uniform
initial states. This is a finite combinatorial identity and does not itself
prove the probabilistic hitting-time interpretation; that follows from A1.
Source: Doerr--Doerr (2013), Collecting Coupons with Random Initial Stake.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- Count the initial strings with exactly k zero bits. -/
theorem bitStrings_zeroCount_card_eq_choose
    (n k : Nat) :
    (Finset.univ.filter (fun x : BitString n => zeroCount x = k)).card =
      Nat.choose n k := by
  classical
  let decode : Finset (Fin n) → BitString n :=
    fun s i => if i ∈ s then false else true
  have hinverse (s : Finset (Fin n)) : zeroPositions (decode s) = s := by
    ext i
    by_cases hi : i ∈ s <;> simp [decode, zeroPositions, hi]
  have hcount :
      (Finset.univ.filter (fun x : BitString n => zeroCount x = k)).card =
        (Finset.powersetCard k (Finset.univ : Finset (Fin n))).card := by
    refine Finset.card_bij (fun x _ => zeroPositions x) ?_ ?_ ?_
    · intro x hx
      refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
      have hz : zeroCount x = k := (Finset.mem_filter.mp hx).2
      simpa [zeroPositions_card] using hz
    · intro x hx y hy heq
      funext i
      have hiff : x i = false ↔ y i = false := by
        have hm := congrArg (fun s : Finset (Fin n) => i ∈ s) heq
        simpa [mem_zeroPositions] using hm
      cases hxi : x i <;> cases hyi : y i <;> simp_all
    · intro s hs
      refine ⟨decode s, ?_, hinverse s⟩
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · have hc : s.card = k := (Finset.mem_powersetCard.mp hs).2
        simpa [← zeroPositions_card, hinverse] using hc
  simpa using hcount.trans (by simp)

/-- Exact uniform average of the harmonic values proposed for deterministic-start RLS.
The runtime convention counts mutation iterations, not the initial evaluation. -/
theorem rlsLinear_uniformInitial_harmonic_average
    (n : Nat) :
    ((Finset.univ.sum (fun x : BitString n =>
        (n : Real) * harmonicReal (zeroCount x))) /
        (2 : Real) ^ n) =
      ((n : Real) / (2 : Real) ^ n) *
        (Finset.sum (Finset.range (n + 1))
          (fun k => (Nat.choose n k : Real) * harmonicReal k)) := by
  classical
  have hpartition :
      (∑ x : BitString n, harmonicReal (zeroCount x)) =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : Real) * harmonicReal k := by
    calc
      (∑ x : BitString n, harmonicReal (zeroCount x)) =
          ∑ x : BitString n,
            ∑ k ∈ Finset.range (n + 1),
              if zeroCount x = k then harmonicReal k else 0 := by
                apply Finset.sum_congr rfl
                intro x _
                have hx : zeroCount x ∈ Finset.range (n + 1) :=
                  Finset.mem_range.mpr (by have h := zeroCount_le x; omega)
                simp [hx]
      _ = ∑ k ∈ Finset.range (n + 1),
            ∑ x : BitString n,
              if zeroCount x = k then harmonicReal k else 0 := by
                rw [Finset.sum_comm]
      _ = ∑ k ∈ Finset.range (n + 1),
            (Nat.choose n k : Real) * harmonicReal k := by
                apply Finset.sum_congr rfl
                intro k _
                calc
                  (∑ x : BitString n,
                      if zeroCount x = k then harmonicReal k else 0) =
                      ∑ x ∈ Finset.univ.filter
                        (fun x : BitString n => zeroCount x = k),
                        harmonicReal k := by
                          rw [Finset.sum_filter]
                  _ = ((Finset.univ.filter
                        (fun x : BitString n => zeroCount x = k)).card : Real) *
                        harmonicReal k := by rw [Finset.sum_const, nsmul_eq_mul]
                  _ = (Nat.choose n k : Real) * harmonicReal k := by
                    rw [bitStrings_zeroCount_card_eq_choose]
  rw [← Finset.mul_sum, hpartition]
  ring

end ECRuntime
