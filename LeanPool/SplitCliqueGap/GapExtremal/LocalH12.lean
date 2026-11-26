/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs

/-!
# The local lemma for the gadget `H12` (ledger §6, L6.1)

`H12` has the twelve edges `01,12,23,45,04,05,14,15,24,25,34,35` on `Fin 6`. For a set `Q` of
colours put
`w(Q) = 2 e_H(Q) - C(|Q|,2) - 1`. The reserved integer bound (1) of the ledger, multiplied by 4,
reads

  `∑_{Q ∈ P} (4 w(Q) - e_H(Q)) ≤ 20`   for every packing `P` (pairwise intersections of size `≤ 1`).

`local_bound` proves it on `Fin 6`; `local_bound_emb` transports it to any colour type `C` along an
embedding `σ : Fin 6 ↪ C`, the remaining colours being isolated (the isolation lemma of L6.1).
-/

@[expose] public section

namespace GapExtremal.H12

open Finset

/-- Adjacency of `H12`. -/
def adj (i j : Fin 6) : Bool :=
  match i.val, j.val with
  | 0, 1 | 1, 2 | 2, 3 | 4, 5 | 0, 4 | 0, 5 | 1, 4 | 1, 5 | 2, 4 | 2, 5 | 3, 4 | 3, 5 => true
  | _, _ => false

/-- Number of `H12` edges inside `Q` (pairs `i < j`). -/
def eH (Q : Finset (Fin 6)) : ℕ := ((Q ×ˢ Q).filter (fun p => p.1 < p.2 ∧ adj p.1 p.2 = true)).card

/-- The reserved local objective `4 w(Q) - e_H(Q)` with `w(Q) = 2 e_H(Q) - C(|Q|,2) - 1`. -/
def f (Q : Finset (Fin 6)) : ℤ := 4 * (2 * (eH Q : ℤ) - (Q.card.choose 2 : ℤ) - 1) - eH Q

/-- The pieces with positive objective. -/
def pos : Finset (Finset (Fin 6)) := univ.filter (fun Q => 0 < f Q)

theorem three_le_card_of_pos : ∀ Q ∈ pos, 3 ≤ Q.card := by decide +kernel

/-- Compatibility of two pieces in a packing. -/
def Compat (Q Q' : Finset (Fin 6)) : Prop := (Q ∩ Q').card ≤ 1

instance : DecidableRel Compat := fun _ _ => inferInstanceAs (Decidable (_ ≤ _))

theorem no_four : ∀ a ∈ pos, ∀ b ∈ pos, a ≠ b → Compat a b → ∀ c ∈ pos, a ≠ c → b ≠ c →
    Compat a c → Compat b c → ∀ d ∈ pos, a ≠ d → b ≠ d → c ≠ d → Compat a d → Compat b d →
    ¬ Compat c d := by
  decide +kernel

theorem triple_bound : ∀ a ∈ pos, ∀ b ∈ pos, a ≠ b → Compat a b → ∀ c ∈ pos, a ≠ c → b ≠ c →
    Compat a c → Compat b c → f a + f b + f c ≤ 20 := by
  decide +kernel

theorem pair_bound : ∀ a ∈ pos, ∀ b ∈ pos, a ≠ b → Compat a b → f a + f b ≤ 20 := by
  decide +kernel

theorem single_bound : ∀ a ∈ pos, f a ≤ 20 := by decide +kernel

/-- Packings of positive pieces have at most three members. -/
theorem card_le_three {T : Finset (Finset (Fin 6))} (hTp : T ⊆ pos)
    (hT : ∀ Q ∈ T, ∀ Q' ∈ T, Q ≠ Q' → Compat Q Q') : T.card ≤ 3 := by
  by_contra h
  push Not at h
  obtain ⟨U, hUT, hU⟩ := Finset.exists_subset_card_eq (show 4 ≤ T.card by omega)
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.mp hU
  have m : ∀ x ∈ ({a, b, c, d} : Finset (Finset (Fin 6))), x ∈ T := fun x hx => hUT hx
  have ha := m a (by simp); have hb := m b (by simp); have hc := m c (by simp); have hd :=
    m d (by simp)
  exact no_four a (hTp ha) b (hTp hb) hab (hT a ha b hb hab) c (hTp hc) hac hbc (hT a ha c hc hac)
    (hT b hb c hc hbc) d (hTp hd) had hbd hcd (hT a ha d hd had) (hT b hb d hd hbd) (hT c hc d hd
      hcd)

/-- **L6.1 on `Fin 6`.** -/
theorem local_bound (T : Finset (Finset (Fin 6)))
    (hT : ∀ Q ∈ T, ∀ Q' ∈ T, Q ≠ Q' → Compat Q Q') : ∑ Q ∈ T, f Q ≤ 20 := by
  set T' := T.filter (fun Q => 0 < f Q) with hT'
  have hle : ∑ Q ∈ T, f Q ≤ ∑ Q ∈ T', f Q := by
    rw [hT', Finset.sum_filter]
    exact Finset.sum_le_sum fun Q _ => by split_ifs with h <;> [exact le_rfl; exact not_lt.mp h]
  have hTp : T' ⊆ pos := fun Q hQ => by
    simp only [hT', Finset.mem_filter] at hQ
    simpa [pos] using hQ.2
  have hT'c : ∀ Q ∈ T', ∀ Q' ∈ T', Q ≠ Q' → Compat Q Q' := fun Q hQ Q' hQ' hne =>
    hT Q (Finset.mem_of_mem_filter Q hQ) Q' (Finset.mem_of_mem_filter Q' hQ') hne
  have hcard := card_le_three hTp hT'c
  refine hle.trans ?_
  interval_cases h : T'.card
  · rw [Finset.card_eq_zero.mp h]; simp
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
    rw [ha, Finset.sum_singleton]
    exact single_bound a (hTp (by simp [ha]))
  · obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp h
    rw [he, Finset.sum_pair hab]
    have ha : a ∈ T' := by simp [he]
    have hb : b ∈ T' := by simp [he]
    exact pair_bound a (hTp ha) b (hTp hb) hab (hT'c a ha b hb hab)
  · obtain ⟨a, b, c, hab, hac, hbc, he⟩ := Finset.card_eq_three.mp h
    have ha : a ∈ T' := by simp [he]
    have hb : b ∈ T' := by simp [he]
    have hc : c ∈ T' := by simp [he]
    rw [he, Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc, ← add_assoc]
    exact triple_bound a (hTp ha) b (hTp hb) hab (hT'c a ha b hb hab) c (hTp hc) hac hbc
      (hT'c a ha c hc hac) (hT'c b hb c hc hbc)

end GapExtremal.H12
