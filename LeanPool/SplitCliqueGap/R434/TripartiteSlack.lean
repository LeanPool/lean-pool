/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.ResidualArithmetic
public import LeanPool.SplitCliqueGap.R434.ExactGraphTransfer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-! Edge counts and the zero-slack cases for tripartite pieces. -/

@[expose] public section

open Finset

namespace GapExtremal.R434

theorem slack_of_tripartite_counts (v e : ℕ) (hv : 2 ≤ v) (he : 3 * e ≤ v ^ 2) :
    let s := ((v.choose 2 : ℕ) : ℝ) + 1 - 4 * (e : ℝ) / 3
    0 ≤ s ∧ (s = 0 → (v = 3 ∧ e = 3) ∨ (v = 6 ∧ e = 12)) ∧
      (s ≠ 0 → (e : ℝ) ≤ 27 * s) := by
  dsimp only
  by_cases hv9 : 9 ≤ v
  · have hchooseN : v.choose 2 * 2 = v * (v - 1) := by
      simpa using (Nat.choose_mul (n := v) (k := 2) (s := 1) (by decide))
    have hchooseR : (v.choose 2 : ℝ) * 2 = (v : ℝ) * ((v : ℝ) - 1) := by
      have hcast : (v.choose 2 : ℝ) * 2 = (v : ℝ) * ((v - 1 : ℕ) : ℝ) := by
        exact_mod_cast hchooseN
      rwa [Nat.cast_sub (by omega : 1 ≤ v), Nat.cast_one] at hcast
    have hvR : (9 : ℝ) ≤ v := by exact_mod_cast hv9
    have heR : (3 : ℝ) * e ≤ (v : ℝ) ^ 2 := by exact_mod_cast he
    obtain ⟨hs, hse⟩ := large_tripartite_slack (v : ℝ) (e : ℝ) hvR (by positivity) heR
    refine ⟨by linarith, fun hz => False.elim (by linarith), fun _ => ?_⟩
    linarith
  · have hv8 : v ≤ 8 := by omega
    have he21 : e < 22 := by
      have hs : v ^ 2 ≤ 8 ^ 2 := Nat.pow_le_pow_left hv8 2
      omega
    obtain ⟨hs, hzero, hpos⟩ := small_slack_check ⟨v, by omega⟩ ⟨e, he21⟩ hv he
    have hid : (slack3 v e : ℝ) =
        3 * ((v.choose 2 : ℝ) + 1 - 4 * (e : ℝ) / 3) := by
      simp only [slack3, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
        Nat.cast_add, Nat.cast_one, ← Nat.choose_two_right]
      ring
    have hsR : (0 : ℝ) ≤ (slack3 v e : ℝ) := by exact_mod_cast hs
    refine ⟨by linarith, ?_, ?_⟩
    · intro hz
      apply hzero
      exact_mod_cast (show (slack3 v e : ℝ) = 0 by linarith)
    · intro hz
      have hn : slack3 v e ≠ 0 := by
        intro hz'
        have hzR : (slack3 v e : ℝ) = 0 := by exact_mod_cast hz'
        exact hz (by linarith)
      have hr : (e : ℝ) ≤ 9 * (slack3 v e : ℝ) := by exact_mod_cast hpos hn
      linarith

section

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The vertices of `Q` in the specified part of the colouring. -/
def partOf (c : V → Fin 3) (Q : Finset V) (i : Fin 3) :=
  Q.filter fun u => c u = i

/-- The ordered vertex pairs in distinct parts, oriented by increasing colour. -/
def crossPairs (c : V → Fin 3) (Q : Finset V) : Finset (V × V) :=
  (partOf c Q 0 ×ˢ partOf c Q 1) ∪ (partOf c Q 0 ×ˢ partOf c Q 2) ∪
    (partOf c Q 1 ×ˢ partOf c Q 2)

omit [Fintype V] in
theorem crossPairs_iff {c : V → Fin 3} {Q : Finset V} {p : V × V} :
    p ∈ crossPairs c Q ↔ p.1 ∈ Q ∧ p.2 ∈ Q ∧ c p.1 < c p.2 := by
  simp only [crossPairs, mem_union, mem_product, partOf, mem_filter]
  have h (i j : Fin 3) : i < j ↔
      (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by
    decide +revert +kernel
  rw [h]
  tauto

omit [DecidableEq V] [Fintype V] in
theorem partOf_card_sum (c : V → Fin 3) (Q : Finset V) :
    Q.card = (partOf c Q 0).card + (partOf c Q 1).card + (partOf c Q 2).card := by
  calc
    Q.card = ∑ i : Fin 3, (partOf c Q i).card :=
      card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    _ = _ := by rw [Fin.sum_univ_three]

omit [Fintype V] in
theorem crossPairs_card (c : V → Fin 3) (Q : Finset V) :
    (crossPairs c Q).card =
      (partOf c Q 0).card * (partOf c Q 1).card +
      (partOf c Q 0).card * (partOf c Q 2).card +
      (partOf c Q 1).card * (partOf c Q 2).card := by
  have h₁ : Disjoint (partOf c Q 0 ×ˢ partOf c Q 1) (partOf c Q 0 ×ˢ partOf c Q 2) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [mem_product, partOf, mem_filter] at hp hq
    have hc := hp.2.2.symm.trans hq.2.2
    exact (by decide : (1 : Fin 3) ≠ 2) hc
  have h₂ : Disjoint ((partOf c Q 0 ×ˢ partOf c Q 1) ∪ (partOf c Q 0 ×ˢ partOf c Q 2))
      (partOf c Q 1 ×ˢ partOf c Q 2) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [mem_union, mem_product, partOf, mem_filter] at hp hq
    have hp' : c p.1 = 0 := hp.elim (fun h => h.1.2) (fun h => h.1.2)
    have hc := hp'.symm.trans hq.1.2
    exact (by decide : (0 : Fin 3) ≠ 1) hc
  rw [crossPairs, card_union_of_disjoint h₂, card_union_of_disjoint h₁]
  simp only [card_product]

omit [Fintype V] in
theorem crossPairs_injOn (c : V → Fin 3) (Q : Finset V) :
    Set.InjOn (fun p : V × V => s(p.1,p.2)) (crossPairs c Q) := by
  intro p hp q hq he
  rcases Sym2.eq_iff.mp he with h | h
  · exact Prod.ext h.1 h.2
  · have hlt := (crossPairs_iff.mp hp).2.2
    rw [h.1, h.2] at hlt
    exact ((not_lt_of_ge (crossPairs_iff.mp hq).2.2.le) hlt).elim

variable (B : SimpleGraph V) [DecidableRel B.Adj]

theorem induced_edges_subset_crossPairs (c : V → Fin 3)
    (hc : ∀ ⦃u v⦄, B.Adj u v → c u ≠ c v) (Q : Finset V) :
    (inducedOn B Q).edgeFinset ⊆ (crossPairs c Q).image (fun p => s(p.1,p.2)) := by
  intro f hf
  induction f using Sym2.inductionOn with
  | _ u v =>
    have h : B.Adj u v ∧ u ∈ Q ∧ v ∈ Q :=
      SimpleGraph.mem_edgeFinset.mp hf
    rcases lt_or_gt_of_ne (hc h.1) with hlt | hgt
    · exact mem_image.mpr ⟨(u,v), crossPairs_iff.mpr ⟨h.2.1, h.2.2, hlt⟩, rfl⟩
    · exact mem_image.mpr ⟨(v,u), crossPairs_iff.mpr ⟨h.2.2, h.2.1, hgt⟩, Sym2.eq_swap⟩

theorem tripartite_edge_bound (c : V → Fin 3)
    (hc : ∀ ⦃u v⦄, B.Adj u v → c u ≠ c v) (Q : Finset V) :
    3 * e B Q ≤ Q.card ^ 2 := by
  have hle := card_le_card (induced_edges_subset_crossPairs B c hc Q)
  rw [card_image_of_injOn (crossPairs_injOn c Q), crossPairs_card] at hle
  change e B Q ≤ _ at hle
  rw [partOf_card_sum c Q]
  zify at hle ⊢
  nlinarith only [hle,
    sq_nonneg ((partOf c Q 0).card - (partOf c Q 1).card : ℤ),
    sq_nonneg ((partOf c Q 0).card - (partOf c Q 2).card : ℤ),
    sq_nonneg ((partOf c Q 1).card - (partOf c Q 2).card : ℤ)]

end

end GapExtremal.R434
