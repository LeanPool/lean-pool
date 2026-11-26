/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Residual
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert
import Mathlib.Tactic.NormNum

/-!
# Mantel with reserve and fragmentation (ledger §7, L7.1–L7.2)

* `mantel`: a `B`-triangle-free column `Q` has `4 e(Q) ≤ |Q|²` (Mathlib's Turán bound for `r = 2`).
* `four_w_le_e`: then `4 w(Q) ≤ e(Q)` (identity `16(e/4 - w) = (v-4)² + 7(v² - 4e)`).
* `frag_le`: if `|A| ≥ 3`, `Z ≠ ∅` is disjoint from `A` and every `z ∈ Z` has at most one
`B`-neighbour in
  `A`, then `w(A ∪ Z) ≤ w(A) + w(Z)`.
-/

@[expose] public section

namespace GapExtremal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (B : SimpleGraph V) [DecidableRel B.Adj]

/-- `Q` contains no triangle of `B`. -/
def TriFree (Q : Finset V) : Prop :=
  ∀ u ∈ Q, ∀ v ∈ Q, ∀ x ∈ Q, B.Adj u v → B.Adj v x → B.Adj u x → False

theorem two_mul_choose_two_int (n : ℕ) : 2 * ((n.choose 2 : ℕ) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  rcases n with _ | n
  · simp
  · have h : 2 * (n + 1).choose 2 = (n + 1) * n := by
      have := Nat.mul_div_cancel' (Nat.even_mul_pred_self (n + 1)).two_dvd
      rw [Nat.choose_two_right]
      simpa using this
    have h' : (2 : ℤ) * (((n + 1).choose 2 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) * (n : ℤ) := by
      exact_mod_cast h
    rw [h']
    push_cast
    ring

/-- **Mantel** for a column. -/
theorem mantel {Q : Finset V} (hQ : TriFree B Q) : 4 * e B Q ≤ Q.card ^ 2 := by
  set G := inducedOn B Q
  have hsupp : G.support ⊆ (Q : Set V) := by
    rintro u ⟨v, huv⟩
    exact huv.2.1
  have hcard : #(G.induce (Q : Set V)).edgeFinset = e B Q := by
    have := SimpleGraph.card_edgeFinset_induce_of_support_subset hsupp
    rw [show e B Q = #G.edgeFinset from rfl]
    (convert this using 2; ext; simp)
  have hcf : (G.induce (Q : Set V)).CliqueFree (2 + 1) := by
    intro t ht
    rw [SimpleGraph.is3Clique_iff] at ht
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := ht
    simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, G, inducedOn] at hab hac hbc
    exact hQ a a.2 b b.2 c c.2 hab.1 hbc.1 hac.1
  have h := hcf.card_edgeFinset_le
  have hQc : Fintype.card (Q : Set V) = Q.card := by simp
  rw [SimpleGraph.turanNumber_two, hcard, hQc] at h
  have := Nat.div_mul_le_self (#Q ^ 2) 4
  omega

/-- **L7.2.** On a triangle-free column, `4 w ≤ e`. -/
theorem four_w_le_e {Q : Finset V} (hQ : TriFree B Q) : 4 * w B Q ≤ (e B Q : ℤ) := by
  have hm : (4 : ℤ) * e B Q ≤ (Q.card : ℤ) ^ 2 := by exact_mod_cast mantel B hQ
  have hc := two_mul_choose_two_int Q.card
  unfold w
  nlinarith [sq_nonneg ((Q.card : ℤ) - 4)]

omit [Fintype V] in
theorem card_union_choose_two {A Z : Finset V} (h : Disjoint A Z) :
    (((A ∪ Z).card.choose 2 : ℕ) : ℤ) =
      ((A.card.choose 2 : ℕ) : ℤ) + ((Z.card.choose 2 : ℕ) : ℤ) + (A.card : ℤ) * Z.card := by
  have h1 := two_mul_choose_two_int (A ∪ Z).card
  have h2 := two_mul_choose_two_int A.card
  have h3 := two_mul_choose_two_int Z.card
  rw [card_union_of_disjoint h] at h1 ⊢
  push_cast at h1 ⊢
  linarith

/-- **L7.1 (fragmentation).** -/
theorem frag_le {A Z : Finset V} (hAZ : Disjoint A Z) (hA : 3 ≤ A.card) (hZ : Z.Nonempty)
    (hone : ∀ z ∈ Z, D B {z} A ≤ 1) : w B (A ∪ Z) ≤ w B A + w B Z := by
  have hD : D B (A ∪ Z) (A ∪ Z) = D B A A + D B A Z + (D B Z A + D B Z Z) := by
    rw [D_union_left B hAZ, D_union_right B hAZ, D_union_right B hAZ]
  have hZA : D B Z A ≤ Z.card := by
    rw [D_eq_sum_singleton_left]
    calc ∑ z ∈ Z, D B {z} A ≤ ∑ _z ∈ Z, 1 := Finset.sum_le_sum hone
      _ = Z.card := by simp
  have hAZ' : D B A Z = D B Z A := D_comm B A Z
  have hc := card_union_choose_two hAZ
  have hZpos : 1 ≤ Z.card := hZ.card_pos
  rw [w_eq_D, w_eq_D, w_eq_D, hD, hc]
  push_cast
  have : ((D B Z A : ℕ) : ℤ) ≤ Z.card := by exact_mod_cast hZA
  have hA' : (3 : ℤ) ≤ A.card := by exact_mod_cast hA
  have hZ' : (1 : ℤ) ≤ Z.card := by exact_mod_cast hZpos
  rw [hAZ']
  nlinarith

/-- A packing of columns: two distinct members share at most one vertex. -/
def IsPack (T : Finset (Finset V)) : Prop := ∀ Q ∈ T, ∀ Q' ∈ T, Q ≠ Q' → (Q ∩ Q').card ≤ 1

variable {B}

omit [Fintype V] [DecidableEq V] [DecidableRel B.Adj] in
theorem triFree_of_card_le_one {p : Finset V} (h : p.card ≤ 1) : TriFree B p := by
  intro u hu v hv _ _ huv _ _
  exact huv.ne (Finset.card_le_one.mp h u hu v hv)

/-- The edges of a column are covered by its parts in the blocks. -/
theorem e_le_sum_blocks {blocks : Finset (Finset V)}
    (hedge : ∀ u v, B.Adj u v → ∃ ℓ ∈ blocks, u ∈ ℓ ∧ v ∈ ℓ) (p : Finset V) :
    e B p ≤ ∑ ℓ ∈ blocks, e B (p ∩ ℓ) := by
  unfold e
  refine (Finset.card_le_card ?_).trans Finset.card_biUnion_le
  intro s hs
  induction s using Sym2.ind with
  | h u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hs
    obtain ⟨huv, hu, hv⟩ := hs
    obtain ⟨ℓ, hℓ, huℓ, hvℓ⟩ := hedge u v huv
    refine Finset.mem_biUnion.mpr ⟨ℓ, hℓ, ?_⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ⟨huv, Finset.mem_inter.mpr ⟨hu, huℓ⟩, Finset.mem_inter.mpr ⟨hv, hvℓ⟩⟩

/-- Pieces sharing at most one vertex use disjoint edges of a block. -/
theorem sum_e_inter_le {ι : Type*} (S : Finset ι) (f : ι → Finset V)
    (hf : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (f x ∩ f y).card ≤ 1) (ℓ : Finset V) :
    ∑ x ∈ S, e B (f x ∩ ℓ) ≤ e B ℓ := by
  unfold e
  rw [← Finset.card_biUnion]
  · refine Finset.card_le_card fun s hs => ?_
    obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp hs
    induction s using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hx ⊢
      exact ⟨hx.1, (Finset.mem_inter.mp hx.2.1).2, (Finset.mem_inter.mp hx.2.2).2⟩
  · intro x hx y hy hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro s hsx hsy
    induction s using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hsx hsy
      have hu : u ∈ f x ∩ f y :=
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hsx.2.1).1, (Finset.mem_inter.mp hsy.2.1).1⟩
      have hv : v ∈ f x ∩ f y :=
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hsx.2.2).1, (Finset.mem_inter.mp hsy.2.2).1⟩
      exact hsx.1.ne (Finset.card_le_one.mp (hf x hx y hy hxy) u hu v hv)

end GapExtremal
