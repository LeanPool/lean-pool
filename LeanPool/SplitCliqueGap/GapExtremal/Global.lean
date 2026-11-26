/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Global2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# The global bound `I(B) ≤ c · #blocks` (ledger §7, L7.3), abstract form

`B` is a graph on a finite type, `blocks` a family of vertex sets such that

* two blocks share at most one vertex;
* every triangle of `B` lies in a block;
* a vertex outside a block has at most one `B`-neighbour in it.

If every block satisfies the reserved local bound `∑ (4 w - e) ≤ 4c - e(ℓ)` for packings inside it,
then every
packing of the whole vertex set has `∑ w ≤ c · #blocks`.

The proof fragments every column (`exists_pieces`), charges local pieces to their block and
triangle-free
pieces to the unused `B`-edges of the blocks (Mantel with reserve).
-/

@[expose] public section

namespace GapExtremal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (B : SimpleGraph V) [DecidableRel B.Adj]

/-- The geometric hypotheses on the blocks (ledger §5). -/
structure BlockHyp (blocks : Finset (Finset V)) : Prop where
  inter : ∀ ℓ ∈ blocks, ∀ ℓ' ∈ blocks, ℓ ≠ ℓ' → (ℓ ∩ ℓ').card ≤ 1
  edge : ∀ u v, B.Adj u v → ∃ ℓ ∈ blocks, u ∈ ℓ ∧ v ∈ ℓ
  tri : ∀ u v x, B.Adj u v → B.Adj v x → B.Adj u x → ∃ ℓ ∈ blocks, u ∈ ℓ ∧ v ∈ ℓ ∧ x ∈ ℓ
  one : ∀ ℓ ∈ blocks, ∀ z ∉ ℓ, ∀ y ∈ ℓ, ∀ y' ∈ ℓ, B.Adj z y → B.Adj z y' → y = y'

variable {B}

omit [Fintype V] [DecidableEq V] in
theorem D_singleton_le_one {ℓ A : Finset V} {z : V} (hA : A ⊆ ℓ)
    (hone : ∀ y ∈ ℓ, ∀ y' ∈ ℓ, B.Adj z y → B.Adj z y' → y = y') : D B {z} A ≤ 1 := by
  have : D B {z} A = (A.filter (fun v => B.Adj z v)).card := by
    rw [D, Finset.sum_singleton, Finset.card_filter]
  rw [this, Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  exact hone a (hA ha.1) b (hA hb.1) ha.2 hb.2

/-- **Fragmentation of one column.** -/
theorem exists_pieces {blocks : Finset (Finset V)} (hB : BlockHyp B blocks) (Q : Finset V) :
    ∃ P : Finset (Finset V), (∀ p ∈ P, p ⊆ Q) ∧ (∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → Disjoint p p') ∧
      (∀ p ∈ P, (∃ ℓ ∈ blocks, p ⊆ ℓ) ∨ TriFree B p) ∧ w B Q ≤ ∑ p ∈ P, w B p := by
  induction Q using Finset.strongInduction with
  | H Q ih =>
    by_cases ht : TriFree B Q
    · exact ⟨{Q}, by simp, by simp, by simp [ht], by simp⟩
    · simp only [TriFree, not_forall] at ht
      obtain ⟨u, hu, v, hv, x, hx, huv, hvx, hux, -⟩ := ht
      obtain ⟨ℓ, hℓ, huℓ, hvℓ, hxℓ⟩ := hB.tri u v x huv hvx hux
      set A := Q ∩ ℓ with hAdef
      set Z := Q \ ℓ with hZdef
      by_cases hZ : Z = ∅
      · have hsub : Q ⊆ ℓ := Finset.sdiff_eq_empty_iff_subset.mp hZ
        refine ⟨{Q}, by simp, by simp, ?_, by simp⟩
        simp only [Finset.mem_singleton, forall_eq]
        exact Or.inl ⟨ℓ, hℓ, hsub⟩
      · have hZne : Z.Nonempty := Finset.nonempty_iff_ne_empty.mpr hZ
        have hZQ : Z ⊂ Q := by
          refine ⟨Finset.sdiff_subset, fun h => ?_⟩
          have := h hu
          simp [hZdef, huℓ] at this
        obtain ⟨PZ, hPZsub, hPZdisj, hPZtype, hPZw⟩ := ih Z hZQ
        have hAZ : Disjoint A Z := by
          rw [hAdef, hZdef]
          exact Finset.disjoint_left.mpr fun a ha haZ =>
            (Finset.mem_sdiff.mp haZ).2 (Finset.mem_inter.mp ha).2
        have huA : u ∈ A := Finset.mem_inter.mpr ⟨hu, huℓ⟩
        have hA3 : 3 ≤ A.card := by
          have hs : ({u, v, x} : Finset V) ⊆ A := by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl <;> simp_all
          have hc : ({u, v, x} : Finset V).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp [huv.ne, hux.ne]),
              Finset.card_pair hvx.ne]
          exact hc ▸ Finset.card_le_card hs
        have hAnot : A ∉ PZ := fun hA => by
          have := hPZsub A hA huA
          simp [hZdef, huℓ] at this
        have hQAZ : Q = A ∪ Z := by
          ext y; by_cases hy : y ∈ ℓ <;> simp [hAdef, hZdef]
        refine ⟨insert A PZ, ?_, ?_, ?_, ?_⟩
        · intro p hp
          rcases Finset.mem_insert.mp hp with rfl | hp
          · exact Finset.inter_subset_left
          · exact (hPZsub p hp).trans Finset.sdiff_subset
        · intro p hp p' hp' hne
          rcases Finset.mem_insert.mp hp with rfl | hp <;>
            rcases Finset.mem_insert.mp hp' with rfl | hp'
          · exact absurd rfl hne
          · exact hAZ.mono_right (hPZsub p' hp')
          · exact (hAZ.mono_right (hPZsub p hp)).symm
          · exact hPZdisj p hp p' hp' hne
        · intro p hp
          rcases Finset.mem_insert.mp hp with rfl | hp
          · exact Or.inl ⟨ℓ, hℓ, Finset.inter_subset_right⟩
          · exact hPZtype p hp
        · rw [Finset.sum_insert hAnot, hQAZ]
          refine (frag_le B hAZ hA3 hZne fun z hz => ?_).trans (by linarith)
          have hzℓ : z ∉ ℓ := (Finset.mem_sdiff.mp hz).2
          exact D_singleton_le_one Finset.inter_subset_right (hB.one ℓ hℓ z hzℓ)

/-- **L7.3 (abstract).** -/
theorem global_bound {blocks : Finset (Finset V)} (hB : BlockHyp B blocks) (c : ℤ)
    (hloc : ∀ ℓ ∈ blocks, ∀ T : Finset (Finset V), (∀ Q ∈ T, Q ⊆ ℓ) → IsPack T →
      ∑ Q ∈ T, (4 * w B Q - e B Q) ≤ 4 * c - e B ℓ)
    {T : Finset (Finset V)} (hT : IsPack T) : ∑ Q ∈ T, w B Q ≤ c * blocks.card := by
  have weaker : BlockHyp2 B blocks := by
    refine ⟨hB.edge, hB.tri, ?_, ?_⟩
    · intro ℓ hℓ z hz y hy y' hy' _ _ hadj hadj' _
      exact Or.inl (hB.one ℓ hℓ z hz y hy y' hy' hadj hadj')
    · intro ℓ hℓ z hz y hy y' hy' hadj hadj' hedge
      have eq := hB.one ℓ hℓ z hz y hy y' hy' hadj hadj'
      subst y'
      exact hedge.ne rfl
  exact global_bound2 weaker c hloc hT

end GapExtremal
