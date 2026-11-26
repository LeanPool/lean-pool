/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.GlobalLemmas
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

/-- A packing of columns: two distinct members share at most one vertex. -/
def IsPack (T : Finset (Finset V)) : Prop := ∀ Q ∈ T, ∀ Q' ∈ T, Q ≠ Q' → (Q ∩ Q').card ≤ 1

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

omit [Fintype V] [DecidableEq V] [DecidableRel B.Adj] in
theorem triFree_of_card_le_one {p : Finset V} (h : p.card ≤ 1) : TriFree B p := by
  intro u hu v hv _ _ huv _ _
  exact huv.ne (Finset.card_le_one.mp h u hu v hv)

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

/-- **L7.3 (abstract).** -/
theorem global_bound {blocks : Finset (Finset V)} (hB : BlockHyp B blocks) (c : ℤ)
    (hloc : ∀ ℓ ∈ blocks, ∀ T : Finset (Finset V), (∀ Q ∈ T, Q ⊆ ℓ) → IsPack T →
      ∑ Q ∈ T, (4 * w B Q - e B Q) ≤ 4 * c - e B ℓ)
    {T : Finset (Finset V)} (hT : IsPack T) : ∑ Q ∈ T, w B Q ≤ c * blocks.card := by
  classical
  choose P hPsub hPdisj hPtype hPw using fun Q => exists_pieces hB Q
  set S := T.sigma P with hS
  have h1 : ∑ Q ∈ T, w B Q ≤ ∑ x ∈ S, w B x.2 := by
    rw [hS, Finset.sum_sigma]
    exact Finset.sum_le_sum fun Q _ => hPw Q
  have hpair : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (x.2 ∩ y.2).card ≤ 1 := by
    rintro ⟨Q, p⟩ hx ⟨Q', p'⟩ hy hne
    simp only [hS, Finset.mem_sigma] at hx hy
    by_cases hQ : Q = Q'
    · subst hQ
      have hp : p ≠ p' := fun h => hne (by rw [h])
      rw [Finset.disjoint_iff_inter_eq_empty.mp (hPdisj Q p hx.2 p' hy.2 hp)]
      simp
    · exact (Finset.card_le_card
        (Finset.inter_subset_inter (hPsub Q p hx.2) (hPsub Q' p' hy.2))).trans (hT Q hx.1 Q' hy.1
          hQ)
  set L : Finset V → Finset (Σ _ : Finset V, Finset V) :=
    fun ℓ => S.filter (fun x => 2 ≤ x.2.card ∧ x.2 ⊆ ℓ) with hL
  set R := S.filter (fun x => ¬ ∃ ℓ ∈ blocks, 2 ≤ x.2.card ∧ x.2 ⊆ ℓ) with hR
  have hcount : ∀ x ∈ S, (∃ ℓ ∈ blocks, 2 ≤ x.2.card ∧ x.2 ⊆ ℓ) →
      (blocks.filter (fun ℓ => 2 ≤ x.2.card ∧ x.2 ⊆ ℓ)).card = 1 := by
    rintro x - ⟨ℓ, hℓ, h2, hsub⟩
    rw [Finset.card_eq_one]
    refine ⟨ℓ, Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hℓ, h2, hsub⟩, ?_⟩⟩
    intro ℓ' hℓ'
    obtain ⟨hℓ'b, -, hsub'⟩ := Finset.mem_filter.mp hℓ'
    by_contra hne
    have h3 := hB.inter ℓ' hℓ'b ℓ hℓ hne
    have h4 : x.2.card ≤ (ℓ' ∩ ℓ).card := Finset.card_le_card (Finset.subset_inter hsub' hsub)
    omega
  have hsplit : ∀ g : (Σ _ : Finset V, Finset V) → ℤ,
      ∑ x ∈ S, g x = ∑ ℓ ∈ blocks, ∑ x ∈ L ℓ, g x + ∑ x ∈ R, g x := by
    intro g
    have hLsum : ∑ ℓ ∈ blocks, ∑ x ∈ L ℓ, g x =
        ∑ x ∈ S, if (∃ ℓ ∈ blocks, 2 ≤ x.2.card ∧ x.2 ⊆ ℓ) then g x else 0 := by
      simp only [hL, Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x hx => ?_
      split_ifs with hloc'
      · rw [← Finset.sum_filter, Finset.sum_const, hcount x hx hloc', one_smul]
      · refine Finset.sum_eq_zero fun ℓ hℓ => ?_
        rw [ite_eq_right]
        exact fun h => hloc' ⟨ℓ, hℓ, h⟩
    rw [hLsum, hR, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  have hRtf : ∀ x ∈ R, TriFree B x.2 := by
    intro x hx
    obtain ⟨hxS, hnot⟩ := Finset.mem_filter.mp hx
    obtain ⟨Q, p⟩ := x
    simp only [hS, Finset.mem_sigma] at hxS
    rcases hPtype Q p hxS.2 with ⟨ℓ, hℓ, hsub⟩ | htf
    · refine triFree_of_card_le_one ?_
      by_contra h2
      exact hnot ⟨ℓ, hℓ, by omega, hsub⟩
    · exact htf
  have hblock : ∀ ℓ ∈ blocks,
      ∑ x ∈ L ℓ, 4 * w B x.2 + ∑ x ∈ R, (e B (x.2 ∩ ℓ) : ℤ) ≤ 4 * c := by
    intro ℓ hℓ
    have hLR : Disjoint (L ℓ) R := by
      rw [Finset.disjoint_left]
      intro x hxL hxR
      exact (Finset.mem_filter.mp hxR).2 ⟨ℓ, hℓ, (Finset.mem_filter.mp hxL).2⟩
    have hedges : ∑ x ∈ L ℓ, (e B x.2 : ℤ) + ∑ x ∈ R, (e B (x.2 ∩ ℓ) : ℤ) ≤ e B ℓ := by
      have hLe : ∑ x ∈ L ℓ, (e B x.2 : ℤ) = ∑ x ∈ L ℓ, (e B (x.2 ∩ ℓ) : ℤ) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.inter_eq_left.mpr (Finset.mem_filter.mp hx).2.2]
      rw [hLe, ← Finset.sum_union hLR]
      have hsub : L ℓ ∪ R ⊆ S :=
        Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      have := sum_e_inter_le (B := B) (L ℓ ∪ R) (fun x => x.2)
        (fun x hx y hy => hpair x (hsub hx) y (hsub hy)) ℓ
      exact_mod_cast this
    have hinj : Set.InjOn (fun x : (Σ _ : Finset V, Finset V) => x.2) (L ℓ : Set _) := by
      intro x hx y hy hxy
      by_contra hne
      have h2 := (Finset.mem_filter.mp hx).2.1
      have h5 := hpair x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hne
      simp only at hxy
      rw [hxy, Finset.inter_self] at h5
      rw [hxy] at h2
      omega
    have hloc' := hloc ℓ hℓ ((L ℓ).image (fun x => x.2))
      (fun Q hQ => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hQ
        exact (Finset.mem_filter.mp hx).2.2)
      (fun Q hQ Q' hQ' hne => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hQ'
        exact hpair x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1
          (fun h => hne (by rw [h])))
    rw [Finset.sum_image hinj] at hloc'
    have hsub' : ∑ x ∈ L ℓ, (4 * w B x.2 - e B x.2) =
        ∑ x ∈ L ℓ, 4 * w B x.2 - ∑ x ∈ L ℓ, (e B x.2 : ℤ) := Finset.sum_sub_distrib _ _
    linarith
  have hR4 : ∑ x ∈ R, 4 * w B x.2 ≤ ∑ ℓ ∈ blocks, ∑ x ∈ R, (e B (x.2 ∩ ℓ) : ℤ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun x hx => (four_w_le_e B (hRtf x hx)).trans ?_
    exact_mod_cast e_le_sum_blocks hB.edge x.2
  have h4 : 4 * ∑ x ∈ S, w B x.2 ≤ 4 * (c * blocks.card) := by
    rw [Finset.mul_sum, hsplit (fun x => 4 * w B x.2)]
    calc ∑ ℓ ∈ blocks, ∑ x ∈ L ℓ, 4 * w B x.2 + ∑ x ∈ R, 4 * w B x.2
        ≤ ∑ ℓ ∈ blocks, ∑ x ∈ L ℓ, 4 * w B x.2 + ∑ ℓ ∈ blocks, ∑ x ∈ R, (e B (x.2 ∩ ℓ) : ℤ) := by
          linarith
      _ = ∑ ℓ ∈ blocks, (∑ x ∈ L ℓ, 4 * w B x.2 + ∑ x ∈ R, (e B (x.2 ∩ ℓ) : ℤ)) :=
          Finset.sum_add_distrib.symm
      _ ≤ ∑ _ℓ ∈ blocks, 4 * c := Finset.sum_le_sum hblock
      _ = 4 * (c * blocks.card) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  linarith

end GapExtremal
