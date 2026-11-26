/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.GlobalLemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# Global bound with twins (ledger §16.2, L16.2)

Hypotheses on the blocks: every `B`-edge and every `B`-triangle lies in a block, and a vertex
outside a block
has at most two neighbours in it, which are then non-adjacent. Blocks may share more than one
  vertex.
Potential `what = 4 w - e`.
-/

@[expose] public section

namespace GapExtremal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (B : SimpleGraph V) [DecidableRel B.Adj]

/-- Twin-tolerant block hypotheses. -/
structure BlockHyp2 (blocks : Finset (Finset V)) : Prop where
  edge : ∀ u v, B.Adj u v → ∃ ℓ ∈ blocks, u ∈ ℓ ∧ v ∈ ℓ
  tri : ∀ u v x, B.Adj u v → B.Adj v x → B.Adj u x → ∃ ℓ ∈ blocks, u ∈ ℓ ∧ v ∈ ℓ ∧ x ∈ ℓ
  two : ∀ ℓ ∈ blocks, ∀ z ∉ ℓ, ∀ y ∈ ℓ, ∀ y' ∈ ℓ, ∀ y'' ∈ ℓ, B.Adj z y → B.Adj z y' → B.Adj z y'' →
    y = y' ∨ y = y'' ∨ y' = y''
  nonadj : ∀ ℓ ∈ blocks, ∀ z ∉ ℓ, ∀ y ∈ ℓ, ∀ y' ∈ ℓ, B.Adj z y → B.Adj z y' → ¬ B.Adj y y'

variable {B}

/-- The potential `what = 4 w - e`. -/
def what (B : SimpleGraph V) [DecidableRel B.Adj] (Q : Finset V) : ℤ := 4 * w B Q - e B Q

omit [DecidableEq V] [Fintype V] in
theorem D_singleton_le_two {ℓ A : Finset V} {z : V} (hA : A ⊆ ℓ)
    (htwo : ∀ y ∈ ℓ, ∀ y' ∈ ℓ, ∀ y'' ∈ ℓ, B.Adj z y → B.Adj z y' → B.Adj z y'' →
      y = y' ∨ y = y'' ∨ y' = y'') : D B {z} A ≤ 2 := by
  have : D B {z} A = (A.filter (fun v => B.Adj z v)).card := by
    rw [D, Finset.sum_singleton, Finset.card_filter]
  rw [this]
  by_contra h
  push Not at h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp h
  simp only [Finset.mem_filter] at ha hb hc
  rcases htwo a (hA ha.1) b (hA hb.1) c (hA hc.1) ha.2 hb.2 hc.2 with h | h | h
  exacts [hab h, hac h, hbc h]

theorem e_union (A Z : Finset V) (h : Disjoint A Z) :
    (e B (A ∪ Z) : ℤ) = e B A + e B Z + D B A Z := by
  have h1 := two_mul_e_eq_D B (A ∪ Z)
  have h2 := two_mul_e_eq_D B A
  have h3 := two_mul_e_eq_D B Z
  have hD : D B (A ∪ Z) (A ∪ Z) = D B A A + D B A Z + (D B Z A + D B Z Z) := by
    rw [D_union_left B h, D_union_right B h, D_union_right B h]
  have hc : D B Z A = D B A Z := D_comm B Z A
  have : 2 * e B (A ∪ Z) = 2 * (e B A + e B Z + D B A Z) := by
    rw [h1, hD, ← h2, ← h3, hc]; ring
  have := Nat.eq_of_mul_eq_mul_left (by norm_num) this
  exact_mod_cast this

/-- Fragmentation identity for `what`. -/
theorem what_union {A Z : Finset V} (h : Disjoint A Z) :
    what B (A ∪ Z) = what B A + what B Z + 7 * D B A Z - 4 * A.card * Z.card + 4 := by
  have hc := card_union_choose_two h
  have he := e_union (B := B) A Z h
  unfold what w
  rw [he, hc]
  ring

/-- **Fragmentation of one column (twin version).** -/
theorem exists_parts {blocks : Finset (Finset V)} (hB : BlockHyp2 B blocks) (Q : Finset V) :
    ∃ P : Finset (Finset V), (∀ p ∈ P, p ⊆ Q) ∧ (∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → Disjoint p p') ∧
      (∀ p ∈ P, ∃ ℓ ∈ blocks, p ⊆ ℓ) ∧ what B Q ≤ ∑ p ∈ P, what B p := by
  induction Q using Finset.strongInduction with
  | H Q ih =>
    by_cases ht : TriFree B Q
    · refine ⟨∅, by simp, by simp, by simp, ?_⟩
      simp only [Finset.sum_empty, what]
      linarith [four_w_le_e B ht]
    · simp only [TriFree, not_forall] at ht
      obtain ⟨u, hu, v, hv, x, hx, huv, hvx, hux, -⟩ := ht
      obtain ⟨ℓ, hℓ, huℓ, hvℓ, hxℓ⟩ := hB.tri u v x huv hvx hux
      set A := Q ∩ ℓ with hAdef
      set Z := Q \ ℓ with hZdef
      have hAsub : A ⊆ ℓ := Finset.inter_subset_right
      by_cases hZ : Z = ∅
      · have hsub : Q ⊆ ℓ := Finset.sdiff_eq_empty_iff_subset.mp hZ
        exact ⟨{Q}, by simp, by simp, by simp only [Finset.mem_singleton, forall_eq]; exact ⟨ℓ,
          hℓ, hsub⟩,
          by simp⟩
      have hZne : Z.Nonempty := Finset.nonempty_iff_ne_empty.mpr hZ
      have hZQ : Z ⊂ Q := by
        refine ⟨Finset.sdiff_subset, fun h => ?_⟩
        have := h hu
        simp [hZdef, huℓ] at this
      obtain ⟨PZ, hPZsub, hPZdisj, hPZblk, hPZw⟩ := ih Z hZQ
      have hAZ : Disjoint A Z := by
        rw [hAdef, hZdef]
        exact Finset.disjoint_left.mpr fun a ha haZ =>
          (Finset.mem_sdiff.mp haZ).2 (Finset.mem_inter.mp ha).2
      have huA : u ∈ A := Finset.mem_inter.mpr ⟨hu, huℓ⟩
      have hvA : v ∈ A := Finset.mem_inter.mpr ⟨hv, hvℓ⟩
      have hxA : x ∈ A := Finset.mem_inter.mpr ⟨hx, hxℓ⟩
      have htriA : ({u, v, x} : Finset V) ⊆ A := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl <;> assumption
      have hc3 : ({u, v, x} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [huv.ne, hux.ne]), Finset.card_pair hvx.ne]
      have hA3 : 3 ≤ A.card := hc3 ▸ Finset.card_le_card htriA
      have hQAZ : Q = A ∪ Z := by
        ext y; by_cases hy : y ∈ ℓ <;> simp [hAdef, hZdef]
      have hAnot : A ∉ PZ := fun hA => by
        have := hPZsub A hA huA
        simp [hZdef, huℓ] at this
      have hpartsA : ∀ PP : Finset (Finset V), (∀ p ∈ PP, p ⊆ Z) →
          (∀ p ∈ PP, ∀ p' ∈ PP, p ≠ p' → Disjoint p p') → (∀ p ∈ PP, ∃ ℓ ∈ blocks, p ⊆ ℓ) →
          A ∉ PP →
          (∀ p ∈ insert A PP, p ⊆ Q) ∧ (∀ p ∈ insert A PP, ∀ p' ∈ insert A PP, p ≠ p' → Disjoint p
            p') ∧
            (∀ p ∈ insert A PP, ∃ ℓ ∈ blocks, p ⊆ ℓ) := by
        intro PP hsub hdisj hblk _
        refine ⟨?_, ?_, ?_⟩
        · intro p hp
          rcases Finset.mem_insert.mp hp with rfl | hp
          · exact Finset.inter_subset_left
          · exact (hsub p hp).trans Finset.sdiff_subset
        · intro p hp p' hp' hne
          rcases Finset.mem_insert.mp hp with rfl | hp <;>
            rcases Finset.mem_insert.mp hp' with rfl | hp'
          · exact absurd rfl hne
          · exact hAZ.mono_right (hsub p' hp')
          · exact (hAZ.mono_right (hsub p hp)).symm
          · exact hdisj p hp p' hp' hne
        · intro p hp
          rcases Finset.mem_insert.mp hp with rfl | hp
          · exact ⟨ℓ, hℓ, hAsub⟩
          · exact hblk p hp
      have hid := what_union (B := B) hAZ
      -- neighbour counts
      have hD2 : D B A Z ≤ 2 * Z.card := by
        rw [D_comm, D_eq_sum_singleton_left]
        calc ∑ z ∈ Z, D B {z} A ≤ ∑ _z ∈ Z, 2 := Finset.sum_le_sum fun z hz =>
              D_singleton_le_two hAsub (hB.two ℓ hℓ z (Finset.mem_sdiff.mp hz).2)
          _ = 2 * Z.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      by_cases hall : ∀ z ∈ Z, D B {z} A ≤ 1
      · -- every outside vertex has at most one neighbour in `A`
        have hD1 : D B A Z ≤ Z.card := by
          rw [D_comm, D_eq_sum_singleton_left]
          calc ∑ z ∈ Z, D B {z} A ≤ ∑ _z ∈ Z, 1 := Finset.sum_le_sum hall
            _ = Z.card := by simp
        obtain ⟨h1, h2, h3⟩ := hpartsA PZ hPZsub hPZdisj hPZblk hAnot
        refine ⟨insert A PZ, h1, h2, h3, ?_⟩
        rw [Finset.sum_insert hAnot, hQAZ, hid]
        have hZ1 : (1 : ℤ) ≤ Z.card := by exact_mod_cast hZne.card_pos
        have hA3' : (3 : ℤ) ≤ A.card := by exact_mod_cast hA3
        have hD1' : (D B A Z : ℤ) ≤ Z.card := by exact_mod_cast hD1
        nlinarith
      · -- some vertex has two non-adjacent neighbours in `A`, so `|A| ≥ 4`
        push Not at hall
        obtain ⟨z0, hz0, hz02⟩ := hall
        have hA4 : 4 ≤ A.card := by
          have hset : 1 < (A.filter (fun y => B.Adj z0 y)).card := by
            have : D B {z0} A = (A.filter (fun y => B.Adj z0 y)).card := by
              rw [D, Finset.sum_singleton, Finset.card_filter]
            omega
          obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hset
          simp only [Finset.mem_filter] at ha hb
          have hnab := hB.nonadj ℓ hℓ z0 (Finset.mem_sdiff.mp hz0).2 a (hAsub ha.1) b (hAsub hb.1)
            ha.2 hb.2
          -- the triangle `u v x` contains at most one of `a, b`
          by_contra h4
          push Not at h4
          have hA3eq : A.card = 3 := by omega
          have hAeq : A = {u, v, x} := (Finset.eq_of_subset_of_card_le htriA (by rw [hc3,
            hA3eq])).symm
          have ha' := ha.1
          have hb' := hb.1
          rw [hAeq] at ha' hb'
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha' hb'
          rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;>
            first | exact hab rfl | exact hnab huv | exact hnab huv.symm | exact hnab hvx |
              exact hnab hvx.symm | exact hnab hux | exact hnab hux.symm
        have hA4' : (4 : ℤ) ≤ A.card := by exact_mod_cast hA4
        have hD2' : (D B A Z : ℤ) ≤ 2 * Z.card := by exact_mod_cast hD2
        by_cases hZ1 : Z.card = 1
        · obtain ⟨z, hzZ⟩ := Finset.card_eq_one.mp hZ1
          refine ⟨{A}, ?_, by simp, ?_, ?_⟩
          · simp only [Finset.mem_singleton, forall_eq]; exact Finset.inter_subset_left
          · simp only [Finset.mem_singleton, forall_eq]; exact ⟨ℓ, hℓ, hAsub⟩
          · rw [Finset.sum_singleton, hQAZ, hid, hzZ]
            rw [hzZ] at hD2'
            have hwz : what B {z} = -4 := by
              have hm := mantel B (triFree_of_card_le_one (B := B) (p := {z}) (by simp))
              simp only [Finset.card_singleton] at hm
              have he0 : e B {z} = 0 := by omega
              unfold what w
              rw [he0]
              simp
            rw [hwz]
            simp only [Finset.card_singleton, Nat.cast_one] at hD2' ⊢
            nlinarith
        · have hZ2 : (2 : ℤ) ≤ Z.card := by
            have := hZne.card_pos
            have : 2 ≤ Z.card := by omega
            exact_mod_cast this
          obtain ⟨h1, h2, h3⟩ := hpartsA PZ hPZsub hPZdisj hPZblk hAnot
          refine ⟨insert A PZ, h1, h2, h3, ?_⟩
          rw [Finset.sum_insert hAnot, hQAZ, hid]
          nlinarith

theorem what_le_of_card_le_one {p : Finset V} (h : p.card ≤ 1) : what B p ≤ 0 := by
  have := four_w_le_e B (triFree_of_card_le_one (B := B) h)
  unfold what; linarith

/-- **L16.2 (global bound with twins).** -/
theorem global_bound2 {blocks : Finset (Finset V)} (hB : BlockHyp2 B blocks) (c : ℤ)
    (hloc : ∀ ℓ ∈ blocks, ∀ T : Finset (Finset V), (∀ Q ∈ T, Q ⊆ ℓ) → IsPack T →
      ∑ Q ∈ T, (4 * w B Q - e B Q) ≤ 4 * c - e B ℓ)
    {T : Finset (Finset V)} (hT : IsPack T) : ∑ Q ∈ T, w B Q ≤ c * blocks.card := by
  classical
  choose P hPsub hPdisj hPblk hPw using fun Q => exists_parts hB Q
  set S := T.sigma P with hS
  -- pieces of distinct parts share at most one vertex
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
  -- step 1: potentials
  have h1 : ∑ Q ∈ T, what B Q ≤ ∑ x ∈ S, what B x.2 := by
    rw [hS, Finset.sum_sigma]
    exact Finset.sum_le_sum fun Q _ => hPw Q
  -- step 2: edges of the columns
  have h2 : ∑ Q ∈ T, (e B Q : ℤ) ≤ ∑ ℓ ∈ blocks, (e B ℓ : ℤ) := by
    have a := sum_e_inter_le (B := B) T id (fun x hx y hy hxy => hT x hx y hy hxy) Finset.univ
    have b := e_le_sum_blocks (B := B) hB.edge Finset.univ
    simp only [id, Finset.inter_univ, Finset.univ_inter] at a b
    exact_mod_cast a.trans b
  -- step 3: keep parts with at least two vertices and charge them to blocks
  set S' := S.filter (fun x => 2 ≤ x.2.card) with hS'
  have h3 : ∑ x ∈ S, what B x.2 ≤ ∑ x ∈ S', what B x.2 := by
    rw [hS', Finset.sum_filter]
    refine Finset.sum_le_sum fun x _ => ?_
    split_ifs with h
    · exact le_rfl
    · exact what_le_of_card_le_one (by omega)
  have hblkS : ∀ x ∈ S, ∃ ℓ ∈ blocks, x.2 ⊆ ℓ := by
    rintro ⟨Q, p⟩ hx
    simp only [hS, Finset.mem_sigma] at hx
    exact hPblk Q p hx.2
  let blk : (Σ _ : Finset V, Finset V) → Finset V := fun x =>
    if h : ∃ ℓ ∈ blocks, x.2 ⊆ ℓ then h.choose else ∅
  have hblk : ∀ x ∈ S, blk x ∈ blocks ∧ x.2 ⊆ blk x := by
    intro x hx
    have h := hblkS x hx
    simp only [blk, dite_eq_left h]
    exact h.choose_spec
  have hmaps : ∀ x ∈ S', blk x ∈ blocks := fun x hx => (hblk x (Finset.mem_filter.mp hx).1).1
  have h4 : ∑ x ∈ S', what B x.2 = ∑ ℓ ∈ blocks, ∑ x ∈ S'.filter (fun x => blk x = ℓ), what B x.2 :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have h5 : ∀ ℓ ∈ blocks, ∑ x ∈ S'.filter (fun x => blk x = ℓ), what B x.2 ≤ 4 * c - e B ℓ := by
    intro ℓ hℓ
    set F := S'.filter (fun x => blk x = ℓ) with hF
    have hFS : ∀ x ∈ F, x ∈ S ∧ 2 ≤ x.2.card ∧ blk x = ℓ := by
      intro x hx
      obtain ⟨hx', hb⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxS, h2⟩ := Finset.mem_filter.mp hx'
      exact ⟨hxS, h2, hb⟩
    have hinj : Set.InjOn (fun x : (Σ _ : Finset V, Finset V) => x.2) (F : Set _) := by
      intro x hx y hy hxy
      by_contra hne
      obtain ⟨hxS, hx2, -⟩ := hFS x hx
      obtain ⟨hyS, -, -⟩ := hFS y hy
      have h6 := hpair x hxS y hyS hne
      simp only at hxy
      rw [hxy, Finset.inter_self] at h6
      rw [hxy] at hx2
      omega
    have := hloc ℓ hℓ (F.image fun x => x.2)
      (fun Q hQ => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨hxS, -, hb⟩ := hFS x hx
        exact hb ▸ (hblk x hxS).2)
      (fun Q hQ Q' hQ' hne => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hQ'
        exact hpair x (hFS x hx).1 y (hFS y hy).1 (fun h => hne (by rw [h])))
    rw [Finset.sum_image hinj] at this
    simpa [what] using this
  have h6 : ∑ ℓ ∈ blocks, ∑ x ∈ S'.filter (fun x => blk x = ℓ), what B x.2 ≤
      ∑ ℓ ∈ blocks, (4 * c - e B ℓ) := Finset.sum_le_sum h5
  have hwhat : ∑ Q ∈ T, 4 * w B Q = ∑ Q ∈ T, what B Q + ∑ Q ∈ T, (e B Q : ℤ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun Q _ => by unfold what; ring
  have h7 : ∑ ℓ ∈ blocks, (4 * c - e B ℓ) + ∑ ℓ ∈ blocks, (e B ℓ : ℤ) = 4 * (c * blocks.card) := by
    rw [← Finset.sum_add_distrib]
    simp only [sub_add_cancel, Finset.sum_const, nsmul_eq_mul]
    ring
  have h8 : 4 * ∑ Q ∈ T, w B Q ≤ 4 * (c * blocks.card) := by
    rw [Finset.mul_sum, hwhat]
    linarith
  linarith

end GapExtremal
