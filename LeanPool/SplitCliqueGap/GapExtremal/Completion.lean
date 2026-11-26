/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Defs
public import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs

/-!
# Packings and completion by loose edges (ledger L1.1)

For any graph `G`, with `E2 G` the number of edges (as 2-cliques):

* `card_eq_of_partition`: a clique partition `P` has `|P| = E2 - ∑_{Q ∈ P} (C(|Q|,2) - 1)`;
* `cpStar_le_completion`: a fractional clique packing `z` (loads `≤ 1`) gives
  `cp* ≤ E2 - ∑ z_k (C(|C_k|,2) - 1)`.

Adapted from the B16 tournament development (`Framework.lean`: `completion`, `completion_isFrac`,
`completion_sum`), generalised from `graph m` to an arbitrary `SimpleGraph`.
-/

@[expose] public section

namespace GapExtremal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

open Classical in
/-- Number of edges, counted as two-element cliques. -/
noncomputable def E2 : ℕ := ((G.cliqueSets).filter (fun Q => Q.card = 2)).card

omit [Fintype V] in
theorem isClq_pair {u v : V} (h : G.Adj u v) : IsClq G {u, v} := by
  refine ⟨by rw [card_pair h.ne], ?_⟩
  intro a ha b hb hab
  simp only [mem_insert, mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · exact h
  · exact h.symm
  · exact absurd rfl hab

omit [DecidableEq V] in
theorem mem_cliques {Q : Finset V} : Q ∈ G.cliqueSets ↔ IsClq G Q :=
  mem_cliqueSets_iff_isClq

omit [Fintype V] [DecidableEq V] in
/-- A two-element subset of a clique is a 2-clique. -/
theorem isClq_of_sub {Q e : Finset V} (hQ : IsClq G Q) (he : e ⊆ Q) (h2 : e.card = 2) :
    IsClq G e := ⟨h2.ge, fun u hu v hv huv => hQ.2 u (he hu) v (he hv) huv⟩

omit [Fintype V] in
theorem pair_of_card_two {e : Finset V} (h2 : e.card = 2) : ∃ u v, u ≠ v ∧ e = {u, v} := by
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp h2
  exact ⟨u, v, huv, rfl⟩

omit [DecidableEq V] in
/-- In a clique partition, `∑ C(|Q|,2) = E2`. -/
theorem sum_choose_of_partition {P : Finset (Finset V)} (hP : G.IsCliquePartition P) :
    ∑ Q ∈ P, Q.card.choose 2 = E2 G := by
  classical
  have hcount : ∀ Q ∈ P, Q.card.choose 2 = (Q.powersetCard 2).card := fun Q _ =>
    (Finset.card_powersetCard 2 Q).symm
  rw [Finset.sum_congr rfl hcount, ← Finset.card_sigma]
  unfold E2
  refine Finset.card_bij (fun x _ => x.2) ?_ ?_ ?_
  · rintro ⟨Q, e⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hx
    rw [Finset.mem_filter, mem_cliques]
    exact ⟨isClq_of_sub G (isClq_iff.mpr ⟨hP.two_le Q hx.1, hP.isClique Q hx.1⟩) hx.2.1 hx.2.2,
      hx.2.2⟩
  · rintro ⟨Q, e⟩ hx ⟨Q', e'⟩ hx' (h : e = e')
    subst h
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hx hx'
    obtain ⟨u, v, huv, rfl⟩ := pair_of_card_two hx.2.2
    have hadj : G.Adj u v := hP.isClique Q hx.1 (hx.2.1 (by simp)) (hx.2.1 (by simp)) huv
    obtain ⟨R, -, hR⟩ := hP.existsUnique u v hadj
    have h1 := hR Q ⟨hx.1, hx.2.1 (by simp), hx.2.1 (by simp)⟩
    have h2 := hR Q' ⟨hx'.1, hx'.2.1 (by simp), hx'.2.1 (by simp)⟩
    rw [h1, h2]
  · intro e he
    rw [Finset.mem_filter, mem_cliques] at he
    obtain ⟨u, v, huv, rfl⟩ := pair_of_card_two he.2
    have hadj : G.Adj u v := he.1.2 u (by simp) v (by simp) huv
    obtain ⟨Q, ⟨hQ, hu, hv⟩, -⟩ := hP.existsUnique u v hadj
    refine ⟨⟨Q, {u, v}⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_powersetCard]
    refine ⟨hQ, ?_, he.2⟩
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption

omit [DecidableEq V] in
/-- **Integer side of L1.1.** -/
theorem card_eq_of_partition {P : Finset (Finset V)} (hP : G.IsCliquePartition P) :
    (P.card : ℤ) = E2 G - ∑ Q ∈ P, (((Q.card.choose 2 : ℕ) : ℤ) - 1) := by
  classical
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, sum_choose_of_partition G hP]
  simp

/-! ### Completion -/

variable {K : Type*} [Fintype K] (z : K → ℝ) (C : K → Finset V)

/-- Load of a weighted clique family on a vertex set. -/
noncomputable def loadQ (Q : Finset V) : ℝ := ∑ k, if Q ⊆ C k then z k else 0

open Classical in
/-- The packing plus a loose edge of mass `1 - load` on each edge. -/
noncomputable def completion (Q : Finset V) : ℝ :=
  (∑ k, if Q = C k then z k else 0) + if IsClq G Q ∧ Q.card = 2 then 1 - loadQ z C Q else 0

variable {G z C}

theorem completion_isFrac (hz : ∀ k, 0 ≤ z k) (hC : ∀ k, IsClq G (C k))
    (hload : ∀ u v, G.Adj u v → loadQ z C {u, v} ≤ 1) :
    G.IsFracCliquePartition (completion G z C) := by
  classical
  refine SimpleGraph.IsFracCliquePartition.of_cliqueSets ?_ ?_ ?_
  · intro Q
    unfold completion
    apply add_nonneg
    · exact Finset.sum_nonneg fun k _ => by split_ifs <;> simp [hz k]
    · split_ifs with h
      · obtain ⟨u, v, huv, rfl⟩ := pair_of_card_two h.2
        have := hload u v (h.1.2 u (by simp) v (by simp) huv)
        linarith
      · exact le_rfl
  · intro Q hQ
    rw [← isClq_iff]
    unfold completion at hQ
    by_contra hnot
    apply hQ
    have h1 : ∀ k, (if Q = C k then z k else 0) = 0 := by
      intro k; split_ifs with h
      · exact absurd (h ▸ hC k) hnot
      · rfl
    rw [Finset.sum_eq_zero (fun k _ => h1 k), zero_add, ite_eq_right (fun h => hnot h.1)]
  · intro u v huv
    unfold completion
    rw [Finset.sum_add_distrib]
    have h1 : ∑ Q ∈ (G.cliqueSets).filter (fun Q => u ∈ Q ∧ v ∈ Q), ∑ k, (if Q = C k then z k else
      0) =
        loadQ z C {u, v} := by
      rw [Finset.sum_comm]
      unfold loadQ
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_ite_eq']
      refine if_congr ?_ rfl rfl
      rw [Finset.mem_filter, mem_cliques]
      constructor
      · rintro ⟨-, hu, hv⟩ x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · intro h
        exact ⟨hC k, h (by simp), h (by simp)⟩
    have h2 : ∑ Q ∈ (G.cliqueSets).filter (fun Q => u ∈ Q ∧ v ∈ Q),
        (if IsClq G Q ∧ Q.card = 2 then 1 - loadQ z C Q else 0) = 1 - loadQ z C {u, v} := by
      rw [Finset.sum_eq_single_of_mem ({u, v} : Finset V)]
      · rw [ite_eq_left ⟨isClq_pair G huv, card_pair huv.ne⟩]
      · rw [Finset.mem_filter, mem_cliques]
        exact ⟨isClq_pair G huv, by simp, by simp⟩
      · intro Q hQ hne
        rw [ite_eq_right]
        rintro ⟨-, h2⟩
        apply hne
        rw [Finset.mem_filter] at hQ
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          exacts [hQ.2.1, hQ.2.2]
        · rw [h2, card_pair huv.ne]
    rw [h1, h2]
    ring

theorem completion_sum (hC : ∀ k, IsClq G (C k)) :
    ∑ Q ∈ G.cliqueSets, completion G z C Q =
      (E2 G : ℝ) - ∑ k, z k * ((((C k).card.choose 2 : ℕ) : ℝ) - 1) := by
  classical
  unfold completion
  rw [Finset.sum_add_distrib]
  have h1 : ∑ Q ∈ G.cliqueSets, ∑ k, (if Q = C k then z k else 0) = ∑ k, z k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_ite_eq']
    rw [ite_eq_left ((mem_cliques G).mpr (hC k))]
  have h2 : ∑ Q ∈ G.cliqueSets, (if IsClq G Q ∧ Q.card = 2 then 1 - loadQ z C Q else 0) =
      ∑ Q ∈ (G.cliqueSets).filter (fun Q => Q.card = 2), (1 - loadQ z C Q) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [mem_cliques] at hQ
    simp [hQ]
  have h3 : ∀ k, ∑ Q ∈ (G.cliqueSets).filter (fun Q => Q.card = 2), (if Q ⊆ C k then z k else 0) =
      z k * (((C k).card.choose 2 : ℕ) : ℝ) := by
    intro k
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 2
    rw [← Finset.card_powersetCard]
    congr 1
    ext Q
    simp only [Finset.mem_filter, mem_cliques, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨-, h2⟩, hsub⟩; exact ⟨hsub, h2⟩
    · rintro ⟨hsub, h2⟩; exact ⟨⟨isClq_of_sub G (hC k) hsub h2, h2⟩, hsub⟩
  rw [h1, h2, Finset.sum_sub_distrib]
  unfold loadQ
  rw [Finset.sum_comm, Finset.sum_congr rfl fun k _ => h3 k]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_sub, Finset.sum_sub_distrib]
  unfold E2
  ring

omit [Fintype V] in
/-- Completing a packing with edges preserves an upper bound on piece sizes. -/
theorem completion_card_le {k : ℕ} (hk : 2 ≤ k)
    (hsize : ∀ i, z i ≠ 0 → (C i).card ≤ k)
    (Q : Finset V) (hq : completion G z C Q ≠ 0) : Q.card ≤ k := by
  classical
  by_contra! h
  have hsum : ∑ i, (if Q = C i then z i else 0) = 0 := by
    apply sum_eq_zero
    intro i _
    split_ifs with hi
    · by_contra hn
      exact (not_le_of_gt h) (hi ▸ hsize i hn)
    · rfl
  have htwo : Q.card ≠ 2 := by omega
  exact hq (by simp [completion, hsum, htwo])

/-- **Fractional side of L1.1.** -/
theorem cpStar_le_completion (hz : ∀ k, 0 ≤ z k) (hC : ∀ k, IsClq G (C k))
    (hload : ∀ u v, G.Adj u v → loadQ z C {u, v} ≤ 1) :
    G.fracCliquePartitionNumber ≤ (E2 G : ℝ) - ∑ k, z k * ((((C k).card.choose 2 : ℕ) : ℝ) - 1) :=
      by
  rw [← completion_sum hC]
  exact SimpleGraph.fracCliquePartitionNumber_le_sum_cliqueSets (completion_isFrac hz hC hload)

section BoundedFractional

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Fractional clique partition cost with pieces of order at most four. -/
noncomputable def fracPartitionFour (G : SimpleGraph U) : ℝ :=
  sInf {r | ∃ x, G.IsFracCliquePartition x ∧ (∀ Q, x Q ≠ 0 → Q.card ≤ 4) ∧ ∑ Q, x Q = r}

theorem fracPartitionFour_le {G : SimpleGraph U} {x : Finset U → ℝ}
    (hx : G.IsFracCliquePartition x) (hsmall : ∀ Q, x Q ≠ 0 → Q.card ≤ 4) :
    fracPartitionFour G ≤ ∑ Q, x Q :=
  csInf_le ⟨0, by rintro _ ⟨y, hy, _, rfl⟩; exact sum_nonneg fun Q _ => hy.nonneg Q⟩
    ⟨x, hx, hsmall, rfl⟩

/-- The gap comparing unrestricted integral pieces to fractional pieces of order at most four.
Bounding this quantity from below also bounds the gap with both sides restricted. -/
noncomputable def gapWithFracFour (G : SimpleGraph U) : ℝ :=
  (G.cliquePartitionNumber : ℝ) - fracPartitionFour G

theorem gapWithFracFour_le_gap (G : SimpleGraph U) : gapWithFracFour G ≤ gap G := by
  classical
  have nonempty : {r | ∃ x : Finset U → ℝ, G.IsFracCliquePartition x ∧
      (∀ Q, x Q ≠ 0 → Q.card ≤ 4) ∧ ∑ Q, x Q = r}.Nonempty := by
    let z : Fin 0 → ℝ := Fin.elim0
    let C : Fin 0 → Finset U := Fin.elim0
    have hx := completion_isFrac (G := G) (z := z) (C := C) (fun i => i.elim0)
      (fun i => i.elim0) (fun _ _ _ => by simp [loadQ])
    exact ⟨_, _, hx, completion_card_le (by decide) (fun i => i.elim0), rfl⟩
  have h : G.fracCliquePartitionNumber ≤ fracPartitionFour G :=
    le_csInf nonempty (by rintro _ ⟨x, hx, _, rfl⟩; exact G.fracCliquePartitionNumber_le hx)
  exact sub_le_sub_left h _

end BoundedFractional

end GapExtremal
