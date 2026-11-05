/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Swap

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 2: counts after the swap

`exists_swap`: for an end `u` unmatched by `J`, with `u'` the other unmatched end of its component
in `J ∪ K`, there is a total colouring `c'` with
`n'_T + [S(u) = T] + [S(u') = T] = n_T + [i S(u) = T] + [i S(u') = T]` for all `T`.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
variable {c : PEC G (Fin k)} {a b : Fin k}

open Classical in
/-- The indicator `[S = T]`. -/
def ind (S T : Finset (Fin k)) : ℕ := if S = T then 1 else 0

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **The swap on a component of `J ∪ K`.** -/
theorem exists_swap (_ : a ≠ b) (htot : Total c) {u u' : V} (hu : IsEnd c a b u)
    (hm : ¬ JMatched c a b u) (hne : u' ≠ u) (hr : (jkGraph c a b).Reachable u u')
    (hum : ¬ JMatched c a b u')
    (huniq : ∀ w, w ≠ u → (jkGraph c a b).Reachable u w → ¬ JMatched c a b w → w = u') :
    ∃ c' : PEC G (Fin k), Total c' ∧ ∀ T,
      cnt c' T + ind (colSet c u) T + ind (colSet c u') T =
        cnt c T + ind (swapSet a b (colSet c u)) T + ind (swapSet a b (colSet c u')) T := by
  classical
  set H := jkGraph c a b
  set Q := univ.filter fun v => H.Reachable u v with hQ
  set X := univ.filter fun v => ∃ q, H.Reachable u q ∧ (c.kempeGraph a b).Reachable q v with hX
  have hXc : KClosed c a b X := by
    intro v w hv hcol
    obtain ⟨q, hq, hqv⟩ := (mem_filter.1 hv).2
    exact mem_filter.2 ⟨mem_univ _, q, hq, hqv.trans (kempeGraph_adj_of_col hcol).reachable⟩
  set c' := swapOn c a b X hXc
  -- colour sets after the swap
  have hset : ∀ v, colSet c' v = if v ∈ Q then swapSet a b (colSet c v) else colSet c v := by
    intro v
    by_cases hvX : v ∈ X
    · rw [colSet_swapOn_of_mem hXc hvX]
      split_ifs with hvQ
      · rfl
      · -- `v` is not an end
        obtain ⟨q, hq, hqv⟩ := (mem_filter.1 hvX).2
        have hqe : IsEnd c a b q := isEnd_of_jk_reachable hu hq
        have hve : ¬ IsEnd c a b v := by
          intro hve
          apply hvQ
          refine mem_filter.2 ⟨mem_univ _, ?_⟩
          by_cases hqv' : q = v
          · rw [← hqv']; exact hq
          · exact hq.trans (Adj.reachable ⟨hqv', hqe, hve, Or.inl hqv⟩)
        apply swapSet_eq_of_iff
        simp only [IsEnd, not_or, not_and, not_not] at hve
        tauto
    · rw [colSet_swapOn_of_not_mem hXc hvX]
      split_ifs with hvQ
      · exact absurd (mem_filter.2 ⟨mem_univ _, v, (mem_filter.1 hvQ).2, Reachable.refl _⟩) hvX
      · rfl
  refine ⟨c', Total.swapOn hXc htot, fun T => ?_⟩
  -- split `V` into `Q` and its complement, and `Q` into `{u, u'}` and the matched rest
  have huQ : u ∈ Q := mem_filter.2 ⟨mem_univ _, Reachable.refl _⟩
  have hu'Q : u' ∈ Q := mem_filter.2 ⟨mem_univ _, hr⟩
  set P : Finset V := {u, u'}
  set Qm := Q \ P
  have hQm : ∀ v ∈ Qm, JMatched c a b v := fun v hv => by
    obtain ⟨hvQ, hvP⟩ := mem_sdiff.1 hv
    by_contra hvm
    have hvu : v ≠ u := fun h => hvP (h ▸ mem_insert_self _ _)
    exact hvP (huniq v hvu (mem_filter.1 hvQ).2 hvm ▸ mem_insert_of_mem (mem_singleton_self _))
  -- the `J`-partner, an involution of `Qm` exchanging `S` and `i S`
  let jp : V → V := fun v => if h : ∃ y, JRel c a b v y then h.choose else v
  have hjp : ∀ v ∈ Qm, JRel c a b v (jp v) := fun v hv => by
    have h := jMatched_iff.1 (hQm v hv)
    simp only [jp, dite_eq_left h]; exact h.choose_spec
  have hjpQm : ∀ v ∈ Qm, jp v ∈ Qm := fun v hv => by
    have hj := hjp v hv
    obtain ⟨hvQ, -⟩ := mem_sdiff.1 hv
    have hve : IsEnd c a b v := isEnd_of_jk_reachable hu (mem_filter.1 hvQ).2
    have hne' : v ≠ jp v := fun e => hve.swap_ne (by rw [← hj.1, ← e])
    have hadj : H.Adj v (jp v) := ⟨hne', hve, hve.of_swap _ hj.1, Or.inr hj⟩
    refine mem_sdiff.2 ⟨mem_filter.2 ⟨mem_univ _, (mem_filter.1 hvQ).2.trans hadj.reachable⟩, ?_⟩
    intro hP
    have hmat : JMatched c a b (jp v) := jMatched_iff.2 ⟨v, hj.symm⟩
    rcases mem_insert.1 hP with h | h
    · rw [h] at hmat; exact hm hmat
    · rw [mem_singleton.1 h] at hmat; exact hum hmat
  have hjpjp : ∀ v ∈ Qm, jp (jp v) = v := fun v hv =>
    JRel.unique (hjp _ (hjpQm v hv)) (hjp v hv).symm
  have hQmswap : #(Qm.filter fun v => swapSet a b (colSet c v) = T) =
      #(Qm.filter fun v => colSet c v = T) := by
    refine card_bij (fun v _ => jp v) (fun v hv => ?_) (fun v hv w hw h => ?_) (fun w hw => ?_)
    · obtain ⟨hvQm, hvT⟩ := mem_filter.1 hv
      exact mem_filter.2 ⟨hjpQm v hvQm, by rw [(hjp v hvQm).1, hvT]⟩
    · rw [← hjpjp v (mem_filter.1 hv).1, h, hjpjp w (mem_filter.1 hw).1]
    · obtain ⟨hwQm, hwT⟩ := mem_filter.1 hw
      refine ⟨jp w, mem_filter.2 ⟨hjpQm w hwQm, ?_⟩, hjpjp w hwQm⟩
      rw [(hjp w hwQm).1, swapSet_swapSet, hwT]
  -- assemble the counts
  have hcnt : ∀ (f : V → Finset (Fin k)), #(univ.filter fun v => f v = T) =
      #((univ \ Q).filter fun v => f v = T) + #(Qm.filter fun v => f v = T) +
        #(P.filter fun v => f v = T) := by
    intro f
    have hPQ : P ⊆ Q := by
      intro v hv; rcases mem_insert.1 hv with rfl | hv
      · exact huQ
      · rw [mem_singleton.1 hv]; exact hu'Q
    rw [← card_union_of_disjoint, ← card_union_of_disjoint]
    · congr 1; ext v
      simp only [mem_union, mem_filter, mem_sdiff, mem_univ, true_and, Qm]
      have hv := @hPQ v
      by_cases hvQ : v ∈ Q <;> by_cases hvP : v ∈ P <;> simp_all
    · rw [Finset.disjoint_left]; intro v h1 h2
      rcases mem_union.1 h1 with h1 | h1
      · exact (mem_sdiff.1 (mem_filter.1 h1).1).2 (hPQ (mem_filter.1 h2).1)
      · exact (mem_sdiff.1 (mem_filter.1 h1).1).2 (mem_filter.1 h2).1
    · rw [Finset.disjoint_left]; intro v h1 h2
      exact (mem_sdiff.1 (mem_filter.1 h1).1).2 (mem_sdiff.1 (mem_filter.1 h2).1).1
  have h1 := hcnt (colSet c')
  have h2 := hcnt (colSet c)
  have e1 : ((univ \ Q).filter fun v => colSet c' v = T) = (univ \ Q).filter
      fun v => colSet c v = T := filter_congr fun v hv => by
    rw [hset, ite_eq_right (mem_sdiff.1 hv).2]
  have e2 : (Qm.filter fun v => colSet c' v = T) = Qm.filter
      fun v => swapSet a b (colSet c v) = T := filter_congr fun v hv => by
    rw [hset, ite_eq_left (mem_sdiff.1 hv).1]
  have e3 : (P.filter fun v => colSet c' v = T) = P.filter
      fun v => swapSet a b (colSet c v) = T := filter_congr fun v hv => by
    have : v ∈ Q := by
      rcases mem_insert.1 hv with rfl | hv
      · exact huQ
      · rw [mem_singleton.1 hv]; exact hu'Q
    rw [hset, ite_eq_left this]
  have hP : ∀ f : V → Finset (Fin k), #(P.filter fun v => f v = T) = ind (f u) T + ind (f u')
      T := by
    intro f
    rw [filter_insert, filter_singleton]
    unfold ind
    split_ifs with h1 h2 h2 <;> simp [card_insert_of_notMem, Ne.symm hne, *]
  unfold cnt
  rw [h1, h2, e1, e2, e3, hQmswap, hP, hP]
  omega
end Bkls

end LeanPool.BalancedEdgeColourings
