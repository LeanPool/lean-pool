/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Rec
public import Mathlib.Tactic.LinearCombination

/-!
# Swapping a set of ends closed under Kempe partners and `J`

`swapQ`: swapping `a, b` on all the Kempe paths through a set `Q` of ends closed under Kempe
partners replaces `S(v)` by `i S(v)` exactly for `v ∈ Q`.

`swap_exchange`: if moreover `Q` is closed under `J` and the colouring is optimal, the `J`-matched
vertices of `Q` cancel, and optimality forces every pair `{T, i T}` met by a `J`-unmatched vertex of
`Q` to be exchanged completely (`Σ_T 2 p_T (p_T - δ_T) ≤ 0` with equality only then): the result is
an optimal colouring whose counts are those of `c` with these pairs interchanged.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
variable {c : PEC G (Fin k)} {a b : Fin k}

open Classical in
omit [DecidableRel G.Adj] [Fintype V] in
/-- **Swapping the Kempe paths through `Q`.** -/
theorem swapQ [Finite V] (htot : Total c) {Q : Finset V}
    (hQK : ∀ q ∈ Q, ∀ v, IsEnd c a b v → (c.kempeGraph a b).Reachable q v → v ∈ Q) :
    ∃ c' : PEC G (Fin k), Total c' ∧
      ∀ v, colSet c' v = if v ∈ Q then swapSet a b (colSet c v) else colSet c v := by
  classical
  let : Fintype V := Fintype.ofFinite V
  set X := univ.filter fun v => ∃ q ∈ Q, (c.kempeGraph a b).Reachable q v
  have hXc : KClosed c a b X := by
    intro v w hv hcol
    obtain ⟨q, hq, hqv⟩ := (mem_filter.1 hv).2
    exact mem_filter.2 ⟨mem_univ _, q, hq, hqv.trans (kempeGraph_adj_of_col hcol).reachable⟩
  refine ⟨swapOn c a b X hXc, Total.swapOn hXc htot, fun v => ?_⟩
  by_cases hvX : v ∈ X
  · rw [colSet_swapOn_of_mem hXc hvX]
    split_ifs with hvQ
    · rfl
    · obtain ⟨q, hq, hqv⟩ := (mem_filter.1 hvX).2
      have hve : ¬ IsEnd c a b v := fun hve => hvQ (hQK q hq v hve hqv)
      apply swapSet_eq_of_iff
      simp only [IsEnd, not_or, not_and, not_not] at hve
      tauto
  · rw [colSet_swapOn_of_not_mem hXc hvX]
    split_ifs with hvQ
    · exact absurd (mem_filter.2 ⟨mem_univ _, v, hvQ, Reachable.refl _⟩) hvX
    · rfl

open Classical in
/-- The number of `J`-unmatched vertices of `P` with colour set `T`. -/
noncomputable def pcnt (c : PEC G (Fin k)) (P : Finset V) (T : Finset (Fin k)) : ℕ :=
  #(P.filter fun v => colSet c v = T)

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- `J`-unmatched vertices with colour set `T`: at most `n_T - n_{i T}` of them. -/
theorem card_unmatched_le (P : Finset V) (hP : ∀ v ∈ P, ¬ JMatched c a b v)
    (T : Finset (Fin k)) : pcnt c P T ≤ cnt c T - cnt c (swapSet a b T) := by
  classical
  unfold pcnt
  have hmaps : ∀ v ∈ P.filter (fun v => colSet c v = T), rank c v ∈ Ico (cnt c (swapSet a b T))
      (cnt c T) := by
    intro v hv
    obtain ⟨hvP, hvT⟩ := mem_filter.1 hv
    have h1 := rank_lt_cnt c v
    have h2 := hP v hvP
    unfold JMatched at h2
    rw [hvT] at h1 h2
    exact mem_Ico.2 ⟨by omega, h1⟩
  have hinj : Set.InjOn (rank c) ↑(P.filter fun v => colSet c v = T) := by
    intro u hu v hv h
    exact rank_injOn c ((mem_filter.1 hu).2.trans (mem_filter.1 hv).2.symm) h
  have := card_le_card_of_injOn (rank c) hmaps hinj
  rwa [Nat.card_Ico] at this
open Classical in
theorem swapSet_equiv_sum {M : Type*} [AddCommMonoid M] (g : Finset (Fin k) → M) :
    ∑ T, g (swapSet a b T) = ∑ T, g T := by
  refine Fintype.sum_equiv ⟨swapSet a b, swapSet a b, fun T => swapSet_swapSet a b T,
    fun T => swapSet_swapSet a b T⟩ _ _ (fun T => rfl)

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **The exchange swap.** -/
theorem swap_exchange (hopt : IsOptimal c) (_ : a ≠ b) {Q : Finset V}
    (hQK : ∀ q ∈ Q, ∀ v, IsEnd c a b v → (c.kempeGraph a b).Reachable q v → v ∈ Q)
    (hQJ : ∀ q ∈ Q, ∀ v, JRel c a b q v → v ∈ Q) :
    ∃ c' : PEC G (Fin k), IsOptimal c' ∧ ∀ T, cnt c' T = cnt c
      (if 0 < pcnt c (Q.filter fun v => ¬ JMatched c a b v) T ∨
          0 < pcnt c (Q.filter fun v => ¬ JMatched c a b v) (swapSet a b T)
        then swapSet a b T else T) := by
  classical
  obtain ⟨c', htot', hset⟩ := swapQ hopt.1 hQK
  set P := Q.filter fun v => ¬ JMatched c a b v with hPdef
  set Qm := Q.filter fun v => JMatched c a b v
  have hPu : ∀ v ∈ P, ¬ JMatched c a b v := fun v hv => (mem_filter.1 hv).2
  -- the `J`-partner, an involution of `Qm`
  let jp : V → V := fun v => if h : ∃ y, JRel c a b v y then h.choose else v
  have hjp : ∀ v ∈ Qm, JRel c a b v (jp v) := fun v hv => by
    have h := jMatched_iff.1 (mem_filter.1 hv).2
    simp only [jp, dite_eq_left h]; exact h.choose_spec
  have hjpQm : ∀ v ∈ Qm, jp v ∈ Qm := fun v hv =>
    mem_filter.2 ⟨hQJ v (mem_filter.1 hv).1 _ (hjp v hv), jMatched_iff.2 ⟨v, (hjp v hv).symm⟩⟩
  have hjpjp : ∀ v ∈ Qm, jp (jp v) = v := fun v hv =>
    JRel.unique (hjp _ (hjpQm v hv)) (hjp v hv).symm
  have hQmswap : ∀ T, #(Qm.filter fun v => swapSet a b (colSet c v) = T) =
      #(Qm.filter fun v => colSet c v = T) := by
    intro T
    refine card_bij (fun v _ => jp v) (fun v hv => ?_) (fun v hv w hw h => ?_) (fun w hw => ?_)
    · obtain ⟨hvQm, hvT⟩ := mem_filter.1 hv
      exact mem_filter.2 ⟨hjpQm v hvQm, by rw [(hjp v hvQm).1, hvT]⟩
    · rw [← hjpjp v (mem_filter.1 hv).1, h, hjpjp w (mem_filter.1 hw).1]
    · obtain ⟨hwQm, hwT⟩ := mem_filter.1 hw
      refine ⟨jp w, mem_filter.2 ⟨hjpQm w hwQm, ?_⟩, hjpjp w hwQm⟩
      rw [(hjp w hwQm).1, swapSet_swapSet, hwT]
  -- the counts
  have hsplit : ∀ (f : V → Finset (Fin k)) (T : Finset (Fin k)),
      #(univ.filter fun v => f v = T) = #((univ \ Q).filter fun v => f v = T) +
        #(Qm.filter fun v => f v = T) + #(P.filter fun v => f v = T) := by
    intro f T
    rw [← card_union_of_disjoint, ← card_union_of_disjoint]
    · congr 1; ext v
      simp only [mem_union, mem_filter, mem_sdiff, mem_univ, true_and, Qm, P]
      by_cases hvQ : v ∈ Q <;> by_cases hvm : JMatched c a b v <;> simp_all
    · rw [Finset.disjoint_left]; intro v h1 h2
      rcases mem_union.1 h1 with h1 | h1
      · exact (mem_sdiff.1 (mem_filter.1 h1).1).2 (mem_filter.1 (mem_filter.1 h2).1).1
      · exact (mem_filter.1 (mem_filter.1 h2).1).2 (mem_filter.1 (mem_filter.1 h1).1).2
    · rw [Finset.disjoint_left]; intro v h1 h2
      exact (mem_sdiff.1 (mem_filter.1 h1).1).2 (mem_filter.1 (mem_filter.1 h2).1).1
  have hc' : ∀ T, (cnt c' T : ℤ) = cnt c T - pcnt c P T + pcnt c P (swapSet a b T) := by
    intro T
    have h1 := hsplit (colSet c') T
    have h2 := hsplit (colSet c) T
    have e1 : ((univ \ Q).filter fun v => colSet c' v = T) =
        (univ \ Q).filter fun v => colSet c v = T :=
      filter_congr fun v hv => by rw [hset, ite_eq_right (mem_sdiff.1 hv).2]
    have e2 : (Qm.filter fun v => colSet c' v = T) =
        Qm.filter fun v => swapSet a b (colSet c v) = T :=
      filter_congr fun v hv => by rw [hset, ite_eq_left (mem_filter.1 hv).1]
    have e3 : (P.filter fun v => colSet c' v = T) =
        P.filter fun v => colSet c v = swapSet a b T :=
      filter_congr fun v hv => by
        rw [hset, ite_eq_left (mem_filter.1 hv).1]
        constructor
        · intro h; rw [← h, swapSet_swapSet]
        · intro h; rw [h, swapSet_swapSet]
    unfold cnt pcnt
    rw [h1, h2, e1, e2, e3, hQmswap]
    push_cast; ring
  -- `p_T > 0` only on the larger side
  have hle := card_unmatched_le P hPu
  have hone : ∀ T, 0 < pcnt c P T → pcnt c P (swapSet a b T) = 0 := by
    intro T hT
    have h1 := hle T
    have h2 := hle (swapSet a b T)
    rw [swapSet_swapSet] at h2
    omega
  -- the cost identity
  have hz : ∀ T, (pcnt c P T : ℤ) * pcnt c P (swapSet a b T) = 0 := by
    intro T
    by_cases h : 0 < pcnt c P T
    · rw [hone T h]; simp
    · have : pcnt c P T = 0 := by omega
      rw [this]; simp
  set G : Finset (Fin k) → ℤ := fun T =>
    ((cnt c T : ℤ) - pcnt c P T + pcnt c P (swapSet a b T)) ^ 2 - (cnt c T : ℤ) ^ 2 with hGdef
  set H : Finset (Fin k) → ℤ := fun T =>
    2 * ((pcnt c P T : ℤ) * (pcnt c P T - (cnt c T - cnt c (swapSet a b T)))) with hHdef
  have hG : ∀ T, G T + G (swapSet a b T) = H T + H (swapSet a b T) := by
    intro T
    simp only [hGdef, hHdef, swapSet_swapSet]
    linear_combination (-4 : ℤ) * hz T
  have hsumG : ∑ T, G T = ∑ T, H T := by
    have e1 := swapSet_equiv_sum (a := a) (b := b) G
    have e2 := swapSet_equiv_sum (a := a) (b := b) H
    have e3 : ∑ T, (G T + G (swapSet a b T)) = ∑ T, (H T + H (swapSet a b T)) :=
      sum_congr rfl fun T _ => hG T
    rw [sum_add_distrib, sum_add_distrib, e1, e2] at e3
    linarith
  have hcost : ∑ T, ((cnt c' T : ℤ)) ^ 2 - ∑ T, ((cnt c T : ℤ)) ^ 2 =
      2 * ∑ T, (pcnt c P T : ℤ) * (pcnt c P T - (cnt c T - cnt c (swapSet a b T))) := by
    simp only [hc']
    rw [← sum_sub_distrib, mul_sum]
    exact hsumG
  have hnp : ∀ T, (pcnt c P T : ℤ) * (pcnt c P T - (cnt c T - cnt c (swapSet a b T))) ≤ 0 := by
    intro T
    by_cases hp : pcnt c P T = 0
    · rw [hp]; simp
    have := hle T
    have h0 : (0 : ℤ) ≤ pcnt c P T := by positivity
    have : (pcnt c P T : ℤ) - (cnt c T - cnt c (swapSet a b T)) ≤ 0 := by
      have : pcnt c P T + cnt c (swapSet a b T) ≤ cnt c T := by omega
      have : (pcnt c P T : ℤ) + cnt c (swapSet a b T) ≤ cnt c T := by exact_mod_cast this
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos h0 this
  have hopt' := cost_le_of_opt hopt htot'
  have hsum0 : ∑ T, (pcnt c P T : ℤ) * (pcnt c P T - (cnt c T - cnt c (swapSet a b T))) = 0 := by
    apply le_antisymm (sum_nonpos fun T _ => hnp T)
    linarith
  have heach := (sum_eq_zero_iff_of_nonpos (fun T _ => hnp T)).1 hsum0
  refine ⟨c', isOptimal_of_cost_eq hopt htot' (by linarith), fun T => ?_⟩
  have hT := heach T (mem_univ T)
  have hiT := heach (swapSet a b T) (mem_univ _)
  rw [swapSet_swapSet] at hiT
  have hcT := hc' T
  split_ifs with h
  · rcases h with h | h
    · have h0 := hone T h
      rw [h0, Nat.cast_zero] at hcT
      rcases mul_eq_zero.1 hT with e | e
      · exact absurd (by exact_mod_cast e) (Nat.pos_iff_ne_zero.1 h)
      · have : (cnt c' T : ℤ) = cnt c (swapSet a b T) := by linarith
        exact_mod_cast this
    · have h0 := hone _ h
      rw [swapSet_swapSet] at h0
      rw [h0, Nat.cast_zero] at hcT
      rcases mul_eq_zero.1 hiT with e | e
      · exact absurd (by exact_mod_cast e) (Nat.pos_iff_ne_zero.1 h)
      · have : (cnt c' T : ℤ) = cnt c (swapSet a b T) := by linarith
        exact_mod_cast this
  · push Not at h
    have h1 : pcnt c P T = 0 := by omega
    have h2 : pcnt c P (swapSet a b T) = 0 := by omega
    rw [h1, h2] at hcT
    have : (cnt c' T : ℤ) = cnt c T := by simpa using hcT
    exact_mod_cast this
end Bkls

end LeanPool.BalancedEdgeColourings
