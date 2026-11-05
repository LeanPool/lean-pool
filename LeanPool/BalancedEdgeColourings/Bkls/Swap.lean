/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Rank

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 2: the simultaneous swap

For an end `u` unmatched by `J`, the component of `u` in `J ∪ K` contains exactly one other
unmatched end `u'` (`exists_unique_other_end`). Swapping `a, b` on all the Kempe paths of that
component changes the colour sets of its ends only, and the counts `n_T` change by
`n'_T = n_T − [S(u) = T] − [S(u') = T] + [i S(u) = T] + [i S(u') = T]` (`exists_swap`).
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
variable {c : PEC G (Fin k)} {a b : Fin k}

open Classical in
omit [DecidableEq V] [Fintype V] in
/-- Reachability stays in a set closed under adjacency. -/
theorem mem_of_reachable_of_closed {H : SimpleGraph V} {T : Finset V}
    (hT : ∀ x ∈ T, ∀ z, H.Adj x z → z ∈ T) {x z : V} (hx : x ∈ T) (h : H.Reachable x z) :
    z ∈ T := by
  classical
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hx
  | cons hadj _ ih => exact ih (hT _ hx _ hadj)

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem isEnd_of_jk_adj {u v : V} (h : (jkGraph c a b).Adj u v) : IsEnd c a b u := by
  classical
  exact h.2.1

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Every vertex reachable from an end in `J ∪ K` is an end. -/
theorem isEnd_of_jk_reachable {u v : V} (hu : IsEnd c a b u) (h : (jkGraph c a b).Reachable u v) :
    IsEnd c a b v := by
  classical
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact hu
  | cons hadj p =>
    obtain ⟨q⟩ := (Walk.reachable p).symm
    cases q with
    | nil => exact hadj.2.2.1
    | cons hadj' _ => exact (jkGraph c a b).symm.symm _ _ hadj' |>.2.2.1

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The neighbours of an end in `J ∪ K`: its Kempe partner and its `J`-partner. -/
theorem jk_adj_iff {u v : V} (hu : IsEnd c a b u) {x : V} (hx : x ≠ u)
    (hrx : (c.kempeGraph a b).Reachable u x) (hxe : IsEnd c a b x) :
    (jkGraph c a b).Adj u v ↔ v = x ∨ (JRel c a b u v) := by
  classical
  constructor
  · rintro ⟨huv, -, hv, h | h⟩
    · left; exact end_reach_unique hu hv hxe huv hx.symm h hrx
    · right; exact h
  · rintro (rfl | h)
    · exact ⟨hx.symm, hu, hxe, Or.inl hrx⟩
    · refine ⟨fun e => hu.swap_ne ?_, hu, hu.of_swap v h.1, Or.inr h⟩
      rw [← h.1, e]

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem jk_degree_le_two (hab : a ≠ b) (u : V) : (jkGraph c a b).degree u ≤ 2 := by
  classical
  by_cases hu : IsEnd c a b u
  · obtain ⟨x, hx, hrx, hxe⟩ := exists_kempe_partner c hab hu
    rw [← card_neighborFinset_eq_degree]
    by_cases hm : ∃ y, JRel c a b u y
    · obtain ⟨y, hy⟩ := hm
      calc _ ≤ #({x, y} : Finset V) := card_le_card fun v hv => by
            rw [mem_neighborFinset, jk_adj_iff hu hx hrx hxe] at hv
            rcases hv with rfl | h
            · exact mem_insert_self _ _
            · rw [JRel.unique h hy]; exact mem_insert_of_mem (mem_singleton_self _)
        _ ≤ 2 := card_le_two
    · calc _ ≤ #({x} : Finset V) := card_le_card fun v hv => by
            rw [mem_neighborFinset, jk_adj_iff hu hx hrx hxe] at hv
            rcases hv with rfl | h
            · exact mem_singleton_self _
            · exact absurd ⟨v, h⟩ hm
        _ ≤ 2 := by simp
  · rw [← card_neighborFinset_eq_degree]
    have : (jkGraph c a b).neighborFinset u = ∅ := by
      ext v; simp only [mem_neighborFinset, notMem_empty, iff_false]
      exact fun h => hu h.2.1
    rw [this]; simp

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem jk_degree_unmatched (hab : a ≠ b) {u : V} (hu : IsEnd c a b u)
    (hm : ¬ JMatched c a b u) : (jkGraph c a b).degree u = 1 := by
  classical
  obtain ⟨x, hx, hrx, hxe⟩ := exists_kempe_partner c hab hu
  rw [← card_neighborFinset_eq_degree, card_eq_one]
  refine ⟨x, ?_⟩
  ext v
  rw [mem_neighborFinset, jk_adj_iff hu hx hrx hxe, mem_singleton, jMatched_iff] at *
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd ⟨v, h⟩ hm
  · exact Or.inl

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **The other unmatched end.** -/
theorem exists_unique_other_end (hab : a ≠ b) {u : V} (hu : IsEnd c a b u)
    (hm : ¬ JMatched c a b u) :
    ∃ u', u' ≠ u ∧ (jkGraph c a b).Reachable u u' ∧ IsEnd c a b u' ∧ ¬ JMatched c a b u' ∧
      ∀ w, w ≠ u → (jkGraph c a b).Reachable u w → ¬ JMatched c a b w → w = u' := by
  classical
  have hdu := jk_degree_unmatched hab hu hm
  obtain ⟨u', hne, hr, hodd⟩ := exists_reachable_odd (jkGraph c a b) (u := u)
    (by rw [hdu]; exact odd_one)
  have hd1 : (jkGraph c a b).degree u' = 1 := by
    have := jk_degree_le_two (c := c) hab u'
    obtain ⟨m, hm'⟩ := hodd
    omega
  have hue : IsEnd c a b u' := isEnd_of_jk_reachable hu hr
  -- `u'` is unmatched
  have hum : ¬ JMatched c a b u' := by
    intro hmat
    obtain ⟨y, hy⟩ := jMatched_iff.1 hmat
    obtain ⟨x, hx, hrx, hxe⟩ := exists_kempe_partner c hab hue
    have hadjx : (jkGraph c a b).Adj u' x := (jk_adj_iff hue hx hrx hxe).2 (Or.inl rfl)
    have hadjy : (jkGraph c a b).Adj u' y := (jk_adj_iff hue hx hrx hxe).2 (Or.inr hy)
    have hxy : x = y := by
      have h1 : #({x, y} : Finset V) ≤ (jkGraph c a b).degree u' := by
        rw [← card_neighborFinset_eq_degree]
        exact card_le_card fun v hv => by
          rcases mem_insert.1 hv with rfl | hv
          · exact (mem_neighborFinset _ _ _).2 hadjx
          · rw [mem_singleton.1 hv]; exact (mem_neighborFinset _ _ _).2 hadjy
      by_contra hxy
      rw [card_pair hxy] at h1; omega
    subst hxy
    -- the component of `u'` is `{u', x}`
    have hye : IsEnd c a b x := hxe
    have hTclosed : ∀ z ∈ ({u', x} : Finset V), ∀ w, (jkGraph c a b).Adj z w →
        w ∈ ({u', x} : Finset V) := by
      intro z hz w hw
      rcases mem_insert.1 hz with rfl | hz
      · rw [jk_adj_iff hue hx hrx hxe] at hw
        rcases hw with rfl | hw
        · exact mem_insert_of_mem (mem_singleton_self _)
        · rw [JRel.unique hw hy]; exact mem_insert_of_mem (mem_singleton_self _)
      · rw [mem_singleton.1 hz] at hw
        rw [jk_adj_iff hxe (Ne.symm hx) hrx.symm hue] at hw
        rcases hw with rfl | hw
        · exact mem_insert_self _ _
        · rw [JRel.unique hw hy.symm]; exact mem_insert_self _ _
    have huT := mem_of_reachable_of_closed hTclosed (mem_insert_self _ _) hr.symm
    rcases mem_insert.1 huT with h | h
    · exact hne h.symm
    · rw [mem_singleton.1 h] at hm
      exact hm (jMatched_iff.2 ⟨u', hy.symm⟩)
  refine ⟨u', hne, hr, hue, hum, fun w hwu hrw hwm => ?_⟩
  by_contra hww
  have hwe := isEnd_of_jk_reachable hu hrw
  exact no_three_endpoints (H := jkGraph c a b) (jk_degree_le_two hab) (Ne.symm hne)
    (Ne.symm hwu) (fun e => hww e.symm) (by rw [hdu])
    (by rw [hd1]) (by rw [jk_degree_unmatched hab hwe hwm]) hr hrw
end Bkls

end LeanPool.BalancedEdgeColourings
