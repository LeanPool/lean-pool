/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.SwapX

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 8, part (a): the graph `J ∪ J' ∪ K`

`Jx` is a matching on the ends unmatched by `J`. In `mGraph` (ends; Kempe partners, `J`, `Jx`)
every vertex has degree at most two and a vertex unmatched by `J` and `Jx` has degree one, so its
component contains exactly one other such vertex (`exists_unique_other_endX`). The component is
closed under Kempe partners and `J`, so `swap_exchange` applies to it (`swap_component`).
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
variable {c : PEC G (Fin k)} {a b : Fin k}

/-- A matching on the `J`-unmatched ends. -/
structure XMatch (c : PEC G (Fin k)) (a b : Fin k) (Jx : V → V → Prop) : Prop where
  symm : ∀ u v, Jx u v → Jx v u
  uniq : ∀ u v w, Jx u v → Jx u w → v = w
  ends : ∀ u v, Jx u v → IsEnd c a b u ∧ ¬ JMatched c a b u ∧ u ≠ v

variable (c a b) in
open Classical in
/-- The graph `J ∪ J' ∪ K` on the ends. -/
def mGraph (Jx : V → V → Prop) (hJ : XMatch c a b Jx) : SimpleGraph V where
  Adj u v := u ≠ v ∧ IsEnd c a b u ∧ IsEnd c a b v ∧
    ((c.kempeGraph a b).Reachable u v ∨ JRel c a b u v ∨ Jx u v)
  symm.symm := by
    rintro u v ⟨h1, h2, h3, h4⟩
    refine ⟨h1.symm, h3, h2, ?_⟩
    rcases h4 with r | ⟨e, er⟩ | x
    · exact Or.inl r.symm
    · right; left; exact ⟨by rw [e, swapSet_swapSet], er.symm⟩
    · right; right; exact hJ.symm _ _ x
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {Jx : V → V → Prop} {hJ : XMatch c a b Jx}

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem isEnd_of_m_reachable {u v : V} (hu : IsEnd c a b u)
    (h : (mGraph c a b Jx hJ).Reachable u v) : IsEnd c a b v := by
  classical
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact hu
  | cons hadj p =>
    obtain ⟨q⟩ := (Walk.reachable p).symm
    cases q with
    | nil => exact hadj.2.2.1
    | cons hadj' _ => exact (mGraph c a b Jx hJ).symm.symm _ _ hadj' |>.2.2.1

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem m_adj_iff {u v : V} (hu : IsEnd c a b u) {x : V} (hx : x ≠ u)
    (hrx : (c.kempeGraph a b).Reachable u x) (hxe : IsEnd c a b x) :
    (mGraph c a b Jx hJ).Adj u v ↔ v = x ∨ JRel c a b u v ∨ Jx u v := by
  classical
  constructor
  · rintro ⟨huv, -, hv, h | h | h⟩
    · left; exact end_reach_unique hu hv hxe huv hx.symm h hrx
    · right; left; exact h
    · right; right; exact h
  · rintro (rfl | h | h)
    · exact ⟨hx.symm, hu, hxe, Or.inl hrx⟩
    · refine ⟨fun e => hu.swap_ne ?_, hu, hu.of_swap v h.1, Or.inr (Or.inl h)⟩
      rw [← h.1, e]
    · obtain ⟨-, -, hne⟩ := hJ.ends u v h
      exact ⟨hne, hu, (hJ.ends v u (hJ.symm u v h)).1, Or.inr (Or.inr h)⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The `J ∪ J'` partner, if any. -/
theorem m_partner_unique (hJ : XMatch c a b Jx) {u y z : V} (hy : JRel c a b u y ∨ Jx u y)
    (hz : JRel c a b u z ∨ Jx u z) : y = z := by
  classical
  rcases hy with hy | hy <;> rcases hz with hz | hz
  · exact JRel.unique hy hz
  · exact absurd (jMatched_iff.2 ⟨y, hy⟩) (hJ.ends u z hz).2.1
  · exact absurd (jMatched_iff.2 ⟨z, hz⟩) (hJ.ends u y hy).2.1
  · exact hJ.uniq u y z hy hz

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem m_degree_le_two (hab : a ≠ b) (u : V) : (mGraph c a b Jx hJ).degree u ≤ 2 := by
  classical
  rw [← card_neighborFinset_eq_degree]
  by_cases hu : IsEnd c a b u
  · obtain ⟨x, hx, hrx, hxe⟩ := exists_kempe_partner c hab hu
    by_cases hm : ∃ y, JRel c a b u y ∨ Jx u y
    · obtain ⟨y, hy⟩ := hm
      calc _ ≤ #({x, y} : Finset V) := card_le_card fun v hv => by
            rw [mem_neighborFinset, m_adj_iff hu hx hrx hxe] at hv
            rcases hv with rfl | h
            · exact mem_insert_self _ _
            · rw [m_partner_unique hJ h hy]; exact mem_insert_of_mem (mem_singleton_self _)
        _ ≤ 2 := card_le_two
    · calc _ ≤ #({x} : Finset V) := card_le_card fun v hv => by
            rw [mem_neighborFinset, m_adj_iff hu hx hrx hxe] at hv
            rcases hv with rfl | h
            · exact mem_singleton_self _
            · exact absurd ⟨v, h⟩ hm
        _ ≤ 2 := by simp
  · have : (mGraph c a b Jx hJ).neighborFinset u = ∅ := by
      ext v; simp only [mem_neighborFinset, notMem_empty, iff_false]
      exact fun h => hu h.2.1
    rw [this]; simp

open Classical in
/-- Unmatched by `J` and `J'`. -/
def FreeX (c : PEC G (Fin k)) (a b : Fin k) (Jx : V → V → Prop) (u : V) : Prop :=
  ¬ JMatched c a b u ∧ ¬ ∃ v, Jx u v

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem freeX_iff {u : V} : FreeX c a b Jx u ↔ ¬ ∃ v, JRel c a b u v ∨ Jx u v := by
  classical
  unfold FreeX
  rw [jMatched_iff]
  constructor
  · rintro ⟨h1, h2⟩ ⟨v, hv | hv⟩
    · exact h1 ⟨v, hv⟩
    · exact h2 ⟨v, hv⟩
  · intro h
    exact ⟨fun ⟨v, hv⟩ => h ⟨v, Or.inl hv⟩, fun ⟨v, hv⟩ => h ⟨v, Or.inr hv⟩⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem m_degree_free (hab : a ≠ b) {u : V} (hu : IsEnd c a b u) (hf : FreeX c a b Jx u) :
    (mGraph c a b Jx hJ).degree u = 1 := by
  classical
  obtain ⟨x, hx, hrx, hxe⟩ := exists_kempe_partner c hab hu
  rw [← card_neighborFinset_eq_degree, card_eq_one]
  refine ⟨x, ?_⟩
  ext v
  rw [mem_neighborFinset, m_adj_iff hu hx hrx hxe, mem_singleton]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd ⟨v, h⟩ (freeX_iff.1 hf)
  · exact Or.inl

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **The other free end.** -/
theorem exists_unique_other_endX (hab : a ≠ b) {u : V} (hu : IsEnd c a b u)
    (hf : FreeX c a b Jx u) :
    ∃ u', u' ≠ u ∧ (mGraph c a b Jx hJ).Reachable u u' ∧ IsEnd c a b u' ∧ FreeX c a b Jx u' ∧
      ∀ w, w ≠ u → (mGraph c a b Jx hJ).Reachable u w → FreeX c a b Jx w → w = u' := by
  classical
  have hdu := m_degree_free (hJ := hJ) hab hu hf
  obtain ⟨u', hne, hr, hodd⟩ := exists_reachable_odd (mGraph c a b Jx hJ) (u := u)
    (by rw [hdu]; exact odd_one)
  have hd1 : (mGraph c a b Jx hJ).degree u' = 1 := by
    have := m_degree_le_two (hJ := hJ) hab u'
    obtain ⟨m, hm'⟩ := hodd
    omega
  have hue : IsEnd c a b u' := isEnd_of_m_reachable hu hr
  have hum : FreeX c a b Jx u' := by
    rw [freeX_iff]
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hrx, hxe⟩ := exists_kempe_partner c hab hue
    have hadjx : (mGraph c a b Jx hJ).Adj u' x := (m_adj_iff hue hx hrx hxe).2 (Or.inl rfl)
    have hadjy : (mGraph c a b Jx hJ).Adj u' y := (m_adj_iff hue hx hrx hxe).2 (Or.inr hy)
    have hxy : x = y := by
      have h1 : #({x, y} : Finset V) ≤ (mGraph c a b Jx hJ).degree u' := by
        rw [← card_neighborFinset_eq_degree]
        exact card_le_card fun v hv => by
          rcases mem_insert.1 hv with rfl | hv
          · exact (mem_neighborFinset _ _ _).2 hadjx
          · rw [mem_singleton.1 hv]; exact (mem_neighborFinset _ _ _).2 hadjy
      by_contra hxy
      rw [card_pair hxy] at h1; omega
    subst hxy
    -- the component of `u'` is `{u', x}`
    have hyx : JRel c a b x u' ∨ Jx x u' := by
      rcases hy with h | h
      · exact Or.inl h.symm
      · exact Or.inr (hJ.symm _ _ h)
    have hTclosed : ∀ z ∈ ({u', x} : Finset V), ∀ w, (mGraph c a b Jx hJ).Adj z w →
        w ∈ ({u', x} : Finset V) := by
      intro z hz w hw
      rcases mem_insert.1 hz with rfl | hz
      · rw [m_adj_iff hue hx hrx hxe] at hw
        rcases hw with rfl | hw
        · exact mem_insert_of_mem (mem_singleton_self _)
        · rw [m_partner_unique hJ hw hy]; exact mem_insert_of_mem (mem_singleton_self _)
      · rw [mem_singleton.1 hz] at hw
        rw [m_adj_iff hxe (Ne.symm hx) hrx.symm hue] at hw
        rcases hw with rfl | hw
        · exact mem_insert_self _ _
        · rw [m_partner_unique hJ hw hyx]; exact mem_insert_self _ _
    have huT := mem_of_reachable_of_closed hTclosed (mem_insert_self _ _) hr.symm
    rcases mem_insert.1 huT with h | h
    · exact hne h.symm
    · rw [mem_singleton.1 h] at hf
      exact (freeX_iff.1 hf) ⟨u', hyx⟩
  refine ⟨u', hne, hr, hue, hum, fun w hwu hrw hwm => ?_⟩
  by_contra hww
  have hwe := isEnd_of_m_reachable hu hrw
  exact no_three_endpoints (H := mGraph c a b Jx hJ) (m_degree_le_two hab) (Ne.symm hne)
    (Ne.symm hwu) (fun e => hww e.symm) (by rw [hdu])
    (by rw [hd1]) (by rw [m_degree_free hab hwe hwm]) hr hrw

open Classical in
/-- The component of `u`. -/
noncomputable def mComp (c : PEC G (Fin k)) (a b : Fin k) (Jx : V → V → Prop)
    (hJ : XMatch c a b Jx) (u : V) : Finset V :=
  univ.filter fun v => (mGraph c a b Jx hJ).Reachable u v

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem mComp_closed {u q v : V} (hq : q ∈ mComp c a b Jx hJ u)
    (hadj : (mGraph c a b Jx hJ).Adj q v) : v ∈ mComp c a b Jx hJ u := by
  classical
  exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hq).2.trans hadj.reachable⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem mComp_end {u q : V} (hu : IsEnd c a b u) (hq : q ∈ mComp c a b Jx hJ u) :
    IsEnd c a b q := by
  classical
  exact isEnd_of_m_reachable hu (mem_filter.1 hq).2

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **The swap of a component.** -/
theorem swap_component (hopt : IsOptimal c) (hab : a ≠ b) {u : V} (hu : IsEnd c a b u) :
    ∃ c' : PEC G (Fin k), IsOptimal c' ∧ ∀ T, cnt c' T = cnt c
      (if 0 < pcnt c ((mComp c a b Jx hJ u).filter fun v => ¬ JMatched c a b v) T ∨
          0 < pcnt c ((mComp c a b Jx hJ u).filter fun v => ¬ JMatched c a b v) (swapSet a b T)
        then swapSet a b T else T) := by
  classical
  apply swap_exchange hopt hab
  · intro q hq v hv hr
    by_cases hqv : q = v
    · rw [← hqv]; exact hq
    · exact mComp_closed hq ⟨hqv, mComp_end hu hq, hv, Or.inl hr⟩
  · intro q hq v hv
    exact mComp_closed hq ⟨fun e => (mComp_end hu hq).swap_ne (by rw [← hv.1, e]), mComp_end hu hq,
      (mComp_end hu hq).of_swap v hv.1, Or.inr (Or.inl hv)⟩
end Bkls

end LeanPool.BalancedEdgeColourings
