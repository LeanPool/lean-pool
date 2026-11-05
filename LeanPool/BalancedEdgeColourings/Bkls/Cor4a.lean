/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.L3L

/-!
# Corollary 4: the graph of edges

`H` has maximum degree `2`; `m` is a partial matching of its vertices. The graph `LG H m` on the
edges of `H` joins two edges sharing a vertex (a vertex of degree two), and the edges at two matched
vertices of degree one (the article identifies such vertices). It has maximum degree two
(`degree_LG_le`): through each end of an edge passes at most one neighbour. The edge `Lv u` of
`LG` at a vertex `u` of degree two joins its two edges (`Lv_spec`, `Lv_inj`).
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.C4

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

omit [DecidableEq V] in
theorem mem_inc {v : V} {e : Sym2 V} : e ∈ H.incidenceFinset v ↔ e ∈ H.edgeSet ∧ v ∈ e := by
  classical
  rw [mem_incidenceFinset]; rfl

omit [DecidableEq V] in
theorem card_inc (v : V) : #(H.incidenceFinset v) = H.degree v := by
  classical
  exact card_incidenceFinset_eq_degree H v
variable {H}

omit [DecidableEq V] [DecidableRel H.Adj] [Fintype V] in
theorem edge_eq_of_mem {e : Sym2 V} (he : e ∈ H.edgeSet) {u v : V} (hu : u ∈ e) (hv : v ∈ e)
    (huv : u ≠ v) : e = s(u, v) := by
  classical
  induction e using Sym2.inductionOn with
  | hf a b =>
    rcases Sym2.mem_iff.1 hu with rfl | rfl <;> rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact absurd rfl huv
    · rfl
    · exact Sym2.eq_swap
    · exact absurd rfl huv

/-- Two distinct edges at `v`: `v` has degree two and these are its edges. -/
theorem inc_eq_pair (hdeg : ∀ v, H.degree v ≤ 2) {v : V} {e e' : Sym2 V}
    (he : e ∈ H.incidenceFinset v) (he' : e' ∈ H.incidenceFinset v) (hne : e ≠ e') :
    H.degree v = 2 ∧ H.incidenceFinset v = {e, e'} := by
  have hsub : ({e, e'} : Finset (Sym2 V)) ⊆ H.incidenceFinset v := by
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact he
    · rw [mem_singleton.1 hx]; exact he'
  have h2 := card_le_card hsub
  rw [card_pair hne, card_inc] at h2
  have h3 := hdeg v
  refine ⟨by omega, (eq_of_subset_of_card_le hsub ?_).symm⟩
  rw [card_pair hne, card_inc]; omega

omit [DecidableEq V] in
theorem inc_unique_of_deg_one {v : V} (h1 : H.degree v = 1) {e e' : Sym2 V}
    (he : e ∈ H.incidenceFinset v) (he' : e' ∈ H.incidenceFinset v) : e = e' := by
  classical
  rw [← card_inc] at h1
  obtain ⟨x, hx⟩ := card_eq_one.1 h1
  rw [hx] at he he'
  rw [mem_singleton.1 he, mem_singleton.1 he']
variable (H)

/-- The edges at two matched vertices of degree one. -/
def Merge (m : V → Option V) (e e' : Sym2 V) : Prop :=
  ∃ u v, m u = some v ∧ H.degree u = 1 ∧ H.degree v = 1 ∧ e ∈ H.incidenceFinset u ∧
    e' ∈ H.incidenceFinset v

/-- The graph on the edges of `H`. -/
def LG (m : V → Option V) : SimpleGraph (Sym2 V) where
  Adj e e' := e ≠ e' ∧ e ∈ H.edgeSet ∧ e' ∈ H.edgeSet ∧
    ((∃ w, w ∈ e ∧ w ∈ e') ∨ Merge H m e e' ∨ Merge H m e' e)
  symm := ⟨fun e e' ⟨h1, h2, h3, h4⟩ => ⟨fun h => h1 h.symm, h3, h2, by
    rcases h4 with ⟨w, hw, hw'⟩ | h | h
    · exact Or.inl ⟨w, hw', hw⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩⟩
  loopless := ⟨fun e h => h.1 rfl⟩

variable {H}

omit [DecidableEq V] in
theorem LG_adj {m : V → Option V} {e e' : Sym2 V} : (LG H m).Adj e e' ↔ e ≠ e' ∧
    e ∈ H.edgeSet ∧ e' ∈ H.edgeSet ∧ ((∃ w, w ∈ e ∧ w ∈ e') ∨ Merge H m e e' ∨ Merge H m e' e) := by
  classical
  exact Iff.rfl
variable (H) in
/-- The neighbours of `e` through its end `x`. -/
def Through (m : V → Option V) (e : Sym2 V) (x : V) (e' : Sym2 V) : Prop :=
  e' ≠ e ∧ e' ∈ H.edgeSet ∧ (x ∈ e' ∨ ∃ y, m x = some y ∧ H.degree x = 1 ∧ H.degree y = 1 ∧
    e' ∈ H.incidenceFinset y)

omit [DecidableEq V] in
/-- At most one neighbour of `e` passes through each end. -/
theorem through_unique (hdeg : ∀ v, H.degree v ≤ 2) {m : V → Option V} {e : Sym2 V}
    (he : e ∈ H.edgeSet) {x : V} (hx : x ∈ e) {a b : Sym2 V} (ha : Through H m e x a)
    (hb : Through H m e x b) : a = b := by
  classical
  have hex : e ∈ H.incidenceFinset x := (mem_inc H).2 ⟨he, hx⟩
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  rcases ha3 with hxa | ⟨y, hy, hx1, hy1, hay⟩ <;> rcases hb3 with hxb | ⟨y', hy', hx1', hy1', hby⟩
  · have hpa := inc_eq_pair hdeg hex ((mem_inc H).2 ⟨ha2, hxa⟩) (Ne.symm ha1)
    have hb' : b ∈ H.incidenceFinset x := (mem_inc H).2 ⟨hb2, hxb⟩
    rw [hpa.2] at hb'
    rcases mem_insert.1 hb' with h | h
    · exact absurd h hb1
    · exact (mem_singleton.1 h).symm
  · exfalso
    have := (inc_eq_pair hdeg hex ((mem_inc H).2 ⟨ha2, hxa⟩) (Ne.symm ha1)).1
    omega
  · exfalso
    have := (inc_eq_pair hdeg hex ((mem_inc H).2 ⟨hb2, hxb⟩) (Ne.symm hb1)).1
    omega
  · rw [hy] at hy'
    cases hy'
    exact inc_unique_of_deg_one hy1 hay hby

omit [DecidableEq V] in
/-- A neighbour of `e` passes through one of its ends. -/
theorem exists_through {m : V → Option V} (hm : ∀ u v, m u = some v → m v = some u)
    {e e' : Sym2 V} (h : (LG H m).Adj e e') : ∃ x ∈ e, Through H m e x e' := by
  classical
  obtain ⟨hne, he, he', h⟩ := h
  rcases h with ⟨w, hw, hw'⟩ | ⟨u, v, huv, hu1, hv1, heu, he'v⟩ | ⟨u, v, huv, hu1, hv1, he'u, hev⟩
  · exact ⟨w, hw, Ne.symm hne, he', Or.inl hw'⟩
  · exact ⟨u, ((mem_inc H).1 heu).2, Ne.symm hne, he', Or.inr ⟨v, huv, hu1, hv1, he'v⟩⟩
  · exact ⟨v, ((mem_inc H).1 hev).2, Ne.symm hne, he', Or.inr ⟨u, hm u v huv, hv1, hu1, he'u⟩⟩

omit [DecidableEq V] in
/-- **`LG` has maximum degree two.** -/
theorem degree_LG_le (hdeg : ∀ v, H.degree v ≤ 2) {m : V → Option V}
    (hm : ∀ u v, m u = some v → m v = some u) [DecidableRel (LG H m).Adj] (e : Sym2 V) :
    (LG H m).degree e ≤ 2 := by
  classical
  rw [← card_neighborFinset_eq_degree]
  induction e using Sym2.inductionOn with
  | hf a b =>
    by_cases he : s(a, b) ∈ H.edgeSet
    · set A := (LG H m).neighborFinset s(a, b) |>.filter fun e' => Through H m s(a, b) a e'
      set B := (LG H m).neighborFinset s(a, b) |>.filter fun e' => Through H m s(a, b) b e'
      have hsub : (LG H m).neighborFinset s(a, b) ⊆ A ∪ B := by
        intro e' he'
        obtain ⟨x, hx, hxe⟩ := exists_through hm ((mem_neighborFinset _ _ _).1 he')
        rcases Sym2.mem_iff.1 hx with rfl | rfl
        · exact mem_union_left _ (mem_filter.2 ⟨he', hxe⟩)
        · exact mem_union_right _ (mem_filter.2 ⟨he', hxe⟩)
      have hA : #A ≤ 1 := card_le_one.2 fun x hx y hy =>
        through_unique hdeg he (Sym2.mem_mk_left a b) (mem_filter.1 hx).2 (mem_filter.1 hy).2
      have hB : #B ≤ 1 := card_le_one.2 fun x hx y hy =>
        through_unique hdeg he (Sym2.mem_mk_right a b) (mem_filter.1 hx).2 (mem_filter.1 hy).2
      have := card_le_card hsub
      have := card_union_le A B
      omega
    · have : (LG H m).neighborFinset s(a, b) = ∅ := by
        ext e'
        simp only [mem_neighborFinset, notMem_empty, iff_false]
        exact fun h => he h.2.1
      rw [this, card_empty]; omega
variable (H)

/-- The edge of `LG` at a vertex of degree two: its two edges. -/
noncomputable def Lv (u : V) : Sym2 (Sym2 V) :=
  if h : #(H.incidenceFinset u) = 2 then
    s((card_eq_two.1 h).choose, (card_eq_two.1 h).choose_spec.choose)
  else s(s(u, u), s(u, u))

variable {H}

theorem Lv_spec {u : V} (hu : H.degree u = 2) : ∃ e1 e2, e1 ≠ e2 ∧
    H.incidenceFinset u = {e1, e2} ∧ Lv H u = s(e1, e2) := by
  have h : #(H.incidenceFinset u) = 2 := by rw [card_inc]; exact hu
  obtain ⟨hne, heq⟩ := (card_eq_two.1 h).choose_spec.choose_spec
  exact ⟨_, _, hne, heq, by simp only [Lv, dite_eq_left h]⟩

theorem Lv_mem {u : V} (hu : H.degree u = 2) {e : Sym2 V} (he : e ∈ Lv H u) :
    e ∈ H.incidenceFinset u := by
  obtain ⟨e1, e2, -, heq, hL⟩ := Lv_spec hu
  rw [hL] at he
  rw [heq]
  rcases Sym2.mem_iff.1 he with rfl | rfl <;> simp

theorem Lv_inj {u u' : V} (hu : H.degree u = 2) (hu' : H.degree u' = 2) (h : Lv H u = Lv H u') :
    u = u' := by
  obtain ⟨e1, e2, hne, heq, hL⟩ := Lv_spec hu
  by_contra huu
  have h1 : e1 ∈ H.incidenceFinset u' := Lv_mem hu' (by rw [← h, hL]; exact Sym2.mem_mk_left _ _)
  have h2 : e2 ∈ H.incidenceFinset u' := Lv_mem hu' (by rw [← h, hL]; exact Sym2.mem_mk_right _ _)
  have h1u : e1 ∈ H.incidenceFinset u := by rw [heq]; simp
  have h2u : e2 ∈ H.incidenceFinset u := by rw [heq]; simp
  have a1 := edge_eq_of_mem ((mem_inc H).1 h1u).1 ((mem_inc H).1 h1u).2 ((mem_inc H).1 h1).2 huu
  have a2 := edge_eq_of_mem ((mem_inc H).1 h2u).1 ((mem_inc H).1 h2u).2 ((mem_inc H).1 h2).2 huu
  exact hne (a1.trans a2.symm)

theorem Lv_adj {m : V → Option V} {u : V} (hu : H.degree u = 2) : Lv H u ∈ (LG H m).edgeSet := by
  obtain ⟨e1, e2, hne, heq, hL⟩ := Lv_spec hu
  rw [hL, mem_edgeSet]
  have h1 : e1 ∈ H.incidenceFinset u := by rw [heq]; simp
  have h2 : e2 ∈ H.incidenceFinset u := by rw [heq]; simp
  exact ⟨hne, ((mem_inc H).1 h1).1, ((mem_inc H).1 h2).1,
    Or.inl ⟨u, ((mem_inc H).1 h1).2, ((mem_inc H).1 h2).2⟩⟩

end Bkls.C4

end LeanPool.BalancedEdgeColourings
