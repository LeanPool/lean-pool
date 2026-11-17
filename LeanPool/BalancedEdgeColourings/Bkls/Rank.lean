/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Ends

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 2: the matchings `J` and `K`

Fix an enumeration of `V`. The *rank* of `v` is the number of vertices with the same colour set
before `v`; on `V_S` it is a bijection onto `{0, …, n_S − 1}`. `J` pairs the vertex of rank `r` in
`V_S` with the vertex of rank `r` in `V_{i_ab S}` (a maximal partial matching between `V_S` and
`V_{i_ab S}`); `K` pairs the two ends of each `(a, b)`-path. `jkGraph` is `J ∪ K` on the ends: every
end has degree at most `2`, and the ends unmatched by `J` (rank `≥ n_{i_ab S}`) degree at most `1`.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

open Classical in
/-- A fixed enumeration of `V`. -/
noncomputable def ord (v : V) : ℕ := (Fintype.equivFin V v : ℕ)

open Classical in
omit [DecidableEq V] in
theorem ord_injective : Function.Injective (ord (V := V)) := fun _ _ h =>
  (Fintype.equivFin V).injective (Fin.ext h)

open Classical in
/-- The rank of `v` in its colour class. -/
noncomputable def rank (c : PEC G (Fin k)) (v : V) : ℕ :=
  #(univ.filter fun u => colSet c u = colSet c v ∧ ord u < ord v)

variable (c : PEC G (Fin k))

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem rank_lt_cnt (v : V) : rank c v < cnt c (colSet c v) := by
  classical
  unfold rank cnt
  apply card_lt_card
  refine ⟨fun u hu => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hu).2.1⟩, fun h => ?_⟩
  have := (mem_filter.1 (h (mem_filter.2 ⟨mem_univ v, rfl⟩))).2.2
  exact lt_irrefl _ this

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem rank_injOn {u v : V} (hS : colSet c u = colSet c v) (hr : rank c u = rank c v) :
    u = v := by
  classical
  by_contra hne
  rcases lt_or_gt_of_ne (fun h => hne (ord_injective h)) with h | h
  · have : rank c u < rank c v := by
      unfold rank
      apply card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · obtain ⟨-, h1, h2⟩ := mem_filter.1 hx
        exact mem_filter.2 ⟨mem_univ _, h1.trans hS, h2.trans h⟩
      · have := (mem_filter.1 (hsub (mem_filter.2 ⟨mem_univ u, hS, h⟩))).2.2
        exact lt_irrefl _ this
    omega
  · have : rank c v < rank c u := by
      unfold rank
      apply card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · obtain ⟨-, h1, h2⟩ := mem_filter.1 hx
        exact mem_filter.2 ⟨mem_univ _, h1.trans hS.symm, h2.trans h⟩
      · have := (mem_filter.1 (hsub (mem_filter.2 ⟨mem_univ v, hS.symm, h⟩))).2.2
        exact lt_irrefl _ this
    omega

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Every rank below `n_S` is taken in `V_S`. -/
theorem exists_rank {S : Finset (Fin k)} {r : ℕ} (hr : r < cnt c S) :
    ∃ v, colSet c v = S ∧ rank c v = r := by
  classical
  set VS := univ.filter fun v => colSet c v = S
  have hmaps : ∀ v ∈ VS, rank c v ∈ range (cnt c S) := fun v hv => by
    rw [mem_range, ← (mem_filter.1 hv).2]; exact rank_lt_cnt c v
  have hinj : Set.InjOn (rank c) VS := fun u hu v hv h =>
    rank_injOn c (((mem_filter.1 hu).2).trans ((mem_filter.1 hv).2).symm) h
  have hcard : #(range (cnt c S)) ≤ #VS := by rw [card_range]; rfl
  obtain ⟨v, hv, hvr⟩ := surj_on_of_inj_on_of_card_le (fun v hv => rank c v)
    hmaps (fun u v hu hv h => hinj hu hv h) hcard r (mem_range.2 hr)
  exact ⟨v, (mem_filter.1 hv).2, hvr.symm⟩
variable (a b : Fin k)

open Classical in
/-- `J`: same rank, exchanged colour sets. -/
def JRel (u v : V) : Prop := colSet c v = swapSet a b (colSet c u) ∧ rank c u = rank c v

open Classical in
/-- `v` is matched by `J`. -/
def JMatched (u : V) : Prop := rank c u < cnt c (swapSet a b (colSet c u))

open Classical in
/-- The graph `J ∪ K` on the ends. -/
def jkGraph : SimpleGraph V where
  Adj u v := u ≠ v ∧ IsEnd c a b u ∧ IsEnd c a b v ∧
    ((c.kempeGraph a b).Reachable u v ∨ JRel c a b u v)
  symm.symm := by
    rintro u v ⟨h1, h2, h3, h4⟩
    refine ⟨h1.symm, h3, h2, ?_⟩
    rcases h4 with r | ⟨e, er⟩
    · exact Or.inl r.symm
    · right; exact ⟨by rw [e, swapSet_swapSet], er.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {c a b}

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem JRel.symm {u v : V} (h : JRel c a b u v) : JRel c a b v u := by
  classical
  exact ⟨by rw [h.1, swapSet_swapSet], h.2.symm⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem JRel.unique {u v w : V} (h1 : JRel c a b u v) (h2 : JRel c a b u w) : v = w := by
  classical
  exact rank_injOn c (h1.1.trans h2.1.symm) (h1.2.symm.trans h2.2)

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem jMatched_iff {u : V} : JMatched c a b u ↔ ∃ v, JRel c a b u v := by
  classical
  constructor
  · intro h
    obtain ⟨v, hv, hr⟩ := exists_rank c h
    exact ⟨v, hv, hr.symm⟩
  · rintro ⟨v, hv, hr⟩
    unfold JMatched
    rw [hr, ← hv]; exact rank_lt_cnt c v
end Bkls

end LeanPool.BalancedEdgeColourings
