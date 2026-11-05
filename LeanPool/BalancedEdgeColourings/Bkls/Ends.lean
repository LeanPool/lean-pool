/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Balanced.RSc

/-!
# Balister–Kostochka–Li–Schelp 2004: ends of Kempe paths

* `exists_reachable_odd`: a vertex of odd degree is joined by a path to another vertex of odd
  degree (handshake inside a component).
* `kempe_degree_eq`: the degree of `v` in the `(a, b)`-Kempe graph is the number of the colours
  `a, b` present at `v`.
* `exists_kempe_partner`: every end of an `(a, b)`-path (exactly one of `a, b` present) is joined by
  that path to another end.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- **A vertex of odd degree reaches another vertex of odd degree.** -/
theorem exists_reachable_odd (H : SimpleGraph V) [DecidableRel H.Adj] {u : V}
    (hu : Odd (H.degree u)) : ∃ v, v ≠ u ∧ H.Reachable u v ∧ Odd (H.degree v) := by
  classical
  by_contra hne
  push Not at hne
  set Q := univ.filter fun v => H.Reachable u v with hQ
  -- the darts leaving `Q` stay in `Q`, and pair up under reversal
  set D := univ.filter fun d : H.Dart => d.fst ∈ Q with hD
  have hDcard : #D = ∑ v ∈ Q, H.degree v := by
    rw [card_eq_sum_card_fiberwise (s := D) (f := fun d : H.Dart => d.fst) (t := Q)
      (fun d hd => (mem_filter.1 hd).2)]
    refine sum_congr rfl fun v hv => ?_
    rw [← dart_fst_fiber_card_eq_degree]
    congr 1
    ext d
    simp only [mem_filter, mem_univ, true_and, hD]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨h ▸ hv, h⟩
  have heven : Even #D := by
    have key : ∑ d ∈ D, (1 : ZMod 2) = 0 := by
      refine sum_involution (fun d _ => d.symm) (fun _ _ => rfl) (fun d _ _ h => ?_)
        (fun d hd => ?_) (fun d _ => d.symm_symm)
      · exact absurd h (Dart.symm_ne d)
      · have h1 : d.fst ∈ Q := (mem_filter.1 hd).2
        have h2 : d.snd ∈ Q :=
          mem_filter.2 ⟨mem_univ _, (mem_filter.1 h1).2.trans d.adj.reachable⟩
        exact mem_filter.2 ⟨mem_univ _, h2⟩
    rw [sum_const, nsmul_eq_mul, mul_one] at key
    exact (ZMod.natCast_eq_zero_iff_even).1 key
  have huQ : u ∈ Q := mem_filter.2 ⟨mem_univ _, Reachable.refl u⟩
  rw [hDcard, ← sum_erase_add _ _ huQ] at heven
  have hrest : Even (∑ v ∈ Q.erase u, H.degree v) := by
    refine Finset.sum_induction _ Even (fun _ _ => Even.add) ⟨0, rfl⟩ fun v hv => ?_
    obtain ⟨hvu, hv⟩ := mem_erase.1 hv
    exact Nat.not_odd_iff_even.1 (hne v hvu (mem_filter.1 hv).2)
  have := (Nat.even_add.1 heven).1 hrest
  exact (Nat.not_even_iff_odd.2 hu) this
variable {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The degree in the `(a, b)`-Kempe graph counts the colours `a, b` present at `v`. -/
theorem kempe_degree_eq (c : PEC G (Fin k)) {a b : Fin k} (hab : a ≠ b) (v : V) :
    (c.kempeGraph a b).degree v =
      (if c.IsFree v a then 0 else 1) + (if c.IsFree v b then 0 else 1) := by
  classical
  rw [← card_neighborFinset_eq_degree]
  have hsplit : (c.kempeGraph a b).neighborFinset v =
      ((c.kempeGraph a b).neighborFinset v).filter (fun u => c.col v u = some a) ∪
      ((c.kempeGraph a b).neighborFinset v).filter (fun u => c.col v u = some b) := by
    ext u
    simp only [mem_union, mem_filter, mem_neighborFinset, kempeGraph_adj]
    tauto
  have hdisj : Disjoint (((c.kempeGraph a b).neighborFinset v).filter
      (fun u => c.col v u = some a))
      (((c.kempeGraph a b).neighborFinset v).filter (fun u => c.col v u = some b)) := by
    rw [Finset.disjoint_left]
    intro u h1 h2
    have := (mem_filter.1 h1).2.symm.trans (mem_filter.1 h2).2
    exact hab (Option.some_injective _ this)
  have hcount : ∀ γ, γ = a ∨ γ = b → #(((c.kempeGraph a b).neighborFinset v).filter
      (fun u => c.col v u = some γ)) = if c.IsFree v γ then 0 else 1 := by
    intro γ hγ
    split_ifs with hf
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro u _ h; exact hf u h
    · simp only [IsFree, not_forall, not_not] at hf
      obtain ⟨u, hu⟩ := hf
      rw [card_eq_one]
      refine ⟨u, ?_⟩
      ext x
      simp only [mem_filter, mem_neighborFinset, kempeGraph_adj, mem_singleton]
      constructor
      · rintro ⟨-, hx⟩; exact c.col_proper hx hu
      · rintro rfl
        refine ⟨⟨fun h => ?_, ?_⟩, hu⟩
        · subst h; rw [c.col_self] at hu; cases hu
        · rcases hγ with rfl | rfl
          · exact Or.inl hu
          · exact Or.inr hu
  rw [hsplit, card_union_of_disjoint hdisj, hcount a (Or.inl rfl), hcount b (Or.inr rfl)]

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- **The other end of a Kempe path.** -/
theorem exists_kempe_partner [Finite V] (c : PEC G (Fin k)) {a b : Fin k} (hab : a ≠ b) {u : V}
    (hu : IsEnd c a b u) :
    ∃ v, v ≠ u ∧ (c.kempeGraph a b).Reachable u v ∧ IsEnd c a b v := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hdeg : ∀ v, IsEnd c a b v ↔ (c.kempeGraph a b).degree v = 1 := by
    intro v
    rw [kempe_degree_eq c hab v]
    simp only [IsEnd, mem_colSet]
    split_ifs <;> simp_all
  have hodd : Odd ((c.kempeGraph a b).degree u) := by rw [(hdeg u).1 hu]; exact odd_one
  obtain ⟨v, hvu, hr, hv⟩ := exists_reachable_odd _ hodd
  refine ⟨v, hvu, hr, (hdeg v).2 ?_⟩
  have h2 := kempe_degree_le_two c a b v
  rcases hv with ⟨m, hm⟩
  omega
end Bkls

end LeanPool.BalancedEdgeColourings
