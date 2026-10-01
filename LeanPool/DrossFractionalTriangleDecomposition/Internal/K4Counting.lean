/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card

/-! # K₄ counting in Dross's deficient-cut argument -/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `T_e` — the number of triangles through the edge `uv`, i.e. the common neighbours of
`u` and `v`. -/
@[expose] public def codeg (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℕ :=
  (G.neighborFinset u ∩ G.neighborFinset v).card

open scoped Classical in
/-- The number of `K₄`'s containing edge `uv`: edges of `G` both of whose endpoints are
common neighbours of `u` and `v` (each such edge `{w,x}` completes `{u,v,w,x}` to a `K₄`). -/
@[expose] public noncomputable def numK4Through (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : ℕ :=
  (G.edgeFinset.filter
    (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∩ G.neighborFinset v)).card

/-- Ordered adjacent pairs inside `S`. -/
private def orderedPairsIn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (V × V) := (S ×ˢ S).filter (fun p => G.Adj p.1 p.2)

omit [DecidableEq V] in
/-- Claim A: `|S|·(|S| − d) ≤ #ordered adjacent pairs in S`. -/
theorem claimA (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (d : ℕ)
    (hd : ∀ w, Fintype.card V - G.degree w ≤ d) :
    S.card * (S.card - d) ≤ (orderedPairsIn G S).card := by
  classical
  have hfib : (orderedPairsIn G S).card
      = ∑ w ∈ S, (S.filter (fun x => G.Adj w x)).card := by
    unfold orderedPairsIn
    rw [Finset.card_eq_sum_card_fiberwise
      (f := Prod.fst) (t := S)
      (by intro p hp; exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)]
    apply Finset.sum_congr rfl
    intro w hw
    apply Finset.card_bij (fun p _ => p.2)
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product] at hp
      rw [Finset.mem_filter]
      obtain ⟨⟨⟨_, hp2⟩, hadj⟩, hfst⟩ := hp
      subst hfst
      exact ⟨hp2, hadj⟩
    · intro p hp q hq hpq
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product] at hp hq
      obtain ⟨_, hpf⟩ := hp
      obtain ⟨_, hqf⟩ := hq
      exact Prod.ext (hpf.trans hqf.symm) hpq
    · intro x hx
      rw [Finset.mem_filter] at hx
      refine ⟨(w, x), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨⟨hw, hx.1⟩, hx.2⟩, rfl⟩
  rw [hfib]
  have hlb : ∀ w ∈ S, S.card - d ≤ (S.filter (fun x => G.Adj w x)).card := by
    intro w hw
    have hcompl : (S.filter (fun x => ¬ G.Adj w x)).card ≤ d := by
      have hsub : S.filter (fun x => ¬ G.Adj w x) ⊆ (G.neighborFinset w)ᶜ := by
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [Finset.mem_compl, SimpleGraph.mem_neighborFinset]
        exact hx.2
      calc (S.filter (fun x => ¬ G.Adj w x)).card
          ≤ (G.neighborFinset w)ᶜ.card := Finset.card_le_card hsub
        _ = Fintype.card V - G.degree w := by
            rw [Finset.card_compl, SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ d := hd w
    have hsplit : (S.filter (fun x => G.Adj w x)).card
        + (S.filter (fun x => ¬ G.Adj w x)).card = S.card :=
      Finset.card_filter_add_card_filter_not _
    omega
  calc S.card * (S.card - d)
      = ∑ _w ∈ S, (S.card - d) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ w ∈ S, (S.filter (fun x => G.Adj w x)).card := Finset.sum_le_sum hlb

/-- Claim B: ordered adjacent pairs in `S = N(u)∩N(v)` double-count the K₄-edges. -/
private theorem claimB (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    (orderedPairsIn G (G.neighborFinset u ∩ G.neighborFinset v)).card
      = 2 * numK4Through G u v := by
  classical
  set S := G.neighborFinset u ∩ G.neighborFinset v with hSdef
  have hnum : numK4Through G u v
      = (G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ S)).card := rfl
  rw [hnum]
  set EF := G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ S) with hEF
  have key : (orderedPairsIn G S).card
      = ∑ e ∈ EF, ((orderedPairsIn G S).filter (fun p => s(p.1, p.2) = e)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hmem := Finset.mem_product.mp hp'.1
    rw [hEF]
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hp'.2
    · intro x hx
      rw [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact hmem.1
      · exact hmem.2
  rw [key]
  have hfib2 : ∀ e ∈ EF, ((orderedPairsIn G S).filter (fun p => s(p.1, p.2) = e)).card = 2 := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      rw [hEF, Finset.mem_filter] at he
      obtain ⟨hedge, hsub⟩ := he
      have hab : G.Adj a b := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hedge; exact hedge
      have hne : a ≠ b := hab.ne
      have haS : a ∈ S := hsub a (by rw [Sym2.mem_iff]; left; rfl)
      have hbS : b ∈ S := hsub b (by rw [Sym2.mem_iff]; right; rfl)
      have hset : (orderedPairsIn G S).filter (fun p => s(p.1, p.2) = s(a, b))
          = {(a, b), (b, a)} := by
        ext p
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨_, heq⟩
          obtain ⟨x, y⟩ := p
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · left; rfl
          · right; rfl
        · rintro (rfl | rfl)
          · refine ⟨?_, rfl⟩
            unfold orderedPairsIn
            rw [Finset.mem_filter, Finset.mem_product]
            exact ⟨⟨haS, hbS⟩, hab⟩
          · refine ⟨?_, ?_⟩
            · unfold orderedPairsIn
              rw [Finset.mem_filter, Finset.mem_product]
              exact ⟨⟨hbS, haS⟩, hab.symm⟩
            · rw [Sym2.eq_iff]; right; exact ⟨rfl, rfl⟩
      rw [hset, Finset.card_insert_of_notMem, Finset.card_singleton]
      rw [Finset.mem_singleton]
      intro hcontra
      exact hne (Prod.ext_iff.mp hcontra).1
  rw [Finset.sum_congr rfl hfib2, Finset.sum_const, smul_eq_mul, mul_comm]

/-- **A6 — K₄ counting lower bound.** If every vertex fails to be adjacent to at most `d`
other vertices (the complement of the min-degree hypothesis `δ(G) ≥ |V| − d`), then the
edge `uv` lies in at least `T_e·(T_e − d)/2` copies of `K₄`. -/
public theorem k4_lower_bound (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (d : ℕ) (hd : ∀ w, Fintype.card V - G.degree w ≤ d) :
    codeg G u v * (codeg G u v - d) ≤ 2 * numK4Through G u v := by
  have hA := claimA G (G.neighborFinset u ∩ G.neighborFinset v) d hd
  have hB := claimB G u v
  rw [hB] at hA
  simpa only [codeg] using hA

end LeanPool.DrossFractionalTriangleDecomposition
