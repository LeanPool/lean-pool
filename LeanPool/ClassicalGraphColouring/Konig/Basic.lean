/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Vizing.Main

/-!
# Kőnig's edge-colouring theorem

`lineGraph_colorable_of_colorable_two`: a finite bipartite graph has a proper edge colouring with
`Δ(G)` colours. The proof colours the edges one at a time with the partial proper edge colourings
`LeanPool.Vizing.PEC` of the Vizing development. To colour an uncoloured edge `xy`, take a colour
`a` free at `x` and a colour `b` free at `y` (both exist since `xy` is uncoloured and there are
`Δ(G)` colours). If neither colours `xy` directly, swap `a` and `b` on the `a/b` Kempe component
of `y`. Since `b` is free at `y`, the colours along any Kempe path ending at `y` alternate, the
edge farthest from `y` having colour `a` exactly when the path has odd length; and a Kempe path
from `y` to `x` has odd length because `G` is bipartite. So `x` is not in the component, `a` is
still free at `x`, and `a` becomes free at `y`.
-/

@[expose] public section

open SimpleGraph Finset

namespace Konig

open LeanPool.Vizing LeanPool.Vizing.PEC

variable {V : Type*} {C : Type*} {G : SimpleGraph V}

/-- At an endpoint of an uncoloured edge some colour is free, provided there are at least `Δ(G)`
colours. -/
theorem exists_free_of_none [Fintype V] [Fintype C] [DecidableRel G.Adj] (c : PEC G C)
    (hcard : G.maxDegree ≤ Fintype.card C) {x y : V} (hadj : G.Adj x y)
    (hnone : c.col x y = none) : ∃ γ, c.IsFree x γ := by
  classical
  by_contra hcon
  push Not at hcon
  simp only [IsFree, not_forall, not_not] at hcon
  choose g hg using hcon
  have hginj : Set.InjOn g (univ : Finset C) := by
    intro γ₁ _ γ₂ _ h
    have : (some γ₁ : Option C) = some γ₂ := by rw [← hg γ₁, ← hg γ₂, h]
    exact Option.some_injective _ this
  have hmem : ∀ γ ∈ (univ : Finset C), g γ ∈ (G.neighborFinset x).erase y := by
    intro γ _
    refine Finset.mem_erase.2 ⟨fun h => ?_, (mem_neighborFinset _ _ _).2 (c.col_adj (hg γ))⟩
    have := hg γ
    rw [h, hnone] at this
    simp at this
  have hcards := Finset.card_le_card_of_injOn g hmem hginj
  rw [card_univ, Finset.card_erase_of_mem ((mem_neighborFinset _ _ _).2 hadj),
    card_neighborFinset_eq_degree] at hcards
  have hdeg := G.degree_le_maxDegree x
  have hpos : 0 < G.degree x := G.degree_pos_iff_exists_adj x |>.2 ⟨y, hadj⟩
  omega

/-- Along a walk of a graph contained in `G`, a proper 2-colouring of `G` changes at every step. -/
theorem colour_walk {H : SimpleGraph V} (hHG : H ≤ G) (s : G.Coloring (Fin 2)) {u v : V}
    (p : H.Walk u v) : (s v : ℕ) % 2 = ((s u : ℕ) + p.length) % 2 := by
  induction p with
  | nil => simp
  | @cons u w v h p ih =>
    rw [Walk.length_cons, ih]
    have hne : (s u : ℕ) ≠ (s w : ℕ) := fun he => s.valid (hHG h) (Fin.ext he)
    have hu := (s u).isLt
    have hw := (s w).isLt
    omega

/-- **Alternation along a Kempe path.** If `b` is free at `y`, then on every path of the `a/b`
Kempe graph ending at `y`, the first edge has colour `a` if the length is odd and `b` if it is
even (and positive). -/
theorem col_snd_of_kempe_path (c : PEC G C) {a b : C} {y : V}
    (hy : c.IsFree y b) {u : V} (p : (c.kempeGraph a b).Walk u y) (hp : p.IsPath)
    (hlen : 0 < p.length) :
    c.col u p.snd = some (if p.length % 2 = 1 then a else b) := by
  induction p with
  | nil => simp at hlen
  | @cons u w y h r ih =>
    have hcol := h.2
    rw [Walk.snd_cons]
    rw [Walk.cons_isPath_iff] at hp
    rcases Nat.eq_zero_or_pos r.length with h0 | hpos
    · -- `r` is trivial: `w = y`
      have hwy : w = y := Walk.eq_of_length_eq_zero h0
      subst hwy
      rw [Walk.length_cons, h0, zero_add]
      rcases hcol with hcol | hcol
      · simpa using hcol
      · exact absurd ((c.col_symm w u).trans hcol) (hy u)
    · have hih := ih hy hp.1 hpos
      have hne : u ≠ r.snd := by
        intro he
        exact hp.2 (by rw [he]; exact r.getVert_mem_support 1)
      rw [Walk.length_cons]
      -- the colours of `w u` and `w r.snd` differ
      have hdiff : c.col w u ≠ c.col w r.snd := by
        intro he
        rw [hih] at he
        exact hne (c.col_proper he hih)
      rw [c.col_symm w u] at hdiff
      rcases Nat.mod_two_eq_zero_or_one r.length with hr | hr
      · have h1 : (r.length + 1) % 2 = 1 := by omega
        rw [hr] at hih
        simp only [zero_ne_one, ite_false] at hih
        rw [hih] at hdiff
        simp only [h1, ite_true]
        rcases hcol with hcol | hcol
        · exact hcol
        · exact absurd hcol hdiff
      · have h1 : (r.length + 1) % 2 = 0 := by omega
        rw [hr] at hih
        simp only [ite_true] at hih
        rw [hih] at hdiff
        simp only [h1, zero_ne_one, ite_false]
        rcases hcol with hcol | hcol
        · exact absurd hcol hdiff
        · exact hcol

/-- The Kempe graph is a subgraph of `G`. -/
theorem kempeGraph_le (c : PEC G C) (a b : C) : c.kempeGraph a b ≤ G := by
  intro u v h
  rcases h.2 with h | h <;> exact c.col_adj h

/-- **Kőnig's extension step.** In a bipartite graph with at least `Δ(G)` colours, any uncoloured
edge can be coloured after recolouring. -/
theorem konig_step [Fintype V] [Fintype C] [DecidableRel G.Adj]
    (s : G.Coloring (Fin 2)) (c : PEC G C)
    (hcard : G.maxDegree ≤ Fintype.card C) {x y : V} (hadj : G.Adj x y)
    (hnone : c.col x y = none) :
    ∃ c' : PEC G C, Extends c c' ∧ c'.col x y ≠ none := by
  classical
  obtain ⟨a, ha⟩ := exists_free_of_none c hcard hadj hnone
  obtain ⟨b, hb⟩ := exists_free_of_none c hcard hadj.symm (by rw [c.col_symm]; exact hnone)
  by_cases hay : c.IsFree y a
  · exact ⟨c.setEdge a hadj ha hay, extends_setEdge c a hadj ha hay, by
      simp [setEdge]⟩
  have hab : a ≠ b := fun h => hay (h ▸ hb)
  -- `x` is not in the `a/b` Kempe component of `y`
  have hxy : ¬ (c.kempeGraph a b).Reachable y x := by
    rintro ⟨q⟩
    set p := q.toPath.1.reverse with hpdef
    have hp : p.IsPath := q.toPath.2.reverse
    have hpar := colour_walk (kempeGraph_le c a b) s p
    have hsx : s x ≠ s y := s.valid hadj
    have hodd : p.length % 2 = 1 := by
      have hx := (s x).isLt
      have hy' := (s y).isLt
      have : (s x : ℕ) ≠ (s y : ℕ) := fun h => hsx (Fin.ext h)
      omega
    have hlen : 0 < p.length := by omega
    have := col_snd_of_kempe_path c hb p hp hlen
    simp only [hodd, ↓reduceIte] at this
    exact ha _ this
  set c1 := c.kempeSwap a b y
  have ha1 : c1.IsFree x a := (isFree_kempeSwap_of_not_reachable c a b hxy a).2 ha
  have hay1 : c1.IsFree y a := by
    rw [isFree_kempeSwap_of_reachable c a b (Reachable.refl y) a, Equiv.swap_apply_left]
    exact hb
  refine ⟨c1.setEdge a hadj ha1 hay1, (extends_kempeSwap c a b y).trans
    (extends_setEdge c1 a hadj ha1 hay1), by simp [setEdge]⟩

/-- **Kőnig's theorem.** A finite bipartite graph has a total proper partial edge colouring with
any colour type of size at least `Δ(G)`. -/
theorem exists_total_of_bipartite [Fintype V] [Fintype C] [DecidableRel G.Adj]
    (s : G.Coloring (Fin 2))
    (hcard : G.maxDegree ≤ Fintype.card C) :
    ∃ c : PEC G C, ∀ u v, G.Adj u v → c.col u v ≠ none := by
  classical
  suffices H : ∀ (k : ℕ) (c : PEC G C), c.uncoloured.card ≤ k →
      ∃ c' : PEC G C, ∀ u v, G.Adj u v → c'.col u v ≠ none by
    exact H (empty G C).uncoloured.card (empty G C) le_rfl
  intro k
  induction k with
  | zero =>
    intro c hk
    refine ⟨c, fun u v huv hcol => ?_⟩
    have hmem : (u, v) ∈ c.uncoloured := (c.mem_uncoloured (u, v)).2 ⟨huv, hcol⟩
    have := Finset.card_pos.2 ⟨_, hmem⟩
    omega
  | succ k ih =>
    intro c hk
    by_cases hall : ∀ u v, G.Adj u v → c.col u v ≠ none
    · exact ⟨c, hall⟩
    · push Not at hall
      obtain ⟨x, y, hadj, hnone⟩ := hall
      obtain ⟨c1, hext, hc1⟩ := konig_step s c hcard hadj hnone
      refine ih c1 ?_
      have hsub : c1.uncoloured ⊆ c.uncoloured := by
        intro p hp
        rw [mem_uncoloured] at hp ⊢
        refine ⟨hp.1, ?_⟩
        by_contra hcon
        exact (hext p.1 p.2 hcon) hp.2
      have hxy : (x, y) ∈ c.uncoloured := (c.mem_uncoloured (x, y)).2 ⟨hadj, hnone⟩
      have hxy' : (x, y) ∉ c1.uncoloured := by
        rw [mem_uncoloured]
        rintro ⟨-, h⟩
        exact hc1 h
      have hlt : c1.uncoloured.card < c.uncoloured.card :=
        Finset.card_lt_card ⟨hsub, fun hcon => hxy' (hcon hxy)⟩
      omega

/-- **Kőnig's edge-colouring theorem.** The line graph of a finite bipartite graph is
`Δ(G)`-colourable. -/
theorem lineGraph_colorable_of_colorable_two [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.Colorable 2) : G.lineGraph.Colorable G.maxDegree := by
  classical
  obtain ⟨s⟩ := h
  obtain ⟨c, hc⟩ := exists_total_of_bipartite (C := Fin G.maxDegree) s (by simp)
  exact ⟨c.lineGraphColoring hc⟩

/-- The edges at a vertex of maximum degree are pairwise adjacent in the line graph, so
`Δ(G) ≤ χ'(G)`. -/
theorem maxDegree_le_lineGraph_chromaticNumber [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : (G.maxDegree : ℕ∞) ≤ G.lineGraph.chromaticNumber := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · have : G.maxDegree = 0 := by
      rw [← Nat.le_zero]
      exact G.maxDegree_le_of_forall_degree_le 0 (fun v => isEmptyElim v)
    rw [this, Nat.cast_zero]
    exact zero_le
  · obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    rw [hv]
    refine le_chromaticNumber_of_pairwise_adj (ι := G.neighborSet v) ?_
      (fun u => (⟨s(v, u), u.2⟩ : G.edgeSet)) ?_
    · rw [Nat.card_eq_fintype_card, card_neighborSet_eq_degree]
    · intro u u' huu
      rw [lineGraph_adj_iff_exists]
      refine ⟨fun h => huu (Subtype.ext ?_), v, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
      have : (u : V) = u' ∨ v = u' ∧ (u : V) = v := by simpa using congrArg Subtype.val h
      rcases this with h' | ⟨-, h'⟩
      · exact h'
      · exact absurd h' (G.ne_of_adj u.2).symm

/-- **Kőnig's edge-colouring theorem**, chromatic-number form: `χ'(G) = Δ(G)` for a finite
bipartite graph. -/
theorem lineGraph_chromaticNumber_of_colorable_two [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : G.Colorable 2) :
    G.lineGraph.chromaticNumber = G.maxDegree :=
  le_antisymm (lineGraph_colorable_of_colorable_two G h).chromaticNumber_le
    (maxDegree_le_lineGraph_chromaticNumber G)

end Konig
