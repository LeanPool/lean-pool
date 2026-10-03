/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.ListEdgeColoringComplete.Polynomial
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-! # Häggkvist--Janssen: the list chromatic index of `K_n` is at most `n`

Theorem 1.1 / Theorem 3.1 of Häggkvist--Janssen (CPC 6 (1997) 295--313): if every edge
of the complete graph on `n` vertices carries a list of at least `n` colours, there is a
proper edge colouring (a colouring of the line graph) choosing every colour from its list.

This is an alternative presentation of the proof, not a literal formalization
of the article's argument. It applies Mathlib's combinatorial Nullstellensatz
to the product of the
extended-star Vandermonde polynomials (`graphPoly`), whose certificate coefficient is
`±1` (`coeff_graphPoly_certificate`). The colours are encoded injectively into `ℚ`; the
artificial star vertices receive the artificial lists `{0, …, n-1}`, and only the values
at actual edges are transported back. Graphs with at most one vertex have no edges and
are handled separately.
-/

@[expose] public section

namespace LeanPool.ListEdgeColoringComplete

open MvPolynomial Finset

variable {V : Type*} [DecidableEq V] {n : ℕ}

omit [DecidableEq V] in
/-- With at most one vertex the complete graph has no edges. -/
theorem isEmpty_edgeSet_top_of_card_le_one [Fintype V] (h : Fintype.card V ≤ 1) :
    IsEmpty (⊤ : SimpleGraph V).edgeSet := by
  constructor
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa using he
    exact hab (Fintype.card_le_one_iff.mp h a b)

/-- Every actual edge at `v` is a member of the extended star at `v`. -/
theorem exists_starMember_eq_inl (f : V ≃ Fin n) {v : V} (e : (⊤ : SimpleGraph V).edgeSet)
    (hv : v ∈ (e : Sym2 V)) : ∃ k, starMember f v k = Sum.inl e := by
  obtain ⟨e, he⟩ := e
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hv
  have hvw : w ≠ v := fun h => by simp [h] at he
  exact ⟨f w, by rw [starMember_of_ne f hvw]⟩

/-- The certificate exponent of an actual edge is its target degree, at most `n - 1`. -/
theorem expo_canonicalPerm_inl_lt [Fintype V] (f : V ≃ Fin n)
    (e : (⊤ : SimpleGraph V).edgeSet) : expo f (canonicalPerm f) (Sum.inl e) < n := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa using he
    have hfab : f a ≠ f b := fun h => hab (f.injective h)
    rw [expo_inl, canonicalPerm_apply, canonicalPerm_apply]
    have hs := canonicalRow_spec.2.2 (f a) (f b) hfab
    have h2 : 2 ≤ n := by
      have := (f a).isLt; have := (f b).isLt
      have : (f a : ℕ) ≠ f b := fun h => hfab (Fin.ext h)
      omega
    have := targetDegree_lt n (f a) (f b) h2
    omega

/-- The certificate exponent of an artificial vertex is its blocked value, below `n`. -/
theorem expo_canonicalPerm_inr_lt [Fintype V] (f : V ≃ Fin n) (u : V) :
    expo f (canonicalPerm f) (Sum.inr u) < n := by
  rw [expo_inr]
  exact (canonicalPerm f u (f u)).isLt

/-- **Häggkvist--Janssen.** The list chromatic index of the complete graph on `V` is at
most `|V|`: for arbitrary lists of at least `|V|` colours on the edges (from an arbitrary
colour type) there is a proper colouring of the line graph choosing from the lists. -/
theorem exists_listEdgeColoring_complete
    {V Color : Type*} [Fintype V]
    (lists : (⊤ : SimpleGraph V).edgeSet → Finset Color)
    (hLists : ∀ e, Fintype.card V ≤ (lists e).card) :
    ∃ coloring : (⊤ : SimpleGraph V).lineGraph.Coloring Color,
      ∀ e, coloring e ∈ lists e := by
  classical
  by_cases hn : Fintype.card V ≤ 1
  · -- no edges at all
    have := isEmpty_edgeSet_top_of_card_le_one hn
    exact ⟨SimpleGraph.Coloring.mk (fun e => isEmptyElim e) (fun {e} => isEmptyElim e),
      fun e => isEmptyElim e⟩
  -- labels `0, …, n-1`
  set n := Fintype.card V with hn_def
  let f : V ≃ Fin n := Fintype.equivFin V
  -- injective encoding of the colours occurring in some list into `ℚ`
  let U : Finset Color := univ.biUnion lists
  let enc : Color → ℚ := fun c => if h : c ∈ U then ((U.equivFin ⟨c, h⟩ : ℕ) : ℚ) else 0
  have hU : ∀ e, ∀ c ∈ lists e, c ∈ U := fun e c hc => mem_biUnion.mpr ⟨e, mem_univ _, hc⟩
  have henc : ∀ e, Set.InjOn enc (lists e) := by
    intro e c hc d hd hcd
    simp only [enc, hU e c hc, hU e d hd, ↓reduceDIte, Nat.cast_inj] at hcd
    exact congrArg Subtype.val (U.equivFin.injective (Fin.ext hcd))
  -- the lists for the Nullstellensatz: encoded colours, and `{0, …, n-1}` for stars
  let S : StarVar V → Finset ℚ := fun v => match v with
    | Sum.inl e => (lists e).image enc
    | Sum.inr _ => (range n).image (fun k : ℕ => (k : ℚ))
  have hS : ∀ v, expo f (canonicalPerm f) v < #(S v) := by
    rintro (e | u)
    · change _ < #((lists e).image enc)
      rw [card_image_of_injOn (henc e)]
      exact (expo_canonicalPerm_inl_lt f e).trans_le (hLists e)
    · change _ < #((range n).image (fun k : ℕ => (k : ℚ)))
      rw [card_image_of_injective _ Nat.cast_injective, card_range]
      exact expo_canonicalPerm_inr_lt f u
  obtain ⟨x, hxS, hx⟩ := combinatorial_nullstellensatz_exists_eval_nonzero (graphPoly f)
    (expo f (canonicalPerm f)) (coeff_graphPoly_certificate_ne_zero f)
    (totalDegree_graphPoly f) S hS
  -- every star receives distinct values
  have hstar : ∀ v, Function.Injective (fun k => x (starMember f v k)) := by
    intro v
    apply starPoly_eval_ne_zero
    have : ∏ u, eval x (starPoly f u) ≠ 0 := by
      simpa [graphPoly, map_prod] using hx
    exact (prod_ne_zero_iff.mp this) v (mem_univ v)
  -- decode the chosen values back into colours
  have hchoice : ∀ e, ∃ c ∈ lists e, enc c = x (Sum.inl e) := fun e => by
    simpa [S] using hxS (Sum.inl e)
  choose col hcol henc_col using hchoice
  refine ⟨SimpleGraph.Coloring.mk col ?_, hcol⟩
  intro e e' hadj hsame
  obtain ⟨hne, v, hv, hv'⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hadj
  obtain ⟨k, hk⟩ := exists_starMember_eq_inl f e hv
  obtain ⟨k', hk'⟩ := exists_starMember_eq_inl f e' hv'
  have hxx : x (starMember f v k) = x (starMember f v k') := by
    rw [hk, hk', ← henc_col, ← henc_col, hsame]
  have hkk := hstar v hxx
  rw [hkk, hk'] at hk
  exact hne (Sum.inl_injective hk).symm

end LeanPool.ListEdgeColoringComplete
