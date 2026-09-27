/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — per-edge triangle counting inside a uniform triple

Mathlib's regularity machinery gives *global* triangle counts in a triple of `ε`-uniform pairs.
The Haxell–Rödl regularity core needs the *local* form: for all but an `O(ε)`-fraction of the pairs
`(x, y) ∈ A × B`, the number of common neighbours of `x` and `y` inside `C` is
`(d(A,C) ± ε)(d(B,C) ± 2ε)|C|`, i.e. the triangle degree of an edge across a uniform triple is
already near-regular.  This file proves that from the definition of `SimpleGraph.IsUniform` alone.

* `Nibble.AX1.codegreeIn` — the number of common neighbours of `x` and `y` inside a finset `C`.
* `Nibble.AX1.card_interedges_eq_sum` — the number of edges between two finsets is the sum of the
  degrees into the second one.
* `Nibble.AX1.card_filter_lt_le`, `Nibble.AX1.card_filter_gt_le` — **the one-sided degree
  lemmas**: in an `ε`-uniform pair `(B, C)`, and for *any* subset `C' ⊆ C` with `|C'| ≥ ε|C|`, at
  most `ε|B|` vertices of `B` have degree into `C'` below `(d(B,C) − ε)|C'|` (resp. above
  `(d(B,C) + ε)|C'|`).  Taking `C' = C` this is the usual "few vertices have irregular degree";
  taking `C' = N(x) ∩ C` it is the codegree statement.
* `Nibble.AX1.uniform_triple_codegree` — **ingredient 1**: in a triple with `(A,C)` and `(B,C)`
  `ε`-uniform of density at least `2ε`, all but `4ε|A||B|` pairs `(x, y) ∈ A × B` have
  `(d(A,C) − ε)(d(B,C) − 2ε)|C| ≤ codeg(x,y) ≤ (d(A,C) + ε)(d(B,C) + 2ε)|C|`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.ContinuousFunctionalCalculus

/-! # CoreGapUniformCodegree -/

@[expose] public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Counting edges fibrewise -/

/-- The number of pairs of a product satisfying a predicate, summed fibrewise. -/
theorem card_filter_product {α β : Type*} [DecidableEq α] (s : Finset α) (t : Finset β)
    (P : α × β → Prop) [DecidablePred P] :
    #{e ∈ s ×ˢ t | P e} = ∑ x ∈ s, #{y ∈ t | P (x, y)} := by
  classical
  have hmem : ∀ e ∈ {e ∈ s ×ˢ t | P e}, e.1 ∈ s := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_product] at he
    exact he.1.1
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun x hx => ?_
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
    subst h4; exact ⟨h2, h3⟩
  · intro p hp q hq h
    simp only [Finset.mem_filter] at hp hq
    exact Prod.ext (hp.2.trans hq.2.symm) h
  · intro y hy
    simp only [Finset.mem_filter] at hy
    exact ⟨(x, y), by simp [Finset.mem_filter, Finset.mem_product, hx, hy.1, hy.2], rfl⟩

omit [Fintype V] in
/-- The number of edges between two finsets is the sum over the first of the degrees into the
second. -/
theorem card_interedges_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj] (s t : Finset V) :
    #(G.interedges s t) = ∑ x ∈ s, #{z ∈ t | G.Adj x z} := by
  classical
  simpa [SimpleGraph.interedges, Rel.interedges] using
    card_filter_product s t (fun e => G.Adj e.1 e.2)

omit [Fintype V] [DecidableEq V] in
/-- The edge density as a real number. -/
theorem edgeDensity_real (G : SimpleGraph V) [DecidableRel G.Adj] (s t : Finset V) :
    (G.edgeDensity s t : ℝ) = (#(G.interedges s t) : ℝ) / ((#s : ℝ) * (#t : ℝ)) := by
  rw [SimpleGraph.edgeDensity_def]
  push_cast
  ring

/-! ### The one-sided degree lemmas -/

omit [Fintype V] in
/-- **Few vertices have small degree into a large subset.**  If `(B, C)` is `ε`-uniform and
`C' ⊆ C` has `|C'| ≥ ε|C|`, then at most `ε|B|` vertices `y ∈ B` have fewer than `θ|C'|`
neighbours in `C'`, for any `θ ≤ d(B,C) − ε`. -/
theorem card_filter_lt_le (G : SimpleGraph V) [DecidableRel G.Adj] {B C C' : Finset V} {ε θ : ℝ}
    (hε : 0 < ε) (hu : G.IsUniform ε B C) (hC'sub : C' ⊆ C) (hC'card : (#C : ℝ) * ε ≤ (#C' : ℝ))
    (hθ : θ + ε ≤ (G.edgeDensity B C : ℝ)) :
    ((#{y ∈ B | ((#{z ∈ C' | G.Adj y z} : ℕ) : ℝ) < θ * (#C' : ℝ)} : ℕ) : ℝ) ≤ ε * (#B : ℝ) := by
  classical
  set S : Finset V := {y ∈ B | ((#{z ∈ C' | G.Adj y z} : ℕ) : ℝ) < θ * (#C' : ℝ)} with hS
  by_contra hcon
  push Not at hcon
  have hSsub : S ⊆ B := Finset.filter_subset _ _
  have hSpos : (0 : ℝ) < (#S : ℝ) := lt_of_le_of_lt (by positivity) hcon
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hSpos
  -- `C'` is nonempty, else the defining condition is `0 < 0`
  have hC'pos : (0 : ℝ) < (#C' : ℝ) := by
    rcases Nat.eq_zero_or_pos (#C') with h0 | hpos
    · exfalso
      obtain ⟨y, hy⟩ := hSne
      rw [hS, Finset.mem_filter] at hy
      have hsub : {z ∈ C' | G.Adj y z} ⊆ C' := Finset.filter_subset _ _
      have : #{z ∈ C' | G.Adj y z} = 0 := Nat.eq_zero_of_le_zero (h0 ▸ Finset.card_le_card hsub)
      rw [this, h0] at hy
      norm_num at hy
    · exact_mod_cast hpos
  -- uniformity applies
  have h1 : (#B : ℝ) * ε ≤ (#S : ℝ) := by linarith only [hcon]
  have huni := hu hSsub hC'sub h1 hC'card
  have hlow : (G.edgeDensity B C : ℝ) - ε < (G.edgeDensity S C' : ℝ) := by
    have := abs_lt.mp huni
    linarith only [this.1]
  -- but the density of `(S, C')` is less than `θ`
  have hcount : (#(G.interedges S C') : ℝ) < (#S : ℝ) * (θ * (#C' : ℝ)) := by
    have hsum : ((∑ y ∈ S, #{z ∈ C' | G.Adj y z} : ℕ) : ℝ) < ∑ _y ∈ S, θ * (#C' : ℝ) := by
      push_cast
      refine Finset.sum_lt_sum_of_nonempty hSne ?_
      intro y hy
      rw [hS, Finset.mem_filter] at hy
      exact hy.2
    rw [card_interedges_eq_sum]
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum
  have hden : (G.edgeDensity S C' : ℝ) < θ := by
    rw [edgeDensity_real]
    rw [div_lt_iff₀ (by positivity)]
    calc (#(G.interedges S C') : ℝ) < (#S : ℝ) * (θ * (#C' : ℝ)) := hcount
      _ = θ * ((#S : ℝ) * (#C' : ℝ)) := by ring
  linarith only [hθ, hlow, hden]

omit [Fintype V] in
/-- **Few vertices have large degree into a large subset.**  The mirror image of
`Nibble.AX1.card_filter_lt_le`. -/
theorem card_filter_gt_le (G : SimpleGraph V) [DecidableRel G.Adj] {B C C' : Finset V} {ε θ : ℝ}
    (hε : 0 < ε) (hu : G.IsUniform ε B C) (hC'sub : C' ⊆ C) (hC'card : (#C : ℝ) * ε ≤ (#C' : ℝ))
    (hθ : (G.edgeDensity B C : ℝ) + ε ≤ θ) :
    ((#{y ∈ B | θ * (#C' : ℝ) < ((#{z ∈ C' | G.Adj y z} : ℕ) : ℝ)} : ℕ) : ℝ) ≤ ε * (#B : ℝ) := by
  classical
  set S : Finset V := {y ∈ B | θ * (#C' : ℝ) < ((#{z ∈ C' | G.Adj y z} : ℕ) : ℝ)} with hS
  by_contra hcon
  push Not at hcon
  have hSsub : S ⊆ B := Finset.filter_subset _ _
  have hSpos : (0 : ℝ) < (#S : ℝ) := lt_of_le_of_lt (by positivity) hcon
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hSpos
  have hC'pos : (0 : ℝ) < (#C' : ℝ) := by
    rcases Nat.eq_zero_or_pos (#C') with h0 | hpos
    · exfalso
      obtain ⟨y, hy⟩ := hSne
      rw [hS, Finset.mem_filter] at hy
      have hsub : {z ∈ C' | G.Adj y z} ⊆ C' := Finset.filter_subset _ _
      have : #{z ∈ C' | G.Adj y z} = 0 := Nat.eq_zero_of_le_zero (h0 ▸ Finset.card_le_card hsub)
      rw [this, h0] at hy
      norm_num at hy
    · exact_mod_cast hpos
  have h1 : (#B : ℝ) * ε ≤ (#S : ℝ) := by linarith only [hcon]
  have huni := hu hSsub hC'sub h1 hC'card
  have hhigh : (G.edgeDensity S C' : ℝ) < (G.edgeDensity B C : ℝ) + ε := by
    have := abs_lt.mp huni
    linarith only [this.2]
  have hcount : (#S : ℝ) * (θ * (#C' : ℝ)) < (#(G.interedges S C') : ℝ) := by
    have hsum : ∑ _y ∈ S, θ * (#C' : ℝ) < ((∑ y ∈ S, #{z ∈ C' | G.Adj y z} : ℕ) : ℝ) := by
      push_cast
      refine Finset.sum_lt_sum_of_nonempty hSne ?_
      intro y hy
      rw [hS, Finset.mem_filter] at hy
      exact hy.2
    rw [card_interedges_eq_sum]
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum
  have hden : θ < (G.edgeDensity S C' : ℝ) := by
    rw [edgeDensity_real, lt_div_iff₀ (by positivity)]
    calc θ * ((#S : ℝ) * (#C' : ℝ)) = (#S : ℝ) * (θ * (#C' : ℝ)) := by ring
      _ < (#(G.interedges S C') : ℝ) := hcount
  linarith only [hθ, hhigh, hden]

/-! ### Ingredient 1: near-regular triangle degrees across a uniform triple -/

/-- The number of common neighbours of `x` and `y` inside `C`. -/
def codegreeIn (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) (x y : V) : ℕ :=
  #{z ∈ C | G.Adj x z ∧ G.Adj y z}

omit [Fintype V] [DecidableEq V] in
theorem codegreeIn_eq_card_filter (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V)
    (x y : V) : codegreeIn G C x y = #{z ∈ {z ∈ C | G.Adj x z} | G.Adj y z} := by
  rw [codegreeIn, Finset.filter_filter]

omit [Fintype V] in
/-- **Ingredient 1 — per-edge triangle counting in a uniform triple.**  If `(A, C)` and `(B, C)`
are `ε`-uniform pairs of density at least `2ε`, then all but at most `4ε|A||B|` of the pairs
`(x, y) ∈ A × B` have

`(d(A,C) − ε)(d(B,C) − 2ε)|C| ≤ |N(x) ∩ N(y) ∩ C| ≤ (d(A,C) + ε)(d(B,C) + 2ε)|C|`,

i.e. the triangle degree of an edge of the pair `(A, B)` into `C` is already near-regular, at the
scale `d(A,C)·d(B,C)·|C|`.

The proof is the standard two-sided count: all but `2ε|A|` vertices `x ∈ A` have
`|N(x) ∩ C| = (d(A,C) ± ε)|C|` (`Nibble.AX1.card_filter_lt_le` with `C' = C`), and for such an `x`
the set `N(x) ∩ C` is large enough that uniformity of `(B, C)` applies to it, so all but `2ε|B|`
vertices `y ∈ B` have `|N(y) ∩ N(x) ∩ C| = (d(B,C) ± 2ε)|N(x) ∩ C|`. -/
theorem uniform_triple_codegree (G : SimpleGraph V) [DecidableRel G.Adj] {A B C : Finset V} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hAC : G.IsUniform ε A C) (hBC : G.IsUniform ε B C)
    (hdAC : 2 * ε ≤ (G.edgeDensity A C : ℝ)) (hdBC : 2 * ε ≤ (G.edgeDensity B C : ℝ)) :
    ((#{p ∈ A ×ˢ B | ¬ (((G.edgeDensity A C : ℝ) - ε) * ((G.edgeDensity B C : ℝ) - 2 * ε)
            * (#C : ℝ) ≤ (codegreeIn G C p.1 p.2 : ℝ) ∧
          (codegreeIn G C p.1 p.2 : ℝ) ≤ ((G.edgeDensity A C : ℝ) + ε)
            * ((G.edgeDensity B C : ℝ) + 2 * ε) * (#C : ℝ))} : ℕ) : ℝ)
      ≤ 4 * ε * (#A : ℝ) * (#B : ℝ) := by
  classical
  set dA : ℝ := (G.edgeDensity A C : ℝ) with hdA
  set dB : ℝ := (G.edgeDensity B C : ℝ) with hdB
  set Q : V × V → Prop := fun p => ¬ ((dA - ε) * (dB - 2 * ε) * (#C : ℝ)
      ≤ (codegreeIn G C p.1 p.2 : ℝ) ∧
    (codegreeIn G C p.1 p.2 : ℝ) ≤ (dA + ε) * (dB + 2 * ε) * (#C : ℝ)) with hQ
  have hCnn : (0 : ℝ) ≤ (#C : ℝ) := by positivity
  have hBnn : (0 : ℝ) ≤ (#B : ℝ) := by positivity
  have hAnn : (0 : ℝ) ≤ (#A : ℝ) := by positivity
  -- the two exceptional vertex sets in `A`
  set Alo : Finset V := {x ∈ A | ((#{z ∈ C | G.Adj x z} : ℕ) : ℝ) < (dA - ε) * (#C : ℝ)} with hAlo
  set Ahi : Finset V := {x ∈ A | (dA + ε) * (#C : ℝ) < ((#{z ∈ C | G.Adj x z} : ℕ) : ℝ)} with hAhi
  have hCC : (#C : ℝ) * ε ≤ (#C : ℝ) := by nlinarith only [hε1]
  have hAlocard : ((#Alo : ℕ) : ℝ) ≤ ε * (#A : ℝ) :=
    card_filter_lt_le G hε hAC (subset_refl C) hCC (by linarith)
  have hAhicard : ((#Ahi : ℕ) : ℝ) ≤ ε * (#A : ℝ) :=
    card_filter_gt_le G hε hAC (subset_refl C) hCC (by linarith)
  -- the good vertices of `A` have few bad partners in `B`
  have hgood : ∀ x ∈ A, x ∉ Alo → x ∉ Ahi →
      ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ) ≤ 2 * ε * (#B : ℝ) := by
    intro x hxA hxlo hxhi
    set Cx : Finset V := {z ∈ C | G.Adj x z} with hCx
    have hCxsub : Cx ⊆ C := Finset.filter_subset _ _
    have hCxlo : (dA - ε) * (#C : ℝ) ≤ ((#Cx : ℕ) : ℝ) := by
      by_contra hc
      push Not at hc
      exact hxlo (by rw [hAlo, Finset.mem_filter]; exact ⟨hxA, hc⟩)
    have hCxhi : ((#Cx : ℕ) : ℝ) ≤ (dA + ε) * (#C : ℝ) := by
      by_contra hc
      push Not at hc
      exact hxhi (by rw [hAhi, Finset.mem_filter]; exact ⟨hxA, hc⟩)
    have hCxcard : (#C : ℝ) * ε ≤ ((#Cx : ℕ) : ℝ) := by nlinarith only [hdAC, hCxlo]
    set Blo : Finset V := {y ∈ B | ((#{z ∈ Cx | G.Adj y z} : ℕ) : ℝ) < (dB - 2 * ε) * (#Cx : ℝ)}
      with hBlo
    set Bhi : Finset V := {y ∈ B | (dB + 2 * ε) * (#Cx : ℝ) < ((#{z ∈ Cx | G.Adj y z} : ℕ) : ℝ)}
      with hBhi
    have hBlocard : ((#Blo : ℕ) : ℝ) ≤ ε * (#B : ℝ) :=
      card_filter_lt_le G hε hBC hCxsub hCxcard (by linarith)
    have hBhicard : ((#Bhi : ℕ) : ℝ) ≤ ε * (#B : ℝ) :=
      card_filter_gt_le G hε hBC hCxsub hCxcard (by linarith)
    have hsub : {y ∈ B | Q (x, y)} ⊆ Blo ∪ Bhi := by
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨hyB, hyQ⟩ := hy
      by_contra hc
      rw [Finset.mem_union] at hc
      push Not at hc
      obtain ⟨hc1, hc2⟩ := hc
      have h1 : (dB - 2 * ε) * (#Cx : ℝ) ≤ ((#{z ∈ Cx | G.Adj y z} : ℕ) : ℝ) := by
        by_contra hcc
        push Not at hcc
        exact hc1 (by rw [hBlo, Finset.mem_filter]; exact ⟨hyB, hcc⟩)
      have h2 : ((#{z ∈ Cx | G.Adj y z} : ℕ) : ℝ) ≤ (dB + 2 * ε) * (#Cx : ℝ) := by
        by_contra hcc
        push Not at hcc
        exact hc2 (by rw [hBhi, Finset.mem_filter]; exact ⟨hyB, hcc⟩)
      have hcodeg : (codegreeIn G C x y : ℝ) = ((#{z ∈ Cx | G.Adj y z} : ℕ) : ℝ) := by
        rw [codegreeIn_eq_card_filter, hCx]
      apply hyQ
      constructor
      · rw [hcodeg]
        nlinarith only [hdBC, hCxlo, h1]
      · rw [hcodeg]
        nlinarith
    calc ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ) ≤ ((#(Blo ∪ Bhi) : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((#Blo : ℕ) : ℝ) + ((#Bhi : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_union_le Blo Bhi
      _ ≤ 2 * ε * (#B : ℝ) := by linarith
  -- assemble
  rw [card_filter_product A B Q]
  push_cast
  rw [← Finset.sum_filter_add_sum_filter_not A (fun x => x ∈ Alo ∪ Ahi)
    (fun x => ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ))]
  have hbad : ∑ x ∈ {x ∈ A | x ∈ Alo ∪ Ahi}, ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ)
      ≤ 2 * ε * (#A : ℝ) * (#B : ℝ) := by
    have hle : ∀ x ∈ {x ∈ A | x ∈ Alo ∪ Ahi}, ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ) ≤ (#B : ℝ) := by
      intro x _
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    calc ∑ x ∈ {x ∈ A | x ∈ Alo ∪ Ahi}, ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ)
        ≤ ∑ _x ∈ {x ∈ A | x ∈ Alo ∪ Ahi}, (#B : ℝ) := Finset.sum_le_sum hle
      _ = ((#{x ∈ A | x ∈ Alo ∪ Ahi} : ℕ) : ℝ) * (#B : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * ε * (#A : ℝ) * (#B : ℝ) := by
          have hs : {x ∈ A | x ∈ Alo ∪ Ahi} ⊆ Alo ∪ Ahi := by
            intro x hx; exact (Finset.mem_filter.mp hx).2
          have h1 : ((#{x ∈ A | x ∈ Alo ∪ Ahi} : ℕ) : ℝ) ≤ ((#(Alo ∪ Ahi) : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_le_card hs
          have h2 : ((#(Alo ∪ Ahi) : ℕ) : ℝ) ≤ ((#Alo : ℕ) : ℝ) + ((#Ahi : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_union_le Alo Ahi
          nlinarith
  have hgoodsum : ∑ x ∈ {x ∈ A | ¬ (x ∈ Alo ∪ Ahi)}, ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ)
      ≤ 2 * ε * (#A : ℝ) * (#B : ℝ) := by
    have hle : ∀ x ∈ {x ∈ A | ¬ (x ∈ Alo ∪ Ahi)},
        ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ) ≤ 2 * ε * (#B : ℝ) := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_union] at hx
      push Not at hx
      exact hgood x hx.1 hx.2.1 hx.2.2
    calc ∑ x ∈ {x ∈ A | ¬ (x ∈ Alo ∪ Ahi)}, ((#{y ∈ B | Q (x, y)} : ℕ) : ℝ)
        ≤ ∑ _x ∈ {x ∈ A | ¬ (x ∈ Alo ∪ Ahi)}, 2 * ε * (#B : ℝ) := Finset.sum_le_sum hle
      _ = ((#{x ∈ A | ¬ (x ∈ Alo ∪ Ahi)} : ℕ) : ℝ) * (2 * ε * (#B : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * ε * (#A : ℝ) * (#B : ℝ) := by
          have h1 : ((#{x ∈ A | ¬ (x ∈ Alo ∪ Ahi)} : ℕ) : ℝ) ≤ (#A : ℝ) := by
            exact_mod_cast Finset.card_filter_le A _
          have h2 : (0 : ℝ) ≤ 2 * ε * (#B : ℝ) := by positivity
          linarith only [mul_le_mul_of_nonneg_right h1 h2]
  linarith

end Nibble.AX1
