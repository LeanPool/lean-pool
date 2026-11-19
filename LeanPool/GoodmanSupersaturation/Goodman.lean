/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

import Mathlib.Algebra.Order.Chebyshev

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Goodman's formula for monochromatic triangles

Colour the edges of the complete graph on a finite vertex type red (`G`) and blue (`Gᶜ`). A vertex
`v` with red degree `d` and blue degree `d'` is the centre of `d * d'` *mixed wedges* (a red edge
and a blue edge at `v`). Every non-monochromatic triangle has exactly two mixed centres, which gives
**Goodman's formula**

`2 * (T(G) + T(Gᶜ)) + ∑ v, deg_G v * deg_{Gᶜ} v = 2 * C(n, 3)`,

where `T` counts triangles. Since `4 d d' ≤ (n - 1) ^ 2`, every two-colouring of `K_n` has at least
`n (n - 1) (n - 5) / 24` monochromatic triangles, with equality for colourings in which every
vertex has red degree `(n - 1) / 2`.

## Main definitions

* `SimpleGraph.degreeWithin G S v`: the number of neighbours of `v` in the finite set `S`.
* `SimpleGraph.cliqueCountIn G S k`: the number of `k`-cliques of `G` contained in `S`.

## Main statements

* `SimpleGraph.goodman_within`, `SimpleGraph.goodman_sq_within`,
  `SimpleGraph.goodman_bound_within`: the statements below inside any finite vertex set `S`.
* `SimpleGraph.goodman`: Goodman's formula.
* `SimpleGraph.goodman_sq`: the same with degree imbalance,
  `8 (T(G) + T(Gᶜ)) + n (n - 1) ^ 2 = 8 C(n, 3) + ∑ v, (deg_G v - deg_{Gᶜ} v) ^ 2`.
* `SimpleGraph.goodman_bound`: **Goodman's bound** `n (n - 1) (n - 5) ≤ 24 (T(G) + T(Gᶜ))`.
* `SimpleGraph.IsRegularOfDegree.goodman_eq`: the bound is attained by every graph regular of
  degree `(n - 1) / 2`.
* `SimpleGraph.two_le_card_cliqueFinset_add_card_cliqueFinset_compl`: every two-colouring of `K_6`
  has at least two monochromatic triangles.
* `SimpleGraph.degreeWithin_eq_degree_induce`,
  `SimpleGraph.cliqueCountIn_eq_card_cliqueFinset_induce`: the local counts are the degrees and
  clique counts of the induced graph `G.induce S`.
* `SimpleGraph.goodman_bound_of_even_card`: for even `n`, at least `n (n - 2) (n - 4) / 24`.
* `SimpleGraph.exists_monochromatic_book`: if `4q + 2 ≤ n`, some edge of `G` or of `Gᶜ` has `q`
  common neighbours in its own colour (a monochromatic book with `q` pages).
* `SimpleGraph.sq_two_mul_sub_le_card_mul_sum_sq`: **edge balance**. The difference between the
  numbers of red and blue edges is controlled by the degree imbalance,
  `(2 (e(G) - e(Gᶜ))) ^ 2 ≤ n ∑ v, (deg_G v - deg_{Gᶜ} v) ^ 2`.

## Implementation notes

The proof sums a pointwise identity over ordered triples of distinct vertices: for such a triple
the six mixed-wedge indicators (one per ordering) add up to `2` minus twice the monochromatic
indicator.

## References

* [A. W. Goodman, *On sets of acquaintances and strangers at any party*][Goodman1959]
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Local degrees and clique counts -/

/-- The degree of `v` inside the finite set `S`: the number of neighbours of `v` in `S`. -/
def degreeWithin (S : Finset V) (v : V) : ℕ := #{w ∈ S | G.Adj v w}

/-- The number of `k`-cliques of `G` contained in `S`. -/
def cliqueCountIn (S : Finset V) (k : ℕ) : ℕ :=
  #((S.powersetCard k).filter fun T : Finset V => G.IsClique (T : Set V))

omit [DecidableEq V] in
/-- The degree within `univ` is the degree. -/
@[simp] theorem degreeWithin_univ [Fintype V] (v : V) : G.degreeWithin univ v = G.degree v := by
  rw [degreeWithin, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter]

/-- The number of `k`-cliques inside `univ` is the number of `k`-cliques. -/
@[simp] theorem cliqueCountIn_univ [Fintype V] (k : ℕ) :
    G.cliqueCountIn univ k = #(G.cliqueFinset k) := by
  rw [cliqueCountIn]
  congr 1
  ext T
  simp [mem_cliqueFinset_iff, isNClique_iff, and_comm]

omit [DecidableEq V] in
/-- The degree within `S` of a vertex of `S` is its degree in the induced graph `G.induce S`. -/
theorem degreeWithin_eq_degree_induce {S : Finset V} {v : V} (hv : v ∈ S) :
    G.degreeWithin S v = (G.induce (S : Set V)).degree ⟨v, hv⟩ := by
  rw [degreeWithin, ← card_neighborFinset_eq_degree]
  refine card_bij (fun w hw => ⟨w, (mem_filter.mp hw).1⟩) (fun w hw => ?_) (fun a _ b _ h => ?_)
    fun w hw => ⟨w.1, ?_, rfl⟩
  · simpa using (mem_filter.mp hw).2
  · simpa using congrArg Subtype.val h
  · simpa using hw

/-- The number of `k`-cliques of `G` inside `S` is the number of `k`-cliques of `G.induce S`. -/
theorem cliqueCountIn_eq_card_cliqueFinset_induce (S : Finset V) (k : ℕ) :
    G.cliqueCountIn S k = #((G.induce (S : Set V)).cliqueFinset k) := by
  rw [cliqueCountIn]
  symm
  refine card_bij (fun T _ => T.map (Function.Embedding.subtype _)) (fun T hT => ?_)
    (fun a _ b _ h => Finset.map_injective _ h) fun T hT => ?_
  · rw [mem_cliqueFinset_iff, isNClique_iff, isClique_induce_iff] at hT
    simp only [mem_filter, mem_powersetCard, card_map, hT.2, and_true, coe_map,
      Function.Embedding.coe_subtype, hT.1]
    intro x hx
    obtain ⟨y, -, rfl⟩ := mem_map.mp hx
    exact y.2
  · simp only [mem_filter, mem_powersetCard] at hT
    refine ⟨T.subtype (· ∈ S), ?_, subtype_map_of_mem fun x hx => hT.1.1 hx⟩
    rw [mem_cliqueFinset_iff, isNClique_iff, isClique_induce_iff, card_subtype,
      filter_true_of_mem fun x hx => hT.1.1 hx, hT.1.2]
    refine ⟨?_, rfl⟩
    convert hT.2
    ext x
    simp only [Set.mem_image, mem_coe, mem_subtype, Subtype.exists, exists_and_right,
      exists_eq_right]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hT.1.1 h, h⟩⟩

/-- Inside `S`, a vertex of `S` has `#S - 1` neighbours in `G` and `Gᶜ` together. -/
theorem degreeWithin_add_degreeWithin_compl {S : Finset V} {v : V} (hv : v ∈ S) :
    G.degreeWithin S v + Gᶜ.degreeWithin S v + 1 = #S := by
  have h1 : {w ∈ S | Gᶜ.Adj v w} = {w ∈ S.erase v | ¬G.Adj v w} := by
    ext w
    simp only [mem_filter, mem_erase, compl_adj]
    exact ⟨fun ⟨hw, hne, hna⟩ => ⟨⟨Ne.symm hne, hw⟩, hna⟩,
      fun ⟨⟨hne, hw⟩, hna⟩ => ⟨hw, Ne.symm hne, hna⟩⟩
  have h2 : {w ∈ S | G.Adj v w} = {w ∈ S.erase v | G.Adj v w} := by
    ext w
    simp only [mem_filter, mem_erase]
    exact ⟨fun ⟨hw, ha⟩ => ⟨⟨(G.ne_of_adj ha).symm, hw⟩, ha⟩, fun ⟨⟨_, hw⟩, ha⟩ => ⟨hw, ha⟩⟩
  rw [degreeWithin, degreeWithin, h1, h2, card_filter_add_card_filter_not, card_erase_of_mem hv]
  have : 0 < #S := card_pos.mpr ⟨v, hv⟩
  omega

/-! ### Ordered triples -/

/-- Ordered triples of distinct elements of `S`. -/
private def distinctTriples (S : Finset V) : Finset (V × V × V) :=
  {x ∈ S ×ˢ S ×ˢ S | x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ x.2.1 ≠ x.2.2}

/-- A finite set `s` has `#s * ((#s - 1) * (#s - 1) - (#s - 1))` ordered triples of distinct
elements. -/
private theorem card_distinctTriples' (s : Finset V) :
    #(distinctTriples s) = #s * ((#s - 1) * (#s - 1) - (#s - 1)) := by
  rw [distinctTriples, card_filter, sum_product, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun x hx => ?_
  rw [← card_erase_of_mem hx, ← offDiag_card, ← card_filter]
  congr 1
  ext ⟨y, z⟩
  simp only [mem_filter, mem_product, mem_offDiag, mem_erase]
  constructor
  · rintro ⟨⟨hy, hz⟩, hxy, hxz, hyz⟩
    exact ⟨⟨Ne.symm hxy, hy⟩, ⟨Ne.symm hxz, hz⟩, hyz⟩
  · rintro ⟨⟨hxy, hy⟩, ⟨hxz, hz⟩, hyz⟩
    exact ⟨⟨hy, hz⟩, Ne.symm hxy, Ne.symm hxz, hyz⟩

/-- There are `6 * C(|S|, 3)` ordered triples of distinct elements of `S`. -/
private theorem card_distinctTriples (S : Finset V) :
    #(distinctTriples S) = 6 * (#S).choose 3 := by
  rw [card_distinctTriples', show 6 = Nat.factorial 3 from rfl,
    ← Nat.descFactorial_eq_factorial_mul_choose, ← Nat.mul_sub_one]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, mul_one,
    show #S - 1 - 1 = #S - 2 by omega]
  ring

private theorem mem_distinctTriples {S : Finset V} {x : V × V × V} :
    x ∈ distinctTriples S ↔
      (x.1 ∈ S ∧ x.2.1 ∈ S ∧ x.2.2 ∈ S) ∧ x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ x.2.1 ≠ x.2.2 := by
  simp [distinctTriples]

/-- The ordered triangles of `H` inside `S`. -/
private def triangleTriples (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) :
    Finset (V × V × V) :=
  {x ∈ S ×ˢ S ×ˢ S | H.Adj x.1 x.2.1 ∧ H.Adj x.1 x.2.2 ∧ H.Adj x.2.1 x.2.2}

/-- Every triangle gives six ordered triangles. -/
private theorem card_triangleTriples (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) :
    #(triangleTriples H S) = 6 * H.cliqueCountIn S 3 := by
  rw [cliqueCountIn, card_eq_sum_card_fiberwise
    (f := fun x : V × V × V => ({x.1, x.2.1, x.2.2} : Finset V))
    (t := (S.powersetCard 3).filter fun T : Finset V => H.IsClique (T : Set V))]
  · rw [mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun s hs => ?_
    rw [mem_filter, mem_powersetCard] at hs
    obtain ⟨⟨hsS, hs3⟩, hcl⟩ := hs
    have h6 := card_distinctTriples' s
    rw [hs3, show 3 * ((3 - 1) * (3 - 1) - (3 - 1)) = 6 from rfl] at h6
    rw [← h6]
    congr 1
    ext ⟨x, y, z⟩
    simp only [triangleTriples, distinctTriples, mem_filter, mem_product]
    constructor
    · rintro ⟨⟨-, hxy, hxz, hyz⟩, rfl⟩
      exact ⟨⟨by simp, by simp, by simp⟩, hxy.ne, hxz.ne, hyz.ne⟩
    · rintro ⟨⟨hx, hy, hz⟩, hxy, hxz, hyz⟩
      refine ⟨⟨⟨hsS hx, hsS hy, hsS hz⟩, hcl hx hy hxy, hcl hx hz hxz, hcl hy hz hyz⟩, ?_⟩
      refine eq_of_subset_of_card_le (by simp [insert_subset_iff, hx, hy, hz]) ?_
      rw [hs3, card_insert_of_notMem (by simp [hxy, hxz]), card_pair hyz]
  · intro x hx
    have hx := mem_coe.mp hx
    simp only [triangleTriples, mem_filter, mem_product] at hx
    obtain ⟨⟨h1, h2, h3⟩, a, b, c⟩ := hx
    change {x.1, x.2.1, x.2.2} ∈ (((S.powersetCard 3).filter
      fun T : Finset V => H.IsClique (T : Set V) : Finset (Finset V)) : Set (Finset V))
    rw [mem_coe, mem_filter, mem_powersetCard]
    have h := is3Clique_triple_iff.mpr ⟨a, b, c⟩
    exact ⟨⟨by simp [insert_subset_iff, h1, h2, h3], h.card_eq⟩, by
      simpa using h.isClique⟩

/-- Mixed wedges inside `S`: a centre, a red neighbour and a blue neighbour. -/
private def mixedTriples (S : Finset V) : Finset (V × V × V) :=
  {x ∈ S ×ˢ S ×ˢ S | G.Adj x.1 x.2.1 ∧ Gᶜ.Adj x.1 x.2.2}

private theorem card_mixedTriples (S : Finset V) :
    #(mixedTriples G S) = ∑ v ∈ S, G.degreeWithin S v * Gᶜ.degreeWithin S v := by
  rw [mixedTriples, card_filter, sum_product]
  refine sum_congr rfl fun u _ => ?_
  rw [degreeWithin, degreeWithin, ← card_product, ← card_filter]
  congr 1
  ext ⟨v, w⟩
  simp only [mem_filter, mem_product]
  tauto

/-- The sum of `f ∘ σ` over the distinct triples equals the sum of `f`, for a permutation `σ` of
the coordinates. -/
private theorem sum_distinctTriples_comp (S : Finset V) (f : V × V × V → ℕ)
    (σ τ : V × V × V → V × V × V) (hστ : ∀ x, σ (τ x) = x) (hτσ : ∀ x, τ (σ x) = x)
    (hD : ∀ x, σ x ∈ distinctTriples S ↔ x ∈ distinctTriples S) :
    ∑ x ∈ distinctTriples S, f (σ x) = ∑ x ∈ distinctTriples S, f x :=
  sum_nbij' σ τ (fun x hx => (hD x).2 hx) (fun x hx => by rw [← hD, hστ]; exact hx)
    (fun x _ => hτσ x) (fun x _ => hστ x) fun _ _ => rfl

/-- The mixed-wedge indicator. -/
private def mixedInd (x : V × V × V) : ℕ := if G.Adj x.1 x.2.1 ∧ Gᶜ.Adj x.1 x.2.2 then 1 else 0

/-- The monochromatic-triangle indicator. -/
private def monoInd (x : V × V × V) : ℕ :=
  (if G.Adj x.1 x.2.1 ∧ G.Adj x.1 x.2.2 ∧ G.Adj x.2.1 x.2.2 then 1 else 0) +
    if Gᶜ.Adj x.1 x.2.1 ∧ Gᶜ.Adj x.1 x.2.2 ∧ Gᶜ.Adj x.2.1 x.2.2 then 1 else 0

/-- The pointwise identity behind Goodman's formula. -/
private theorem pointwise {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    mixedInd G (u, v, w) + mixedInd G (u, w, v) + mixedInd G (v, u, w) + mixedInd G (v, w, u) +
      mixedInd G (w, u, v) + mixedInd G (w, v, u) + 2 * monoInd G (u, v, w) = 2 := by
  simp only [mixedInd, monoInd, compl_adj, ne_eq, huv, huw, hvw, Ne.symm huv, Ne.symm huw,
    Ne.symm hvw, not_false_eq_true, true_and, G.adj_comm v u, G.adj_comm w u, G.adj_comm w v]
  by_cases a : G.Adj u v <;> by_cases b : G.Adj u w <;> by_cases c : G.Adj v w <;> simp [a, b, c]

/-! ### Goodman's formula -/

/-- **Goodman's formula inside a finite set.** For every finite vertex set `S`, twice the number of
monochromatic triangles in `S` plus the number of mixed wedges in `S` is `2 * C(|S|, 3)`. -/
theorem goodman_within (S : Finset V) :
    2 * (G.cliqueCountIn S 3 + Gᶜ.cliqueCountIn S 3) +
        ∑ v ∈ S, G.degreeWithin S v * Gᶜ.degreeWithin S v = 2 * (#S).choose 3 := by
  have hsum : ∑ x ∈ distinctTriples S, (mixedInd G x + mixedInd G (x.1, x.2.2, x.2.1) +
      mixedInd G (x.2.1, x.1, x.2.2) + mixedInd G (x.2.1, x.2.2, x.1) +
      mixedInd G (x.2.2, x.1, x.2.1) + mixedInd G (x.2.2, x.2.1, x.1) + 2 * monoInd G x) =
      ∑ _x ∈ distinctTriples S, 2 := by
    refine sum_congr rfl fun ⟨u, v, w⟩ hx => ?_
    obtain ⟨-, huv, huw, hvw⟩ := mem_distinctTriples.mp hx
    exact pointwise G huv huw hvw
  have hsub : distinctTriples S ⊆ S ×ˢ S ×ˢ S := filter_subset _ _
  -- each permuted sum is the mixed-wedge count
  have hperm : ∀ (σ τ : V × V × V → V × V × V), (∀ x, σ (τ x) = x) → (∀ x, τ (σ x) = x) →
      (∀ x, σ x ∈ distinctTriples S ↔ x ∈ distinctTriples S) →
      ∑ x ∈ distinctTriples S, mixedInd G (σ x) = #(mixedTriples G S) := by
    intro σ τ h1 h2 h3
    rw [sum_distinctTriples_comp S _ σ τ h1 h2 h3, mixedTriples, card_filter]
    refine (sum_subset hsub fun x hxS hx => ?_).trans rfl
    simp only [mixedInd, ite_eq_right_iff, one_ne_zero, imp_false, not_and]
    intro h h'
    refine hx (mem_distinctTriples.mpr ⟨by simpa [mem_product] using hxS, h.ne, h'.ne,
      fun e => ?_⟩)
    rw [compl_adj] at h'
    exact h'.2 (e ▸ h)
  have hmono : ∑ x ∈ distinctTriples S, monoInd G x =
      #(triangleTriples G S) + #(triangleTriples Gᶜ S) := by
    rw [triangleTriples, triangleTriples, card_filter, card_filter, ← sum_add_distrib]
    refine (sum_subset hsub fun x hxS hx => ?_).trans rfl
    rw [mem_distinctTriples] at hx
    have hS : x.1 ∈ S ∧ x.2.1 ∈ S ∧ x.2.2 ∈ S := by simpa [mem_product] using hxS
    have hA : ¬(G.Adj x.1 x.2.1 ∧ G.Adj x.1 x.2.2 ∧ G.Adj x.2.1 x.2.2) := fun h =>
      hx ⟨hS, h.1.ne, h.2.1.ne, h.2.2.ne⟩
    have hB : ¬(Gᶜ.Adj x.1 x.2.1 ∧ Gᶜ.Adj x.1 x.2.2 ∧ Gᶜ.Adj x.2.1 x.2.2) := fun h =>
      hx ⟨hS, h.1.ne, h.2.1.ne, h.2.2.ne⟩
    simp only [monoInd, hA, hB, ↓reduceIte, add_zero]
  have h0 : ∑ x ∈ distinctTriples S, mixedInd G x = #(mixedTriples G S) :=
    hperm id id (fun _ => rfl) (fun _ => rfl) (fun _ => Iff.rfl)
  simp only [sum_add_distrib, ← mul_sum] at hsum
  rw [h0,
    hperm (fun x => (x.1, x.2.2, x.2.1)) (fun x => (x.1, x.2.2, x.2.1)) (fun _ => rfl)
      (fun _ => rfl) (fun x => by simp only [mem_distinctTriples]; tauto),
    hperm (fun x => (x.2.1, x.1, x.2.2)) (fun x => (x.2.1, x.1, x.2.2)) (fun _ => rfl)
      (fun _ => rfl) (fun x => by simp only [mem_distinctTriples]; tauto),
    hperm (fun x => (x.2.1, x.2.2, x.1)) (fun x => (x.2.2, x.1, x.2.1)) (fun _ => rfl)
      (fun _ => rfl) (fun x => by simp only [mem_distinctTriples]; tauto),
    hperm (fun x => (x.2.2, x.1, x.2.1)) (fun x => (x.2.1, x.2.2, x.1)) (fun _ => rfl)
      (fun _ => rfl) (fun x => by simp only [mem_distinctTriples]; tauto),
    hperm (fun x => (x.2.2, x.2.1, x.1)) (fun x => (x.2.2, x.2.1, x.1)) (fun _ => rfl)
      (fun _ => rfl) (fun x => by simp only [mem_distinctTriples]; tauto),
    hmono, sum_const, smul_eq_mul, card_distinctTriples, card_triangleTriples,
    card_triangleTriples, card_mixedTriples] at hsum
  linarith

omit [DecidableEq V] in
/-- `6 C(n, 3) = n (n - 1) (n - 2)`, over `ℤ`. -/
private theorem six_mul_choose_three (n : ℕ) :
    (6 * n.choose 3 : ℤ) = n * (n - 1) * (n - 2) := by
  rcases n with _ | _ | _ | n
  · simp [Nat.choose]
  · simp [Nat.choose]
  · simp [Nat.choose]
  · have : 6 * (n + 3).choose 3 = (n + 3) * (n + 2) * (n + 1) := by
      rw [show 6 = Nat.factorial 3 from rfl, ← Nat.descFactorial_eq_factorial_mul_choose]
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero]
      simp only [show n + 3 - 2 = n + 1 by omega, show n + 3 - 1 = n + 2 by omega,
        Nat.sub_zero]
      ring
    have := congrArg (fun m : ℕ => (m : ℤ)) this
    push_cast at this ⊢
    linarith

/-- **Goodman's formula with degree imbalance, inside a finite set.**
`8 (T + T') + |S| (|S| - 1) ^ 2 = 8 C(|S|, 3) + ∑ v ∈ S, (d v - d' v) ^ 2`. -/
theorem goodman_sq_within (S : Finset V) :
    8 * ((G.cliqueCountIn S 3 + Gᶜ.cliqueCountIn S 3 : ℕ) : ℤ) + #S * ((#S : ℤ) - 1) ^ 2 =
      8 * (#S).choose 3 + ∑ v ∈ S, ((G.degreeWithin S v : ℤ) - Gᶜ.degreeWithin S v) ^ 2 := by
  have h := congrArg (fun m : ℕ => (m : ℤ)) (goodman_within G S)
  push_cast at h
  have hsq : ∀ v ∈ S, ((#S : ℤ) - 1) ^ 2 = 4 * (G.degreeWithin S v * Gᶜ.degreeWithin S v : ℤ) +
      ((G.degreeWithin S v : ℤ) - Gᶜ.degreeWithin S v) ^ 2 := fun v hv => by
    have h1 := degreeWithin_add_degreeWithin_compl G hv
    have : (#S : ℤ) - 1 = G.degreeWithin S v + Gᶜ.degreeWithin S v := by omega
    rw [this]
    ring
  have hn : (#S : ℤ) * ((#S : ℤ) - 1) ^ 2 =
      4 * ∑ v ∈ S, (G.degreeWithin S v * Gᶜ.degreeWithin S v : ℤ) +
        ∑ v ∈ S, ((G.degreeWithin S v : ℤ) - Gᶜ.degreeWithin S v) ^ 2 := by
    rw [mul_sum, ← sum_add_distrib, ← sum_congr rfl hsq, sum_const, nsmul_eq_mul]
  rw [hn]
  push_cast
  linarith

/-- **Goodman's bound inside a finite set.** Every finite vertex set `S` contains at least
`|S| (|S| - 1) (|S| - 5) / 24` monochromatic triangles. -/
theorem goodman_bound_within (S : Finset V) :
    #S * (#S - 1) * (#S - 5) ≤ 24 * (G.cliqueCountIn S 3 + Gᶜ.cliqueCountIn S 3) := by
  have h := goodman_sq_within G S
  have hnn : 0 ≤ ∑ v ∈ S, ((G.degreeWithin S v : ℤ) - Gᶜ.degreeWithin S v) ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hc := six_mul_choose_three (#S)
  rcases Nat.lt_or_ge (#S) 5 with h5 | h5
  · rw [show #S - 5 = 0 by omega, mul_zero]
    exact Nat.zero_le _
  zify [h5, show 1 ≤ #S by omega]
  push_cast at h
  linarith

section Fintype

variable [Fintype V]

/-- **Goodman's formula.** For a red/blue colouring of `K_n` given by `G` and `Gᶜ`, twice the
number of monochromatic triangles plus the number of mixed wedges is `2 * C(n, 3)`. -/
theorem goodman :
    2 * (#(G.cliqueFinset 3) + #(Gᶜ.cliqueFinset 3)) + ∑ v, G.degree v * Gᶜ.degree v =
      2 * (Fintype.card V).choose 3 := by
  simpa using goodman_within G univ

/-- The red and blue degrees of a vertex add up to `n - 1`. -/
theorem degree_add_degree_compl (v : V) : G.degree v + Gᶜ.degree v = Fintype.card V - 1 := by
  have := G.degree_lt_card_verts v
  rw [degree_compl]
  omega

/-- **Goodman's formula with degree imbalance.**
`8 (T(G) + T(Gᶜ)) + n (n - 1) ^ 2 = 8 C(n, 3) + ∑ v, (deg_G v - deg_{Gᶜ} v) ^ 2`. -/
theorem goodman_sq :
    8 * ((#(G.cliqueFinset 3) + #(Gᶜ.cliqueFinset 3) : ℕ) : ℤ) +
        Fintype.card V * ((Fintype.card V : ℤ) - 1) ^ 2 =
      8 * (Fintype.card V).choose 3 + ∑ v, ((G.degree v : ℤ) - Gᶜ.degree v) ^ 2 := by
  simpa using goodman_sq_within G univ

/-- **Goodman's bound.** Every red/blue colouring of `K_n` has at least `n (n - 1) (n - 5) / 24`
monochromatic triangles. -/
theorem goodman_bound :
    Fintype.card V * (Fintype.card V - 1) * (Fintype.card V - 5) ≤
      24 * (#(G.cliqueFinset 3) + #(Gᶜ.cliqueFinset 3)) := by
  simpa using goodman_bound_within G univ

/-- **Goodman's bound for even orders.** If `n` is even, every red/blue colouring of `K_n` has at
least `n (n - 2) (n - 4) / 24` monochromatic triangles: each red and blue degree differ by an odd
number, so every squared difference in `goodman_sq` is at least `1`. -/
theorem goodman_bound_of_even_card (hn : Even (Fintype.card V)) :
    (Fintype.card V : ℤ) * (Fintype.card V - 2) * (Fintype.card V - 4) ≤
      24 * ((#(G.cliqueFinset 3) + #(Gᶜ.cliqueFinset 3) : ℕ) : ℤ) := by
  have h := goodman_sq G
  have hone : ∀ v, 1 ≤ ((G.degree v : ℤ) - Gᶜ.degree v) ^ 2 := fun v => by
    have hd := degree_add_degree_compl G v
    have hpos := Fintype.card_pos_iff.mpr ⟨v⟩
    obtain ⟨k, hk⟩ := hn
    have hz : (G.degree v : ℤ) - Gᶜ.degree v ≠ 0 := by
      intro h0
      have : G.degree v = Gᶜ.degree v := by omega
      omega
    have : 0 < ((G.degree v : ℤ) - Gᶜ.degree v) ^ 2 := by positivity
    exact Int.add_one_le_iff.mpr this
  have hsum : (Fintype.card V : ℤ) ≤ ∑ v, ((G.degree v : ℤ) - Gᶜ.degree v) ^ 2 := by
    simpa using sum_le_sum fun v (_ : v ∈ univ) => hone v
  have hc := six_mul_choose_three (Fintype.card V)
  linarith

/-- **Sharpness of Goodman's bound.** If `G` is regular of degree `k` on `2k + 1` vertices, then
`24 (T(G) + T(Gᶜ)) = n (n - 1) (n - 5)` exactly. -/
theorem IsRegularOfDegree.goodman_eq {k : ℕ} (hG : G.IsRegularOfDegree k)
    (hn : Fintype.card V = 2 * k + 1) :
    (24 * (#(G.cliqueFinset 3) + #(Gᶜ.cliqueFinset 3)) : ℤ) =
      Fintype.card V * (Fintype.card V - 1) * (Fintype.card V - 5) := by
  have h := goodman_sq G
  have hd : ∀ v, ((G.degree v : ℤ) - Gᶜ.degree v) ^ 2 = 0 := fun v => by
    have := degree_add_degree_compl G v
    rw [hG v, hn] at this
    rw [hG v, show Gᶜ.degree v = k by omega, sub_self]
    ring
  simp only [hd, sum_const_zero, add_zero] at h
  have hc := six_mul_choose_three (Fintype.card V)
  push_cast at h
  linarith

/-- Every red/blue colouring of `K_6` has at least two monochromatic triangles. -/
theorem two_le_card_cliqueFinset_add_card_cliqueFinset_compl (h6 : Fintype.card V = 6) :
    2 ≤ #(G.cliqueFinset 3) + #(Gᶜ.cliqueFinset 3) := by
  have := goodman_bound G
  rw [h6] at this
  omega

/-! ### Monochromatic books -/

omit [DecidableEq V] in
/-- Codegrees as filters. -/
private theorem card_commonNeighbors_eq_filter (H : SimpleGraph V) [DecidableRel H.Adj] (u v : V) :
    Fintype.card (H.commonNeighbors u v) = #{w | H.Adj u w ∧ H.Adj v w} := by
  rw [← Set.toFinset_card]
  congr 1
  ext w
  simp [mem_commonNeighbors]

/-- Summing codegrees over ordered adjacent pairs counts ordered triangles. -/
private theorem sum_codegree_eq (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∑ u, ∑ v ∈ H.neighborFinset u, Fintype.card (H.commonNeighbors u v) =
      6 * #(H.cliqueFinset 3) := by
  rw [← cliqueCountIn_univ, ← card_triangleTriples]
  simp only [triangleTriples, card_filter, sum_product, card_commonNeighbors_eq_filter]
  refine sum_congr rfl fun u _ => ?_
  rw [neighborFinset_eq_filter, sum_filter]
  refine sum_congr rfl fun v _ => ?_
  split_ifs with h <;> simp [h]

/-- **Monochromatic books.** If `4q + 2 ≤ n`, every red/blue colouring of `K_n` has an edge whose
endpoints have at least `q` common neighbours in the colour of that edge. For `q = 1` this is the
monochromatic triangle in `K_6`. -/
theorem exists_monochromatic_book {q : ℕ} (hq : 4 * q + 2 ≤ Fintype.card V) :
    ∃ u v, (G.Adj u v ∧ q ≤ Fintype.card (G.commonNeighbors u v)) ∨
      (Gᶜ.Adj u v ∧ q ≤ Fintype.card (Gᶜ.commonNeighbors u v)) := by
  have hcard : 2 ≤ Fintype.card V := by omega
  obtain ⟨u, v, huv⟩ := Fintype.exists_pair_of_one_lt_card hcard
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · by_cases h : G.Adj u v
    · exact ⟨u, v, .inl ⟨h, Nat.zero_le _⟩⟩
    · exact ⟨u, v, .inr ⟨(compl_adj G u v).mpr ⟨huv, h⟩, Nat.zero_le _⟩⟩
  by_contra hne
  simp only [not_exists, not_or, not_and, not_le] at hne
  have hle : ∀ H : SimpleGraph V, [DecidableRel H.Adj] →
      (∀ u v, H.Adj u v → Fintype.card (H.commonNeighbors u v) < q) →
      6 * #(H.cliqueFinset 3) ≤ (q - 1) * ∑ u, H.degree u := by
    intro H _ hH
    rw [← sum_codegree_eq, mul_sum]
    refine sum_le_sum fun u _ => ?_
    rw [← card_neighborFinset_eq_degree, mul_comm, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun v hv => Nat.le_sub_one_of_lt (hH u v ((mem_neighborFinset _ _ _).mp hv))
  have h1 := hle G fun u v h => (hne u v).1 h
  have h2 := hle Gᶜ fun u v h => (hne u v).2 h
  have hdeg : ∑ u, G.degree u + ∑ u, Gᶜ.degree u = Fintype.card V * (Fintype.card V - 1) := by
    rw [← sum_add_distrib, sum_congr rfl fun v _ => degree_add_degree_compl G v, sum_const,
      card_univ, smul_eq_mul]
  have hg := goodman_bound G
  set n := Fintype.card V
  set T := #(G.cliqueFinset 3) + #(Gᶜ.cliqueFinset 3)
  have hsum : 6 * T ≤ (q - 1) * (n * (n - 1)) := by
    rw [← hdeg, mul_add]
    simp only [mul_add]
    omega
  have h5 : n * (n - 1) * (4 * q - 3) ≤ n * (n - 1) * (n - 5) :=
    Nat.mul_le_mul_left _ (by omega)
  have hpos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  have : n * (n - 1) * (4 * q - 3) ≤ n * (n - 1) * (4 * (q - 1)) := by
    calc n * (n - 1) * (4 * q - 3) ≤ 24 * T := h5.trans hg
      _ = 4 * (6 * T) := by ring
      _ ≤ 4 * ((q - 1) * (n * (n - 1))) := Nat.mul_le_mul_left 4 hsum
      _ = n * (n - 1) * (4 * (q - 1)) := by ring
  have := Nat.le_of_mul_le_mul_left this hpos
  omega

/-! ### Edge balance -/

/-- **Edge balance.** `(2 (e(G) - e(Gᶜ))) ^ 2 ≤ n ∑ v, (deg_G v - deg_{Gᶜ} v) ^ 2`: if the red and
blue degrees are nearly equal at every vertex, so are the numbers of red and blue edges. -/
theorem sq_two_mul_sub_le_card_mul_sum_sq :
    (2 * ((#G.edgeFinset : ℤ) - #Gᶜ.edgeFinset)) ^ 2 ≤
      Fintype.card V * ∑ v, ((G.degree v : ℤ) - Gᶜ.degree v) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset V))
    (f := fun v => (G.degree v : ℤ) - Gᶜ.degree v)
  rw [card_univ] at h
  have hs : ∑ v, ((G.degree v : ℤ) - Gᶜ.degree v) =
      2 * ((#G.edgeFinset : ℤ) - #Gᶜ.edgeFinset) := by
    rw [sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges,
      Gᶜ.sum_degrees_eq_twice_card_edges]
    push_cast
    ring
  rw [← hs]
  exact h

end Fintype

end SimpleGraph
