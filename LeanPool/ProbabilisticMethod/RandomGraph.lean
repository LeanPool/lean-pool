/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.ProbabilisticMethod.BernoulliWeights
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Sym

import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The random graph `G(n, p)` and lower bounds for Ramsey numbers

The random graph `G(n, p)` keeps each pair of distinct vertices independently with probability
`p`. Here it is the `p`-biased cube (`Finset.bernoulliWeight`) on the set of pairs
`SimpleGraph.possibleEdges V`, read as a graph through `SimpleGraph.fromEdgeSet`. A vertex set `s`
is a clique with probability `p ^ C(|s|, 2)` and independent with probability
`(1 - p) ^ C(|s|, 2)`, and the first-moment method gives Erdős's lower bounds for Ramsey numbers.

## Main definitions

* `SimpleGraph.possibleEdges V`: the pairs of distinct vertices, as a `Finset (Sym2 V)`.
* `Finset.pairs s`: the pairs of distinct elements of `s`.

## Main statements

* `SimpleGraph.isClique_fromEdgeSet_iff`, `SimpleGraph.isClique_compl_fromEdgeSet_iff`: cliques and
  independent sets of `fromEdgeSet A` in terms of `A`.
* `SimpleGraph.bernoulliProb_isClique`, `SimpleGraph.bernoulliProb_isClique_compl`: a fixed
  `k`-set is a clique of `G(n, p)` with probability `p ^ C(k, 2)`, and independent with probability
  `(1 - p) ^ C(k, 2)`.
* `SimpleGraph.exists_cliqueFree_of_lt_one`: **the biased first-moment bound**. If
  `C(n, k) p ^ C(k, 2) + C(n, l) (1 - p) ^ C(l, 2) < 1`, some graph on `n` vertices has no
  `k`-clique and no independent `l`-set; that is, `R(k, l) > n`.
* `SimpleGraph.exists_cliqueFree_of_sq_le_two_pow`: **Erdős's bound** `R(k, k) > 2 ^ (k / 2)`:
  if `k ≥ 3` and `n ^ 2 ≤ 2 ^ k`, some graph on `n` vertices has neither a `k`-clique nor an
  independent `k`-set.
* `SimpleGraph.exists_large_cliqueFree_of_deletion`: **the deletion method**. Some graph on `n`
  vertices has a set of at least `n - C(n, k) p ^ C(k, 2) - C(n, l) (1 - p) ^ C(l, 2)` vertices
  containing no `k`-clique and no independent `l`-set.

## References

* [P. Erdős, *Some remarks on the theory of graphs*][Erdos1947]
* [N. Alon, J. H. Spencer, *The probabilistic method*][AlonSpencer2016]
-/

@[expose] public section

open Finset

namespace Finset

variable {V : Type*} [DecidableEq V]

/-- The pairs of distinct elements of `s`. -/
def pairs (s : Finset V) : Finset (Sym2 V) := {e ∈ s.sym2 | ¬e.IsDiag}

/-- `s(v, w)` is a pair of `s` when `v` and `w` are distinct elements of `s`. -/
theorem mem_pairs {s : Finset V} {v w : V} : s(v, w) ∈ s.pairs ↔ v ∈ s ∧ w ∈ s ∧ v ≠ w := by
  simp [pairs, mem_sym2_iff, and_assoc]

/-- The pairs of a subset are pairs of the superset. -/
theorem pairs_mono {s t : Finset V} (h : s ⊆ t) : s.pairs ⊆ t.pairs :=
  filter_subset_filter _ (sym2_mono h)

/-- The pairs of distinct elements of `s` are the image of `s.offDiag` in `Sym2`. -/
theorem pairs_eq_image_offDiag (s : Finset V) : s.pairs = s.offDiag.image Sym2.mk.uncurry := by
  ext e
  induction e using Sym2.ind with
  | _ v w =>
    rw [mem_pairs, mem_image]
    constructor
    · rintro ⟨hv, hw, hvw⟩
      exact ⟨(v, w), mem_offDiag.mpr ⟨hv, hw, hvw⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, hab, h⟩
      obtain ⟨ha, hb, hne⟩ := mem_offDiag.mp hab
      rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨ha, hb, hne⟩
      · exact ⟨hb, ha, Ne.symm hne⟩

/-- A set of size `n` has `C(n, 2)` pairs of distinct elements (Mathlib's
`Sym2.card_image_offDiag`). -/
theorem card_pairs (s : Finset V) : #s.pairs = (#s).choose 2 := by
  rw [pairs_eq_image_offDiag, Sym2.card_image_offDiag]

end Finset

namespace SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- The pairs of distinct vertices of a finite type: the possible edges, that is, the edges of
the complete graph. -/
def possibleEdges (V : Type*) [Fintype V] [DecidableEq V] : Finset (Sym2 V) :=
  (⊤ : SimpleGraph V).edgeFinset

/-- The possible edges are the pairs of distinct vertices. -/
theorem possibleEdges_eq_pairs_univ [Fintype V] : possibleEdges V = (univ : Finset V).pairs := by
  ext e
  induction e using Sym2.ind with
  | _ v w => simp [possibleEdges, mem_pairs]

/-- The pairs of any vertex set are possible edges. -/
theorem pairs_subset_possibleEdges [Fintype V] (s : Finset V) : s.pairs ⊆ possibleEdges V :=
  possibleEdges_eq_pairs_univ (V := V) ▸ pairs_mono (subset_univ s)

/-- A set `s` is a clique of `fromEdgeSet A` exactly when every pair of `s` lies in `A`. -/
theorem isClique_fromEdgeSet_iff {A : Finset (Sym2 V)} {s : Finset V} :
    (fromEdgeSet (A : Set (Sym2 V))).IsClique (s : Set V) ↔ s.pairs ⊆ A := by
  constructor
  · intro h e he
    induction e using Sym2.ind with
    | _ v w =>
      obtain ⟨hv, hw, hvw⟩ := mem_pairs.mp he
      exact (fromEdgeSet_adj _).mp (h hv hw hvw) |>.1
  · intro h v hv w hw hvw
    exact (fromEdgeSet_adj _).mpr ⟨h (mem_pairs.mpr ⟨hv, hw, hvw⟩), hvw⟩

/-- A set `s` is independent in `fromEdgeSet A` exactly when no pair of `s` lies in `A`. -/
theorem isClique_compl_fromEdgeSet_iff {A : Finset (Sym2 V)} {s : Finset V} :
    (fromEdgeSet (A : Set (Sym2 V)))ᶜ.IsClique (s : Set V) ↔ Disjoint s.pairs A := by
  constructor
  · intro h
    refine Finset.disjoint_left.mpr fun e he heA => ?_
    induction e using Sym2.ind with
    | _ v w =>
      obtain ⟨hv, hw, hvw⟩ := mem_pairs.mp he
      exact ((compl_adj _ _ _).mp (h hv hw hvw)).2 ((fromEdgeSet_adj _).mpr ⟨heA, hvw⟩)
  · intro h v hv w hw hvw
    refine (compl_adj _ _ _).mpr ⟨hvw, fun hadj => ?_⟩
    exact Finset.disjoint_left.mp h (mem_pairs.mpr ⟨hv, hw, hvw⟩)
      (by exact_mod_cast ((fromEdgeSet_adj _).mp hadj).1)

variable [Fintype V] {p : ℝ}

/-- A fixed set `s` is a clique of `G(n, p)` with probability `p ^ C(|s|, 2)`. -/
theorem bernoulliProb_isClique (s : Finset V) :
    (possibleEdges V).bernoulliProb p (s.pairs ⊆ ·) = p ^ (#s).choose 2 := by
  rw [bernoulliProb_superset (pairs_subset_possibleEdges s),
    card_pairs]

/-- A fixed set `s` is independent in `G(n, p)` with probability `(1 - p) ^ C(|s|, 2)`. -/
theorem bernoulliProb_isClique_compl (s : Finset V) :
    (possibleEdges V).bernoulliProb p (Disjoint · s.pairs) = (1 - p) ^ (#s).choose 2 := by
  rw [bernoulliProb_disjoint (pairs_subset_possibleEdges s),
    card_pairs]

/-- The expected number of `k`-cliques plus independent `l`-sets in `G(n, p)`. -/
private theorem expectation_bad (k l : ℕ) :
    ∑ A ∈ (possibleEdges V).powerset, (possibleEdges V).bernoulliWeight p A *
        ((#{s ∈ (univ : Finset V).powersetCard k | s.pairs ⊆ A} : ℝ) +
          #{s ∈ (univ : Finset V).powersetCard l | Disjoint A s.pairs}) =
      (Fintype.card V).choose k * p ^ k.choose 2 +
        (Fintype.card V).choose l * (1 - p) ^ l.choose 2 := by
  simp_rw [mul_add, sum_add_distrib]
  have x1 := expectation_card_filter (U := possibleEdges V) (p := p)
    ((univ : Finset V).powersetCard k) (fun s A => s.pairs ⊆ A)
  have x2 := expectation_card_filter (U := possibleEdges V) (p := p)
    ((univ : Finset V).powersetCard l) (fun s A => Disjoint A s.pairs)
  rw [x1, x2]
  have e1 : ∀ s ∈ (univ : Finset V).powersetCard k,
      (possibleEdges V).bernoulliProb p (s.pairs ⊆ ·) = p ^ k.choose 2 := fun s hs => by
    rw [bernoulliProb_isClique, (mem_powersetCard.mp hs).2]
  have e2 : ∀ s ∈ (univ : Finset V).powersetCard l,
      (possibleEdges V).bernoulliProb p (Disjoint · s.pairs) = (1 - p) ^ l.choose 2 :=
    fun s hs => by
    rw [bernoulliProb_isClique_compl, (mem_powersetCard.mp hs).2]
  rw [sum_congr rfl e1, sum_congr rfl e2, sum_const, sum_const, card_powersetCard,
    card_powersetCard, card_univ, nsmul_eq_mul, nsmul_eq_mul]

omit [DecidableEq V] in
/-- **The deletion method.** For `0 ≤ p ≤ 1`, some graph on `V` has a vertex set `t` of size at
least `n - C(n, k) p ^ C(k, 2) - C(n, l) (1 - p) ^ C(l, 2)` containing no `k`-clique and no
independent `l`-set, provided `k, l ≥ 1`. -/
theorem exists_large_cliqueFree_of_deletion (h0 : 0 ≤ p) (h1 : p ≤ 1) {k l : ℕ} (hk : 1 ≤ k)
    (hl : 1 ≤ l) :
    ∃ (G : SimpleGraph V) (t : Finset V),
      (Fintype.card V : ℝ) - ((Fintype.card V).choose k * p ^ k.choose 2 +
        (Fintype.card V).choose l * (1 - p) ^ l.choose 2) ≤ #t ∧
      (∀ s ⊆ t, ¬G.IsNClique k s) ∧ ∀ s ⊆ t, ¬Gᶜ.IsNClique l s := by
  classical
  obtain ⟨A, -, hA⟩ := exists_le_expectation h0 h1 fun A =>
    ((#{s ∈ (univ : Finset V).powersetCard k | s.pairs ⊆ A} : ℝ) +
      #{s ∈ (univ : Finset V).powersetCard l | Disjoint A s.pairs})
  rw [expectation_bad] at hA
  set G := fromEdgeSet (A : Set (Sym2 V))
  set B := ({s ∈ (univ : Finset V).powersetCard k | s.pairs ⊆ A} ∪
    {s ∈ (univ : Finset V).powersetCard l | Disjoint A s.pairs})
  -- every bad set is nonempty; delete one vertex from each
  have hne : ∀ s ∈ B, s.Nonempty := by
    intro s hs
    rcases mem_union.mp hs with hs | hs <;> rw [mem_filter, mem_powersetCard] at hs <;>
      exact card_pos.mp (by omega)
  let H : Finset V := B.attach.image fun s => (hne s.1 s.2).choose
  refine ⟨G, univ \ H, ?_, ?_, ?_⟩
  · have hH : (#H : ℝ) ≤ #B := by exact_mod_cast card_image_le.trans (card_attach).le
    have hB : (#B : ℝ) ≤ (#{s ∈ (univ : Finset V).powersetCard k | s.pairs ⊆ A} : ℝ) +
        #{s ∈ (univ : Finset V).powersetCard l | Disjoint A s.pairs} := by
      exact_mod_cast card_union_le _ _
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Nat.cast_sub (card_le_univ _)]
    linarith
  · intro s hs hcl
    have hsB : s ∈ B := mem_union_left _ (mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,
      hcl.card_eq⟩, isClique_fromEdgeSet_iff.mp hcl.isClique⟩)
    have hmem := (hne s hsB).choose_spec
    exact (mem_sdiff.mp (hs hmem)).2 (mem_image.mpr ⟨⟨s, hsB⟩, mem_attach _ _, rfl⟩)
  · intro s hs hcl
    have hsB : s ∈ B := mem_union_right _ (mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,
      hcl.card_eq⟩, (isClique_compl_fromEdgeSet_iff.mp hcl.isClique).symm⟩)
    have hmem := (hne s hsB).choose_spec
    exact (mem_sdiff.mp (hs hmem)).2 (mem_image.mpr ⟨⟨s, hsB⟩, mem_attach _ _, rfl⟩)

omit [DecidableEq V] in
/-- **The biased first-moment bound.** If `0 ≤ p ≤ 1` and
`C(n, k) p ^ C(k, 2) + C(n, l) (1 - p) ^ C(l, 2) < 1`, some graph on `n` vertices has no `k`-clique
and no independent `l`-set. -/
theorem exists_cliqueFree_of_lt_one (h0 : 0 ≤ p) (h1 : p ≤ 1) {k l : ℕ}
    (h : (Fintype.card V).choose k * p ^ k.choose 2 +
      (Fintype.card V).choose l * (1 - p) ^ l.choose 2 < 1) :
    ∃ G : SimpleGraph V, G.CliqueFree k ∧ Gᶜ.CliqueFree l := by
  classical
  obtain ⟨A, -, hA⟩ := exists_le_expectation h0 h1 fun A =>
    ((#{s ∈ (univ : Finset V).powersetCard k | s.pairs ⊆ A} : ℝ) +
      #{s ∈ (univ : Finset V).powersetCard l | Disjoint A s.pairs})
  rw [expectation_bad] at hA
  have hzero : #{s ∈ (univ : Finset V).powersetCard k | s.pairs ⊆ A} = 0 ∧
      #{s ∈ (univ : Finset V).powersetCard l | Disjoint A s.pairs} = 0 := by
    have : ((#{s ∈ (univ : Finset V).powersetCard k | s.pairs ⊆ A} +
        #{s ∈ (univ : Finset V).powersetCard l | Disjoint A s.pairs} : ℕ) : ℝ) < 1 := by
      push_cast; linarith
    have : #{s ∈ (univ : Finset V).powersetCard k | s.pairs ⊆ A} +
        #{s ∈ (univ : Finset V).powersetCard l | Disjoint A s.pairs} = 0 := by
      exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
    omega
  refine ⟨fromEdgeSet (A : Set (Sym2 V)), fun s hs => ?_, fun s hs => ?_⟩
  · exact (card_eq_zero.mp hzero.1 ▸ mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,
      hs.card_eq⟩, isClique_fromEdgeSet_iff.mp hs.isClique⟩ : s ∈ (∅ : Finset (Finset V))) |>
      Finset.notMem_empty s
  · exact (card_eq_zero.mp hzero.2 ▸ mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,
      hs.card_eq⟩, (isClique_compl_fromEdgeSet_iff.mp hs.isClique).symm⟩ :
      s ∈ (∅ : Finset (Finset V))) |>
      Finset.notMem_empty s

/-- `2 ^ (k + 2) < (k !) ^ 2` for `k ≥ 3`. -/
private theorem two_pow_lt_factorial_sq {k : ℕ} (hk : 3 ≤ k) : 2 ^ (k + 2) < k.factorial ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.factorial_succ, mul_pow, pow_succ]
    have : 2 ≤ (k + 1) ^ 2 := by nlinarith
    nlinarith

omit [DecidableEq V] in
/-- **Erdős's lower bound** `R(k, k) > 2 ^ (k / 2)`. If `k ≥ 3` and `n ^ 2 ≤ 2 ^ k`, some graph on
`n` vertices has neither a `k`-clique nor an independent `k`-set.

This is the `p = 1 / 2` case of `exists_cliqueFree_of_lt_one`. The pool's `FiniteRamsey` project
proves the Ramsey-number form `2 ^ (k / 2) ≤ ramseyNumber ![k, k]` with natural-number division
in the exponent (`SimpleGraph.two_pow_half_le_ramseyNumber`), by counting colourings. For odd `k`
the hypothesis `n ^ 2 ≤ 2 ^ k` allows every `n` up to `√(2 ^ k)`, which exceeds `2 ^ (k / 2)`. -/
theorem exists_cliqueFree_of_sq_le_two_pow {k : ℕ} (hk : 3 ≤ k)
    (hn : Fintype.card V ^ 2 ≤ 2 ^ k) :
    ∃ G : SimpleGraph V, G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  classical
  set n := Fintype.card V
  -- `2 C(n, k) < 2 ^ C(k, 2)`, by squaring
  have hfac : k.factorial * n.choose k ≤ n ^ k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow n k
  have hsq : (k.factorial * n.choose k) ^ 2 ≤ 2 ^ (k * k) := by
    calc (k.factorial * n.choose k) ^ 2 ≤ (n ^ k) ^ 2 := Nat.pow_le_pow_left hfac 2
      _ = (n ^ 2) ^ k := by ring
      _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left hn k
      _ = 2 ^ (k * k) := by rw [← pow_mul]
  have hck : 2 * k.choose 2 = k * (k - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self k).two_dvd
  have hkey : 2 * n.choose k < 2 ^ k.choose 2 := by
    by_contra hge
    rw [not_lt] at hge
    have h1 : 2 ^ (2 * k.choose 2) ≤ 4 * n.choose k ^ 2 := by
      rw [pow_mul]
      calc (2 ^ 2) ^ k.choose 2 = (2 ^ k.choose 2) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ (2 * n.choose k) ^ 2 := Nat.pow_le_pow_left hge 2
        _ = 4 * n.choose k ^ 2 := by ring
    have h2 := two_pow_lt_factorial_sq hk
    have hpos : 0 < k.factorial ^ 2 := by positivity
    -- `2^(k(k-1)) (k!)^2 ≤ 4 (k! C)^2 ≤ 4 · 2^(k k)`, so `(k!)^2 ≤ 4 · 2^k`
    have h3 : 2 ^ (k * (k - 1)) * k.factorial ^ 2 ≤ 4 * 2 ^ (k * k) := by
      calc 2 ^ (k * (k - 1)) * k.factorial ^ 2 ≤ 4 * n.choose k ^ 2 * k.factorial ^ 2 := by
            rw [← hck]; exact Nat.mul_le_mul_right _ h1
        _ = 4 * (k.factorial * n.choose k) ^ 2 := by ring
        _ ≤ 4 * 2 ^ (k * k) := Nat.mul_le_mul_left 4 hsq
    have h4 : 2 ^ (k * k) = 2 ^ (k * (k - 1)) * 2 ^ k := by
      rw [← pow_add]; congr 1
      rcases k with _ | k
      · omega
      · rw [Nat.add_sub_cancel]; ring
    rw [h4] at h3
    have h5 : k.factorial ^ 2 ≤ 4 * 2 ^ k := by
      have hp : 0 < 2 ^ (k * (k - 1)) := by positivity
      nlinarith
    rw [pow_add] at h2
    omega
  refine exists_cliqueFree_of_lt_one (p := 1 / 2) (by norm_num) (by norm_num) ?_
  have hpow : ((1 : ℝ) / 2) ^ k.choose 2 = 1 / 2 ^ k.choose 2 := by rw [div_pow, one_pow]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hpow, ← two_mul, ← mul_assoc,
    mul_one_div, div_lt_one (by positivity)]
  exact_mod_cast hkey

end SimpleGraph
