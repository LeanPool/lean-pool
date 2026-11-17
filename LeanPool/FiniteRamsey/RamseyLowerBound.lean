/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.FiniteRamsey.RamseyNumber
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A counting lower bound for the diagonal Ramsey number

Every other file in this series proves an upper bound on `ramseyNumber`, by a construction or an
existence argument showing the Ramsey property holds at some host size. This file proves a lower
bound: a witness that the property fails below a threshold, by the probabilistic-method argument
of Erdős, recast as a `Finset`/`Nat.card` counting argument that needs no probability library.

Fix `k` and consider all `2 ^ (n.choose 2)` two-colourings of `K_n`'s edges. For a `k`-subset `s`,
the colourings monochromatic on `s` number exactly `2 * 2 ^ (n.choose 2 - k.choose 2)`: a common
colour for the `k.choose 2` edges inside `s`, and a free choice for the rest. A union bound over
the `n.choose k` many `k`-subsets bounds the colourings with some monochromatic `k`-subset by
`n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2))`. Whenever this is less than `2 ^ (n.choose 2)`,
some colouring avoids every monochromatic `k`-subset, so `RamseyProperty n k k` fails and
`ramseyNumber ![k, k] > n`.

## Main declarations

* `SimpleGraph.IsMonochromaticOn`: a `Finset` of vertices on which a two-colouring is constant,
  equivalent to `RedClique`/`BlueClique` at that size
  (`isMonochromaticOn_iff_redClique_or_blueClique`).
* `SimpleGraph.not_ramseyProperty_of_choose_lt`: the counting lower bound itself, a colouring of
  `K_n` with no monochromatic `k`-set whenever `n.choose k * 2 < 2 ^ (k.choose 2)`.
* `SimpleGraph.lt_ramseyNumber_of_choose_lt`: the same bound, phrased as `n < ramseyNumber ![k, k]`.

## Implementation notes

Cardinalities throughout are stated with `Nat.card` rather than `Fintype.card`. `Nat.card` takes
no `Fintype`/`Decidable` instance argument, so lemmas about it compose regardless of which
decidability witness a caller's own instance search picks for the same proposition, while
`Fintype.card` bakes a specific instance into every statement, and two independently-elaborated
instances for the same predicate need not be definitionally equal, which makes downstream
`rw`/`simp` calls fail with "motive is not type correct" for reasons unrelated to the underlying
mathematics. The closed-form consequence of this bound, `2 ^ (k / 2) ≤ ramseyNumber ![k, k]` at
`n := 2 ^ (k / 2)`, needs additional `Nat.choose` estimation beyond what is proved here and is
given in `RamseyLowerBoundAsymptotic.lean`.

## References

* P. Erdős, *Some remarks on the theory of graphs*, Bull. Amer. Math. Soc. 53 (1947), 292-294.

## Tags

ramsey theory, probabilistic method, combinatorics
-/

@[expose] public section

namespace SimpleGraph

open Finset

variable {n : ℕ}

/-! ### Counting colourings agreeing on a set of edges -/

/-- Counting `edgeSet` elements landing in a Finset `t` of `Sym2` equals counting `t`'s
intersection with `edgeFinset`. -/
lemma natCard_subtype_edgeSet_mem (t : Finset (Sym2 (Fin n))) :
    Nat.card {e : (⊤ : SimpleGraph (Fin n)).edgeSet // (↑e : Sym2 (Fin n)) ∈ t} =
      ((⊤ : SimpleGraph (Fin n)).edgeFinset ∩ t).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
    (Equiv.subtypeEquivRight fun x => by simp))

/-- The edges of `⊤ : SimpleGraph (Fin n)` with both endpoints in `s` number `s.card.choose 2`. -/
lemma card_edgeFinset_inter_sym2 (s : Finset (Fin n)) :
    ((⊤ : SimpleGraph (Fin n)).edgeFinset ∩ s.sym2).card = s.card.choose 2 := by
  classical
  rw [← Sym2.card_image_offDiag]
  congr 1
  ext ⟨a, b⟩
  simp only [mem_inter, mem_edgeFinset, edgeSet_top, Set.mem_compl_iff, Sym2.mem_diagSet,
    Sym2.mk_isDiag_iff, mk_mem_sym2_iff, mem_image, mem_offDiag, Prod.exists,
    Function.uncurry_apply_pair]
  constructor
  · rintro ⟨h, ha, hb⟩; exact ⟨a, b, ⟨ha, hb, h⟩, rfl⟩
  · rintro ⟨x, y, ⟨hx, hy, h⟩, hxy⟩
    rcases Sym2.eq_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [⟨h, hx, hy⟩, ⟨Ne.symm h, hy, hx⟩]



/-- At most two `Bool`-valued functions on any type are constant. -/
lemma natCard_subtype_isConst_le (α : Type*) :
    Nat.card {f : α → Bool // ∃ b, f = fun _ => b} ≤ 2 := by
  simpa using Nat.card_le_card_of_surjective
    (fun b : Bool => (⟨fun _ => b, b, rfl⟩ : {f : α → Bool // ∃ b, f = fun _ => b}))
    (fun ⟨_, b, hb⟩ => ⟨b, Subtype.ext hb.symm⟩)

/-! ### Monochromatic sets -/

/-- `s` is monochromatic under `C`: every pair of distinct vertices of `s` gets the same colour.
Equivalent to `RedClique C s.card s ∨ BlueClique C s.card s`
(`isMonochromaticOn_iff_redClique_or_blueClique`), but easier to count directly since it names the
witness colour instead of branching into two cases. -/
def IsMonochromaticOn (C : TwoColoring (Fin n)) (s : Finset (Fin n)) : Prop :=
  ∃ b : Bool, ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s) (h : x ≠ y), C.get x y h = b

/-- The colourings monochromatic on a fixed `s` number at most `2 * 2 ^ (n.choose 2 -
s.card.choose 2)`: a common colour for the `s.card.choose 2` edges inside `s` (at most `2`
choices), and any colouring at all of the remaining edges. -/
lemma natCard_subtype_isMonochromaticOn_le (s : Finset (Fin n)) :
    Nat.card {C : TwoColoring (Fin n) // IsMonochromaticOn C s} ≤
      2 * 2 ^ (n.choose 2 - s.card.choose 2) := by
  classical
  let p : (⊤ : SimpleGraph (Fin n)).edgeSet → Prop := fun e => (↑e : Sym2 (Fin n)) ∈ s.sym2
  -- on an edge inside `s`, a monochromatic colouring takes its witness colour
  have hval (C : TwoColoring (Fin n)) (hC : IsMonochromaticOn C s)
      (x : (⊤ : SimpleGraph (Fin n)).edgeSet) (hx : p x) : C x = hC.choose := by
    obtain ⟨y, hy⟩ := x
    induction y using Sym2.inductionOn with
    | _ a c =>
      exact hC.choose_spec (mk_mem_sym2_iff.mp hx).1 (mk_mem_sym2_iff.mp hx).2
        ((mem_edgeSet _).mp hy).ne
  have hout : Nat.card {x // ¬p x} = n.choose 2 - s.card.choose 2 := by
    have := Nat.card_congr (Equiv.sumCompl p)
    rw [Nat.card_sum, natCard_subtype_edgeSet_mem, card_edgeFinset_inter_sym2,
      Nat.card_eq_fintype_card (α := (⊤ : SimpleGraph (Fin n)).edgeSet), card_edgeSet,
      card_edgeFinset_top_eq_card_choose_two,
      Fintype.card_fin] at this
    omega
  calc _ ≤ Nat.card (Bool × ({x // ¬p x} → Bool)) :=
        Nat.card_le_card_of_injective (fun C => (C.2.choose, fun x => C.1 x))
          fun ⟨C1, h1⟩ ⟨C2, h2⟩ h => by
            simp only [Prod.mk.injEq, funext_iff] at h
            exact Subtype.ext <| funext fun x => if hx : p x then
              (hval _ h1 x hx).trans (h.1.trans (hval _ h2 x hx).symm) else h.2 ⟨x, hx⟩
    _ = 2 * 2 ^ (n.choose 2 - s.card.choose 2) := by
        rw [Nat.card_prod, Nat.card_fun, hout]; simp



/-- The forward direction of `isMonochromaticOn_iff_redClique_or_blueClique`. -/
lemma IsMonochromaticOn.redClique_or_blueClique {C : TwoColoring (Fin n)} {s : Finset (Fin n)}
    (h : IsMonochromaticOn C s) : RedClique C s.card s ∨ BlueClique C s.card s := by
  obtain ⟨b, hb⟩ := h
  have hclique : (C.labelGraph b).IsNClique s.card s :=
    ⟨fun x hx y hy hxy => (TopEdgeLabeling.labelGraph_adj x y).mpr ⟨hxy, hb hx hy hxy⟩, rfl⟩
  cases b
  exacts [.inr hclique, .inl hclique]

/-- The backward direction of `isMonochromaticOn_iff_redClique_or_blueClique`. -/
lemma redClique_or_blueClique.isMonochromaticOn {C : TwoColoring (Fin n)} {s : Finset (Fin n)}
    (h : RedClique C s.card s ∨ BlueClique C s.card s) : IsMonochromaticOn C s := by
  rcases h with ⟨hclique, -⟩ | ⟨hclique, -⟩
  · exact ⟨true, fun x hx y hy hxy => ((TopEdgeLabeling.labelGraph_adj x y).mp
      (hclique hx hy hxy)).2⟩
  · exact ⟨false, fun x hx y hy hxy => ((TopEdgeLabeling.labelGraph_adj x y).mp
      (hclique hx hy hxy)).2⟩

theorem isMonochromaticOn_iff_redClique_or_blueClique {C : TwoColoring (Fin n)}
    {s : Finset (Fin n)} : IsMonochromaticOn C s ↔ RedClique C s.card s ∨ BlueClique C s.card s :=
  ⟨IsMonochromaticOn.redClique_or_blueClique, redClique_or_blueClique.isMonochromaticOn⟩

/-! ### The union bound over all `k`-subsets -/

/-- The union bound: the colourings of `K_n` with some monochromatic `k`-subset number at most
`n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2))`, summing
`natCard_subtype_isMonochromaticOn_le`'s per-subset bound over all `n.choose k` many `k`-subsets. -/
lemma natCard_subtype_existsMonochromaticOn_le (k : ℕ) :
    Nat.card
      {C : TwoColoring (Fin n) // ∃ s : Finset (Fin n), s.card = k ∧ IsMonochromaticOn C s} ≤
      n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
  classical
  let β : {s : Finset (Fin n) // s.card = k} → Type :=
    fun s => {C : TwoColoring (Fin n) // IsMonochromaticOn C s.1}
  calc _ ≤ Nat.card (Sigma β) :=
        Nat.card_le_card_of_injective (fun C => (⟨⟨C.2.choose, C.2.choose_spec.1⟩,
            C.1, C.2.choose_spec.2⟩ : Sigma β))
          fun _ _ heq => Subtype.ext (by simpa using congrArg (fun x : Sigma β => x.2.1) heq)
    _ = ∑ a, Nat.card (β a) := Nat.card_sigma
    _ ≤ ∑ _a : {s : Finset (Fin n) // s.card = k}, 2 * 2 ^ (n.choose 2 - k.choose 2) :=
        sum_le_sum fun a _ => a.2 ▸ natCard_subtype_isMonochromaticOn_le a.1
    _ = _ := by simp [Fintype.card_finset_len]

/-! ### The lower bound -/

/-- The counting lower bound for the diagonal Ramsey number. If the union bound over all
`k`-subsets is strictly less than the total number of two-colourings, a colouring of `K_n` with no
monochromatic `k`-clique of either colour exists, so `K_n` does not force one. -/
theorem not_ramseyProperty_of_choose_lt {n k : ℕ} (hk : k ≤ n)
    (h : n.choose k * 2 < 2 ^ (k.choose 2)) : ¬ RamseyProperty n k k := by
  intro hR
  have hall (C : TwoColoring (Fin n)) :
      ∃ s : Finset (Fin n), s.card = k ∧ IsMonochromaticOn C s := by
    rcases hR C with ⟨t, ht⟩ | ⟨t, ht⟩
    exacts [⟨t, ht.card_eq, redClique_or_blueClique.isMonochromaticOn (.inl (ht.card_eq ▸ ht))⟩,
      ⟨t, ht.card_eq, redClique_or_blueClique.isMonochromaticOn (.inr (ht.card_eq ▸ ht))⟩]
  have hbad := natCard_subtype_existsMonochromaticOn_le (n := n) k
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_eq_fintype_card,
    card_topEdgeLabeling, Fintype.card_bool, Fintype.card_fin, ← mul_assoc] at hbad
  have hmul := Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos (n.choose 2 - k.choose 2))
  rw [← pow_add, Nat.add_sub_cancel' (Nat.choose_le_choose 2 hk)] at hmul
  omega

/-- The counting lower bound, phrased for `ramseyNumber`. -/
theorem lt_ramseyNumber_of_choose_lt {n k : ℕ} (hk : k ≤ n)
    (h : n.choose k * 2 < 2 ^ (k.choose 2)) : n < ramseyNumber ![k, k] :=
  not_le.mp (mt ramseyProperty_iff_ramseyNumber_le.mpr (not_ramseyProperty_of_choose_lt hk h))

/-- A worked instance showing this bound is genuine but weak at small `k`. At `k = 4`, `n = 6`:
`6.choose 4 * 2 = 30 < 2 ^ (4.choose 2) = 64`, so `lt_ramseyNumber_of_choose_lt` certifies
`ramseyNumber ![4, 4] > 6`, i.e. `ramseyNumber ![4, 4] ≥ 7`. This is far short of the true value
`ramseyNumber ![4, 4] = 18` (proved by exhaustive search, not by this counting argument), since the
union bound over all `k`-subsets is wasteful for small `n`; its real content is asymptotic, giving
`2 ^ (k / 2) ≤ ramseyNumber ![k, k]` for every `k` (`RamseyLowerBoundAsymptotic.lean`), which no
exact search could hope to match at large `k`. -/
example : (6 : ℕ).choose 4 * 2 < 2 ^ (4 : ℕ).choose 2 := by decide

end SimpleGraph
