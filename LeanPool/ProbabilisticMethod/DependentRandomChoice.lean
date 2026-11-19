/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic.Rify

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Dependent random choice

**Dependent random choice** finds, in a dense graph, a large vertex set `W` in which every
`r`-subset has many common neighbours. Pick `t` vertices at random (with repetition) and let `W₀`
be their common neighbourhood; vertices of high degree are likely to land in `W₀`, while an
`r`-set with few common neighbours is unlikely to lie in it. Deleting one vertex from each such
`r`-set leaves `W`.

Here the random choice is replaced by averaging over all `n ^ t` tuples, so every statement is
elementary counting.

## Main statements

* `Finset.sum_card_common_eq_sum_choose`, `Finset.exists_card_common_ge`: the common-neighbour
  moment identity for any relation, and the selection of an `h`-set with many common
  neighbours.
* `SimpleGraph.sum_card_commonNeighbors_tuple`: summing the size of the common neighbourhood over
  all `t`-tuples gives `∑ v, deg v ^ t`.
* `SimpleGraph.exists_dependentRandomChoice`: **dependent random choice**. If
  `a n ^ t + C(n, r) m ^ t ≤ ∑ v, deg v ^ t` and `r ≥ 1`, there is a set `W` of at least `a`
  vertices in which every `r`-subset has at least `m` common neighbours.
* `SimpleGraph.exists_dependentRandomChoice_of_card_edgeFinset`: the same with the edge count, in
  Fox and Sudakov's form `n (d / n) ^ t - C(n, r) (m / n) ^ t ≥ a`, `d = 2e / n`.

## References

* [J. Fox, B. Sudakov, *Dependent random choice*][FoxSudakov2011]
-/

@[expose] public section

open Finset

namespace Finset

variable {α β : Type*}

/-- **Common-neighbour moments.** For a relation `r` between `α` and `β`, summing over the
`h`-subsets `U` of `L` the number of `y ∈ R` related to all of `U` gives
`∑ y ∈ R, C(deg y, h)`, where `deg y` counts the `x ∈ L` related to `y`. -/
theorem sum_card_common_eq_sum_choose (r : α → β → Prop) [∀ x y, Decidable (r x y)]
    (L : Finset α) (R : Finset β) (h : ℕ) :
    ∑ U ∈ L.powersetCard h, #{y ∈ R | ∀ x ∈ U, r x y} =
      ∑ y ∈ R, (#{x ∈ L | r x y}).choose h := by
  calc ∑ U ∈ L.powersetCard h, #{y ∈ R | ∀ x ∈ U, r x y}
      = ∑ U ∈ L.powersetCard h, ∑ y ∈ R, if ∀ x ∈ U, r x y then 1 else 0 :=
        sum_congr rfl fun U _ => card_filter _ _
    _ = ∑ y ∈ R, ∑ U ∈ L.powersetCard h, if ∀ x ∈ U, r x y then 1 else 0 := sum_comm
    _ = ∑ y ∈ R, #{U ∈ L.powersetCard h | ∀ x ∈ U, r x y} :=
        sum_congr rfl fun y _ => (card_filter _ _).symm
    _ = _ := sum_congr rfl fun y _ => ?_
  rw [← card_powersetCard]
  congr 1
  ext U
  simp only [mem_filter, mem_powersetCard, subset_iff]
  constructor
  · rintro ⟨⟨hUL, hU⟩, hr⟩
    exact ⟨fun x hx => ⟨hUL hx, hr x hx⟩, hU⟩
  · rintro ⟨hU, hcard⟩
    exact ⟨⟨fun x hx => (hU hx).1, hcard⟩, fun x hx => (hU hx).2⟩

/-- **Moment selection.** If `t C(|L|, h) ≤ ∑ y ∈ R, C(deg y, h)` and `h ≤ |L|`, some `h`-subset of
`L` has at least `t` common neighbours in `R`. -/
theorem exists_card_common_ge (r : α → β → Prop) [∀ x y, Decidable (r x y)] {L : Finset α}
    {R : Finset β} {h t : ℕ} (hh : h ≤ #L)
    (hmoment : t * (#L).choose h ≤ ∑ y ∈ R, (#{x ∈ L | r x y}).choose h) :
    ∃ U ⊆ L, #U = h ∧ t ≤ #{y ∈ R | ∀ x ∈ U, r x y} := by
  rw [← sum_card_common_eq_sum_choose] at hmoment
  by_contra! hlt
  have hne : (L.powersetCard h).Nonempty := powersetCard_nonempty.mpr hh
  have := sum_lt_sum_of_nonempty hne fun U hU =>
    hlt U (mem_powersetCard.mp hU).1 (mem_powersetCard.mp hU).2
  rw [sum_const, card_powersetCard, smul_eq_mul, mul_comm] at this
  omega

end Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- Summing the size of the common neighbourhood of a `t`-tuple over all tuples gives
`∑ v, deg v ^ t`. -/
theorem sum_card_commonNeighbors_tuple (t : ℕ) :
    ∑ τ : Fin t → V, #{v | ∀ i, G.Adj (τ i) v} = ∑ v, G.degree v ^ t := by
  simp_rw [card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [← card_filter, ← card_neighborFinset_eq_degree, ← Fintype.card_piFinset_const]
  congr 1
  ext τ
  simp [Fintype.mem_piFinset, G.adj_comm]

/-- Summing the number of `r`-sets with fewer than `m` common neighbours that lie in the common
neighbourhood of a `t`-tuple gives at most `C(n, r) m ^ t`. -/
theorem sum_card_bad_le (t r m : ℕ) :
    ∑ τ : Fin t → V, #{S ∈ (univ : Finset V).powersetCard r |
        #{u | ∀ v ∈ S, G.Adj v u} < m ∧ ∀ i, ∀ v ∈ S, G.Adj (τ i) v} ≤
      (Fintype.card V).choose r * m ^ t := by
  calc ∑ τ : Fin t → V, #{S ∈ (univ : Finset V).powersetCard r |
        #{u | ∀ v ∈ S, G.Adj v u} < m ∧ ∀ i, ∀ v ∈ S, G.Adj (τ i) v}
      = ∑ S ∈ (univ : Finset V).powersetCard r, #{τ : Fin t → V |
          #{u | ∀ v ∈ S, G.Adj v u} < m ∧ ∀ i, ∀ v ∈ S, G.Adj (τ i) v} := by
        simp only [card_eq_sum_ones, sum_filter]
        exact sum_comm
    _ ≤ ∑ _S ∈ (univ : Finset V).powersetCard r, m ^ t := by
        refine sum_le_sum fun S _ => ?_
        by_cases hS : #{u | ∀ v ∈ S, G.Adj v u} < m
        · simp only [hS, true_and]
          calc #{τ : Fin t → V | ∀ i, ∀ v ∈ S, G.Adj (τ i) v}
              = #{u | ∀ v ∈ S, G.Adj v u} ^ t := by
                rw [← Fintype.card_piFinset_const]
                congr 1
                ext τ
                simp [Fintype.mem_piFinset, G.adj_comm]
            _ ≤ m ^ t := Nat.pow_le_pow_left hS.le t
        · simp [hS]
    _ = _ := by rw [sum_const, card_powersetCard, card_univ, smul_eq_mul]

/-- **Dependent random choice.** If `r ≥ 1` and `a n ^ t + C(n, r) m ^ t ≤ ∑ v, deg v ^ t`, there
is a set `W` of at least `a` vertices in which every `r`-subset has at least `m` common
neighbours. -/
theorem exists_dependentRandomChoice [Nonempty V] {t r m a : ℕ} (hr : 1 ≤ r)
    (h : a * Fintype.card V ^ t + (Fintype.card V).choose r * m ^ t ≤ ∑ v, G.degree v ^ t) :
    ∃ W : Finset V, a ≤ #W ∧ ∀ S ⊆ W, #S = r → m ≤ #{u | ∀ v ∈ S, G.Adj v u} := by
  set bad : (Fin t → V) → Finset (Finset V) := fun τ =>
    {S ∈ (univ : Finset V).powersetCard r |
      #{u | ∀ v ∈ S, G.Adj v u} < m ∧ ∀ i, ∀ v ∈ S, G.Adj (τ i) v}
  set W₀ : (Fin t → V) → Finset V := fun τ => {v | ∀ i, G.Adj (τ i) v}
  -- some tuple has `a + #bad ≤ |W₀|`
  have hsum : ∑ τ : Fin t → V, (a + #(bad τ)) ≤ ∑ τ : Fin t → V, #(W₀ τ) := by
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul,
      sum_card_commonNeighbors_tuple]
    have hb : ∑ τ : Fin t → V, #(bad τ) ≤ (Fintype.card V).choose r * m ^ t :=
      sum_card_bad_le G t r m
    rw [mul_comm]
    omega
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin t → V, a + #(bad τ) ≤ #(W₀ τ) := by
    by_contra! hlt
    exact (sum_lt_sum_of_nonempty univ_nonempty fun τ _ => hlt τ).not_ge hsum
  -- delete one vertex from each bad set
  have hne : ∀ S ∈ bad τ, S.Nonempty := fun S hS => by
    rw [mem_filter, mem_powersetCard] at hS
    exact card_pos.mp (by omega)
  set H : Finset V := (bad τ).attach.image fun S => (hne S.1 S.2).choose
  refine ⟨W₀ τ \ H, ?_, fun S hS hSr => ?_⟩
  · have hH : #H ≤ #(bad τ) := card_image_le.trans card_attach.le
    have := le_card_sdiff H (W₀ τ)
    omega
  · by_contra! hlt
    have hSW : ∀ i, ∀ v ∈ S, G.Adj (τ i) v := fun i v hv =>
      (mem_filter.mp (mem_sdiff.mp (hS hv)).1).2 i
    have hSbad : S ∈ bad τ := mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hSr⟩, hlt, hSW⟩
    have hmem := (hne S hSbad).choose_spec
    exact (mem_sdiff.mp (hS hmem)).2 (mem_image.mpr ⟨⟨S, hSbad⟩, mem_attach _ _, rfl⟩)

/-- **Dependent random choice, edge-count form** (Fox–Sudakov). Let `d = 2e / n` be the average
degree. If `a + C(n, r) (m / n) ^ t ≤ n (d / n) ^ t` and `r ≥ 1`, there is a set `W` of at least
`a` vertices in which every `r`-subset has at least `m` common neighbours. -/
theorem exists_dependentRandomChoice_of_card_edgeFinset [Nonempty V] {t r m a : ℕ} (hr : 1 ≤ r)
    (h : (a : ℝ) + (Fintype.card V).choose r * ((m : ℝ) / Fintype.card V) ^ t ≤
      Fintype.card V * ((2 * #G.edgeFinset : ℝ) / Fintype.card V / Fintype.card V) ^ t) :
    ∃ W : Finset V, a ≤ #W ∧ ∀ S ⊆ W, #S = r → m ≤ #{u | ∀ v ∈ S, G.Adj v u} := by
  refine G.exists_dependentRandomChoice (t := t) hr ?_
  set n := Fintype.card V
  have hn : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  -- power mean: `n (∑ deg / n) ^ t ≤ ∑ deg ^ t`
  have hpm : (n : ℝ) * ((2 * #G.edgeFinset : ℝ) / n) ^ t ≤ ∑ v, (G.degree v : ℝ) ^ t := by
    have hjensen := pow_sum_div_card_le_sum_pow (s := (univ : Finset V))
      (f := fun v => (G.degree v : ℝ)) (fun _ _ => by positivity) (t - 1)
    have hdeg : ∑ v, (G.degree v : ℝ) = 2 * #G.edgeFinset := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [n]
    rw [card_univ, hdeg, Nat.sub_add_cancel ht] at hjensen
    calc (n : ℝ) * ((2 * #G.edgeFinset : ℝ) / n) ^ t
        = (2 * #G.edgeFinset : ℝ) ^ t / (n : ℝ) ^ (t - 1) := by
          rw [div_pow, ← mul_div_assoc, mul_comm, mul_div_assoc,
            show (n : ℝ) ^ t = n ^ (t - 1) * n by rw [← pow_succ, Nat.sub_add_cancel ht]]
          field_simp
      _ ≤ _ := hjensen
  have hnt : (0 : ℝ) < (n : ℝ) ^ t := pow_pos hn t
  have key : ((a * n ^ t + n.choose r * m ^ t : ℕ) : ℝ) ≤ ∑ v, (G.degree v : ℝ) ^ t := by
    push_cast
    have : ((a : ℝ) + n.choose r * ((m : ℝ) / n) ^ t) * (n : ℝ) ^ t ≤
        (n * ((2 * #G.edgeFinset : ℝ) / n / n) ^ t) * (n : ℝ) ^ t :=
      mul_le_mul_of_nonneg_right h hnt.le
    have e1 : ((a : ℝ) + n.choose r * ((m : ℝ) / n) ^ t) * (n : ℝ) ^ t =
        a * n ^ t + n.choose r * m ^ t := by
      rw [div_pow]; field_simp
    have e2 : (n * ((2 * #G.edgeFinset : ℝ) / n / n) ^ t) * (n : ℝ) ^ t =
        n * ((2 * #G.edgeFinset : ℝ) / n) ^ t := by
      rw [mul_assoc, ← mul_pow, div_div, div_mul_eq_mul_div, mul_div_mul_right _ _ hn.ne']
    rw [e1, e2] at this
    exact this.trans hpm
  exact_mod_cast key

end SimpleGraph
