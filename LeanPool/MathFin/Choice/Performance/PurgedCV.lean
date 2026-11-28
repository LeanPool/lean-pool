/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Performance.LabelUniqueness
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Purged train/test interval disjointness

López de Prado (*Advances in Financial Machine Learning*, ch. 7) purges a
training interval `[t0 i, t1 i]` from a cross-validation fold whenever it
overlaps a test interval `[t0' j, t1' j]`: it starts inside the test interval,
ends inside it, or envelops it. This file states that three-way overlap
predicate literally as given (for times in any linear order) and proves the
combinatorial payoff: any training interval surviving purging against every
test interval is genuinely disjoint from each of them, and in fact ends
strictly before it starts or starts strictly after it ends.

**Why purging works.** When each label is a measurable function of the increments
of a pre-Brownian motion over its own nonempty span (`IsSpanLabel`), a surviving training
label and any test label sit on separated spans, so the weak Markov property of
Brownian motion (`IsPreBrownianReal.indepFun_shift`: the increments after a time are
independent of the path before it) makes them independent
(`indepFun_of_purged`): no single test label carries information about a surviving
training label. The statement is pairwise; joint independence of the whole test
fold from the whole surviving training set is not proved. On the sample-weight side,
a surviving label's uniqueness (`Choice/Performance/LabelUniqueness.lean`) is the same
whether computed on the training sample alone or on the pooled sample
(`uniqueness_pooled_eq_of_purged`).

## Main definitions

* `overlapsTest`: the purge trigger, training interval `i` starts inside, ends inside, or
  envelops test interval `j`.
* `IsSpanLabel`: a label determined by the increments of `X` over a span `[a, b]`.

## Main results

* `overlapsTest_of_mem_of_mem`: if some point lies in both a training and a test
  interval, the overlap predicate holds between them (the interval-arithmetic
  heart of the result).
* `purged_disjoint`: a training interval `i` purging leaves untouched (no
  test interval triggers the overlap predicate against it) is disjoint from
  every test interval.
* `lt_or_lt_of_not_overlapsTest`: for nonempty spans, surviving purging means the
  two spans are strictly separated.
* `IsSpanLabel.indepFun_of_le`, `indepFun_of_purged`: labels determined by
  the increments of a pre-Brownian motion over separated spans are independent; after
  purging, every test label is independent of every surviving training label.
* `uniqueness_pooled_eq_of_purged`: purging keeps test labels out of a surviving training
  label's uniqueness.

## References

* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991],
  §2.1
* [López de Prado, *Advances in Financial Machine Learning*][LopezDePrado2018], ch. 7, §7.4

## Tags

purged cross-validation, overlapping labels, information leakage, weak Markov property,
López de Prado, time series validation, MSC 60J65, MSC 62M10, JEL C58
-/

@[expose] public section

namespace MathFin

variable {ι κ T : Type*} [LinearOrder T]

/-- The purge-trigger predicate: training interval `i` starts inside, ends
inside, or envelops test interval `j`. -/
def overlapsTest (lo hi : ι → T) (lo' hi' : κ → T) (i : ι) (j : κ) : Prop :=
  (lo' j ≤ lo i ∧ lo i ≤ hi' j) ∨ (lo' j ≤ hi i ∧ hi i ≤ hi' j) ∨ (lo i ≤ lo' j ∧ hi' j ≤ hi i)

/-- If a point lies in both intervals, the overlap predicate holds between
them: comparing `lo' j` with `lo i`, and then `hi i` with `hi' j`, picks which
of the three overlap cases applies. -/
theorem overlapsTest_of_mem_of_mem (lo hi : ι → T) (lo' hi' : κ → T) {i : ι} {j : κ} {t : T}
    (ht : t ∈ Set.Icc (lo i) (hi i)) (ht' : t ∈ Set.Icc (lo' j) (hi' j)) :
    overlapsTest lo hi lo' hi' i j := by
  obtain ⟨hlo, hhi⟩ := ht
  obtain ⟨hlo', hhi'⟩ := ht'
  rcases le_total (lo' j) (lo i) with h1 | h1
  · exact Or.inl ⟨h1, hlo.trans hhi'⟩
  · rcases le_total (hi i) (hi' j) with h2 | h2
    · exact Or.inr (Or.inl ⟨hlo'.trans hhi, h2⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)

/-- The disjointness invariant: a training interval `i` that no test interval
`j` triggers the purge predicate on is disjoint from every test interval. -/
theorem purged_disjoint (lo hi : ι → T) (lo' hi' : κ → T) {i : ι}
    (hret : ∀ j, ¬ overlapsTest lo hi lo' hi' i j) (j : κ) :
    Disjoint (Set.Icc (lo i) (hi i)) (Set.Icc (lo' j) (hi' j)) := by
  rw [Set.disjoint_left]
  intro t ht ht'
  exact hret j (overlapsTest_of_mem_of_mem lo hi lo' hi' ht ht')

/-- **Surviving purging separates the spans strictly**: if training span `[lo i, hi i]` and
test span `[lo' j, hi' j]` are nonempty and do not trigger the overlap predicate, one ends
strictly before the other starts. (Otherwise `max (lo i) (lo' j)` lies in both.) -/
theorem lt_or_lt_of_not_overlapsTest {lo hi : ι → T} {lo' hi' : κ → T} {i : ι} {j : κ}
    (hspan : lo i ≤ hi i) (hspan' : lo' j ≤ hi' j) (h : ¬ overlapsTest lo hi lo' hi' i j) :
    hi i < lo' j ∨ hi' j < lo i := by
  by_contra! hc
  exact h (overlapsTest_of_mem_of_mem lo hi lo' hi' (t := max (lo i) (lo' j))
    ⟨le_max_left _ _, max_le hspan hc.1⟩ ⟨le_max_right _ _, max_le hc.2 hspan'⟩)

/-- **Purging keeps test labels out of a surviving training label's uniqueness.** If training
label `i` survives purging against every test label, then at every time `t` of its span no test
label is active, so its uniqueness computed on the pooled sample (training ⊕ test) equals its
uniqueness computed on the training sample alone. -/
theorem uniqueness_pooled_eq_of_purged [Fintype ι] [Fintype κ] (lo hi : ι → ℝ)
    (lo' hi' : κ → ℝ) {i : ι} (hret : ∀ j, ¬ overlapsTest lo hi lo' hi' i j) {t : ℝ}
    (ht : t ∈ Set.Icc (lo i) (hi i)) :
    uniqueness (Sum.elim lo lo') (Sum.elim hi hi') t (Sum.inl i) = uniqueness lo hi t i := by
  have h0 : concurrency lo' hi' t = 0 :=
    Finset.sum_eq_zero fun j _ ↦
      ite_eq_right fun ht' ↦ hret j (overlapsTest_of_mem_of_mem lo hi lo' hi' ht ht')
  unfold uniqueness
  rw [concurrency_sumElim, h0, add_zero]
  rfl

section Brownian

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω E E' : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [MeasurableSpace E] [MeasurableSpace E']

/-- A label **determined by the increments of `X` over its span `[a, b]`**: a measurable
function of the increment family `(X u - X s)_{s, u ∈ [a, b]}`. For instance, with `X` the
log-price, López de Prado's fixed-horizon label (the sign of the return `X b - X a` over the
span) is of this form. -/
def IsSpanLabel (X : ℝ≥0 → Ω → ℝ) (a b : ℝ≥0) (L : Ω → E) : Prop :=
  ∃ F : (Set.Icc a b × Set.Icc a b → ℝ) → E, Measurable F ∧
    L = fun ω ↦ F fun p ↦ X p.2 ω - X p.1 ω

/-- **Labels on ordered spans of a pre-Brownian motion are independent.** If `L` is determined
by the increments of `B` over `[a, b]`, `L'` by those over `[c, d]`, and `b ≤ c`, then `L` and
`L'` are independent: `L` is a measurable function of the path up to time `c`, `L'` of the
increments after `c`, and these are independent by the weak Markov property
`IsPreBrownianReal.indepFun_shift`. -/
theorem IsSpanLabel.indepFun_of_le {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {a b c d : ℝ≥0} (hbc : b ≤ c) {L : Ω → E} {L' : Ω → E'}
    (hL : IsSpanLabel B a b L) (hL' : IsSpanLabel B c d L') :
    IndepFun L L' P := by
  obtain ⟨F, hF, rfl⟩ := hL
  obtain ⟨G, hG, rfl⟩ := hL'
  have hφ : Measurable fun x : Set.Iic c → ℝ ↦
      F fun p : Set.Icc a b × Set.Icc a b ↦
        x ⟨p.2, p.2.2.2.trans hbc⟩ - x ⟨p.1, p.1.2.2.trans hbc⟩ :=
    hF.comp (.of_eval fun _ ↦ (measurable_pi_apply _).sub (measurable_pi_apply _))
  have hψ : Measurable fun y : ℝ≥0 → ℝ ↦
      G fun p : Set.Icc c d × Set.Icc c d ↦ y (p.2 - c) - y (p.1 - c) :=
    hG.comp (.of_eval fun _ ↦ (measurable_pi_apply _).sub (measurable_pi_apply _))
  refine ((hB.indepFun_shift c).symm.comp hφ hψ).congr (ae_of_all _ fun ω ↦ rfl)
    (ae_of_all _ fun ω ↦ ?_)
  simp only [Function.comp_apply]
  congr 1
  funext p
  rw [add_tsub_cancel_of_le p.2.2.1, add_tsub_cancel_of_le p.1.2.1]
  abel

/-- **After purging, test labels are independent of surviving training labels.** Let every
label be determined by the increments of a pre-Brownian motion `B` over its own nonempty span
(`IsSpanLabel`). If training label `i` survives purging — no test span triggers the overlap
predicate against it — then it is independent of every test label `j`. The spans are strictly
separated (`lt_or_lt_of_not_overlapsTest`), and `IsSpanLabel.indepFun_of_le` applies in
whichever order they come. -/
theorem indepFun_of_purged {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {lo hi : ι → ℝ≥0} {lo' hi' : κ → ℝ≥0} (hspan : ∀ i, lo i ≤ hi i)
    (hspan' : ∀ j, lo' j ≤ hi' j) {L : ι → Ω → E} {L' : κ → Ω → E'}
    (hL : ∀ i, IsSpanLabel B (lo i) (hi i) (L i))
    (hL' : ∀ j, IsSpanLabel B (lo' j) (hi' j) (L' j)) {i : ι}
    (hret : ∀ j, ¬ overlapsTest lo hi lo' hi' i j) (j : κ) :
    IndepFun (L i) (L' j) P := by
  rcases lt_or_lt_of_not_overlapsTest (hspan i) (hspan' j) (hret j) with h | h
  · exact (hL i).indepFun_of_le hB h.le (hL' j)
  · exact ((hL' j).indepFun_of_le hB h.le (hL i)).symm

end Brownian

end MathFin
