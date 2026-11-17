/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Order.Lattice.Nat

/-!
# Orbits of a self-map on a finite type

The quantitative facts every fixed-point iteration in this library rests on,
stated for a bare self-map `f : α → α` with no logic in sight:

* once an orbit plateaus it is constant
  (`DescriptiveComplexity.iterate_eq_of_isFixedPt`);
* an orbit on a finite type repeats within `Nat.card α` steps
  (`DescriptiveComplexity.exists_iterate_eq_of_finite`), so if it ever reaches
  a fixed point, the `Nat.card α`-th iterate already is one
  (`DescriptiveComplexity.isFixedPt_iterate_card_iff`) – the pigeonhole behind
  the partial fixed-point semantics;
* an *inflationary* map on the subsets of a finite type reaches a fixed point
  within `Nat.card X` steps – the height of the subset lattice, not its size
  (`DescriptiveComplexity.isFixedPt_iterate_card_of_subset`), via the plateau
  of any monotone chain of subsets
  (`DescriptiveComplexity.exists_succ_eq_of_monotone_subset`, with the dual
  `DescriptiveComplexity.exists_succ_eq_of_antitone_subset` for descending
  refinement chains).

Consumers: the stages of `DescriptiveComplexity.derivesIn`
(`DescriptiveComplexity.FixedPoint`), the inflationary and partial iterations of
`DescriptiveComplexity.StepDef` (`DescriptiveComplexity.FixedPointStep`), and any
future exponential iteration (SO(LFP), SO(PFP)). Everything is stated over an
arbitrary starting point, so ascending chains from `⊥` and descending chains
from `⊤` are both instances.
-/

@[expose] public section

namespace DescriptiveComplexity

open Function (IsFixedPt)

variable {α : Type*} {f : α → α}

/-! ### Constancy from a plateau -/

/-- Once an orbit reaches a fixed point, it stays there: the orbit is constant
from any index whose value is a fixed point. -/
theorem iterate_eq_of_isFixedPt {a : α} {N : ℕ} (h : IsFixedPt f (f^[N] a)) {n : ℕ}
    (hn : N ≤ n) : f^[n] a = f^[N] a := by
  conv_lhs => rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply]
  exact h.iterate (n - N)

/-! ### Pigeonhole: repeats and eventual periodicity -/

/-- An orbit on a finite type repeats within `Nat.card α` steps. -/
theorem exists_iterate_eq_of_finite [Finite α] (f : α → α) (a : α) :
    ∃ i j, i < j ∧ j ≤ Nat.card α ∧ f^[i] a = f^[j] a := by
  cases nonempty_fintype α
  obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun n : Fin (Nat.card α + 1) => f^[n] a)
    (by simp [Nat.card_eq_fintype_card])
  rcases hne.lt_or_gt with hij | hij
  · exact ⟨i, j, hij, Nat.lt_succ_iff.mp j.isLt, heq⟩
  · exact ⟨j, i, hij, Nat.lt_succ_iff.mp i.isLt, heq.symm⟩

/-- **If an orbit on a finite type ever reaches a fixed point, the
`Nat.card α`-th iterate already is one.** This is what bounds the partial
fixed-point iteration: convergence, if it happens at all, happens within the
number of states. -/
theorem isFixedPt_iterate_card_iff [Finite α] (f : α → α) (a : α) :
    IsFixedPt f (f^[Nat.card α] a) ↔ ∃ n, IsFixedPt f (f^[n] a) := by
  refine ⟨fun h => ⟨_, h⟩, fun h => ?_⟩
  have hmem : sInf {n | IsFixedPt f (f^[n] a)} ∈ {n | IsFixedPt f (f^[n] a)} :=
    Nat.sInf_mem h
  set N := sInf {n | IsFixedPt f (f^[n] a)} with hN
  have hmem' : IsFixedPt f (f^[N] a) := hmem
  -- the least index reaching a fixed point is at most `Nat.card α`
  have hle : N ≤ Nat.card α := by
    by_contra hgt
    push Not at hgt
    obtain ⟨i, j, hij, hjcard, heq⟩ := exists_iterate_eq_of_finite f a
    -- the orbit is `(j - i)`-periodic from index `i` on
    have hper : ∀ m, i ≤ m → f^[m + (j - i)] a = f^[m] a := by
      intro m him
      have h1 : m + (j - i) = (m - i) + j := by omega
      have h2 : m = (m - i) + i := by omega
      rw [h1, Function.iterate_add_apply, ← heq, ← Function.iterate_add_apply, ← h2]
    -- so a fixed point one period earlier, contradicting minimality
    have hstep : f^[N - (j - i)] a = f^[N] a := by
      have hp := hper (N - (j - i)) (by omega)
      rw [show N - (j - i) + (j - i) = N from by omega] at hp
      exact hp.symm
    have hprev : N - (j - i) ∈ {n | IsFixedPt f (f^[n] a)} := by
      change IsFixedPt f _
      rw [hstep]
      exact hmem'
    have hcon := Nat.sInf_le hprev
    omega
  rw [iterate_eq_of_isFixedPt hmem' hle]
  exact hmem'

/-! ### Monotone chains of subsets plateau within the cardinality

The bound here is `Nat.card X` – the height of the subset lattice – rather
than the `2 ^ Nat.card X` states a bare pigeonhole would give. -/

/-- A monotone chain of subsets of a finite type plateaus within `Nat.card X`
steps. -/
theorem exists_succ_eq_of_monotone_subset {X : Type*} [Finite X] {c : ℕ → Set X}
    (hc : ∀ n, c n ⊆ c (n + 1)) : ∃ N ≤ Nat.card X, c (N + 1) = c N := by
  by_contra hcon
  push Not at hcon
  have hcard : ∀ N ≤ Nat.card X + 1, (c 0).ncard + N ≤ (c N).ncard := by
    intro N
    induction N with
    | zero => simp
    | succ N ihN =>
      intro hN
      have hssub : c N ⊂ c (N + 1) :=
        (hc N).ssubset_of_ne (Ne.symm (hcon N (by omega)))
      have h1 := ihN (by omega)
      have h2 := Set.ncard_lt_ncard hssub (Set.toFinite _)
      omega
  have h1 := hcard (Nat.card X + 1) le_rfl
  have h2 := Set.ncard_le_ncard (Set.subset_univ (c (Nat.card X + 1))) (Set.toFinite _)
  rw [Set.ncard_univ] at h2
  omega

/-- An antitone chain of subsets of a finite type plateaus within `Nat.card X`
steps: the dual of `DescriptiveComplexity.exists_succ_eq_of_monotone_subset`,
for descending refinement chains. -/
theorem exists_succ_eq_of_antitone_subset {X : Type*} [Finite X] {c : ℕ → Set X}
    (hc : ∀ n, c (n + 1) ⊆ c n) : ∃ N ≤ Nat.card X, c (N + 1) = c N := by
  obtain ⟨N, hN, heq⟩ := exists_succ_eq_of_monotone_subset
    (c := fun n => (c n)ᶜ) fun n => Set.compl_subset_compl.mpr (hc n)
  exact ⟨N, hN, compl_injective heq⟩

/-- **An inflationary map on the subsets of a finite type reaches a fixed
point within `Nat.card X` steps**, from any starting point: the chain of
iterates can only grow `Nat.card X` many times. -/
theorem isFixedPt_iterate_card_of_subset {X : Type*} [Finite X] {f : Set X → Set X}
    (hf : ∀ s, s ⊆ f s) (s : Set X) : IsFixedPt f (f^[Nat.card X] s) := by
  obtain ⟨N, hN, heq⟩ := exists_succ_eq_of_monotone_subset
    (c := fun n => f^[n] s) fun n => by rw [Function.iterate_succ_apply']; exact hf _
  have hfix : IsFixedPt f (f^[N] s) := by
    rwa [Function.iterate_succ_apply'] at heq
  rw [iterate_eq_of_isFixedPt hfix hN]
  exact hfix

end DescriptiveComplexity
