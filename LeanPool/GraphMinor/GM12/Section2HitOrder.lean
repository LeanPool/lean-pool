/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Set.Card

/-!
# Ordering the finitely many hit parameters

The trace construction in XII, page 243, lists the vertex hits in their
order along the parameter interval. A finite set in a linear order has
an increasing enumeration. If it contains the two interval endpoints,
those are its first and last entries. The number of intervening
intervals is one less than the number of entries.
-/

public section

namespace GraphMinor.GM12

open Set

/-- Enumerate a finite set in an interval in increasing order, retaining
its endpoints and cardinality. This supplies the ordered parameters
used in the trace construction of XII, page 243. -/
theorem exists_ordered_interval_enumeration {α : Type*} [LinearOrder α]
    {H : Set α} (hH : H.Finite) {a b : α} (hsub : H ⊆ Icc a b)
    (ha : a ∈ H) (hb : b ∈ H) :
    ∃ (n : ℕ) (t : Fin (n + 1) → α), StrictMono t ∧ t 0 = a ∧ t (Fin.last n) = b ∧
      range t = H ∧ n + 1 = H.ncard := by
  classical
  let s := hH.toFinset
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨a, hH.mem_toFinset.mpr ha⟩
  let n := s.card - 1
  have hcard : s.card = n + 1 := by dsimp only [n]; omega
  let t : Fin (n + 1) ↪o α := s.orderEmbOfFin hcard
  have ht : StrictMono t := t.strictMono
  have hrange : range t = H := (Finset.range_orderEmbOfFin s hcard).trans hH.coe_toFinset
  have ha' : a ∈ range t := hrange.symm ▸ ha
  have hb' : b ∈ range t := hrange.symm ▸ hb
  obtain ⟨i, hi⟩ := ha'
  obtain ⟨j, hj⟩ := hb'
  have hfirst : t 0 = a := le_antisymm
    ((ht.monotone (Fin.zero_le i)).trans_eq hi)
    (hsub (hrange ▸ mem_range_self 0)).1
  have hlast : t (Fin.last n) = b := le_antisymm
    (hsub (hrange ▸ mem_range_self (Fin.last n))).2
    (hj ▸ ht.monotone (Fin.le_last j))
  refine ⟨n, t, ht, hfirst, hlast, hrange, ?_⟩
  rw [Set.ncard_eq_toFinset_card H hH]
  exact hcard.symm

end GraphMinor.GM12
