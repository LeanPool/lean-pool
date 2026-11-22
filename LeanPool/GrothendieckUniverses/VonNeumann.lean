/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.GrothendieckUniverses.Basic
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.ZFC.VonNeumann

/-!
# The inaccessible stages of the von Neumann hierarchy are universes

For a regular strong limit cardinal `κ` (that is, `κ = ℵ₀` or `κ` inaccessible), the stage
`V_ κ.ord` of the von Neumann hierarchy is a Grothendieck universe of cardinality `κ`. In
particular `V_ ω`, the hereditarily finite sets, is a universe, and so is `V_ κ.ord` for every
inaccessible cardinal `κ` (Williams 1969, Theorem 1; Kruse 1965, Theorem 1).

## References

* A. H. Kruse, *Grothendieck universes and the super-complete models of Shepherdson*,
  Compositio Math. 17 (1965), 96–101.
* N. H. Williams, *On Grothendieck universes*, Compositio Math. 21 (1969), 1–3.
-/

@[expose] public section

namespace LeanPool.GrothendieckUniverses

open ZFSet Cardinal Ordinal

universe u

/-- A regular strong limit cardinal is a fixed point of `preBeth ∘ ord`. -/
theorem preBeth_ord_of_isRegular {κ : Cardinal.{u}} (hr : κ.IsRegular) (hs : κ.IsStrongLimit) :
    preBeth κ.ord = κ := by
  rcases hr.aleph0_le.eq_or_lt with h | h
  · rw [← h, ord_aleph0, preBeth_omega]
  · exact (isInaccessible_def.2 ⟨h, hr, hs⟩).preBeth_ord

/-- The stage `V_ κ.ord` has cardinality `κ` when `κ` is a regular strong limit cardinal. -/
theorem card_vonNeumann_ord {κ : Cardinal.{u}} (hr : κ.IsRegular) (hs : κ.IsStrongLimit) :
    card (V_ κ.ord) = κ := by
  rw [card_vonNeumann, preBeth_ord_of_isRegular hr hs]

/-- Elements of `V_ κ.ord` have cardinality `< κ` when `κ` is a regular strong limit. -/
theorem card_lt_of_mem_vonNeumann_ord {κ : Cardinal.{u}} (hr : κ.IsRegular)
    (hs : κ.IsStrongLimit) {x : ZFSet.{u}} (hx : x ∈ V_ κ.ord) : card x < κ := by
  rw [mem_vonNeumann] at hx
  calc card x ≤ card (V_ (rank x)) := card_mono (subset_vonNeumann_self x)
    _ = preBeth (rank x) := card_vonNeumann _
    _ < preBeth κ.ord := preBeth_lt_preBeth.2 hx
    _ = κ := preBeth_ord_of_isRegular hr hs

/-- **`V_ κ` is a universe** for every regular strong limit cardinal `κ`. -/
theorem isGrothendieckUniverse_vonNeumann_of_isRegular {κ : Cardinal.{u}} (hr : κ.IsRegular)
    (hs : κ.IsStrongLimit) : IsGrothendieckUniverse (V_ κ.ord) where
  isTransitive := isTransitive_vonNeumann _
  powerset_mem x hx := by
    rw [mem_vonNeumann] at hx ⊢
    rw [rank_powerset]
    exact (isSuccLimit_ord hr.aleph0_le).succ_lt hx
  singleton_mem x hx := by
    rw [mem_vonNeumann] at hx ⊢
    rw [rank_singleton]
    exact (isSuccLimit_ord hr.aleph0_le).succ_lt hx
  iUnion_mem I hI f hf := by
    simp_rw [mem_vonNeumann] at hf ⊢
    rw [rank_iUnion]
    apply lift_iSup_lt_of_lt_cof _ hf
    rw [cardinalMk_coe_sort, ← lift_cof, hr.cof_ord, Cardinal.lift_lift, Cardinal.lift_lt]
    exact card_lt_of_mem_vonNeumann_ord hr hs hI
  nonempty h := by
    have : (∅ : ZFSet.{u}) ∈ V_ κ.ord := by
      rw [mem_vonNeumann, rank_empty]
      exact hr.ord_pos
    rw [h] at this
    exact notMem_empty _ this

/-- **`V_ κ` is a universe** for every inaccessible cardinal `κ` (Williams 1969, Theorem 1). -/
theorem isGrothendieckUniverse_vonNeumann {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    IsGrothendieckUniverse (V_ κ.ord) :=
  isGrothendieckUniverse_vonNeumann_of_isRegular hκ.isRegular hκ.isStrongLimit

/-- **`V_ ω` is a universe**: the hereditarily finite sets (Williams 1969, Theorem 1). -/
theorem isGrothendieckUniverse_vonNeumann_omega0 :
    IsGrothendieckUniverse (V_ Ordinal.omega0.{u}) := by
  simpa using isGrothendieckUniverse_vonNeumann_of_isRegular isRegular_aleph0
    isStrongLimit_aleph0

end LeanPool.GrothendieckUniverses
