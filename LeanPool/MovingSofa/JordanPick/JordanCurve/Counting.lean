/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.SetTheory.Cardinal.Finite
/-!
# Counting plumbing for the Jordan curve theorem

Pure-topology lemmas, independent of any geometry, used to turn the statement
"the complement of the curve has exactly two connected components" into the
numerical fact `Nat.card (ConnectedComponents …) = 2`.

The geometry side works with `connectedComponentIn S x` for `S : Set Plane` the
(open, nonempty) complement of the curve, and with two distinguished points in
the two components.  This file provides:

* `nat_card_connectedComponents_eq_two` — from two points in distinct components
  together covering everything, conclude `Nat.card (ConnectedComponents X) = 2`.
* `connectedComponents_subtype_eq_iff` — the bridge identifying equality of
  classes of subtype points with equality of `connectedComponentIn`.
-/

@[expose] public section

namespace JordanCurve.Counting

open Set

variable {X : Type*} [TopologicalSpace X]

/-- If a space `X` has two points `a`, `b` lying in distinct connected components
and every point's component is one of those two, then `X` has exactly two
connected components. -/
theorem nat_card_connectedComponents_eq_two
    (a b : X) (hab : ConnectedComponents.mk a ≠ ConnectedComponents.mk b)
    (hcover : ∀ x : X, ConnectedComponents.mk x = ConnectedComponents.mk a
                     ∨ ConnectedComponents.mk x = ConnectedComponents.mk b) :
    Nat.card (ConnectedComponents X) = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨ConnectedComponents.mk a, ConnectedComponents.mk b, hab, ?_⟩
  rw [eq_univ_iff_forall]
  intro z
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
  rcases hcover x with h | h
  · exact mem_insert_iff.mpr (Or.inl h)
  · exact mem_insert_iff.mpr (Or.inr (mem_singleton_iff.mpr h))

/-- Bridge lemma.  For two points `x`, `y` of a subset `S`, the connected
components of the corresponding subtype points agree iff their
`connectedComponentIn S` subsets agree.  This lets the geometry side, which
phrases things via `connectedComponentIn S`, feed
`nat_card_connectedComponents_eq_two`. -/
theorem connectedComponents_subtype_eq_iff {S : Set X} {x y : X}
    (hx : x ∈ S) (hy : y ∈ S) :
    ConnectedComponents.mk (⟨x, hx⟩ : S) = ConnectedComponents.mk (⟨y, hy⟩ : S)
      ↔ connectedComponentIn S x = connectedComponentIn S y := by
  rw [connectedComponentIn_eq_image hx, connectedComponentIn_eq_image hy,
    (image_injective.mpr Subtype.coe_injective).eq_iff,
    ← ConnectedComponents.coe_eq_coe]

end JordanCurve.Counting
