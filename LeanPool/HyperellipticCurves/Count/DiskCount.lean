/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.Basic
public import LeanPool.HyperellipticCurves.Disks.OrdSpace
public import LeanPool.HyperellipticCurves.Disks.Reduction

import Mathlib.Data.Set.Card.Arithmetic

/-!
# Counting the points disk by disk

The bookkeeping half of the Chabauty–Coleman count: the residue disks are the fibres of the
reduction map (`ChabautyColeman.ResidueDisk` is `redPoint ⁻¹' {P_bar}` by definition), so a set of
points whose reductions all lie in a finite set `T` of residue points has at most
`#T + ∑_{P_bar ∈ T} m_{P_bar}` elements once each disk carries at most `1 + m_{P_bar}` of them
(`ChabautyColeman.ratPoints_disk_decomp`). Applied to the rational points, with the per-disk
bound of blueprint `thm:disk-bound` and the vanishing budget `∑ m_{P_bar} ≤ 2r` of
`ChabautyColeman.sum_ordSpace_le`, this is the main theorem.

Counts are `Set.encard`s (`ℕ∞`-valued), so no finiteness has to be assumed: a bound on the
fibres forces the whole set to be finite, which is exactly the finiteness of the rational
points (`ChabautyColeman.ratPoints_finite_of_rank_le`).

Blueprint nodes: `lem:disk-decomp`, `thm:main-count`.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

/-- **Counting along the fibres of a map**: if every element of `S` is mapped into the finite
set `T` and the fibre of `S` over each point *of `T`* carries at most `1 + m b` elements, then
`S` has at most `#T + ∑_{b ∈ T} m b` elements. -/
theorem encard_le_of_fiber_encard_le {α β : Type*} (red : α → β) {S : Set α} {m : β → ℕ}
    (T : Finset β) (hT : ∀ a ∈ S, red a ∈ T)
    (hfib : ∀ b ∈ T, (S ∩ red ⁻¹' {b}).encard ≤ 1 + m b) :
    S.encard ≤ T.card + ∑ b ∈ T, m b := by
  have hsub : S ⊆ ⋃ b ∈ T, S ∩ red ⁻¹' {b} := fun a ha ↦ Set.mem_biUnion (hT a ha) ⟨ha, rfl⟩
  calc S.encard
      ≤ (⋃ b ∈ T, S ∩ red ⁻¹' {b}).encard := Set.encard_mono hsub
    _ ≤ ∑ b ∈ T, (S ∩ red ⁻¹' {b}).encard := Finset.set_encard_biUnion_le T _
    _ ≤ ∑ b ∈ T, (1 + m b : ℕ∞) := Finset.sum_le_sum hfib
    _ = T.card + ∑ b ∈ T, m b := by rw [Finset.sum_add_distrib]; push_cast; simp

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K] {f : O[X]}

/-- **Disk decomposition of the rational points** (blueprint `lem:disk-decomp`): the residue
disks are the fibres of the reduction, so a set `S` of points reducing into a finite set `T`
of residue points is counted disk by disk. With `S` the rational points, `T` the residue
points rational over the residue field of the base, and the per-disk bound of blueprint
`thm:disk-bound`, this is the counting step of the main theorem. -/
theorem ratPoints_disk_decomp {S : Set (CurvePoint K (f.map (algebraMap O K)))}
    {m : CurvePoint (ResidueField O) (f.map (residue O)) → ℕ}
    (T : Finset (CurvePoint (ResidueField O) (f.map (residue O))))
    (hT : ∀ P ∈ S, redPoint P ∈ T)
    (hdisk : ∀ P₀ ∈ T, (S ∩ ResidueDisk P₀).encard ≤ 1 + m P₀) :
    S.encard ≤ T.card + ∑ P₀ ∈ T, m P₀ :=
  encard_le_of_fiber_encard_le redPoint T hT hdisk

variable [Invertible (2 : O)] {C : HyperellipticCurve O} [C.IsOdd]

/-- **The Chabauty–Coleman count** (blueprint `thm:main-count`, counting step): summing the per-disk
bound of blueprint `thm:disk-bound` over the disks costs `#T` — one point per disk — plus the
total vanishing budget `∑_P_bar n(V, P_bar) ≤ 2r` of blueprint `cor:sum-ord`, for `V` the space of
numerators of the annihilating differentials, of codimension at most the rank `r`.

The two inputs still to be supplied are the hypotheses: `hT`, that the reduction of a point of
`S` is rational over the residue field of the *base* (the arithmetic half of blueprint
`lem:disk-decomp`), and `hdisk`, the per-disk bound with the intrinsic order
`ChabautyColeman.ordSpace` of the differential chosen in that disk — which for the disk
expansion is blueprint `lem:ord-match`. -/
theorem ratPoints_encard_le {S : Set (CurvePoint K (C.f.map (algebraMap O K)))}
    (T : Finset (CurvePoint (ResidueField O) (C.f.map (residue O))))
    (hT : ∀ P ∈ S, redPoint P ∈ T) {V : Submodule (ResidueField O) (ResidueField O)[X]}
    (hdisk : ∀ P₀ ∈ T, (S ∩ ResidueDisk P₀).encard ≤ 1 + ordSpace (C.f.map (residue O)) V P₀)
    (hV : V ≠ ⊥) (hdeg : ∀ h ∈ V, h.degree < genus (C.f.map (residue O))) {r : ℕ}
    (hr : genus (C.f.map (residue O)) ≤ Module.finrank (ResidueField O) V + r) :
    S.encard ≤ T.card + 2 * r := by
  refine (ratPoints_disk_decomp T hT hdisk).trans ?_
  gcongr
  exact_mod_cast sum_ordSpace_le hV hdeg hr T

end ChabautyColeman

end
