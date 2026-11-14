/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.AcyclicIndegreeOrientation

-- [TABLET NODE: P5532T1OrientationPullback]

/-!
# P5532T1OrientationPullback

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5532T1OrientationPullback (D E : Finset GaussianInt)
    (σ τ : GaussianInt → ℤ) (L : GaussianInt → GaussianInt)
    (hDE : E = D.image L) (hinj : Function.Injective L)
    (hadj : ∀ x y, FourNeighborAdjacent x y ↔ FourNeighborAdjacent (L x) (L y))
    (hσ : ∀ x ∈ D, τ (L x) = σ x)
    (o : AcyclicIndegreeOrientation E τ) :
    Nonempty (AcyclicIndegreeOrientation D σ) := by
-- BODY
  classical
  have hmem (x : GaussianInt) : x ∈ D ↔ L x ∈ E := by
    rw [hDE]
    constructor
    · exact fun hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · intro hx
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
      exact hinj heq ▸ hy
  refine ⟨{
    edge := fun x y => o.edge (L x) (L y)
    edgeDecidable := fun x y => o.edgeDecidable (L x) (L y)
    rank := fun x => o.rank (L x)
    supported := ?_
    oriented := ?_
    increasing := ?_
    indegree := ?_ }⟩
  · intro x y he
    obtain ⟨hx, hy, ha⟩ := o.supported _ _ he
    exact ⟨(hmem x).mpr hx, (hmem y).mpr hy, (hadj x y).mpr ha⟩
  · intro x hx y hy ha
    exact o.oriented _ ((hmem x).mp hx) _ ((hmem y).mp hy) ((hadj x y).mp ha)
  · intro x y he
    exact o.increasing _ _ he
  · intro x hx
    have hc :
        (D.filter fun y => @decide (o.edge (L y) (L x))
          (o.edgeDecidable (L y) (L x))).card =
        (E.filter fun y => @decide (o.edge y (L x))
          (o.edgeDecidable y (L x))).card := by
      apply Finset.card_bij (fun y _ => L y)
      · intro y hy
        exact Finset.mem_filter.mpr ⟨(hmem y).mp (Finset.mem_filter.mp hy).1,
          (Finset.mem_filter.mp hy).2⟩
      · intro y hy z hz heq
        exact hinj heq
      · intro z hz
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hDE ▸ (Finset.mem_filter.mp hz).1)
        exact ⟨y, Finset.mem_filter.mpr ⟨hy, (Finset.mem_filter.mp hz).2⟩, rfl⟩
    rw [hc, ← hσ x hx]
    exact o.indegree (L x) ((hmem x).mp hx)

end ApollonianSuperharmonic

end
