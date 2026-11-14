/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.GridRayCrossingIndexZeroOfEdgeLifts
public import LeanPool.ApollonianSuperharmonic.TopologicalDiskExponentialLift

/-!
# TopologicalDiskGridRayCrossingIndexZero

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open Set

noncomputable section

-- [TABLET NODE: TopologicalDiskGridRayCrossingIndexZero]
theorem TopologicalDiskGridRayCrossingIndexZero
    (S : Set (Real × Real)) (hS : TopologicalDisk S) (q : LatticeCell)
    (hq : ((((q.re : Int) : Real) + (1 / 2 : Real)),
      (((q.im : Int) : Real) + (1 / 2 : Real))) ∉ S)
    (p : List GaussianInt) (x y : GaussianInt)
    (hhead : p.head? = some x) (hlast : p.getLast? = some y)
    (hadj : ∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
      p = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b)
    (hclose : FourNeighborAdjacent y x)
    (hedge : ∀ a b : GaussianInt,
      ((∃ l₁ l₂ : List GaussianInt, p = l₁ ++ a :: b :: l₂) ∨
        (a = y ∧ b = x)) →
      ∀ t : Set.Icc (0 : Real) 1,
        ((1 - (t : Real)) * ((a.re : Int) : Real) +
            (t : Real) * ((b.re : Int) : Real),
          (1 - (t : Real)) * ((a.im : Int) : Real) +
            (t : Real) * ((b.im : Int) : Real)) ∈ S) :
    GridRayCrossingIndex q p = 0 := by
-- BODY
  classical
  let center : Real × Real :=
    ((((q.re : Int) : Real) + (1 / 2 : Real)),
      (((q.im : Int) : Real) + (1 / 2 : Real)))
  rcases TopologicalDiskExponentialLift S hS center hq with ⟨G, hG, hGexp⟩
  let point : GaussianInt → Real × Real := fun a ↦
    (((a.re : Int) : Real), ((a.im : Int) : Real))
  let F : GaussianInt → ℂ := fun a ↦
    if ha : point a ∈ S then G ⟨point a, ha⟩ else 0
  apply GridRayCrossingIndexZeroOfEdgeLifts q p x y F hhead hlast hadj hclose
  intro a b hoccur
  let edge : Set.Icc (0 : Real) 1 → S := fun t ↦
    ⟨((1 - (t : Real)) * ((a.re : Int) : Real) +
          (t : Real) * ((b.re : Int) : Real),
        (1 - (t : Real)) * ((a.im : Int) : Real) +
          (t : Real) * ((b.im : Int) : Real)), hedge a b hoccur t⟩
  let L : Set.Icc (0 : Real) 1 → ℂ := fun t ↦ G (edge t)
  have hedgeCont : Continuous edge := by
    fun_prop
  have hL : Continuous L := hG.comp hedgeCont
  have ha : point a ∈ S := by
    simpa [point] using hedge a b hoccur ⟨0, by norm_num⟩
  have hb : point b ∈ S := by
    simpa [point] using hedge a b hoccur ⟨1, by norm_num⟩
  refine ⟨L, hL, ?_, ?_, ?_⟩
  · change G (edge ⟨0, by norm_num⟩) = F a
    rw [show F a = G ⟨point a, ha⟩ by simp [F, ha]]
    congr 1
    apply Subtype.ext
    simp [edge, point]
  · change G (edge ⟨1, by norm_num⟩) = F b
    rw [show F b = G ⟨point b, hb⟩ by simp [F, hb]]
    congr 1
    apply Subtype.ext
    simp [edge, point]
  · intro t
    have he := hGexp (edge t)
    rw [he]
    apply Complex.ext <;>
      simp [edge, center, GridCellCenter] <;> ring

end

end ApollonianSuperharmonic

end
