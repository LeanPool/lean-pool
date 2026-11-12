/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5352T2DomainRows

-- [TABLET NODE: P5537T1PredecessorCoordinates]

/-!
# P5537T1PredecessorCoordinates

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5537T1PredecessorCoordinates (K : DiamondParameter)
    (hk : 1 < K.1) (x : GaussianInt) :
    let n : Int := K.1
    ((x ∈ FootprintVertices (DiamondTile K.1) ∧
        x-⟨n,1-n⟩ ∈ FootprintVertices (DiamondTile (K.1-1))) ↔
      1 ≤ x.re ∧ x.re ≤ n ∧ 0 ≤ x.im ∧ x.im ≤ n-1 ∧
        x.re-1 ≤ x.im ∧ x.im ≤ x.re) ∧
    ((x ∈ FootprintVertices (DiamondTile K.1) ∧
        x-⟨n,n+1⟩ ∈ FootprintVertices (DiamondTile (K.1-1))) ↔
      1 ≤ x.re ∧ x.re ≤ n ∧ n+1 ≤ x.im ∧ x.im ≤ 2*n ∧
        2*n ≤ x.re+x.im ∧ x.re+x.im ≤ 2*n+1) ∧
    ((x ∈ FootprintVertices (DiamondTile K.1) ∧
        x-⟨-n,n+1⟩ ∈ FootprintVertices (DiamondTile (K.1-1))) ↔
      -n ≤ x.re ∧ x.re ≤ -1 ∧ n+1 ≤ x.im ∧ x.im ≤ 2*n ∧
        2*n ≤ x.im-x.re ∧ x.im-x.re ≤ 2*n+1) ∧
    ((x ∈ FootprintVertices (DiamondTile K.1) ∧
        x-⟨-n,1-n⟩ ∈ FootprintVertices (DiamondTile (K.1-1))) ↔
      -n ≤ x.re ∧ x.re ≤ -1 ∧ 0 ≤ x.im ∧ x.im ≤ n-1 ∧
        -1 ≤ x.re+x.im ∧ x.re+x.im ≤ 0) := by
-- BODY
  have hc := (P5352T2DomainRows K x).1
  have hp (a b : Int) :=
    (P5352T2DomainRows ⟨K.1-1, by omega⟩ (x-⟨a,b⟩)).1
  simp only [Nat.cast_sub (by omega : 1 ≤ K.1), Nat.cast_one,
    Zsqrtd.re_sub, Zsqrtd.im_sub] at hp
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [hc, hp]
    omega

end ApollonianSuperharmonic

end
