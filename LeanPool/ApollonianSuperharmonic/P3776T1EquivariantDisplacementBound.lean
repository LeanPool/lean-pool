/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.LatticeFundamentalSet
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.Linarith

-- [TABLET NODE: P3776T1EquivariantDisplacementBound]

/-!
# P3776T1EquivariantDisplacementBound

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3776T1EquivariantDisplacementBound
    (L : AddSubgroup GaussianInt) (R : Finset GaussianInt)
    (hR : LatticeFundamentalSet L R)
    (f : (Real × Real) → (Real × Real)) (hf : Continuous f)
    (hperiodic : ∀ u : L, ∀ x, f (x + GaussianRealPoint u) = f x + GaussianRealPoint u) :
    ∃ M : Real, 0 ≤ M ∧ ∀ x, dist (f x) x ≤ M := by
-- BODY
  classical
  let A : Set (Real × Real) := Set.Icc (0 : Real) 1 ×ˢ Set.Icc (0 : Real) 1
  let Q : Set (Real × Real) := ⋃ r ∈ R, (fun v => v + GaussianRealPoint r) '' A
  have hA : IsCompact A := isCompact_Icc.prod isCompact_Icc
  have hQ : IsCompact Q := R.isCompact_biUnion fun r _ =>
    hA.image (continuous_id.add continuous_const)
  obtain ⟨M, hM, hbound⟩ :=
    (hQ.image (hf.dist continuous_id)).isBounded.exists_pos_norm_le
  refine ⟨M, hM.le, ?_⟩
  intro x
  let n : GaussianInt := ⟨Int.floor x.1, Int.floor x.2⟩
  let v : Real × Real := x - GaussianRealPoint n
  have hv : v ∈ A := by
    change (0 ≤ x.1 - (Int.floor x.1 : Real) ∧ x.1 - (Int.floor x.1 : Real) ≤ 1) ∧
      (0 ≤ x.2 - (Int.floor x.2 : Real) ∧ x.2 - (Int.floor x.2 : Real) ≤ 1)
    constructor <;> constructor
    · linarith [Int.floor_le x.1]
    · linarith [Int.lt_floor_add_one x.1]
    · linarith [Int.floor_le x.2]
    · linarith [Int.lt_floor_add_one x.2]
  obtain ⟨r, ⟨hr, hnr⟩, _⟩ := hR n
  let u : L := ⟨n - r, hnr⟩
  let y : Real × Real := x - GaussianRealPoint u
  have hpoint : GaussianRealPoint (n - r) = GaussianRealPoint n - GaussianRealPoint r := by
    ext <;> simp [GaussianRealPoint]
  have hy : y ∈ Q := by
    apply Set.mem_iUnion.mpr
    refine ⟨r, Set.mem_iUnion.mpr ⟨hr, ?_⟩⟩
    refine ⟨v, hv, ?_⟩
    change x - GaussianRealPoint n + GaussianRealPoint r = x - GaussianRealPoint (n - r)
    rw [hpoint]
    abel
  have hxy : y + GaussianRealPoint u = x := sub_add_cancel x _
  have hp : f x = f y + GaussianRealPoint u := by
    rw [← hxy]
    exact hperiodic u y
  have hdist : dist (f y) y ≤ M := by
    simpa [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using
      hbound _ ⟨y, hy, rfl⟩
  rw [hp, ← hxy]
  simpa [Prod.dist_eq, Real.dist_eq] using hdist

end ApollonianSuperharmonic

end
