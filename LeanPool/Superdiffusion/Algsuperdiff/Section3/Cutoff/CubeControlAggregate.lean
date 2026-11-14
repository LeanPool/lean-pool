/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CubeControlBoundary

/-!
# CubeControlAggregate

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Finite aggregation of unit-cube controls

The half-open origin cube is partitioned by finitely many unit descendants.
Their finite maximum, rather than their sum, gives the measurable control
used by the Gaussian maximum estimate.
-/

namespace Algsuperdiff.Section3.Cutoff

open Set
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- The finite maximum of translated unit-cube controls over the exact
unit-descendant lattice of a nonnegative-scale origin cube.  The explicit
nonemptiness witness is part of the definition, so this is the genuine finite
maximum rather than an empty-set convention. -/
def originCubeUnitControlMax (q : ℤ) (hq : 0 ≤ q) (j : ShellField d) : ℝ :=
  (descendantsAtScale (originCube d q) 0).sup'
    (descendantsAtScale_nonempty (originCube d q) hq)
    (fun R => translatedUnitCubeControl (triadicCubeShift R) j)

theorem originCubeUnitControlMax_nonneg (q : ℤ) (hq : 0 ≤ q) (j : ShellField d) :
    0 ≤ originCubeUnitControlMax q hq j := by
  unfold originCubeUnitControlMax
  obtain ⟨R, hR⟩ := descendantsAtScale_nonempty (originCube d q) hq
  exact (translatedUnitCubeControl_nonneg (triadicCubeShift R) j).trans
    (Finset.le_sup' (f := fun R => translatedUnitCubeControl (triadicCubeShift R) j)
      hR)

private theorem scale_eq_zero_of_mem_unitDescendants
    (q : ℤ) (hq : 0 ≤ q) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d q) 0) :
    R.scale = 0 := by
  have hscale := scale_eq_sub_of_mem_descendantsAtScale hq hR
  change R.scale = q - ↑((q - 0).toNat) at hscale
  have htoNat : (q - 0).toNat = q.toNat := by omega
  rw [htoNat, Int.toNat_of_nonneg hq] at hscale
  omega

/-- The finite unit-descendant maximum controls the matrix operator norm at every
point of the canonical half-open origin cube. -/
theorem matrixOperatorNorm_le_originCubeUnitControlMax
    (q : ℤ) (hq : 0 ≤ q) (j : ShellField d) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d q)) :
    HCPolySupport.Book.Ch02.matrixOperatorNorm (j x) ≤
      originCubeUnitControlMax q hq j := by
  have hcover := cubeSet_originCube_subset_iUnion_unitDescendants d q hq hx
  rw [Set.mem_iUnion] at hcover
  obtain ⟨R, hcover⟩ := hcover
  rw [Set.mem_iUnion] at hcover
  obtain ⟨hR, hxR⟩ := hcover
  have hR' : R ∈ descendantsAtScale (originCube d q) 0 := by
    simpa using hR
  have hscale := scale_eq_zero_of_mem_unitDescendants q hq hR'
  calc
    HCPolySupport.Book.Ch02.matrixOperatorNorm (j x) ≤
        translatedUnitCubeControl (triadicCubeShift R) j :=
      matrixOperatorNorm_le_translatedUnitCubeControl_of_mem_cubeSet R hscale j hxR
    _ ≤ originCubeUnitControlMax q hq j := by
      unfold originCubeUnitControlMax
      exact Finset.le_sup'
        (f := fun S => translatedUnitCubeControl (triadicCubeShift S) j) hR'

/-- The number of variables in `originCubeUnitControlMax` is the expected
number of unit descendants. -/
theorem card_originCubeUnitControlMax_lattice (q : ℤ) (hq : 0 ≤ q) :
    (descendantsAtScale (originCube d q) 0).card = (3 ^ d) ^ q.toNat :=
  card_unitDescendants_originCube d q hq

end

end Algsuperdiff.Section3.Cutoff
