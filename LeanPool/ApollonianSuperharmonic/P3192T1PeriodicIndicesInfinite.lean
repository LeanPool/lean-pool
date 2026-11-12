/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PeriodicTileIndexedMultiplicityOne
public import Mathlib.Data.Set.Finite.Lattice

-- [TABLET NODE: P3192T1PeriodicIndicesInfinite]

/-!
# P3192T1PeriodicIndicesInfinite

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3192T1PeriodicIndicesInfinite {ι : Type}
    (P : PeriodicTileComplex ι) : Infinite ι := by
-- BODY
  classical
  have : Infinite GaussianInt := Infinite.of_injective
    (fun z : Int => (⟨z, 0⟩ : GaussianInt)) (by
      intro a b hab
      exact congrArg Zsqrtd.re hab)
  by_contra h
  have : Finite ι := not_infinite_iff_finite.mp h
  have hfinite : Set.Finite (⋃ a : ι, ((P.tile a).cells : Set GaussianInt)) :=
    Set.finite_iUnion fun a => (P.tile a).cells.finite_toSet
  have hcover : (⋃ a : ι, ((P.tile a).cells : Set GaussianInt)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, ha, _⟩ := PeriodicTileIndexedMultiplicityOne P x
    exact Set.mem_iUnion.mpr ⟨a, ha⟩
  rw [hcover] at hfinite
  exact Set.infinite_univ hfinite

end ApollonianSuperharmonic

end
