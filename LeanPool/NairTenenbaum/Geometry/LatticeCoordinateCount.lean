/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Geometry.LipschitzBoundaryLatticeCount
public import Mathlib.Algebra.Module.ZLattice.Basic

/-! # Exact lattice counts under an integral basis

The real basis extending an integral lattice basis maps lattice elements to
integer coordinate vectors, preserving the count in every subset.
-/

@[expose] public section

namespace NairTenenbaum

open Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Finite ι] (b : Basis ι ℤ L)

theorem ofZLatticeBasis_equivFun_eq (x : L) :
    (b.ofZLatticeBasis ℝ).equivFunL (x : E) = integerLatticePoint (b.equivFun x) := by
  ext i
  change (b.ofZLatticeBasis ℝ).repr (x : E) i = (b.repr x i : ℝ)
  exact b.ofZLatticeBasis_repr_apply ℝ L x i

theorem integerLatticeCount_basis_image (s : Set E) :
    integerLatticeCount ((b.ofZLatticeBasis ℝ).equivFunL '' s) = Nat.card {x : L // (x : E) ∈ s}
        := by
  have hmem (x : L) : (x : E) ∈ s ↔
      integerLatticePoint (b.equivFun x) ∈ (b.ofZLatticeBasis ℝ).equivFunL '' s := by
    rw [← ofZLatticeBasis_equivFun_eq b x]
    exact ((b.ofZLatticeBasis ℝ).equivFunL.injective.mem_set_image).symm
  exact (Nat.card_congr (b.equivFun.toEquiv.subtypeEquiv hmem)).symm

end NairTenenbaum
