/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Isotony
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

/-!
# Directed unions of actual von Neumann algebras

The union is a unital star algebra. Every continuous functional-calculus
expression remains in the same witnessing von Neumann algebra, although
the union itself need not be closed in operator norm.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vonNeumannAlgebra_isClosed (A : VonNeumannAlgebra H) :
    IsClosed (A : Set (H →L[ℂ] H)) := by
  rw [← A.centralizer_centralizer]
  exact Set.isClosed_centralizer _

theorem cfc_mem_vonNeumannAlgebra (A : VonNeumannAlgebra H) (f : ℝ → ℝ)
    {T : H →L[ℂ] H} (hT : T ∈ A) : cfc f T ∈ A := by
  let : IsClosed (A.toStarSubalgebra : Set (H →L[ℂ] H)) := vonNeumannAlgebra_isClosed A
  exact cfc_mem (𝕜' := ℂ) (s := A.toStarSubalgebra) f hT

variable {ι : Type*} [Nonempty ι]

/-- Set-theoretic union of a directed family of von Neumann subalgebras. -/
def directedAlgebraUnion (A : ι → VonNeumannAlgebra H) (hd : Directed (· ≤ ·) A) :
    StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {T | ∃ i, T ∈ A i}
  zero_mem' := ⟨Classical.arbitrary ι, zero_mem _⟩
  one_mem' := ⟨Classical.arbitrary ι, one_mem _⟩
  add_mem' := by
    rintro T U ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, add_mem (hik hi) (hjk hj)⟩
  mul_mem' := by
    rintro T U ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, mul_mem (hik hi) (hjk hj)⟩
  algebraMap_mem' c :=
    ⟨Classical.arbitrary ι, (A (Classical.arbitrary ι)).toStarSubalgebra.algebraMap_mem c⟩
  star_mem' := by
    rintro T ⟨i, hi⟩
    exact ⟨i, star_mem hi⟩

theorem cfc_mem_directedAlgebraUnion (A : ι → VonNeumannAlgebra H)
    (hd : Directed (· ≤ ·) A) (f : ℝ → ℝ) {T : H →L[ℂ] H}
    (hT : T ∈ directedAlgebraUnion A hd) : cfc f T ∈ directedAlgebraUnion A hd := by
  obtain ⟨i, hi⟩ := hT
  exact ⟨i, cfc_mem_vonNeumannAlgebra (A i) f hi⟩

end VacuumBellSeparation
