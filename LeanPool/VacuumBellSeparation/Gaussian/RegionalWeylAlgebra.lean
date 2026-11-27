/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.PhysicalOscillatorCoordinates

/-!
# The actual polynomial and norm-closed regional Weyl algebras

A real label subspace supplies the actual Weyl generators. Their complex
linear span is already a unital star algebra by the proved Weyl relation.
Its operator-norm closure is the regional C-star algebra; no tensor-product
identification or independence is part of this definition.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ComplexConjugate

variable {m : ℕ}

/-- Weyl operators with test-function labels supported in the given region. -/
def regionalWeylGenerators (L : Submodule ℝ (Fin m × Fin 2 → ℝ)) :
    Set (MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :=
  {A | ∃ x ∈ L, A = physicalOscillatorWeyl x}

/-- Regional Weyl span obtained from `Submodule.span`. -/
def regionalWeylSpan (L : Submodule ℝ (Fin m × Fin 2 → ℝ)) :
    Submodule ℂ (MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :=
  Submodule.span ℂ (regionalWeylGenerators L)

theorem physicalOscillatorWeyl_mem_regionalWeylSpan
    (L : Submodule ℝ (Fin m × Fin 2 → ℝ)) {x : Fin m × Fin 2 → ℝ} (hx : x ∈ L) :
    physicalOscillatorWeyl x ∈ regionalWeylSpan L :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem one_mem_regionalWeylSpan (L : Submodule ℝ (Fin m × Fin 2 → ℝ)) :
    1 ∈ regionalWeylSpan L := by
  simpa only [physicalOscillatorWeyl_zero] using
    physicalOscillatorWeyl_mem_regionalWeylSpan L L.zero_mem

theorem mul_mem_regionalWeylSpan (L : Submodule ℝ (Fin m × Fin 2 → ℝ))
    {A B : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : A ∈ regionalWeylSpan L) (hB : B ∈ regionalWeylSpan L) :
    A * B ∈ regionalWeylSpan L := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    rcases hA with ⟨x, hx, rfl⟩
    induction hB using Submodule.span_induction with
    | mem B hB =>
      rcases hB with ⟨y, hy, rfl⟩
      rw [physicalOscillatorWeyl_mul]
      exact (regionalWeylSpan L).smul_mem _
        (physicalOscillatorWeyl_mem_regionalWeylSpan L (L.add_mem hx hy))
    | zero => simpa only [mul_zero] using (regionalWeylSpan L).zero_mem
    | add B C hB hC ihB ihC =>
      simpa only [mul_add] using (regionalWeylSpan L).add_mem ihB ihC
    | smul c B hB ih =>
      simpa only [mul_smul_comm] using (regionalWeylSpan L).smul_mem c ih
  | zero => simpa only [zero_mul] using (regionalWeylSpan L).zero_mem
  | add A C hA hC ihA ihC =>
    simpa only [add_mul] using (regionalWeylSpan L).add_mem ihA ihC
  | smul c A hA ih =>
    simpa only [smul_mul_assoc] using (regionalWeylSpan L).smul_mem c ih

theorem star_mem_regionalWeylSpan (L : Submodule ℝ (Fin m × Fin 2 → ℝ))
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : A ∈ regionalWeylSpan L) : star A ∈ regionalWeylSpan L := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    rcases hA with ⟨x, hx, rfl⟩
    rw [physicalOscillatorWeyl_star]
    exact physicalOscillatorWeyl_mem_regionalWeylSpan L (L.neg_mem hx)
  | zero => simpa only [star_zero] using (regionalWeylSpan L).zero_mem
  | add A B hA hB ihA ihB =>
    simpa only [star_add] using (regionalWeylSpan L).add_mem ihA ihB
  | smul c A hA ih =>
    simpa only [star_smul] using (regionalWeylSpan L).smul_mem (star c) ih

/-- Continuous linear map for the regional Weyl polynomial algebra, of type `StarSubalgebra ℂ
(MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) where carrier`. -/
def regionalWeylPolynomialAlgebra (L : Submodule ℝ (Fin m × Fin 2 → ℝ)) :
    StarSubalgebra ℂ (MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) where
  carrier := regionalWeylSpan L
  zero_mem' := (regionalWeylSpan L).zero_mem
  add_mem' := (regionalWeylSpan L).add_mem
  mul_mem' := mul_mem_regionalWeylSpan L
  one_mem' := one_mem_regionalWeylSpan L
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (regionalWeylSpan L).smul_mem c (one_mem_regionalWeylSpan L)
  star_mem' := star_mem_regionalWeylSpan L

theorem regionalWeylPolynomialAlgebra_eq_adjoin (L : Submodule ℝ (Fin m × Fin 2 → ℝ)) :
    regionalWeylPolynomialAlgebra L = StarAlgebra.adjoin ℂ (regionalWeylGenerators L) := by
  apply le_antisymm
  · change Submodule.span ℂ (regionalWeylGenerators L) ≤
      (StarAlgebra.adjoin ℂ (regionalWeylGenerators L)).toSubalgebra.toSubmodule
    apply Submodule.span_le.mpr
    intro A hA
    exact StarAlgebra.subset_adjoin ℂ (regionalWeylGenerators L) hA
  · apply StarAlgebra.adjoin_le
    exact Submodule.subset_span

/-- Continuous linear map for the regional Weyl C⋆ algebra, of type `StarSubalgebra ℂ
(MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m)`. -/
def regionalWeylCStarAlgebra (L : Submodule ℝ (Fin m × Fin 2 → ℝ)) :
    StarSubalgebra ℂ (MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :=
  (regionalWeylPolynomialAlgebra L).topologicalClosure

end VacuumBellSeparation.Gaussian
