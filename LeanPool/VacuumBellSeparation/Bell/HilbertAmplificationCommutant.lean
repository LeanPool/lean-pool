/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.HilbertAmplification
public import LeanPool.VacuumBellSeparation.FreeField.Isotony

/-!
# Actual amplified double commutants

Continuity on single-coordinate vectors proves the block commutation
criterion for arbitrary Hilbert direct sums. It transports the original
double commutant into the amplified one. Conversely, the coordinate
matrix units extract an actual underlying operator from every member of
the amplified double commutant, when an anchor coordinate is given.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (ι : Type*)

omit [CompleteSpace H] in
theorem hilbertAmplification_commutes_iff (A : H →L[ℂ] H)
    (B : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2) :
    hilbertAmplification ι A * B = B * hilbertAmplification ι A ↔
      ∀ i j, A * hilbertAmplificationBlock ι B i j = hilbertAmplificationBlock ι B i j * A := by
  classical
  constructor
  · intro h i j
    ext x
    have he := congrArg (fun C => C (lp.single 2 j x) i) h
    simpa only [mul_apply_eq_comp, hilbertAmplification_apply,
      hilbertAmplification_single, hilbertAmplificationBlock_apply] using he
  · intro h
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro j
    ext x i
    simpa only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
      mul_apply_eq_comp, hilbertAmplification_apply,
      hilbertAmplification_single, hilbertAmplificationBlock_apply] using
        congrArg (fun C : H →L[ℂ] H => C x) (h i j)

theorem hilbertAmplification_mem_generatedVNA (S : Set (H →L[ℂ] H))
    {T : H →L[ℂ] H} (hT : T ∈ generatedVNA S) :
    hilbertAmplification ι T ∈ generatedVNA (hilbertAmplification ι '' S) := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro B hB
  have hblocks : ∀ i j, hilbertAmplificationBlock ι B i j ∈ commutantOf S := by
    intro i j
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro A hA
    have hb := ((StarSubalgebra.mem_centralizer_iff ℂ).mp hB) _ ⟨A, hA, rfl⟩
    refine ⟨(hilbertAmplification_commutes_iff ι A B).mp hb.1 i j, ?_⟩
    have hs : hilbertAmplification ι (star A) * B = B * hilbertAmplification ι (star A) := by
      simpa only [hilbertAmplification_star] using hb.2
    exact (hilbertAmplification_commutes_iff ι (star A) B).mp hs i j
  exact ((hilbertAmplification_commutes_iff ι T B).mpr
    (fun i j => (VonNeumannAlgebra.mem_commutant_iff.mp hT _ (hblocks i j)).symm)).symm

theorem hilbertCoordinateUnit_mem_commutant (S : Set (H →L[ℂ] H)) (i j : ι) :
    hilbertCoordinateUnit (H := H) ι i j ∈ commutantOf (hilbertAmplification ι '' S) := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  rintro _ ⟨A, hA, rfl⟩
  refine ⟨hilbertAmplification_commutes_coordinateUnit ι A i j, ?_⟩
  rw [← hilbertAmplification_star]
  exact hilbertAmplification_commutes_coordinateUnit ι (star A) i j

/-- Every amplified-algebra operator is the amplification of one actual
bounded operator. No representation-equivalence assumption is used. -/
theorem eq_hilbertAmplification_of_mem_generatedVNA
    (S : Set (H →L[ℂ] H)) (k : ι)
    {B : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2}
    (hB : B ∈ generatedVNA (hilbertAmplification ι '' S)) :
    B = hilbertAmplification ι (hilbertAmplificationBlock ι B k k) :=
  eq_hilbertAmplification_of_commutes_coordinateUnits ι B k (fun i j =>
    (VonNeumannAlgebra.mem_commutant_iff.mp hB _
      (hilbertCoordinateUnit_mem_commutant ι S i j)).symm)

end VacuumBellSeparation
