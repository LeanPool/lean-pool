/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.HilbertAmplificationOrder

/-!
# Faithfulness and algebra membership of amplified operators

An explicit coordinate makes diagonal amplification injective. Applying
the original commutant diagonally proves that the extracted diagonal block
of an amplified-algebra operator belongs to the original generated algebra.
Thus extraction preserves the actual selected generator subalgebras.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (ι : Type*)

omit [CompleteSpace H] in
theorem hilbertAmplification_injective (k : ι) :
    Function.Injective (hilbertAmplification (H := H) ι) := by
  classical
  intro A B h
  ext x
  have he := congrArg (fun T => T (lp.single 2 k x) k) h
  simpa only [hilbertAmplification_apply, lp.single_apply_self] using he

theorem hilbertAmplification_mem_commutant (S : Set (H →L[ℂ] H))
    {X : H →L[ℂ] H} (hX : X ∈ commutantOf S) :
    hilbertAmplification ι X ∈ commutantOf (hilbertAmplification ι '' S) := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  rintro _ ⟨A, hA, rfl⟩
  obtain ⟨h, hs⟩ := (StarSubalgebra.mem_centralizer_iff ℂ).mp hX A hA
  have hh := congrArg (fun T : H →L[ℂ] H => (hilbertAmplificationHom (H := H) ι) T) h
  have hhs := congrArg (fun T : H →L[ℂ] H => (hilbertAmplificationHom (H := H) ι) T) hs
  constructor
  · change (hilbertAmplificationHom (H := H) ι) A *
        (hilbertAmplificationHom (H := H) ι) X =
        (hilbertAmplificationHom (H := H) ι) X *
          (hilbertAmplificationHom (H := H) ι) A
    simpa only [map_mul] using hh
  · change star ((hilbertAmplificationHom (H := H) ι) A) *
        (hilbertAmplificationHom (H := H) ι) X =
        (hilbertAmplificationHom (H := H) ι) X *
          star ((hilbertAmplificationHom (H := H) ι) A)
    simpa only [map_mul, map_star] using hhs

theorem hilbertAmplificationBlock_mem_generatedVNA (S : Set (H →L[ℂ] H)) (k : ι)
    {B : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2}
    (hB : B ∈ generatedVNA (hilbertAmplification ι '' S)) :
    hilbertAmplificationBlock ι B k k ∈ generatedVNA S := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro X hX
  have h := VonNeumannAlgebra.mem_commutant_iff.mp hB _
    (hilbertAmplification_mem_commutant ι S hX)
  rw [eq_hilbertAmplification_of_mem_generatedVNA ι S k hB] at h
  apply hilbertAmplification_injective ι k
  change (hilbertAmplificationHom (H := H) ι) (X * hilbertAmplificationBlock ι B k k) =
    (hilbertAmplificationHom (H := H) ι) (hilbertAmplificationBlock ι B k k * X)
  change (hilbertAmplificationHom (H := H) ι) X *
      (hilbertAmplificationHom (H := H) ι) (hilbertAmplificationBlock ι B k k) =
      (hilbertAmplificationHom (H := H) ι) (hilbertAmplificationBlock ι B k k) *
        (hilbertAmplificationHom (H := H) ι) X at h
  simpa only [map_mul] using h

end VacuumBellSeparation
