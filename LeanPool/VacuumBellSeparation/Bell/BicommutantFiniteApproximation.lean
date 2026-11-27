/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.FiniteAmplification

/-!
# Simultaneous double-commutant approximation

Amplification preserves membership in the double commutant because every
block of a commuting operator is in the original commutant. The one-vector
orbit argument on the genuine Hilbert direct sum therefore approximates
any finite family simultaneously. No bound on the approximating operator
norm is asserted.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem mem_commutantOf_starSubalgebra_iff
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (B : H →L[ℂ] H) :
    B ∈ commutantOf (S : Set (H →L[ℂ] H)) ↔ ∀ A ∈ S, A * B = B * A := by
  rw [mem_commutantOf_iff, StarMemClass.star_coe_eq, Set.union_self]
  exact Set.mem_centralizer_iff

theorem finiteAmplification_mem_bicommutant
    (ι : Type*) [Fintype ι]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ generatedVNA (S : Set (H →L[ℂ] H))) :
    finiteAmplification ι T ∈ generatedVNA
      ((S.map (finiteAmplificationHom ι)) : Set
        (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))) := by
  classical
  rw [generatedVNA, VonNeumannAlgebra.mem_commutant_iff]
  intro B hB
  have hb := (mem_commutantOf_starSubalgebra_iff _ B).mp hB
  have hblocks : ∀ i j, amplificationBlock ι B i j ∈ commutantOf (S : Set (H →L[ℂ] H)) := by
    intro i j
    apply (mem_commutantOf_starSubalgebra_iff S _).mpr
    intro A hA
    exact (finiteAmplification_commutes_iff ι A B).mp
      (hb _ (StarSubalgebra.mem_map.mpr ⟨A, hA, rfl⟩)) i j
  have ht := VonNeumannAlgebra.mem_commutant_iff.mp hT
  exact ((finiteAmplification_commutes_iff ι T B).mpr
    (fun i j => (ht _ (hblocks i j)).symm)).symm

/-- Approximation on every member of an arbitrary finite indexed family. -/
theorem bicommutant_approximate_finite_family
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ generatedVNA (S : Set (H →L[ℂ] H)))
    {ι : Type*} [Finite ι] (x : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ A ∈ S, ∀ i, ‖T (x i) - A (x i)‖ < ε := by
  let _ : Fintype ι := Fintype.ofFinite ι
  classical
  have hAmp : finiteAmplification ι T ∈ generatedVNA
      ((S.map (finiteAmplificationHom ι)) : Set
        (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))) :=
    finiteAmplification_mem_bicommutant ι S hT
  obtain ⟨B, hB, hdist⟩ := bicommutant_approximate_one_vector
    (H := PiLp 2 (fun _ : ι => H)) (T := finiteAmplification ι T)
    (S.map (finiteAmplificationHom ι)) hAmp (WithLp.toLp 2 x) hε
  obtain ⟨A, hA, rfl⟩ := StarSubalgebra.mem_map.mp hB
  refine ⟨A, hA, fun i => ?_⟩
  have hi := PiLp.norm_apply_le
    (finiteAmplification ι T (WithLp.toLp 2 x) -
      finiteAmplification ι A (WithLp.toLp 2 x)) i
  exact lt_of_le_of_lt hi hdist

/-- The same conclusion for a literal finite set of vectors. -/
theorem bicommutant_approximate_finset
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ generatedVNA (S : Set (H →L[ℂ] H))) (s : Finset H)
    {ε : ℝ} (hε : 0 < ε) : ∃ A ∈ S, ∀ x ∈ s, ‖T x - A x‖ < ε := by
  obtain ⟨A, hA, hdist⟩ := bicommutant_approximate_finite_family S hT
    (fun x : s => (x : H)) hε
  exact ⟨A, hA, fun x hx => hdist ⟨x, hx⟩⟩

end VacuumBellSeparation
