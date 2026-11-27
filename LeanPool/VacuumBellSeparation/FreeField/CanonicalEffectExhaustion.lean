/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CanonicalUnionStarAlgebra
public import LeanPool.VacuumBellSeparation.FreeField.TimeSliceTheorem
public import LeanPool.VacuumBellSeparation.Bell.KaplanskyEffects
public import LeanPool.VacuumBellSeparation.Bell.StrongExpectationLimits

/-!
# Passage from actual finite canonical effects to all local effects

The approximants lie in genuine finite canonical algebras in the original
vacuum Hilbert space. Independent nets and their uniform norm bounds pass
every continuous non-strict scalar inequality in the three actual vacuum
expectations to all regional effects. The double-cone statement uses the
proved same-representation time-slice identity.
-/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology

variable {m : ℝ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem local_effect_finite_canonical_strong_approximation
    (V : FreeFieldVacuum m H) (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))
    {E : H →L[ℂ] H} (hE : E ∈ effects (timeZeroLocalAlgebra V hm U)) :
    ∃ Es : (Finset H × ℕ) → (H →L[ℂ] H),
      (∀ i, ∃ S : Submodule ℝ TimeZeroSource, IsCanonicalSourceSystem U S ∧
        Es i ∈ effects (canonicalSourceAlgebra V hm S)) ∧
      (∀ i, ‖Es i‖ ≤ 1) ∧ ∀ x : H, Tendsto (fun i => Es i x) atTop (𝓝 (E x)) := by
  classical
  have hE0 := ContinuousLinearMap.nonneg_iff_isPositive.mpr hE.2.1
  have hE1 : E ≤ 1 := sub_nonneg.mp (ContinuousLinearMap.nonneg_iff_isPositive.mpr hE.2.2)
  have hmem : E ∈ generatedVNA (canonicalUnionStarAlgebra V hm U : Set (H →L[ℂ] H)) := by
    rw [generatedVNA_canonicalUnionStarAlgebra]
    exact hE.1
  obtain ⟨Es, hEs, hstrong⟩ := exists_effect_strong_approximation (canonicalUnionStarAlgebra V hm U)
    (fun f A hA => cfc_mem_canonicalUnionStarAlgebra V hm U f hA) hmem hE0 hE1
  refine ⟨Es, ?_, ?_, hstrong⟩
  · intro i
    obtain ⟨S, hS, hA⟩ := (mem_canonicalUnionStarAlgebra_iff V hm U _).mp (hEs i).1
    exact ⟨S, hS, hA, ContinuousLinearMap.nonneg_iff_isPositive.mp (hEs i).2.1,
      ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr (hEs i).2.2)⟩
  · intro i
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg (Es i) (hEs i).2.1).mpr (hEs i).2.2

/-- Lemma 2.3 for its continuous closed-inequality applications, with actual
effects in arbitrary two time-zero regions and a fixed original vacuum. -/
theorem canonical_effect_inequality_extends_to_local
    (V : FreeFieldVacuum m H) (hm : 0 < m)
    (U W : Set (EuclideanSpace ℝ (Fin 3)))
    (f : ℝ × ℝ × ℝ → ℝ) (hf : Continuous f)
    (hfinite : ∀ S T : Submodule ℝ TimeZeroSource,
      IsCanonicalSourceSystem U S → IsCanonicalSourceSystem W T →
      ∀ E ∈ effects (canonicalSourceAlgebra V hm S),
      ∀ P ∈ effects (canonicalSourceAlgebra V hm T),
        f (vacuumExpectationTriple V.vacuum E P) ≤ 0)
    {E P : H →L[ℂ] H} (hE : E ∈ effects (timeZeroLocalAlgebra V hm U))
    (hP : P ∈ effects (timeZeroLocalAlgebra V hm W)) :
    f (vacuumExpectationTriple V.vacuum E P) ≤ 0 := by
  classical
  obtain ⟨Es, hEs, hEnorm, hElim⟩ := local_effect_finite_canonical_strong_approximation V hm U hE
  obtain ⟨Ps, hPs, hPnorm, hPlim⟩ := local_effect_finite_canonical_strong_approximation V hm W hP
  apply vacuum_inequality_of_independent_strong_limits V.vacuum hEnorm hElim hPlim f hf
  apply Eventually.of_forall
  intro ij
  obtain ⟨S, hS, hE'⟩ := hEs ij.1
  obtain ⟨T, hT, hP'⟩ := hPs ij.2
  exact hfinite S T hS hT (Es ij.1) hE' (Ps ij.2) hP'

/-- The same conclusion for the original spacetime double-cone algebras. -/
theorem canonical_effect_inequality_extends_to_doubleCones
    (V : FreeFieldVacuum m H) (hm : 0 < m)
    (x₀ y₀ : EuclideanSpace ℝ (Fin 3)) {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (f : ℝ × ℝ × ℝ → ℝ) (hf : Continuous f)
    (hfinite : ∀ K L : Submodule ℝ TimeZeroSource,
      IsCanonicalSourceSystem (Metric.ball x₀ R) K →
      IsCanonicalSourceSystem (Metric.ball y₀ S) L →
      ∀ E ∈ effects (canonicalSourceAlgebra V hm K),
      ∀ P ∈ effects (canonicalSourceAlgebra V hm L),
        f (vacuumExpectationTriple V.vacuum E P) ≤ 0)
    {E P : H →L[ℂ] H} (hE : E ∈ effects (localAlgebra V (doubleCone (0, x₀) R)))
    (hP : P ∈ effects (localAlgebra V (doubleCone (0, y₀) S))) :
    f (vacuumExpectationTriple V.vacuum E P) ≤ 0 := by
  rw [localAlgebra_doubleCone_eq_timeZeroLocalAlgebra V hm hR x₀] at hE
  rw [localAlgebra_doubleCone_eq_timeZeroLocalAlgebra V hm hS y₀] at hP
  exact canonical_effect_inequality_extends_to_local V hm _ _ f hf hfinite hE hP

end VacuumBellSeparation
