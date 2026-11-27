/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.VacuumComplexCovarianceDefs
public import LeanPool.VacuumBellSeparation.FreeField.CanonicalEffectExhaustion
public import LeanPool.VacuumBellSeparation.Bell.KaplanskyContractions

/-!
# Finite canonical exhaustion for selfadjoint contractions and covariance

The covariance is the actual complex vacuum covariance, with its complex
norm. Thus the limit argument does not need to assume the product of two
observables is selfadjoint. All approximants act in the same physical
vacuum Hilbert space and retain operator norm at most one.
-/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology
open scoped InnerProductSpace

variable {m : ℝ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem local_saContraction_finite_canonical_strong_approximation
    (V : FreeFieldVacuum m H) (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))
    {A : H →L[ℂ] H} (hA : A ∈ saContractions (timeZeroLocalAlgebra V hm U)) :
    ∃ As : (Finset H × ℕ) → (H →L[ℂ] H),
      (∀ i, ∃ S : Submodule ℝ TimeZeroSource, IsCanonicalSourceSystem U S ∧
        As i ∈ saContractions (canonicalSourceAlgebra V hm S)) ∧
      (∀ i, ‖As i‖ ≤ 1) ∧ ∀ x : H, Tendsto (fun i => As i x) atTop (𝓝 (A x)) := by
  have hmem : A ∈ generatedVNA (canonicalUnionStarAlgebra V hm U : Set (H →L[ℂ] H)) := by
    rw [generatedVNA_canonicalUnionStarAlgebra]
    exact hA.1
  obtain ⟨As, hAs, hstrong⟩ := exists_saContraction_strong_approximation
    (canonicalUnionStarAlgebra V hm U)
    (fun f B hB => cfc_mem_canonicalUnionStarAlgebra V hm U f hB) hmem hA.2.1 hA.2.2
  refine ⟨As, ?_, fun i => (hAs i).2.2, hstrong⟩
  intro i
  obtain ⟨S, hS, hmem⟩ := (mem_canonicalUnionStarAlgebra_iff V hm U _).mp (hAs i).1
  exact ⟨S, hS, hmem, (hAs i).2⟩

omit [CompleteSpace H] in
theorem tendsto_vacuumComplexCovariance {ι : Type*} {l : Filter ι}
    (Ω : H) {As Bs : ι → H →L[ℂ] H} {A B : H →L[ℂ] H} {C : ℝ}
    (hbound : ∀ i, ‖As i‖ ≤ C)
    (hA : ∀ x, Tendsto (fun i => As i x) l (𝓝 (A x)))
    (hB : ∀ x, Tendsto (fun i => Bs i x) l (𝓝 (B x))) :
    Tendsto (fun i => vacuumComplexCovariance Ω (As i) (Bs i)) l
      (𝓝 (vacuumComplexCovariance Ω A B)) := by
  have heval : Continuous (fun x : H => ⟪Ω, x⟫_ℂ) := by fun_prop
  exact (heval.continuousAt.tendsto.comp (strong_tendsto_mul_of_bounded hbound hA hB Ω)).sub
    ((heval.continuousAt.tendsto.comp (hA Ω)).mul (heval.continuousAt.tendsto.comp (hB Ω)))

/-- The full covariance clause of Lemma 2.3 for actual local contractions. -/
theorem canonical_covariance_bound_extends_to_local
    (V : FreeFieldVacuum m H) (hm : 0 < m)
    (U W : Set (EuclideanSpace ℝ (Fin 3))) (C : ℝ)
    (hfinite : ∀ S T : Submodule ℝ TimeZeroSource,
      IsCanonicalSourceSystem U S → IsCanonicalSourceSystem W T →
      ∀ A ∈ saContractions (canonicalSourceAlgebra V hm S),
      ∀ B ∈ saContractions (canonicalSourceAlgebra V hm T),
        ‖vacuumComplexCovariance V.vacuum A B‖ ≤ C)
    {A B : H →L[ℂ] H} (hA : A ∈ saContractions (timeZeroLocalAlgebra V hm U))
    (hB : B ∈ saContractions (timeZeroLocalAlgebra V hm W)) :
    ‖vacuumComplexCovariance V.vacuum A B‖ ≤ C := by
  classical
  obtain ⟨As, hAs, hAnorm, hAlim⟩ := local_saContraction_finite_canonical_strong_approximation V
    hm U hA
  obtain ⟨Bs, hBs, hBnorm, hBlim⟩ := local_saContraction_finite_canonical_strong_approximation V
    hm W hB
  have ht := tendsto_vacuumComplexCovariance V.vacuum
    (l := (atTop : Filter (Finset H × ℕ)) ×ˢ (atTop : Filter (Finset H × ℕ)))
    (fun ij => hAnorm ij.1) (fun x => (hAlim x).comp tendsto_fst)
    (fun x => (hBlim x).comp tendsto_snd)
  apply isClosed_Iic.mem_of_tendsto ht.norm
  apply Eventually.of_forall
  intro ij
  obtain ⟨S, hS, hA'⟩ := hAs ij.1
  obtain ⟨T, hT, hB'⟩ := hBs ij.2
  exact hfinite S T hS hT (As ij.1) hA' (Bs ij.2) hB'

theorem canonical_covariance_bound_extends_to_doubleCones
    (V : FreeFieldVacuum m H) (hm : 0 < m)
    (x₀ y₀ : EuclideanSpace ℝ (Fin 3)) {R S : ℝ} (hR : 0 < R) (hS : 0 < S) (C : ℝ)
    (hfinite : ∀ K L : Submodule ℝ TimeZeroSource,
      IsCanonicalSourceSystem (Metric.ball x₀ R) K → IsCanonicalSourceSystem (Metric.ball y₀ S) L →
      ∀ A ∈ saContractions (canonicalSourceAlgebra V hm K),
      ∀ B ∈ saContractions (canonicalSourceAlgebra V hm L),
        ‖vacuumComplexCovariance V.vacuum A B‖ ≤ C)
    {A B : H →L[ℂ] H} (hA : A ∈ saContractions (localAlgebra V (doubleCone (0, x₀) R)))
    (hB : B ∈ saContractions (localAlgebra V (doubleCone (0, y₀) S))) :
    ‖vacuumComplexCovariance V.vacuum A B‖ ≤ C := by
  rw [localAlgebra_doubleCone_eq_timeZeroLocalAlgebra V hm hR x₀] at hA
  rw [localAlgebra_doubleCone_eq_timeZeroLocalAlgebra V hm hS y₀] at hB
  exact canonical_covariance_bound_extends_to_local V hm _ _ C hfinite hA hB

end VacuumBellSeparation
