/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.LocalSourceTotality
public import LeanPool.VacuumBellSeparation.FreeField.LiteralFockVacuum
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroAlgebra

/-!
# Local vacuum cyclicity for actual time-zero algebras

The full original Hilbert space is used throughout. The unitary equivalence
with literal Fock space preserves the physical Weyl labels and the vacuum.
The double-cone conclusion here has time-zero center; arbitrary temporal
centers require a separate covariance proof.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open MeasureTheory Fock
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {m : ℝ} (hm : 0 < m) (V : FreeFieldVacuum m H)

theorem FreeFieldVacuum.vacuum_cyclic_timeZero
    (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hbounded : Bornology.IsBounded U) (hopen : IsOpen U) (hne : U.Nonempty) :
    (Submodule.span ℂ {x : H | ∃ A : H →L[ℂ] H,
      A ∈ timeZeroLocalAlgebra V hm U ∧ x = A V.vacuum}).topologicalClosure = ⊤ := by
  let K := Submodule.span ℂ {x : H | ∃ A : H →L[ℂ] H,
    A ∈ timeZeroLocalAlgebra V hm U ∧ x = A V.vacuum}
  obtain ⟨T, hΩ, hW, _, _⟩ := V.exists_literalFock_equiv hm
  have horth : Kᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hz : T x = 0 := by
      apply sourceFock_eq_zero_of_coherent_orthogonal hm U hbounded hopen hne
      intro u
      have he : T (V.timeZeroWeyl hm u.1 V.vacuum) =
          coherentVector _ (timeZeroL2 hm u.1) := by
        change T (V.weyl (timeZeroSpacetimeRepresentative hm u.1) V.vacuum) = _
        rw [hW, hΩ, oneParticleL2_timeZeroSpacetimeRepresentative,
          literalFockWeyl_vacuum]
      rw [← he, T.inner_map_map]
      apply K.inner_left_of_mem_orthogonal ?_ hx
      apply Submodule.subset_span
      exact ⟨V.timeZeroWeyl hm u.1,
        V.timeZeroWeyl_mem_timeZeroLocalAlgebra hm u.1 u.2.1 u.2.2, rfl⟩
    apply T.injective
    simpa only [map_zero] using hz
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, horth]

theorem FreeFieldVacuum.vacuum_cyclic_timeZero_ball
    (x₀ : EuclideanSpace ℝ (Fin 3)) {R : ℝ} (hR : 0 < R) :
    (Submodule.span ℂ {x : H | ∃ A : H →L[ℂ] H,
      A ∈ timeZeroLocalAlgebra V hm (Metric.ball x₀ R) ∧ x = A V.vacuum}).topologicalClosure = ⊤ :=
  V.vacuum_cyclic_timeZero hm (Metric.ball x₀ R)
    Metric.isBounded_ball Metric.isOpen_ball (Metric.nonempty_ball.mpr hR)

include hm in
theorem FreeFieldVacuum.vacuum_cyclic_doubleCone_timeZero
    (x₀ : EuclideanSpace ℝ (Fin 3)) {R : ℝ} (hR : 0 < R) :
    (Submodule.span ℂ {x : H | ∃ A : H →L[ℂ] H,
      A ∈ localAlgebra V (doubleCone (0, x₀) R) ∧ x = A V.vacuum}).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← V.vacuum_cyclic_timeZero_ball hm x₀ hR]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro x ⟨A, hA, hx⟩
  exact ⟨A, timeZeroLocalAlgebra_ball_le V hm hR x₀ hA, hx⟩

end VacuumBellSeparation
