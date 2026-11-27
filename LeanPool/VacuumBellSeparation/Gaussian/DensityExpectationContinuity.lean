/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.DensityExpectationIndependence
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Bounded weak and strong continuity of actual density expectations

The absolutely convergent square-root basis series is continuous along
uniformly bounded weakly convergent families, for arbitrary filters and
arbitrary Hilbert basis index types. Strong convergence is a direct
corollary. Neither a separability hypothesis nor an assumed normal-state
field is used. The common operator norm bound need hold only eventually.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Filter Topology

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
theorem tendsto_familyExpectation_of_weak (v : ι → E)
    (hv : Summable fun j => ‖v j‖ ^ 2) {α : Type*} {l : Filter α}
    {As : α → E →L[ℂ] E} {A : E →L[ℂ] E} {C : ℝ}
    (hweak : ∀ x y, Tendsto (fun i => inner ℂ x (As i y)) l (𝓝 (inner ℂ x (A y))))
    (hbounded : ∀ᶠ i in l, ‖As i‖ ≤ C) :
    Tendsto (fun i => familyExpectation v (As i)) l (𝓝 (familyExpectation v A)) := by
  apply tendsto_tsum_of_dominated_convergence (hv.mul_right C)
  · intro j
    exact hweak (v j) (v j)
  · filter_upwards [hbounded] with i hi j
    exact (norm_familyExpectation_term_le v (As i) j).trans
      (mul_le_mul_of_nonneg_left hi (sq_nonneg _))

omit [CompleteSpace E] in
theorem tendsto_familyExpectation_of_strong (v : ι → E)
    (hv : Summable fun j => ‖v j‖ ^ 2) {α : Type*} {l : Filter α}
    {As : α → E →L[ℂ] E} {A : E →L[ℂ] E} {C : ℝ}
    (hstrong : ∀ x, Tendsto (fun i => As i x) l (𝓝 (A x)))
    (hbounded : ∀ᶠ i in l, ‖As i‖ ≤ C) :
    Tendsto (fun i => familyExpectation v (As i)) l (𝓝 (familyExpectation v A)) :=
  tendsto_familyExpectation_of_weak v hv
    (fun _x y => tendsto_const_nhds.inner (hstrong y)) hbounded

/-- A genuine positive trace-class density yields continuity on every
operator-norm bounded weakly convergent net. -/
theorem tendsto_densityExpectation_of_weak (b : HilbertBasis ι ℂ E)
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass ρ)
    {α : Type*} {l : Filter α} {As : α → E →L[ℂ] E}
    {A : E →L[ℂ] E} {C : ℝ}
    (hweak : ∀ x y, Tendsto (fun i => inner ℂ x (As i y)) l (𝓝 (inner ℂ x (A y))))
    (hbounded : ∀ᶠ i in l, ‖As i‖ ≤ C) :
    Tendsto (fun i => densityExpectation b ρ (As i)) l (𝓝 (densityExpectation b ρ A)) :=
  tendsto_familyExpectation_of_weak _ (summable_sqrt_basis_norm_sq b hρ) hweak hbounded

/-- Strong continuity in the exact bounded-net form used by Kaplansky
approximations. The density may have kernel and need not have trace one. -/
theorem tendsto_densityExpectation_of_strong (b : HilbertBasis ι ℂ E)
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass ρ)
    {α : Type*} {l : Filter α} {As : α → E →L[ℂ] E}
    {A : E →L[ℂ] E} {C : ℝ}
    (hstrong : ∀ x, Tendsto (fun i => As i x) l (𝓝 (A x)))
    (hbounded : ∀ᶠ i in l, ‖As i‖ ≤ C) :
    Tendsto (fun i => densityExpectation b ρ (As i)) l (𝓝 (densityExpectation b ρ A)) :=
  tendsto_familyExpectation_of_strong _ (summable_sqrt_basis_norm_sq b hρ) hstrong hbounded

theorem tendsto_positiveDensityState_of_strong (b : HilbertBasis ι ℂ E)
    {ρ : E →L[ℂ] E} (hρ : 0 ≤ ρ) (ht : positiveTrace ρ = 1)
    {α : Type*} {l : Filter α} {As : α → E →L[ℂ] E}
    {A : E →L[ℂ] E} {C : ℝ}
    (hstrong : ∀ x, Tendsto (fun i => As i x) l (𝓝 (A x)))
    (hbounded : ∀ᶠ i in l, ‖As i‖ ≤ C) :
    Tendsto (fun i => positiveDensityState b hρ ht (As i)) l
      (𝓝 (positiveDensityState b hρ ht A)) :=
  tendsto_densityExpectation_of_strong b ⟨hρ, by rw [ht]; exact ENNReal.one_lt_top⟩
    hstrong hbounded

/-- Multiplication by a fixed bounded operator preserves the bounded
strong convergence needed by the actual density expectation. -/
theorem tendsto_densityExpectation_mul_right_of_strong (b : HilbertBasis ι ℂ E)
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass ρ) (B : E →L[ℂ] E)
    {α : Type*} {l : Filter α} {As : α → E →L[ℂ] E}
    {A : E →L[ℂ] E} {C : ℝ}
    (hstrong : ∀ x, Tendsto (fun i => As i x) l (𝓝 (A x)))
    (hbounded : ∀ᶠ i in l, ‖As i‖ ≤ C) :
    Tendsto (fun i => densityExpectation b ρ (As i * B)) l
      (𝓝 (densityExpectation b ρ (A * B))) := by
  apply tendsto_densityExpectation_of_strong b hρ
    (C := C * ‖B‖) (fun x => hstrong (B x))
  filter_upwards [hbounded] with i hi
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))

theorem tendsto_densityExpectation_mul_left_of_strong (b : HilbertBasis ι ℂ E)
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass ρ) (B : E →L[ℂ] E)
    {α : Type*} {l : Filter α} {As : α → E →L[ℂ] E}
    {A : E →L[ℂ] E} {C : ℝ}
    (hstrong : ∀ x, Tendsto (fun i => As i x) l (𝓝 (A x)))
    (hbounded : ∀ᶠ i in l, ‖As i‖ ≤ C) :
    Tendsto (fun i => densityExpectation b ρ (B * As i)) l
      (𝓝 (densityExpectation b ρ (B * A))) := by
  apply tendsto_densityExpectation_of_strong b hρ
    (As := fun i => B * As i) (A := B * A) (C := ‖B‖ * C)
    (fun x => B.continuous.continuousAt.tendsto.comp (hstrong x))
  filter_upwards [hbounded] with i hi
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hi (norm_nonneg _))

end VacuumBellSeparation.Gaussian
