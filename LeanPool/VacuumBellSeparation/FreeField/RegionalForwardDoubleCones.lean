/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.RegionalForwardSpatial
public import LeanPool.VacuumBellSeparation.FreeField.RegionalBallSeparation

/-!
# Unconditional eventual forward estimates on the physical double cones

The geometric separation proves disjointness and the chosen threshold
implies the finite scalar smallness condition. The established time-slice
identity identifies the same physical spacetime algebras.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian Metric
open scoped ENNReal InnerProductSpace

theorem regionalForward_smallness_of_threshold {A s r : ℝ}
    (hA : 0 < A) (hr : 0 < r) (hs : 0 < s)
    (hsmall : Real.sqrt (8 * r * A) ≤ s) : A / s ^ 2 ≤ 1 / (8 * r) := by
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg (8 * r * A)) hsmall 2
  rw [Real.sq_sqrt (by positivity)] at hp
  rw [div_le_div_iff₀ (pow_pos hs 2) (by positivity : 0 < 8 * r)]
  nlinarith

/-- For each order, one universal separation threshold gives the actual
forward event and covariance bounds on both full double-cone algebras. -/
theorem exists_uniform_doubleCone_forward (n : ℕ) :
    ∃ S A Q₀ : ℝ, 0 < S ∧ 0 < A ∧ 0 < Q₀ ∧
      ∀ (m : ℝ) (_ : 0 < m) (s : ℝ), S ≤ s →
        ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
          (V : FreeFieldVacuum m H),
          (∀ E ∈ effects (localAlgebra V (doubleCone (0, 0) 1)),
            ∀ P ∈ effects (localAlgebra V (doubleCone (0, spatialAxisDisplacement s 0) 1)),
              (⟪V.vacuum, (E * P) V.vacuum⟫_ℂ).re ^ ((n + 2 : ℕ) : ℝ) ≤
                Real.exp (8 * ((n + 2 : ℕ) : ℝ) * (A / s ^ 2)) *
                  ((⟪V.vacuum, E V.vacuum⟫_ℂ).re *
                    (⟪V.vacuum, P V.vacuum⟫_ℂ).re) ^ (((n + 2 : ℕ) : ℝ) - 1)) ∧
          eventConstPlus (vectorState V.vacuum V.vacuum_norm)
            (localAlgebra V (doubleCone (0, 0) 1))
            (localAlgebra V (doubleCone (0, spatialAxisDisplacement s 0) 1)) ((n + 2 : ℕ) : ℝ) ≤
              ENNReal.ofReal (Real.exp (8 * ((n + 2 : ℕ) : ℝ) * (A / s ^ 2))) ∧
          (∀ A₀ ∈ localAlgebra V (doubleCone (0, 0) 1),
            ∀ B₀ ∈ localAlgebra V (doubleCone (0, spatialAxisDisplacement s 0) 1),
              ‖A₀‖ ≤ 1 → ‖B₀‖ ≤ 1 → ‖vacuumComplexCovariance V.vacuum A₀ B₀‖ ≤ Q₀ / s) := by
  obtain ⟨Sgeo, A, Q₀, hSgeo, hA, hQ₀, hbound⟩ := exists_uniform_regional_forward n
  let r : ℝ := ((n + 2 : ℕ) : ℝ)
  have hr : 0 < r := by
    change (0 : ℝ) < ((n + 2 : ℕ) : ℝ)
    exact_mod_cast (show 0 < n + 2 by omega)
  let S := max 3 (max Sgeo (Real.sqrt (8 * r * A)))
  have hS : 0 < S := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) (le_max_left _ _)
  refine ⟨S, A, Q₀, hS, hA, hQ₀, ?_⟩
  intro m hm s hs H _ _ _ V
  have hs₀ : 0 < s := hS.trans_le hs
  have hs₂ : 2 ≤ s := by
    have h3 : 3 ≤ s := (le_max_left _ _).trans hs
    linarith
  have hgeo : Sgeo ≤ s := (le_max_left _ _).trans ((le_max_right _ _).trans hs)
  have hroot : Real.sqrt (8 * r * A) ≤ s :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hs)
  have hsmall := regionalForward_smallness_of_threshold hA hr hs₀ hroot
  have h := hbound m hm s hgeo hsmall H V
    (ball 0 1) (ball (spatialAxisDisplacement s 0) 1) (Set.Subset.refl _) (Set.Subset.refl _)
    (regionalForward_unit_balls_disjoint hs₂)
  simpa only [← localAlgebra_doubleCone_eq_timeZeroLocalAlgebra V hm (by norm_num : (0 : ℝ) < 1) 0,
    ← localAlgebra_doubleCone_eq_timeZeroLocalAlgebra V hm (by norm_num : (0 : ℝ) < 1)
      (spatialAxisDisplacement s 0)] using h

end VacuumBellSeparation
