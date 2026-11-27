/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.RegionalForwardDoubleCones
public import LeanPool.VacuumBellSeparation.Constants.Parameters

/-!
# The literal forward cluster constant

A single enlargement of the universal forward envelope gives the exact
manuscript relation Q₀ = 4 sqrt(A₊/b). The same A₊ controls the event
estimate. All bounds concern the original full double-cone algebras.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian
open scoped ENNReal InnerProductSpace

theorem le_four_sqrt_enlarged_forward {Q b A : ℝ}
    (hQ : 0 ≤ Q) (hb : 0 < b) (hA : b * (Q / 4) ^ 2 ≤ A) :
    Q ≤ 4 * Real.sqrt (A / b) := by
  have hsq : (Q / 4) ^ 2 ≤ A / b :=
    (le_div_iff₀ hb).mpr (by simpa only [mul_comm] using hA)
  have hroot := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (div_nonneg hQ (by norm_num))] at hroot
  linarith

/-- The existential forward constant is fixed once, before mass,
separation and representation. Its literal cluster constant also bounds
arbitrary complex contractions. -/
theorem exists_uniform_doubleCone_forward_exact_constant :
    ∃ S Aplus : ℝ, 0 < S ∧ 0 < Aplus ∧
      ∀ (m : ℝ) (_ : 0 < m) (s : ℝ), S ≤ s →
        ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
          (V : FreeFieldVacuum m H),
          (∀ E ∈ effects (localAlgebra V (doubleCone (0, 0) 1)),
            ∀ P ∈ effects (localAlgebra V (doubleCone (0, spatialAxisDisplacement s 0) 1)),
              (⟪V.vacuum, (E * P) V.vacuum⟫_ℂ).re ^ rPlus ≤
                Real.exp (8 * rPlus * (Aplus / s ^ 2)) *
                  ((⟪V.vacuum, E V.vacuum⟫_ℂ).re *
                    (⟪V.vacuum, P V.vacuum⟫_ℂ).re) ^ (rPlus - 1)) ∧
          eventConstPlus (vectorState V.vacuum V.vacuum_norm)
            (localAlgebra V (doubleCone (0, 0) 1))
            (localAlgebra V (doubleCone (0, spatialAxisDisplacement s 0) 1)) rPlus ≤
              ENNReal.ofReal (Real.exp (8 * rPlus * (Aplus / s ^ 2))) ∧
          (∀ A₀ ∈ localAlgebra V (doubleCone (0, 0) 1),
            ∀ B₀ ∈ localAlgebra V (doubleCone (0, spatialAxisDisplacement s 0) 1),
              ‖A₀‖ ≤ 1 → ‖B₀‖ ≤ 1 → ‖vacuumComplexCovariance V.vacuum A₀ B₀‖ ≤
                (4 * Real.sqrt (Aplus / expB rPlus)) / s) := by
  obtain ⟨S, A, Q, hS, hA, hQ, hbound⟩ := exists_uniform_doubleCone_forward 1048574
  have hr : (((1048574 + 2 : ℕ) : ℝ)) = rPlus := by norm_num [rPlus]
  have hb : 0 < expB rPlus := by norm_num [expB, rPlus]
  let Aplus := max A (expB rPlus * (Q / 4) ^ 2)
  have hAA : A ≤ Aplus := le_max_left _ _
  have hAplus : 0 < Aplus := hA.trans_le hAA
  have hQQ : Q ≤ 4 * Real.sqrt (Aplus / expB rPlus) :=
    le_four_sqrt_enlarged_forward hQ.le hb (le_max_right _ _)
  refine ⟨S, Aplus, hS, hAplus, ?_⟩
  intro m hm s hs H _ _ _ V
  have hs₀ := hS.trans_le hs
  obtain ⟨he, hk, hc⟩ := hbound m hm s hs H V
  rw [hr] at he hk
  have hexp : Real.exp (8 * rPlus * (A / s ^ 2)) ≤
      Real.exp (8 * rPlus * (Aplus / s ^ 2)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hAA (sq_nonneg s))
      (by norm_num [rPlus])
  refine ⟨?_, hk.trans (ENNReal.ofReal_le_ofReal hexp), ?_⟩
  · intro E hE P hP
    apply (he E hE P hP).trans
    apply mul_le_mul_of_nonneg_right hexp
    exact Real.rpow_nonneg (mul_nonneg
      (hE.2.1.re_inner_nonneg_right V.vacuum) (hP.2.1.re_inner_nonneg_right V.vacuum)) _
  · intro A₀ hA₀ B₀ hB₀ hAn hBn
    exact (hc A₀ hA₀ B₀ hB₀ hAn hBn).trans
      (div_le_div_of_nonneg_right hQQ hs₀.le)

end VacuumBellSeparation
