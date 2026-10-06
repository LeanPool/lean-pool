/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop42Scalar.DecayDelay

/-!
# High-contrast homogenization: Provider.Quenched.Prop42Scalar.CorrectedTiltEndpoint

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Scalar endpoint for the corrected tilt transfer

This file composes the halfway scale choice with prefactor
absorption and polynomial delay accounting.  The only inputs are an adapted
tail, its Euclidean comparison, and scalar power bounds.
-/

namespace HCPolySupport.HighContrast.Quenched.Prop42Scalar

noncomputable section

/-- An adapted tail and its corrected halfway transfer yield a unit-prefactor
Euclidean tail after a power-bounded delay. -/
theorem exists_power_bounded_unit_decay_of_corrected_tilt
    {F Fhat : ℕ → ℝ} {A κ base Centry Cpref : ℝ}
    (hA : 0 ≤ A) (hκ : 0 < κ) (hκ_one : κ ≤ 1)
    (hbase : 3 ≤ base) (hCpref : 0 ≤ Cpref) {n₀ : ℕ}
    (hentry : (3 : ℝ) ^ (2 * n₀) ≤ Real.rpow base Centry)
    (hpref :
      A * (Real.rpow (3 : ℝ) (κ / 2) + 1) ≤ Real.rpow base Cpref)
    (hhat : ∀ n : ℕ, 2 * n₀ ≤ n →
      Fhat n ≤ A * Real.rpow (3 : ℝ)
        (-κ * ((n - 2 * n₀ : ℕ) : ℝ)))
    (htransfer : ∀ m : ℕ, 2 * n₀ ≤ m →
      F m ≤ Fhat (correctedTiltScale n₀ m) +
        A * Real.rpow (3 : ℝ)
          (-((m - correctedTiltScale n₀ m : ℕ) : ℝ))) :
    ∃ m₀ : ℕ,
      (3 : ℝ) ^ m₀ ≤
        Real.rpow base (Centry + (1 + Cpref / (κ / 2))) ∧
      ∀ j : ℕ,
        F (m₀ + j) ≤ Real.rpow (3 : ℝ) (-(κ / 2) * (j : ℝ)) := by
  let α : ℝ := κ / 2
  let Aout : ℝ := A * (Real.rpow (3 : ℝ) (κ / 2) + 1)
  have hα : 0 < α := by
    dsimp [α]
    linarith only [hκ]
  have houter : ∀ m : ℕ, 2 * n₀ ≤ m →
      F m ≤ Aout * Real.rpow (3 : ℝ)
        (-α * ((m - 2 * n₀ : ℕ) : ℝ)) := by
    intro m hm
    have hn_admissible : 2 * n₀ ≤ correctedTiltScale n₀ m :=
      (correctedTiltScale_admissible hm).1
    have hhat_m := hhat (correctedTiltScale n₀ m) hn_admissible
    have hresult := corrected_tilt_transfer hA hκ.le hκ_one hm hhat_m (htransfer m hm)
    simpa only [Aout, α, neg_div] using hresult
  let m₀ := totalDecayDelay n₀ Aout α
  refine ⟨m₀, ?_, ?_⟩
  · dsimp [m₀]
    simpa only [Aout, α, Real.rpow_natCast, Real.rpow_def_of_pos,
      Real.rpow_def_of_nonneg, Real.rpow_natCast, Real.rpow_eq_pow] using
      (three_pow_totalDecayDelay_le_rpow
        (A := Aout) (α := α) hα hbase hCpref hentry hpref)
  · intro j
    dsimp [m₀]
    exact unit_prefactor_decay_after_totalDecayDelay hα houter j

end
end HCPolySupport.HighContrast.Quenched.Prop42Scalar
