/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity.Basic

/-!
# High-contrast homogenization: Provider.Quenched.Prop42Scalar.CorrectedTiltTransfer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Corrected adapted-to-Euclidean scale transfer

The intermediate adapted scale is chosen as `m / 2 + n₀`.  The resulting
parity loss is made explicit and absorbed into a fixed prefactor.  All results
are scalar and independent of the probability carrier.
-/

namespace HCPolySupport.HighContrast.Quenched.Prop42Scalar

noncomputable section

/-- The intermediate scale for an outer Euclidean generation. -/
@[expose]
def correctedTiltScale (n₀ m : ℕ) : ℕ :=
  m / 2 + n₀

/-- The corrected intermediate scale satisfies both side conditions of the
adapted-to-Euclidean comparison. -/
theorem correctedTiltScale_admissible {n₀ m : ℕ} (hm : 2 * n₀ ≤ m) :
    2 * n₀ ≤ correctedTiltScale n₀ m ∧
      2 * (correctedTiltScale n₀ m - n₀) ≤ m := by
  dsimp [correctedTiltScale]
  omega

/-- The parity defect in the adapted decay is at most one generation. -/
theorem outer_sub_two_mul_le_two_mul_correctedTiltScale_sub_add_one
    {n₀ m : ℕ} (hm : 2 * n₀ ≤ m) :
    m - 2 * n₀ ≤
      2 * (correctedTiltScale n₀ m - 2 * n₀) + 1 := by
  dsimp [correctedTiltScale]
  omega

/-- The Euclidean comparison gap is at least half of the post-entry outer
generation. -/
theorem outer_sub_two_mul_le_two_mul_outer_sub_correctedTiltScale
    {n₀ m : ℕ} (hm : 2 * n₀ ≤ m) :
    m - 2 * n₀ ≤ 2 * (m - correctedTiltScale n₀ m) := by
  dsimp [correctedTiltScale]
  omega

/-- The hatted decay at the corrected intermediate scale loses only the fixed
parity factor `3^(κ/2)` relative to the outer rate `κ/2`. -/
theorem correctedTiltScale_decay_le
    {κ : ℝ} (hκ : 0 ≤ κ) {n₀ m : ℕ} (hm : 2 * n₀ ≤ m) :
    Real.rpow (3 : ℝ)
        (-κ * ((correctedTiltScale n₀ m - 2 * n₀ : ℕ) : ℝ)) ≤
      Real.rpow (3 : ℝ) (κ / 2) *
        Real.rpow (3 : ℝ) (-κ / 2 * ((m - 2 * n₀ : ℕ) : ℝ)) := by
  have hparity_nat :=
    outer_sub_two_mul_le_two_mul_correctedTiltScale_sub_add_one hm
  have hparity_real :
      ((m - 2 * n₀ : ℕ) : ℝ) ≤
        2 * ((correctedTiltScale n₀ m - 2 * n₀ : ℕ) : ℝ) + 1 := by
    exact_mod_cast hparity_nat
  have hexponent :
      -κ * ((correctedTiltScale n₀ m - 2 * n₀ : ℕ) : ℝ) ≤
        κ / 2 + -κ / 2 * ((m - 2 * n₀ : ℕ) : ℝ) := by
    nlinarith only [hκ, hparity_real]
  calc
    Real.rpow (3 : ℝ)
        (-κ * ((correctedTiltScale n₀ m - 2 * n₀ : ℕ) : ℝ))
        ≤ Real.rpow (3 : ℝ)
            (κ / 2 + -κ / 2 * ((m - 2 * n₀ : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
    _ = Real.rpow (3 : ℝ) (κ / 2) *
        Real.rpow (3 : ℝ) (-κ / 2 * ((m - 2 * n₀ : ℕ) : ℝ)) := by
      exact Real.rpow_add (by norm_num) _ _

/-- If `κ ≤ 1`, the Euclidean comparison error decays at least as fast as the
outer rate `κ/2`. -/
theorem correctedTiltScale_error_decay_le
    {κ : ℝ} (hκ_one : κ ≤ 1)
    {n₀ m : ℕ} (hm : 2 * n₀ ≤ m) :
    Real.rpow (3 : ℝ)
        (-((m - correctedTiltScale n₀ m : ℕ) : ℝ)) ≤
      Real.rpow (3 : ℝ) (-κ / 2 * ((m - 2 * n₀ : ℕ) : ℝ)) := by
  have hgap_nat :=
    outer_sub_two_mul_le_two_mul_outer_sub_correctedTiltScale hm
  have hgap_real :
      ((m - 2 * n₀ : ℕ) : ℝ) ≤
        2 * ((m - correctedTiltScale n₀ m : ℕ) : ℝ) := by
    exact_mod_cast hgap_nat
  have houter_nonneg : 0 ≤ ((m - 2 * n₀ : ℕ) : ℝ) := by positivity
  have herror_nonneg :
      0 ≤ ((m - correctedTiltScale n₀ m : ℕ) : ℝ) := by positivity
  have hrate :
      κ / 2 * ((m - 2 * n₀ : ℕ) : ℝ) ≤
        ((m - correctedTiltScale n₀ m : ℕ) : ℝ) := by
    nlinarith only [hκ_one, hgap_real, houter_nonneg, herror_nonneg]
  have hexponent :
      -((m - correctedTiltScale n₀ m : ℕ) : ℝ) ≤
        -κ / 2 * ((m - 2 * n₀ : ℕ) : ℝ) := by
    nlinarith only [hrate]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent

/-- Scalar transfer from an adapted decay and a Euclidean comparison error to
the corrected outer decay. -/
theorem corrected_tilt_transfer
    {F Fhat : ℕ → ℝ} {A κ : ℝ}
    (hA : 0 ≤ A) (hκ : 0 ≤ κ) (hκ_one : κ ≤ 1)
    {n₀ m : ℕ} (hm : 2 * n₀ ≤ m)
    (hhat : Fhat (correctedTiltScale n₀ m) ≤
      A * Real.rpow (3 : ℝ)
        (-κ * ((correctedTiltScale n₀ m - 2 * n₀ : ℕ) : ℝ)))
    (htransfer : F m ≤ Fhat (correctedTiltScale n₀ m) +
      A * Real.rpow (3 : ℝ)
        (-((m - correctedTiltScale n₀ m : ℕ) : ℝ))) :
    F m ≤
      A * (Real.rpow (3 : ℝ) (κ / 2) + 1) *
        Real.rpow (3 : ℝ) (-κ / 2 * ((m - 2 * n₀ : ℕ) : ℝ)) := by
  have hhat_decay := correctedTiltScale_decay_le hκ hm
  have herror_decay := correctedTiltScale_error_decay_le hκ_one hm
  have hhat_scaled := mul_le_mul_of_nonneg_left hhat_decay hA
  have herror_scaled := mul_le_mul_of_nonneg_left herror_decay hA
  calc
    F m ≤ Fhat (correctedTiltScale n₀ m) +
        A * Real.rpow (3 : ℝ)
          (-((m - correctedTiltScale n₀ m : ℕ) : ℝ)) := htransfer
    _ ≤ A * Real.rpow (3 : ℝ)
          (-κ * ((correctedTiltScale n₀ m - 2 * n₀ : ℕ) : ℝ)) +
        A * Real.rpow (3 : ℝ)
          (-((m - correctedTiltScale n₀ m : ℕ) : ℝ)) :=
      add_le_add hhat (le_rfl)
    _ ≤ A * (Real.rpow (3 : ℝ) (κ / 2) *
          Real.rpow (3 : ℝ) (-κ / 2 * ((m - 2 * n₀ : ℕ) : ℝ))) +
        A * Real.rpow (3 : ℝ) (-κ / 2 * ((m - 2 * n₀ : ℕ) : ℝ)) :=
      add_le_add hhat_scaled herror_scaled
    _ = A * (Real.rpow (3 : ℝ) (κ / 2) + 1) *
        Real.rpow (3 : ℝ) (-κ / 2 * ((m - 2 * n₀ : ℕ) : ℝ)) := by
      ring

end
end HCPolySupport.HighContrast.Quenched.Prop42Scalar
