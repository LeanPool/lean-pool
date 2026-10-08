/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1FixedProjectionAlgebra

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1FixedProjectionDecayCore

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fixed-projection decay in a coefficient-energy space

One exact minimizer is fixed at the base scale.  At an observation scale its
residual is split into the current minimizing residual and the telescoped
finite-affine increments.  Geometric excess decay absorbs the latter without
changing the requested exponent.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Comparison of a fixed competitor with the current minimizer. -/
theorem sqrt_normalizedEnergy_fixed_le_minimizer_add_slopeDifference
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < volume U) (hvoltop : volume U ≠ ⊤)
    (T : Vec d →ₗ[ℝ] HilbertVectorL2 U) (J : HilbertVectorL2 U)
    (bFixed bMin : Vec d) :
    Real.sqrt (normalizedLocalSymmetricEnergy hEll (J - T bFixed)) ≤
      Real.sqrt (normalizedLocalSymmetricEnergy hEll (J - T bMin)) +
        Real.sqrt (normalizedLocalSymmetricEnergy hEll
          (T (bMin - bFixed))) := by
  have hsplit : J - T bFixed = (J - T bMin) + T (bMin - bFixed) := by
    rw [map_sub]
    abel
  rw [hsplit]
  exact sqrt_normalizedLocalSymmetricEnergy_add_le
    hEll hvol hvoltop _ _

/-- The same base-selected slope has the desired real-rate decay at every
intermediate scale once the current-minimizer row and the propagated
successive-increment rows have their bounds. -/
theorem sqrt_normalizedEnergy_fixed_realRateDecay_of_incrementRows
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < volume U) (hvoltop : volume U ≠ ⊤)
    (T : Vec d →ₗ[ℝ] HilbertVectorL2 U) (J : HilbertVectorL2 U)
    (b : ℤ → Vec d) {n q m : ℤ} (hnq : n ≤ q) (hqm : q ≤ m)
    (eta A B terminalEnergy : ℝ) (heta : 1 / 2 ≤ eta)
    (hB : 0 ≤ B) (hterminal : 0 ≤ terminalEnergy)
    (hmin : Real.sqrt
        (normalizedLocalSymmetricEnergy hEll (J - T (b q))) ≤
      A * Real.rpow 3 (-eta * ((m : ℝ) - (q : ℝ))) * terminalEnergy)
    (hincrement : ∀ j ∈ Finset.Ico n q,
      Real.sqrt (normalizedLocalSymmetricEnergy hEll
          (T (b (j + 1) - b j))) ≤
        B * Real.rpow 3 (((q : ℝ) - (j : ℝ)) / 4) *
          Real.rpow 3 (-eta * ((m : ℝ) - (j : ℝ))) * terminalEnergy) :
    Real.sqrt (normalizedLocalSymmetricEnergy hEll (J - T (b n))) ≤
      (A + B * (1 / (1 - Real.rpow 3 (-(eta - 1 / 4))))) *
        Real.rpow 3 (-eta * ((m : ℝ) - (q : ℝ))) * terminalEnergy := by
  let rate : ℝ := Real.rpow 3 (-eta * ((m : ℝ) - (q : ℝ)))
  let geom : ℝ := 1 / (1 - Real.rpow 3 (-(eta - 1 / 4)))
  have hrate : 0 ≤ rate := Real.rpow_nonneg (by norm_num) _
  have hgeom : 0 ≤ geom := by
    have hc : 0 < eta - 1 / 4 := by linarith only [heta]
    have hr : Real.rpow 3 (-(eta - 1 / 4)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hc)
    exact div_nonneg zero_le_one (sub_nonneg.mpr hr.le)
  have hslope := sqrt_normalizedEnergy_linearMap_sub_le_sum_Ico_int
    hEll hvol hvoltop T b hnq
  have hsumRows :
      ∑ j ∈ Finset.Ico n q,
          Real.sqrt (normalizedLocalSymmetricEnergy hEll
            (T (b (j + 1) - b j))) ≤
        B * rate * geom * terminalEnergy := by
    calc
      _ ≤ ∑ j ∈ Finset.Ico n q,
          B * Real.rpow 3 (((q : ℝ) - (j : ℝ)) / 4) *
            Real.rpow 3 (-eta * ((m : ℝ) - (j : ℝ))) * terminalEnergy :=
        Finset.sum_le_sum hincrement
      _ = B * (∑ j ∈ Finset.Ico n q,
          Real.rpow 3 (((q : ℝ) - (j : ℝ)) / 4) *
            Real.rpow 3 (-eta * ((m : ℝ) - (j : ℝ)))) * terminalEnergy := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ ≤ B * (rate * geom) * terminalEnergy := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (by simpa only [rate, geom] using
              sum_quarterGrowth_mul_realRateDecay_le eta heta hnq hqm)
            hB)
          hterminal
      _ = B * rate * geom * terminalEnergy := by ring
  have hfixed := sqrt_normalizedEnergy_fixed_le_minimizer_add_slopeDifference
    hEll hvol hvoltop T J (b n) (b q)
  have hslopeBound : Real.sqrt
      (normalizedLocalSymmetricEnergy hEll (T (b q - b n))) ≤
        B * rate * geom * terminalEnergy := hslope.trans hsumRows
  calc
    Real.sqrt (normalizedLocalSymmetricEnergy hEll (J - T (b n))) ≤
        Real.sqrt (normalizedLocalSymmetricEnergy hEll (J - T (b q))) +
          Real.sqrt (normalizedLocalSymmetricEnergy hEll
            (T (b q - b n))) := hfixed
    _ ≤ A * rate * terminalEnergy +
          B * rate * geom * terminalEnergy := add_le_add hmin hslopeBound
    _ = (A + B * geom) * rate * terminalEnergy := by ring

end

end Root
end HighContrast
end HCPolySupport
