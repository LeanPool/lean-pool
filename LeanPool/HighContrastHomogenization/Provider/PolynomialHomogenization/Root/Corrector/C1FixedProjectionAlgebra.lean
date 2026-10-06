/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1FiniteRateComposition
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1CoefficientEnergySeminorm
public import LeanPool.HighContrastHomogenization.Provider.Transport.DiscreteConvolution

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1FixedProjectionAlgebra

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite geometric control for a fixed affine slope

The affine slope chosen on the smallest cube is compared with the exact
minimizer on every larger cube by summing consecutive slope increments.  The
quarter-power energy growth is summable against any decay exponent at least
one half.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open scoped BigOperators

noncomputable section

/-- A linear family in a coefficient-energy space telescopes over integer
scales. -/
theorem sqrt_normalizedEnergy_linearMap_sub_le_sum_Ico_int
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < MeasureTheory.volume U)
    (hvoltop : MeasureTheory.volume U ≠ ⊤)
    (T : Vec d →ₗ[ℝ] HilbertVectorL2 U) (b : ℤ → Vec d)
    {n q : ℤ} (hnq : n ≤ q) :
    Real.sqrt (normalizedLocalSymmetricEnergy hEll (T (b q - b n))) ≤
      ∑ j ∈ Finset.Ico n q,
        Real.sqrt (normalizedLocalSymmetricEnergy hEll
          (T (b (j + 1) - b j))) := by
  induction q, hnq using Int.leInduction with
  | base => simp [normalizedLocalSymmetricEnergy]
  | succ q hnq ih =>
      have hsplit : T (b (q + 1) - b n) =
          T (b (q + 1) - b q) + T (b q - b n) := by
        rw [← map_add]
        congr 1
        abel
      rw [hsplit]
      calc
        Real.sqrt (normalizedLocalSymmetricEnergy hEll
            (T (b (q + 1) - b q) + T (b q - b n))) ≤
            Real.sqrt (normalizedLocalSymmetricEnergy hEll
              (T (b (q + 1) - b q))) +
              Real.sqrt (normalizedLocalSymmetricEnergy hEll
                (T (b q - b n))) :=
          sqrt_normalizedLocalSymmetricEnergy_add_le
            hEll hvol hvoltop _ _
        _ ≤ Real.sqrt (normalizedLocalSymmetricEnergy hEll
              (T (b (q + 1) - b q))) +
            ∑ j ∈ Finset.Ico n q,
              Real.sqrt (normalizedLocalSymmetricEnergy hEll
                (T (b (j + 1) - b j))) := add_le_add le_rfl ih
        _ = ∑ j ∈ Finset.Ico n (q + 1),
              Real.sqrt (normalizedLocalSymmetricEnergy hEll
                (T (b (j + 1) - b j))) := by
          rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one hnq]
          ac_rfl

/-- The product of the quarter-power scale growth and the inward excess
decay has a uniformly summable geometric tail. -/
theorem sum_quarterGrowth_mul_realRateDecay_le
    (eta : ℝ) (heta : 1 / 2 ≤ eta) {n q m : ℤ}
    (_hnq : n ≤ q) (_hqm : q ≤ m) :
    ∑ j ∈ Finset.Ico n q,
        Real.rpow 3 (((q : ℝ) - (j : ℝ)) / 4) *
          Real.rpow 3 (-eta * ((m : ℝ) - (j : ℝ))) ≤
      Real.rpow 3 (-eta * ((m : ℝ) - (q : ℝ))) *
        (1 / (1 - Real.rpow 3 (-(eta - 1 / 4)))) := by
  let c : ℝ := eta - 1 / 4
  have hc : 0 < c := by dsimp only [c]; linarith only [heta]
  have hfactor : ∀ j ∈ Finset.Ico n q,
      Real.rpow 3 (((q : ℝ) - (j : ℝ)) / 4) *
          Real.rpow 3 (-eta * ((m : ℝ) - (j : ℝ))) =
        Real.rpow 3 (-eta * ((m : ℝ) - (q : ℝ))) *
          Real.rpow 3 (-c * ((q : ℝ) - (j : ℝ))) := by
    intro j _hj
    calc
      Real.rpow 3 (((q : ℝ) - (j : ℝ)) / 4) *
          Real.rpow 3 (-eta * ((m : ℝ) - (j : ℝ))) =
          Real.rpow 3 ((((q : ℝ) - (j : ℝ)) / 4) +
            (-eta * ((m : ℝ) - (j : ℝ)))) :=
        (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
      _ = Real.rpow 3 ((-eta * ((m : ℝ) - (q : ℝ))) +
            (-c * ((q : ℝ) - (j : ℝ)))) := by
        congr 1
        dsimp only [c]
        ring
      _ = Real.rpow 3 (-eta * ((m : ℝ) - (q : ℝ))) *
          Real.rpow 3 (-c * ((q : ℝ) - (j : ℝ))) :=
        Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _
  rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]
  have hgeom := Transport.sum_geom_below_le hc q (Finset.Ico n q) (by
    intro j hj
    exact (Finset.mem_Ico.mp hj).2.le)
  exact mul_le_mul_of_nonneg_left hgeom
    (Real.rpow_nonneg (by norm_num) _)

end

end Root
end HighContrast
end HCPolySupport
