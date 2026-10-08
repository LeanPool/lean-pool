/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineBestFitBounds
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSlopeMatrix

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineSlopeBijective

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Bijectivity of finite affine best-fit slope maps

This module derives interval-scale bijectivity from the valid same-boundary
forward-slope bounds and terminal closeness. No inverse map is used in the
argument.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

/-- On a sufficiently small GoodMax row, every finite affine best-fit slope
map in the interval is bijective and its matrix has unit determinant. -/
theorem exists_scalarIdentityFiniteAffineSlopeBijectiveConstants
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C c : ℝ, 1 ≤ C ∧ c ∈ Set.Ioc (0 : ℝ) ((2 * C)⁻¹) ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n m : ℤ),
        n < m → delta ∈ Set.Ioc (0 : ℝ) c →
          ScalarIdentityGoodMaxOnInterval a s delta n m →
          ∀ (k : ℤ) (_hk : k ∈ Finset.Icc n m),
            Function.Bijective
                (finiteAffineBestFitSlope a k m
                  (Finset.mem_Icc.mp _hk).2) ∧
              IsUnit
                (finiteAffineBestFitSlopeMatrix a k m
                  (Finset.mem_Icc.mp _hk).2).det := by
  obtain ⟨C, c, hC, hc, hbounds⟩ :=
    exists_scalarIdentityFiniteAffineBestFitInductionConstants d s hs hs_lt
  refine ⟨C, c, hC, hc, ?_⟩
  intro a delta n m hnm hdelta hgood k hk
  have hm : m ∈ Finset.Icc n m := Finset.mem_Icc.mpr ⟨hnm.le, le_rfl⟩
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hsmall : C * delta ≤ 1 / 2 := by
    have hd : delta ≤ (2 * C)⁻¹ := hdelta.2.trans hc.2
    calc
      C * delta ≤ C * (2 * C)⁻¹ :=
        mul_le_mul_of_nonneg_left hd hCpos.le
      _ = 1 / 2 := by field_simp
  have hinj : Function.Injective
      (finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2) := by
    intro x y hxy
    let z : Vec d := x - y
    have hPkz : finiteAffineBestFitSlope a k m
        (Finset.mem_Icc.mp hk).2 z = 0 := by
      calc
        finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 z =
            finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 x -
              finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 y := by
          exact map_sub (finiteAffineBestFitSlope a k m
            (Finset.mem_Icc.mp hk).2) x y
        _ = 0 := sub_eq_zero.mpr hxy
    have hPmUpper := ((hbounds a delta n m hnm hdelta hgood m hm z).2.2.1
      k hk (Finset.mem_Icc.mp hk).2).2
    have hPmNorm : euclideanNorm
        (finiteAffineBestFitSlope a m m le_rfl z) = 0 := by
      rw [hPkz, euclideanNorm_zero, mul_zero] at hPmUpper
      exact le_antisymm hPmUpper (euclideanNorm_nonneg _)
    have hPm : finiteAffineBestFitSlope a m m le_rfl z = 0 :=
      euclideanNorm_eq_zero_iff.mp hPmNorm
    have hterminal :=
      (hbounds a delta n m hnm hdelta hgood m hm z).2.2.2 rfl
    rw [hPm, zero_sub, euclideanNorm_neg] at hterminal
    have hzNorm : euclideanNorm z = 0 := by
      nlinarith only [hterminal, hsmall, euclideanNorm_nonneg z]
    have hz : z = 0 := euclideanNorm_eq_zero_iff.mp hzNorm
    exact sub_eq_zero.mp hz
  have hbij : Function.Bijective
      (finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2) :=
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  exact ⟨hbij,
    (finiteAffineBestFitSlopeMatrix_isUnit_det_iff_bijective
      a k m (Finset.mem_Icc.mp hk).2).2 hbij⟩

end

end HighContrast
end HCPolySupport
