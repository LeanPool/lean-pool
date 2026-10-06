/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineBestFitEnergy

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineBestFitEnergyGrowth

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fixed-boundary finite affine energy growth

This module composes same-boundary best-fit slope growth with the two-sided
energy comparison. It is the valid-P replacement for the refuted inverse-map
ratio in the energy-growth step of finite excess decay.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

/-- Under a sufficiently small GoodMax row, the energy of one fixed-boundary
finite affine solution grows between two interval scales by at most the
source factor `3^((k-j)/4)`. -/
theorem exists_scalarIdentityFiniteAffineBestFitEnergyGrowthConstants
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C c : ℝ, 1 ≤ C ∧ c ∈ Set.Ioc (0 : ℝ) ((2 * C)⁻¹) ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n m : ℤ),
        n < m → delta ∈ Set.Ioc (0 : ℝ) c →
          ScalarIdentityGoodMaxOnInterval a s delta n m →
          ∀ (j : ℤ) (_hj : j ∈ Finset.Icc n m)
            (k : ℤ) (_hk : k ∈ Finset.Icc n m), j ≤ k → ∀ b : Vec d,
            finiteCenteredCubeSolutionEnergy a m
                (finiteAffineCubeSolution a m b) k ≤
              C ^ 2 * Real.rpow 3
                  (((Int.toNat (k - j) : ℕ) : ℝ) / 4) *
                finiteCenteredCubeSolutionEnergy a m
                  (finiteAffineCubeSolution a m b) j := by
  obtain ⟨B, cb, hB, hcb, hbounds⟩ :=
    exists_scalarIdentityFiniteAffineBestFitInductionConstants d s hs hs_lt
  obtain ⟨E, ce, hE, hce, henergy⟩ :=
    exists_scalarIdentityFiniteAffineBestFitEnergyConstants d s hs hs_lt
  let rho : ℝ := Real.rpow 3 (1 / 4 : ℝ) - 1
  let C : ℝ := 1 + B + E
  let c : ℝ := min (1 / 2 : ℝ)
    (min cb (min ce (min ((2 * C)⁻¹) (rho / C))))
  have hrho : 0 < rho := by
    dsimp [rho]
    have := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3)
      (by norm_num : (0 : ℝ) < 1 / 4)
    linarith only [this]
  have hC : 1 ≤ C := by dsimp [C]; linarith only [hB, hE]
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hBC : B ≤ C := by dsimp [C]; linarith only [hE]
  have hEC : E ≤ C := by dsimp [C]; linarith only [hB]
  have hcpos : 0 < c := by
    dsimp [c]
    exact lt_min (by norm_num) (lt_min hcb.1 (lt_min hce.1 (lt_min
      (inv_pos.mpr (mul_pos (by norm_num) hCpos)) (div_pos hrho hCpos))))
  have hcC : c ≤ (2 * C)⁻¹ := by
    dsimp [c]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  refine ⟨C, c, hC, ⟨hcpos, hcC⟩, ?_⟩
  intro a delta n m hnm hdelta hgood j hj k hk hjk b
  have hdeltaB : delta ∈ Set.Ioc (0 : ℝ) cb :=
    ⟨hdelta.1, hdelta.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hdeltaE : delta ∈ Set.Ioc (0 : ℝ) ce :=
    ⟨hdelta.1, hdelta.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hdelta_nonneg : 0 ≤ delta := hdelta.1.le
  have hdeltaRho : C * delta ≤ rho := by
    have hd : delta ≤ rho / C :=
      hdelta.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))))
    calc
      C * delta ≤ C * (rho / C) := mul_le_mul_of_nonneg_left hd hCpos.le
      _ = rho := by field_simp
  have hbase : 1 + B * delta ≤ 1 + C * delta := by
    linarith only [mul_le_mul_of_nonneg_right hBC hdelta_nonneg]
  have hbase_nonneg : 0 ≤ 1 + B * delta := by positivity
  have hCbase_nonneg : 0 ≤ 1 + C * delta := by positivity
  have hroot : 1 + C * delta ≤ Real.rpow 3 (1 / 4 : ℝ) := by
    calc
      1 + C * delta ≤ 1 + rho := by
        simpa only [add_comm] using add_le_add_left hdeltaRho 1
      _ = Real.rpow 3 (1 / 4 : ℝ) := by dsimp [rho]; ring
  let N : ℕ := Int.toNat (k - j)
  have hpowBC : (1 + B * delta) ^ N ≤ (1 + C * delta) ^ N :=
    pow_le_pow_left₀ hbase_nonneg hbase N
  have hpowRoot : (1 + C * delta) ^ N ≤
      (Real.rpow 3 (1 / 4 : ℝ)) ^ N :=
    pow_le_pow_left₀ hCbase_nonneg hroot N
  have hrootPow : (Real.rpow 3 (1 / 4 : ℝ)) ^ N =
      Real.rpow 3 ((N : ℝ) / 4) := by
    calc
      (Real.rpow 3 (1 / 4 : ℝ)) ^ N =
          Real.rpow 3 ((1 / 4 : ℝ) * (N : ℝ)) :=
        (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3) (1 / 4 : ℝ) N).symm
      _ = Real.rpow 3 ((N : ℝ) / 4) := by congr 1; ring
  have hpow : (1 + B * delta) ^ N ≤ Real.rpow 3 ((N : ℝ) / 4) :=
    hpowBC.trans (hpowRoot.trans_eq hrootPow)
  have hEk := (henergy a delta n m hnm hdeltaE hgood k hk b).1
  have hEj := (henergy a delta n m hnm hdeltaE hgood j hj b).2
  have hPk := ((hbounds a delta n m hnm hdeltaB hgood k hk b).2.2.1
    j hj hjk).2
  have hDj_nonneg : 0 ≤ finiteCenteredCubeSolutionEnergy a m
      (finiteAffineCubeSolution a m b) j := by
    unfold finiteCenteredCubeSolutionEnergy Book.Ch03.h1EnergyNormOnCube
    exact Real.sqrt_nonneg _
  have hPj_nonneg := euclideanNorm_nonneg
    (finiteAffineBestFitSlope a j m (Finset.mem_Icc.mp hj).2 b)
  have hpowB_nonneg : 0 ≤ (1 + B * delta) ^ N := pow_nonneg hbase_nonneg N
  have hroot_nonneg : 0 ≤ Real.rpow 3 ((N : ℝ) / 4) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    finiteCenteredCubeSolutionEnergy a m
        (finiteAffineCubeSolution a m b) k ≤
        E * euclideanNorm
          (finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b) := hEk
    _ ≤ E * ((1 + B * delta) ^ N * euclideanNorm
          (finiteAffineBestFitSlope a j m (Finset.mem_Icc.mp hj).2 b)) :=
      mul_le_mul_of_nonneg_left (by simpa only [N] using hPk) (zero_le_one.trans hE)
    _ ≤ E * ((1 + B * delta) ^ N *
          (E * finiteCenteredCubeSolutionEnergy a m
            (finiteAffineCubeSolution a m b) j)) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hE)
      exact mul_le_mul_of_nonneg_left hEj hpowB_nonneg
    _ = E ^ 2 * (1 + B * delta) ^ N *
          finiteCenteredCubeSolutionEnergy a m
            (finiteAffineCubeSolution a m b) j := by ring
    _ ≤ C ^ 2 * Real.rpow 3 ((N : ℝ) / 4) *
          finiteCenteredCubeSolutionEnergy a m
            (finiteAffineCubeSolution a m b) j := by
      have hsq : E ^ 2 ≤ C ^ 2 := by nlinarith only [hE, hEC]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hsq hpow hpowB_nonneg (sq_nonneg C)) hDj_nonneg
    _ = C ^ 2 * Real.rpow 3
          (((Int.toNat (k - j) : ℕ) : ℝ) / 4) *
        finiteCenteredCubeSolutionEnergy a m
          (finiteAffineCubeSolution a m b) j := by rfl

end

end HighContrast
end HCPolySupport
