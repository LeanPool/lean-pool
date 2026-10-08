/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSlopeFamily
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSlopeInverseFamily
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineBestFitBounds
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineBestFitEnergyENNReal

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineSlopeFamilyExistence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Existence of finite affine slope families

This module assembles the proof-gated inverse matrices, best-fit flatness,
fixed-boundary energy comparison, and same-boundary forward-slope bounds into
one finite affine slope family.  The flatness intercept is the attained
best-fit intercept of the outer finite solution.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

/-- A sufficiently small good-max row admits a finite affine slope family
whose flatness normalization is the attained outer best-fit intercept. -/
theorem exists_scalarIdentityFiniteAffineSlopeFamilyConstants
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C c : ℝ, 1 ≤ C ∧ c ∈ Set.Ioc (0 : ℝ) ((2 * C)⁻¹) ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n m : ℤ),
        n < m → delta ∈ Set.Ioc (0 : ℝ) c →
          ScalarIdentityGoodMaxOnInterval a s delta n m →
          ∃ Q : ℤ → Mat d, IsFiniteAffineSlopeFamily a delta C n m Q := by
  obtain ⟨I, ci, hI, hci, hinverse⟩ :=
    exists_scalarIdentityFiniteAffineSlopeInverseFamilyConstants d s hs hs_lt
  obtain ⟨B, cb, hB, hcb, hbounds⟩ :=
    exists_scalarIdentityFiniteAffineBestFitInductionConstants d s hs hs_lt
  obtain ⟨E, ce, hE, hce, henergy⟩ :=
    exists_scalarIdentityFiniteAffineBestFitEnergyENNRealConstants d s hs hs_lt
  let C : ℝ := 1 + I + B + E
  let c : ℝ := min ci (min cb (min ce ((2 * C)⁻¹)))
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith only [hI, hB, hE]
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hIC : I ≤ C := by
    dsimp [C]
    linarith only [hB, hE]
  have hBC : B ≤ C := by
    dsimp [C]
    linarith only [hI, hE]
  have hEC : E ≤ C := by
    dsimp [C]
    linarith only [hI, hB]
  have hcpos : 0 < c := by
    dsimp [c]
    exact lt_min hci.1 (lt_min hcb.1 (lt_min hce.1
      (inv_pos.mpr (mul_pos (by norm_num) hCpos))))
  have hcC : c ≤ (2 * C)⁻¹ := by
    dsimp [c]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _))
  refine ⟨C, c, hC, ⟨hcpos, hcC⟩, ?_⟩
  intro a delta n m hnm hdelta hgood
  have hdeltaI : delta ∈ Set.Ioc (0 : ℝ) ci :=
    ⟨hdelta.1, hdelta.2.trans (min_le_left _ _)⟩
  have hdeltaB : delta ∈ Set.Ioc (0 : ℝ) cb :=
    ⟨hdelta.1, hdelta.2.trans
      ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hdeltaE : delta ∈ Set.Ioc (0 : ℝ) ce :=
    ⟨hdelta.1, hdelta.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hsmall : C * delta ≤ (1 / 2 : ℝ) := by
    have hd : delta ≤ (2 * C)⁻¹ := hdelta.2.trans hcC
    calc
      C * delta ≤ C * (2 * C)⁻¹ :=
        mul_le_mul_of_nonneg_left hd hCpos.le
      _ = 1 / 2 := by field_simp
  have hdelta_nonneg : 0 ≤ delta := hdelta.1.le
  obtain ⟨Q, hQinv, hQterminal, _hIsmall⟩ :=
    hinverse a delta n m hnm hdeltaI hgood
  refine ⟨Q, {
    isUnit_det := fun k hk ↦ (hQinv k hk).1
    slopeMatrix_mul_inverse := fun k hk ↦ (hQinv k hk).2.1
    inverse_mul_slopeMatrix := fun k hk ↦ (hQinv k hk).2.2
    flatness_at := ?_
    bestFitEnergy_lower := ?_
    bestFitEnergy_upper := ?_
    bestFitSlope_lower := ?_
    bestFitSlope_upper := ?_
    terminal_matrixNorm := ?_
    small := hsmall }⟩
  · intro k hk e
    let hkm : k ≤ m := (Finset.mem_Icc.mp hk).2
    have hslope : finiteAffineBestFitSlope a k m hkm
        (matVecMul (Q k) e) = e := by
      rw [← finiteAffineBestFitSlopeMatrix_apply, matVecMul_mul,
        (hQinv k hk).2.1, matVecMul_one]
    have hfit := (hbounds a delta n m hnm hdeltaB hgood k hk
      (matVecMul (Q k) e)).1
    calc
      normalizedAffineCandidateError (originCube d k)
          (finiteAffineSolution a m (matVecMul (Q k) e)).toH1.toFun
          (finiteAffineBestFitIntercept a k m hkm (matVecMul (Q k) e)) e =
          finiteAffineBestFitError a k m hkm (matVecMul (Q k) e) := by
            unfold finiteAffineBestFitError
            rw [hslope]
      _ ≤ B * delta * euclideanNorm
          (finiteAffineBestFitSlope a k m hkm (matVecMul (Q k) e)) := hfit
      _ = B * delta * euclideanNorm e := by rw [hslope]
      _ ≤ C * delta * euclideanNorm e := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBC hdelta_nonneg)
          (euclideanNorm_nonneg e)
  · intro k hk b
    have hpack := henergy a delta n m hnm hdeltaE hgood k hk b
    have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE
    have hinv : C⁻¹ ≤ E⁻¹ := (inv_le_inv₀ hCpos hEpos).2 hEC
    exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hinv (euclideanNorm_nonneg _))).trans hpack.1
  · intro k hk b
    have hpack := henergy a delta n m hnm hdeltaE hgood k hk b
    exact hpack.2.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hEC (euclideanNorm_nonneg _)))
  · intro j hj k hk hjk b
    let N : ℕ := Int.toNat (k - j)
    have hpack := (hbounds a delta n m hnm hdeltaB hgood k hk b).2.2.1
      j hj hjk
    have hbase : 1 - C * delta ≤ 1 - B * delta := by
      exact sub_le_sub_left
        (mul_le_mul_of_nonneg_right hBC hdelta_nonneg) 1
    have hbase_nonneg : 0 ≤ 1 - C * delta := by
      linarith only [hsmall]
    have hpow : (1 - C * delta) ^ N ≤ (1 - B * delta) ^ N :=
      pow_le_pow_left₀ hbase_nonneg hbase N
    calc
      (1 - C * delta) ^ Int.toNat (k - j) *
          euclideanNorm
            (finiteAffineBestFitSlope a j m
              (Finset.mem_Icc.mp hj).2 b) ≤
          (1 - B * delta) ^ Int.toNat (k - j) *
            euclideanNorm
              (finiteAffineBestFitSlope a j m
                (Finset.mem_Icc.mp hj).2 b) := by
            exact mul_le_mul_of_nonneg_right hpow (euclideanNorm_nonneg _)
      _ ≤ euclideanNorm
          (finiteAffineBestFitSlope a k m
            (Finset.mem_Icc.mp hk).2 b) := hpack.1
  · intro j hj k hk hjk b
    let N : ℕ := Int.toNat (k - j)
    have hpack := (hbounds a delta n m hnm hdeltaB hgood k hk b).2.2.1
      j hj hjk
    have hbase : 1 + B * delta ≤ 1 + C * delta := by
      simpa only [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_right hBC hdelta_nonneg) 1
    have hbase_nonneg : 0 ≤ 1 + B * delta := by positivity
    have hpow : (1 + B * delta) ^ N ≤ (1 + C * delta) ^ N :=
      pow_le_pow_left₀ hbase_nonneg hbase N
    calc
      euclideanNorm
          (finiteAffineBestFitSlope a k m
            (Finset.mem_Icc.mp hk).2 b) ≤
          (1 + B * delta) ^ Int.toNat (k - j) *
            euclideanNorm
              (finiteAffineBestFitSlope a j m
                (Finset.mem_Icc.mp hj).2 b) := hpack.2
      _ ≤ (1 + C * delta) ^ Int.toNat (k - j) *
          euclideanNorm
            (finiteAffineBestFitSlope a j m
              (Finset.mem_Icc.mp hj).2 b) := by
            exact mul_le_mul_of_nonneg_right hpow (euclideanNorm_nonneg _)
  · exact hQterminal.trans
      (mul_le_mul_of_nonneg_right hIC hdelta_nonneg)

end

end HighContrast
end HCPolySupport
