/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSuccessorLocalEnergy
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitz

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineSuccessorGradient

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Successive finite-corrector gradient estimate

This module combines the two-scale local energy estimate with finite
large-scale Lipschitz descent on centered Euclidean cubes.
-/

namespace HCPolySupport
namespace HighContrast

open scoped ENNReal

noncomputable section

private theorem ScalarIdentityGoodTailOnInterval.mono_interval
    {d : ℕ} {a : Book.Ch02.TriadicCoeffFamily d}
    {s δ : ℝ} {n n' m' m : ℤ}
    (h : ScalarIdentityGoodTailOnInterval a s δ n m)
    (hn : n ≤ n') (hm : m' ≤ m) :
    ScalarIdentityGoodTailOnInterval a s δ n' m' := by
  apply le_trans _ h
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc hn hm) ?_
  intro k _ _
  exact scalarIdentityWeakError_nonneg a s k

/-- A finite good tail bounds the successive finite-corrector gradient on
every centered cube at least two scales below the parent cube. -/
theorem exists_finiteAffineSuccessorWeightedGradientEstimateConstant
    (d : ℕ) [NeZero d] (s : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C c : ℝ, 0 < C ∧ c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (δ : ℝ)
        (n m : ℤ) (e : Vec d),
        δ ∈ Set.Ioc (0 : ℝ) c →
        n ≤ m - 2 →
        ScalarIdentityGoodTailOnInterval a s δ n (m + 1) →
        weightedGradNorm
            (a.coeffOn (originCube d n)).toCoeffField
            (openCubeSet (originCube d n))
            (finiteAffineSuccessorDifference a m e).toH1.grad ≤
          ENNReal.ofReal
            (C * (scalarIdentityCorrectedWeakError a s m +
              scalarIdentityCorrectedWeakError a s (m + 1)) *
              euclideanNorm e) := by
  obtain ⟨C₀, hC₀, hlocal⟩ :=
    exists_finiteAffineSuccessorDifferenceLocalEnergyEstimateConstant
      d s hs hs_lt
  obtain ⟨C₁, c, hC₁, hc, hlipschitz⟩ :=
    exists_scalarIdentityFiniteLipschitzConstant d s hs hs_lt
  let C : ℝ := C₁ * C₀
  have hC₁pos : 0 < C₁ := lt_of_lt_of_le zero_lt_one hC₁
  have hC : 0 < C := mul_pos hC₁pos hC₀
  refine ⟨C, c, hC, hc, ?_⟩
  intro a δ n m e hδ hnm hgood
  let R : TriadicCube d := originCube d (m - 2)
  let v : Book.Ch03.CubeSolution R a :=
    finiteAffineSuccessorDifferenceInnerRestriction a m e
  let B : ℝ := scalarIdentityCorrectedWeakError a s m +
    scalarIdentityCorrectedWeakError a s (m + 1)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg
      (scalarIdentityCorrectedWeakError_nonneg a s m)
      (scalarIdentityCorrectedWeakError_nonneg a s (m + 1))
  have hpair : ScalarIdentityGoodTailOnInterval a s 1 m (m + 1) := by
    exact (hgood.mono_interval (by omega : n ≤ m) le_rfl).mono
      (hδ.2.trans hc.2.le)
  have hlocalEnergy : Book.Ch03.h1EnergyNormOnCube R a v.toH1 ≤
      C₀ * B * euclideanNorm e := by
    simpa only [R, v, B] using hlocal a m e hpair
  have hC₁enn : 1 ≤ ENNReal.ofReal C₁ := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hC₁
  have hdescent : weightedGradNorm
        (a.coeffOn (originCube d n)).toCoeffField
        (openCubeSet (originCube d n)) v.toH1.grad ≤
      ENNReal.ofReal C₁ * weightedGradNorm
        (a.coeffOn R).toCoeffField (openCubeSet R) v.toH1.grad := by
    rcases hnm.eq_or_lt with hEq | hlt
    · subst n
      simpa only [R, one_mul] using mul_le_mul_left hC₁enn
        (weightedGradNorm (a.coeffOn (originCube d (m - 2))).toCoeffField
          (openCubeSet (originCube d (m - 2))) v.toH1.grad)
    · have hgoodR : ScalarIdentityGoodTailOnInterval a s c n (m - 2) := by
        exact (hgood.mono_interval le_rfl (by omega : m - 2 ≤ m + 1)).mono hδ.2
      simpa only [R] using hlipschitz a n (m - 2) hlt hgoodR v
  rw [← finiteAffineSuccessorDifferenceInnerRestriction_grad]
  calc
    weightedGradNorm
        (a.coeffOn (originCube d n)).toCoeffField
        (openCubeSet (originCube d n)) v.toH1.grad ≤
        ENNReal.ofReal C₁ * weightedGradNorm
          (a.coeffOn R).toCoeffField (openCubeSet R) v.toH1.grad := hdescent
    _ = ENNReal.ofReal C₁ *
          ENNReal.ofReal (Book.Ch03.h1EnergyNormOnCube R a v.toH1) := by
      rw [weightedGradNorm_eq_ofReal_h1EnergyNormOnCube]
    _ ≤ ENNReal.ofReal C₁ *
          ENNReal.ofReal (C₀ * B * euclideanNorm e) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal hlocalEnergy) _
    _ = ENNReal.ofReal (C * B * euclideanNorm e) := by
      rw [← ENNReal.ofReal_mul (zero_le_one.trans hC₁)]
      congr 1
      dsimp [C]
      ring

end

end HighContrast
end HCPolySupport
