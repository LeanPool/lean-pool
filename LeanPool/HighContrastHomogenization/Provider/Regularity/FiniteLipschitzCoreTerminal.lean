/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzCoreBase

/-!
# High-contrast homogenization: Provider.Regularity.FiniteLipschitzCoreTerminal

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Terminal affine estimates for finite large-scale regularity

This module contains the terminal error and slope estimates shared by the
energy-recurrence and best-fit branches.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Book.Ch03
open scoped BigOperators ENNReal

noncomputable section


namespace FiniteLipschitzCoreInternal

theorem exists_finiteLipschitzAffineErrorEnergyConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ)
        (u : Book.Ch03.CubeSolution (originCube d m) a)
        (k : ℤ), k ≤ m → scalarIdentityWeakError a s k ≤ 1 →
          finiteLipschitzAffineErrorRow a m u k ≤
            C * finiteLipschitzEnergyRow a m u k := by
  obtain ⟨C, hC, hPoincare⟩ :=
    exists_finiteLipschitzPoincareConstant d s hs hs_lt
  refine ⟨C, hC, ?_⟩
  intro a m u k hkm herror
  let uk : Book.Ch03.CubeSolution (originCube d k) a :=
    finiteCubeSolutionRestriction a hkm u
  let c : ℝ := cubeAverage (originCube d k) uk.toH1.toFun
  have hbest := finiteLipschitzAffineErrorRow_best_le a m u hkm c (0 : Vec d)
  have hcandidate :
      normalizedAffineCandidateError (originCube d k) u.toH1.toFun c (0 : Vec d) =
        cubeBesovScaleWeight 1 (originCube d k) *
          cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
            (cubeFluctuation (originCube d k) uk.toH1.toFun) := by
    unfold normalizedAffineCandidateError normalizedCubeL2Distance cubeFluctuation
    dsimp [c]; rw [finiteCubeSolutionRestriction_toFun]
    simp only [vecDot_zero_left, add_zero]
  have hp := hPoincare a k uk herror
  have henergy :
      Book.Ch03.h1EnergyNormOnCube (originCube d k) a uk.toH1 =
        finiteLipschitzEnergyRow a m u k := by
    simpa only [uk] using
      (finiteLipschitzEnergyRow_eq_h1EnergyNormOnCube_of_le a m u k hkm).symm
  calc
    finiteLipschitzAffineErrorRow a m u k ≤
        normalizedAffineCandidateError (originCube d k) u.toH1.toFun c (0 : Vec d) :=
      hbest
    _ = cubeBesovScaleWeight 1 (originCube d k) *
          cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
            (cubeFluctuation (originCube d k) uk.toH1.toFun) := hcandidate
    _ ≤ C * Book.Ch03.h1EnergyNormOnCube (originCube d k) a uk.toH1 := hp
    _ = C * finiteLipschitzEnergyRow a m u k := by rw [henergy]

theorem exists_finiteLipschitzTerminalSlopeConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ)
        (u : Book.Ch03.CubeSolution (originCube d m) a),
        scalarIdentityWeakError a s m ≤ 1 →
          euclideanNorm (finiteLipschitzBestSlope a m u m) ≤
            C * finiteLipschitzEnergyRow a m u m := by
  obtain ⟨C₀, hC₀, hC₀bound⟩ := exists_originCubeAffineSlopeErrorConstant d
  obtain ⟨C₁, hC₁, hPoincare⟩ :=
    exists_finiteLipschitzPoincareConstant d s hs hs_lt
  let C : ℝ := 1 + 2 * C₀ * C₁
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro a m u herror
  let c₀ := finiteLipschitzBestIntercept a m u m
  let e₀ := finiteLipschitzBestSlope a m u m
  let c₁ := cubeAverage (originCube d m) u.toH1.toFun
  let E := finiteLipschitzAffineErrorRow a m u m
  let D := finiteLipschitzEnergyRow a m u m
  have hres₀ : MemLp (fun x ↦ u.toH1.toFun x - (c₀ + vecDot e₀ x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d m)) := by
    simpa only [c₀, e₀] using
      finiteLipschitzBestResidual_memLp a m u (le_refl m)
  have hres₁ : MemLp (fun x ↦ u.toH1.toFun x - (c₁ + vecDot (0 : Vec d) x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d m)) := by
    simpa only [c₁, vecDot_zero_left, add_zero, cubeFluctuation] using!
      u.toH1.memL2_normalizedCubeMeasure.sub (memLp_const _)
  have htriangle := normalizedAffineCandidateError_zero_sub_le_add
    (originCube d m) u.toH1.toFun c₀ c₁ e₀ (0 : Vec d) hres₀ hres₁
  have hbestEq :
      normalizedAffineCandidateError (originCube d m) u.toH1.toFun c₀ e₀ = E := by
    simp only [E, c₀, e₀, finiteLipschitzAffineErrorRow,
      finiteLipschitzBestIntercept, finiteLipschitzBestSlope,
      finiteLipschitzRestriction_toFun, min_self]
  have hcandidateEq :
      normalizedAffineCandidateError (originCube d m) u.toH1.toFun c₁ (0 : Vec d) =
        cubeBesovScaleWeight 1 (originCube d m) *
          cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
            (cubeFluctuation (originCube d m) u.toH1.toFun) := by
    unfold normalizedAffineCandidateError normalizedCubeL2Distance cubeFluctuation
    simp only [c₁, vecDot_zero_left, add_zero]
  have hP := hPoincare a m u herror
  have htopEnergy :
      Book.Ch03.h1EnergyNormOnCube (originCube d m) a u.toH1 = D := by
    simpa only [D] using (finiteLipschitzEnergyRow_self a m u).symm
  rw [htopEnergy] at hP
  have hE : E ≤ C₁ * D := by
    have hbest : E ≤
        normalizedAffineCandidateError (originCube d m) u.toH1.toFun c₁ (0 : Vec d) := by
      simpa only [E] using
        finiteLipschitzAffineErrorRow_best_le a m u (le_refl m) c₁ (0 : Vec d)
    exact hbest.trans ((le_of_eq hcandidateEq).trans hP)
  have hD_nonneg : 0 ≤ D := finiteLipschitzEnergyRow_nonneg a m u m
  have hslope := hC₀bound m (c₀ - c₁) (e₀ - (0 : Vec d))
  have hcombined :
      normalizedAffineCandidateError (originCube d m) (fun _ ↦ 0)
          (c₀ - c₁) (e₀ - (0 : Vec d)) ≤ 2 * C₁ * D := by
    calc
      normalizedAffineCandidateError (originCube d m) (fun _ ↦ 0)
          (c₀ - c₁) (e₀ - (0 : Vec d)) ≤
          normalizedAffineCandidateError (originCube d m) u.toH1.toFun c₀ e₀ +
            normalizedAffineCandidateError (originCube d m) u.toH1.toFun c₁ (0 : Vec d) :=
        htriangle
      _ = E + normalizedAffineCandidateError (originCube d m)
          u.toH1.toFun c₁ (0 : Vec d) := by rw [hbestEq]
      _ ≤ C₁ * D + C₁ * D := by
        exact add_le_add hE ((le_of_eq hcandidateEq).trans hP)
      _ = 2 * C₁ * D := by ring
  calc
    euclideanNorm (finiteLipschitzBestSlope a m u m) =
        euclideanNorm (e₀ - (0 : Vec d)) := by simp [e₀]
    _ ≤ C₀ * normalizedAffineCandidateError (originCube d m) (fun _ ↦ 0)
          (c₀ - c₁) (e₀ - (0 : Vec d)) := hslope
    _ ≤ C₀ * (2 * C₁ * D) :=
      mul_le_mul_of_nonneg_left hcombined hC₀.le
    _ ≤ C * D := by
      have hfactor : C₀ * (2 * C₁) ≤ C := by
        calc
          C₀ * (2 * C₁) = 2 * C₀ * C₁ := by ring
          _ ≤ 1 + 2 * C₀ * C₁ := le_add_of_nonneg_left zero_le_one
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hfactor hD_nonneg
    _ = C * finiteLipschitzEnergyRow a m u m := rfl


end FiniteLipschitzCoreInternal


end

end HighContrast
end HCPolySupport
