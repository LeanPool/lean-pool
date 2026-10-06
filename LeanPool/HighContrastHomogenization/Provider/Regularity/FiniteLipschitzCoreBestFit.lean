/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzCoreDefinitions
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzCoreTerminal

/-!
# High-contrast homogenization: Provider.Regularity.FiniteLipschitzCoreBestFit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite centered-cube best-fit estimates

This module provides the terminal, integer-rate, one-step, and Caccioppoli
best-fit interfaces.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Book.Ch03
open scoped BigOperators ENNReal

noncomputable section


open FiniteLipschitzCoreInternal

/-- At the outer scale, the canonical affine best-fit slope is controlled by
the solution energy.  This is the public slope estimate used when a ruled
finite-affine flatness bound is applied to an arbitrary harmonic residual. -/
theorem exists_scalarIdentityFiniteTerminalBestFitSlopeConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (k : ℤ)
        (u : Book.Ch03.CubeSolution (originCube d k) a),
        scalarIdentityWeakError a s k ≤ 1 →
          euclideanNorm
              (finiteCenteredCubeBestFitSlopeAt a k u k) ≤
            C * Book.Ch03.h1EnergyNormOnCube (originCube d k) a u.toH1 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_finiteLipschitzTerminalSlopeConstant d s hs hs_lt
  refine ⟨C, hC, ?_⟩
  intro a k u herr
  have h := hbound a k u herr
  rw [finiteLipschitzEnergyRow_self] at h
  exact h

/-- At the outer scale, the canonical best-affine error is controlled by the
solution energy. -/
theorem exists_scalarIdentityFiniteTerminalBestFitErrorConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (k : ℤ)
        (u : Book.Ch03.CubeSolution (originCube d k) a),
        scalarIdentityWeakError a s k ≤ 1 →
          finiteCenteredCubeBestFitErrorAt a k u k (le_refl k) ≤
            C * Book.Ch03.h1EnergyNormOnCube (originCube d k) a u.toH1 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_finiteLipschitzAffineErrorEnergyConstant d s hs hs_lt
  refine ⟨C, hC, ?_⟩
  intro a k u herr
  have h := hbound a k u k (le_refl k) herr
  rw [finiteLipschitzEnergyRow_self] at h
  exact h

/-- Parameterized near-unit-rate improvement for the canonical best-affine
error, with the replacement error kept explicit. -/
theorem exists_scalarIdentityFiniteBestFitIntegerRateStepConstants
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2)
    (p : ℕ) (hp : 0 < p) :
    ∃ (depth : ℕ) (C₀ : ℝ), 0 < C₀ ∧
      ∀ t : ℕ,
        let N := depth + 2 * p * t + 2
        ∃ C : ℝ, 0 < C ∧
          ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ)
            (u : Book.Ch03.CubeSolution (originCube d m) a)
            (k : ℤ) (hkm : k ≤ m),
              finiteCenteredCubeBestFitErrorAt a m u (k - (N : ℤ)) (by omega) ≤
                (C₀ * ((1 : ℝ) / 3) ^ ((2 * p - 1) * t)) *
                    finiteCenteredCubeBestFitErrorAt a m u k hkm +
                  C * scalarIdentityWeakError a s k *
                    finiteCenteredCubeSolutionEnergy a m u k := by
  obtain ⟨depth, C₀, hC₀, hdecay⟩ :=
    CubeCalderonZygmund.exists_identityHarmonic_affineErrorDecay_atIntegerRate
      d p hp
  refine ⟨depth, C₀, hC₀, ?_⟩
  intro t
  dsimp only
  let N : ℕ := depth + 2 * p * t + 2
  let theta : ℝ := C₀ * ((1 : ℝ) / 3) ^ ((2 * p - 1) * t)
  have hN : 0 < N := by dsimp [N]; omega
  have htheta : 0 < theta := by dsimp [theta]; positivity
  have hdecay' : ∀ (k : ℤ)
      (v : H1Function (openCubeSet (originCube d k))),
      WeakPoissonEquationOn (openCubeSet (originCube d k)) v (fun _ => 0) →
        ∀ (c : ℝ) (e : Vec d), ∃ c' e',
          normalizedAffineCandidateError (originCube d (k - (N : ℤ)))
              v.toFun c' e' ≤
            theta * normalizedAffineCandidateError
              (originCube d k) v.toFun c e := by
    simpa only [N, theta] using hdecay t
  obtain ⟨C, hC, hstep⟩ :=
    exists_finiteLipschitzOneStepConstant_of_harmonic_decay d s hs hs_lt
      N hN theta htheta hdecay'
  refine ⟨C, hC, ?_⟩
  intro a m u k hkm
  simpa only [N, theta, finiteCenteredCubeBestFitErrorAt,
    finiteCenteredCubeSolutionEnergy, finiteLipschitzEnergyRow,
    finiteLipschitzRestriction] using
      hstep a m u k hkm

/-- One fixed-step contraction for the canonical best-affine error.  This is
the public analytic interface consumed by finite affine flatness induction. -/
theorem exists_scalarIdentityFiniteBestFitOneStepConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ)
        (u : Book.Ch03.CubeSolution (originCube d m) a)
        (k : ℤ) (hkm : k ≤ m),
          finiteCenteredCubeBestFitErrorAt a m u (k - (N : ℤ)) (by omega) ≤
            (1 / 8 : ℝ) * finiteCenteredCubeBestFitErrorAt a m u k hkm +
              C * scalarIdentityWeakError a s k *
                finiteCenteredCubeSolutionEnergy a m u k := by
  obtain ⟨N, hN, C, hC, hstep⟩ :=
    exists_finiteLipschitzOneStepConstant d s hs hs_lt
  refine ⟨N, hN, C, hC, ?_⟩
  intro a m u k hkm
  simpa only [finiteCenteredCubeBestFitErrorAt,
    finiteCenteredCubeSolutionEnergy, finiteLipschitzEnergyRow,
    finiteLipschitzRestriction] using
      hstep a m u k hkm

/-- Affine Caccioppoli control two centered scales below a cube. -/
theorem exists_scalarIdentityFiniteCaccioppoliAffineConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (k : ℤ)
        (u : Book.Ch03.CubeSolution (originCube d k) a) (c : ℝ) (e : Vec d),
        scalarIdentityWeakError a s k ≤ 1 →
          finiteCenteredCubeSolutionEnergy a k u (k - 2) ≤
            C * (normalizedAffineCandidateError (originCube d k)
              u.toH1.toFun c e + euclideanNorm e) := by
  obtain ⟨C, hC, hcacc⟩ :=
    exists_finiteLipschitzCaccioppoliAffineConstant d s hs hs_lt
  refine ⟨C, hC, ?_⟩
  intro a k u c e herr
  rw [finiteCenteredCubeSolutionEnergy_eq_of_le a k u (k - 2) (by omega)]
  exact hcacc a k u c e herr


end

end HighContrast
end HCPolySupport
