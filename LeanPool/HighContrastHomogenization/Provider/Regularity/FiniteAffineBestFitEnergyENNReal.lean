/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineBestFitEnergy

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineBestFitEnergyENNReal

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# ENNReal finite affine best-fit energy comparison

This module transports the real-valued fixed-boundary energy comparison to
the exact weighted-gradient `ENNReal` carrier used by the finite slope family.
-/

namespace HCPolySupport
namespace HighContrast

open scoped ENNReal

noncomputable section

private theorem weightedGradNorm_finiteAffineSolution_eq_ofReal_energy
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (b : Vec d) :
    weightedGradNorm
        (a.coeffOn (originCube d k)).toCoeffField
        (openCubeSet (originCube d k))
        (finiteAffineSolution a m b).toH1.grad =
      ENNReal.ofReal
        (finiteCenteredCubeSolutionEnergy a m
          (finiteAffineCubeSolution a m b) k) := by
  let u : Book.Ch03.CubeSolution (originCube d m) a :=
    finiteAffineCubeSolution a m b
  let uk : Book.Ch03.CubeSolution (originCube d k) a :=
    finiteCubeSolutionRestriction a hkm u
  calc
    weightedGradNorm
        (a.coeffOn (originCube d k)).toCoeffField
        (openCubeSet (originCube d k))
        (finiteAffineSolution a m b).toH1.grad =
        weightedGradNorm
          (a.coeffOn (originCube d k)).toCoeffField
          (openCubeSet (originCube d k)) uk.toH1.grad := by
      dsimp only [uk, u, finiteAffineCubeSolution]
      rw [finiteCubeSolutionRestriction_grad]
    _ = ENNReal.ofReal
          (Book.Ch03.h1EnergyNormOnCube (originCube d k) a uk.toH1) :=
      weightedGradNorm_eq_ofReal_h1EnergyNormOnCube
        (originCube d k) a uk.toH1
    _ = ENNReal.ofReal
          (finiteCenteredCubeSolutionEnergy a m
            (finiteAffineCubeSolution a m b) k) := by
      apply congrArg ENNReal.ofReal
      exact (finiteCenteredCubeSolutionEnergy_eq_of_le a m
        (finiteAffineCubeSolution a m b) k hkm).symm

/-- On a sufficiently good finite row, the weighted-gradient norm of a
fixed-boundary affine solution is bounded above and below by the `ENNReal`
realization of its current canonical best-fit slope norm. -/
theorem exists_scalarIdentityFiniteAffineBestFitEnergyENNRealConstants
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C c : ℝ, 1 ≤ C ∧ c ∈ Set.Ioc (0 : ℝ) ((2 * C)⁻¹) ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n m : ℤ),
        n < m → delta ∈ Set.Ioc (0 : ℝ) c →
          ScalarIdentityGoodMaxOnInterval a s delta n m →
          ∀ (k : ℤ) (hk : k ∈ Finset.Icc n m) (b : Vec d),
            ENNReal.ofReal
                (C⁻¹ * euclideanNorm
                  (finiteAffineBestFitSlope a k m
                    (Finset.mem_Icc.mp hk).2 b)) ≤
              weightedGradNorm
                (a.coeffOn (originCube d k)).toCoeffField
                (openCubeSet (originCube d k))
                (finiteAffineSolution a m b).toH1.grad ∧
            weightedGradNorm
                (a.coeffOn (originCube d k)).toCoeffField
                (openCubeSet (originCube d k))
                (finiteAffineSolution a m b).toH1.grad ≤
              ENNReal.ofReal
                (C * euclideanNorm
                  (finiteAffineBestFitSlope a k m
                    (Finset.mem_Icc.mp hk).2 b)) := by
  obtain ⟨C, c, hC, hc, henergy⟩ :=
    exists_scalarIdentityFiniteAffineBestFitEnergyConstants d s hs hs_lt
  refine ⟨C, c, hC, hc, ?_⟩
  intro a delta n m hnm hdelta hgood k hk b
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hpack := henergy a delta n m hnm hdelta hgood k hk b
  let D : ℝ := finiteCenteredCubeSolutionEnergy a m
    (finiteAffineCubeSolution a m b) k
  let P : Vec d := finiteAffineBestFitSlope a k m
    (Finset.mem_Icc.mp hk).2 b
  have hlower : C⁻¹ * euclideanNorm P ≤ D := by
    calc
      C⁻¹ * euclideanNorm P ≤ C⁻¹ * (C * D) :=
        mul_le_mul_of_nonneg_left hpack.2 (inv_nonneg.mpr hCpos.le)
      _ = D := by field_simp
  have hbridge := weightedGradNorm_finiteAffineSolution_eq_ofReal_energy
    a k m (Finset.mem_Icc.mp hk).2 b
  constructor
  · rw [hbridge]
    exact ENNReal.ofReal_le_ofReal hlower
  · rw [hbridge]
    exact ENNReal.ofReal_le_ofReal hpack.1

end

end HighContrast
end HCPolySupport
