/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FoldAbsorption
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootInterface.ScaleFactorArithmetic
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootAssembly

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.DirichletHoleConsumption

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The restated negative-Sobolev Dirichlet error clause, transcribed, and its
# acceptance check

An earlier form of the clause took `GoodScale : Mat d → CoeffSpace d → ℝ → Prop`,
`∃ κ`, length `x * eccentricityFoldFactor abar pEcc`).  The root-interface module's
the current form replaces it: `GoodScale` threads `g` and the rate, `κ` is a `∀`-binder
capped at `(1 + g)/4`, and the enlarged length carries a per-`g` factor `Lg ≥ 1`
beside the fold.

`DirichletHole` below is that slot, transcribed from
`RootInterface.RootAssemblyV2.polynomial_homogenization_of_quenched_scale_v2`
The consumption theorem below is the **fail-closed check** that
the transcription is the slot: it feeds a `DirichletHole` into the root
theorem's seventh binder, so any deviation — a renamed binder, a moved premise,
a different rate factor — is an elaboration error, not a silent mismatch.

This module does **not** inhabit the hole.  It fixes its statement in this module
so later supplies can be measured against it.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

open scoped ENNReal

noncomputable section

/-- **The restated internal Dirichlet clause**, transcribed from the root
assembly. -/
@[expose]
def DirichletHole (d : ℕ) [NeZero d]
    (GoodScale : ℝ → ℝ → Mat d → CoeffSpace d → ℝ → Prop) : Prop :=
  ∃ C₀ : ℝ → ℝ → ℝ → ℝ, (∀ s₀ ρ Rad : ℝ, 0 < C₀ s₀ ρ Rad) ∧
    ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
      ∀ κ : ℝ, 0 < κ → κ ≤ (1 + g) / 4 →
        ∃ Lg pEcc : ℝ, 1 ≤ Lg ∧ 0 ≤ pEcc ∧
          ∀ (abar : Mat d) (a : CoeffSpace d) (x : ℝ), 1 ≤ x →
            GoodScale g κ abar a x →
            ∀ s₀ : ℝ, s₀ ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ) →
              ∀ (ρ Rad : ℝ) (U : Set (Vec d)),
                (∃ j : ℤ, ∃ z : Vec d,
                  U = (fun y : Vec d =>
                    z + matVecMul (matSqrt (symmPart abar)) y) ''
                    openCubeSet (originCube d j)) →
                HasBallSandwich
                  (matImage ((matSqrt (symmPart abar))⁻¹) U) ρ Rad →
                U ⊆ ellipsoid abar 1 →
                ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U →
                  ∀ ε : ℝ, 0 < ε →
                    x * (Lg * eccentricityFoldFactor abar pEcc) ≤ ε⁻¹ →
                    ∀ g₀ : H1Function U,
                      (∃ Lb : ℝ, ∀ᵐ y ∂volume.restrict U,
                        |g₀.toFun y| +
                          Real.sqrt (vecNormSq (g₀.grad y)) ≤ Lb) →
                      hsNormSq U s₀ g₀.grad ≠ ⊤ →
                      ∀ h : H1Function U,
                        MemAffineH10 U g₀ h →
                        IsWeakSolutionOn (fun _ => abar) U h.grad →
                        ∀ (uFun : Vec d → ℝ) (uGrad : Vec d → Vec d),
                          MemH1a0 (scaledCoeff ε a) U
                            (fun y => uFun y - g₀.toFun y)
                            (fun y => uGrad y - g₀.grad y) →
                          IsWeakSolutionOn (scaledCoeff ε a) U uGrad →
                          negSobolevNorm U s₀
                              (fun y => matVecMul (matSqrt (symmPart abar))
                                (uGrad y - h.grad y)) +
                            negSobolevNorm U s₀
                              (fun y => matVecMul (matSqrt (symmPart abar))⁻¹
                                (matVecMul (scaledCoeff ε a y - skewPart abar)
                                    (uGrad y) -
                                  matVecMul (symmPart abar) (h.grad y))) ≤
                            ENNReal.ofReal
                                (C₀ s₀ ρ Rad *
                                  (ε * (x *
                                    (Lg * eccentricityFoldFactor abar pEcc)))
                                      ^ κ) *
                              hsNormSq U s₀
                                  (fun y => matVecMul
                                    (matSqrt (symmPart abar)) (g₀.grad y)) ^
                                (1 / 2 : ℝ)

end

end RowSupply
end HighContrast
end HCPolySupport
