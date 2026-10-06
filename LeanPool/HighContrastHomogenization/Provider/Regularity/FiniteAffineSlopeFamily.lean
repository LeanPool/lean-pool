/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSlopeMatrix

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineSlopeFamily

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Valid finite affine slope families

This module records the source-proved forward best-fit slope bounds and a
joint family of proof-gated inverse matrices. It deliberately contains no
same-vector comparison between inverse matrices at different scales.
-/

namespace HCPolySupport
namespace HighContrast

open scoped ENNReal

noncomputable section

/-- One finite family of inverse best-fit slope matrices, characterized by
two-sided inverse identities and the source-proved forward-slope estimates. -/
structure IsFiniteAffineSlopeFamily
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (delta C : ℝ) (n m : ℤ) (Q : ℤ → Mat d) : Prop where
  isUnit_det :
    ∀ (k : ℤ) (_hk : k ∈ Finset.Icc n m), IsUnit (Q k).det
  slopeMatrix_mul_inverse :
    ∀ (k : ℤ) (hk : k ∈ Finset.Icc n m),
      finiteAffineBestFitSlopeMatrix a k m (Finset.mem_Icc.mp hk).2 * Q k = 1
  inverse_mul_slopeMatrix :
    ∀ (k : ℤ) (hk : k ∈ Finset.Icc n m),
      Q k * finiteAffineBestFitSlopeMatrix a k m (Finset.mem_Icc.mp hk).2 = 1
  flatness_at :
    ∀ (k : ℤ) (hk : k ∈ Finset.Icc n m) (e : Vec d),
      normalizedAffineCandidateError (originCube d k)
          (finiteAffineSolution a m (matVecMul (Q k) e)).toH1.toFun
          (finiteAffineBestFitIntercept a k m
            (Finset.mem_Icc.mp hk).2 (matVecMul (Q k) e))
          e ≤
        C * delta * euclideanNorm e
  bestFitEnergy_lower :
    ∀ (k : ℤ) (hk : k ∈ Finset.Icc n m) (b : Vec d),
      ENNReal.ofReal
          (C⁻¹ * euclideanNorm
            (finiteAffineBestFitSlope a k m
              (Finset.mem_Icc.mp hk).2 b)) ≤
        weightedGradNorm
          (a.coeffOn (originCube d k)).toCoeffField
          (openCubeSet (originCube d k))
          (finiteAffineSolution a m b).toH1.grad
  bestFitEnergy_upper :
    ∀ (k : ℤ) (hk : k ∈ Finset.Icc n m) (b : Vec d),
      weightedGradNorm
          (a.coeffOn (originCube d k)).toCoeffField
          (openCubeSet (originCube d k))
          (finiteAffineSolution a m b).toH1.grad ≤
        ENNReal.ofReal
          (C * euclideanNorm
            (finiteAffineBestFitSlope a k m
              (Finset.mem_Icc.mp hk).2 b))
  bestFitSlope_lower :
    ∀ (j : ℤ) (hj : j ∈ Finset.Icc n m)
      (k : ℤ) (hk : k ∈ Finset.Icc n m), j ≤ k → ∀ b : Vec d,
      (1 - C * delta) ^ Int.toNat (k - j) *
          euclideanNorm
            (finiteAffineBestFitSlope a j m
              (Finset.mem_Icc.mp hj).2 b) ≤
        euclideanNorm
          (finiteAffineBestFitSlope a k m
            (Finset.mem_Icc.mp hk).2 b)
  bestFitSlope_upper :
    ∀ (j : ℤ) (hj : j ∈ Finset.Icc n m)
      (k : ℤ) (hk : k ∈ Finset.Icc n m), j ≤ k → ∀ b : Vec d,
      euclideanNorm
          (finiteAffineBestFitSlope a k m
            (Finset.mem_Icc.mp hk).2 b) ≤
        (1 + C * delta) ^ Int.toNat (k - j) *
          euclideanNorm
            (finiteAffineBestFitSlope a j m
              (Finset.mem_Icc.mp hj).2 b)
  terminal_matrixNorm :
    Book.Ch02.matrixNorm (Q m - 1) ≤ C * delta
  small :
    C * delta ≤ (1 / 2 : ℝ)

end

end HighContrast
end HCPolySupport
