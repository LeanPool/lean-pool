/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexCubeComparison
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.DeterministicCore
public import LeanPool.HighContrastHomogenization.Provider.Regularity.GoodTail
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.GeneralCoarseGrainingL2TwoExponent
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarseCaccioppoliRHS.ZeroTraceValue
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.H1Transport
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfaces.AECongruence

/-!
# High-contrast homogenization: Provider.Regularity.HarmonicReplacement

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Identity harmonic replacement on centered cubes

This module selects the identity-coefficient harmonic comparison with the same
boundary trace as a high-contrast weak solution.  The quantitative estimates
use the scale-separated Chapter 3 comparison theorem, so the response error is
evaluated at a strictly lower order than the output norm.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The chosen identity-coefficient harmonic comparison datum for a weak
solution on a centered triadic cube. -/
@[expose]
noncomputable def identityHarmonicReplacementDatum {d : ℕ}
    (a : Book.Ch03.CoeffFamily d) (m : ℤ)
    (u : H1Function (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
    (hu : IsWeakSolutionOn (a.coeffOn (originCube d m)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) u.grad) :
    Book.Ch03.CoarseGrainingComparisonDatum (originCube d m) a
      (identityConstantCoeffMatrix d) (0 : Vec d → Vec d) :=
  Classical.choose
    (exists_identityCoarseGrainingComparisonDatum_of_hcWeakSolution u hu)

/-- The solution component of the chosen comparison datum is the original
weak solution. -/
@[simp] theorem identityHarmonicReplacementDatum_u {d : ℕ}
    (a : Book.Ch03.CoeffFamily d) (m : ℤ)
    (u : H1Function (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
    (hu : IsWeakSolutionOn (a.coeffOn (originCube d m)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) u.grad) :
    (identityHarmonicReplacementDatum a m u hu).u = u :=
  Classical.choose_spec
    (exists_identityCoarseGrainingComparisonDatum_of_hcWeakSolution u hu)

/-- The chosen replacement solves the identity-coefficient homogeneous weak
equation and has the same boundary trace as the original solution. -/
theorem identityHarmonicReplacementDatum_characterization {d : ℕ}
    (a : Book.Ch03.CoeffFamily d) (m : ℤ)
    (u : H1Function (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
    (hu : IsWeakSolutionOn (a.coeffOn (originCube d m)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) u.grad) :
    Book.Ch03.IsConstantCoeffForcedEquation (originCube d m)
        (identityConstantCoeffMatrix d)
        (identityHarmonicReplacementDatum a m u hu).v (0 : Vec d → Vec d) ∧
      ∃ w : H10Function
          (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)),
        w.toH1Function.toFun =ᵐ[
          volumeMeasureOn
            (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
          fun x ↦ u.toFun x -
            (identityHarmonicReplacementDatum a m u hu).v.toFun x := by
  let W := identityHarmonicReplacementDatum a m u hu
  have hWu : W.u = u := identityHarmonicReplacementDatum_u a m u hu
  refine ⟨W.vWeakSolution, ?_⟩
  simpa [W, hWu] using W.zeroTraceDifference

private theorem homogenizationComparisonFluxSeminorm_nonneg
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch03.CoeffFamily d) (a0 : Book.Ch03.ConstantCoeffMatrix d)
    (s : ℝ) (hs : 0 < s)
    (u v : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d))) :
    0 ≤ cubeBesovNegativeVectorSeminormTwo Q s
      (Book.Ch03.homogenizationComparisonFluxField Q a a0 u v) := by
  have huGrad : MemVectorL2 (cubeSet Q) u.grad := by
    simpa using (Book.Ch03.publicH1ToCubeSet u).grad_memVectorL2
  have hvGrad : MemVectorL2 (cubeSet Q) v.grad := by
    simpa using (Book.Ch03.publicH1ToCubeSet v).grad_memVectorL2
  have hEll0 :
      IsEllipticFieldOn a0.lam a0.Lam (cubeSet Q)
        (constantCoeffField a0.matrix) :=
    Book.Ch03.constantCoeffMatrix_isEllipticFieldOn_constantCoeffField a0
      (measurableSet_cubeSet Q)
  let Ginternal : Vec d → Vec d :=
    fluxComparison (Book.Ch03.publicCoeffField Q a) a0.matrix u.grad v.grad
  have hfluxA : MemVectorL2 (cubeSet Q)
      (fun x ↦ matVecMul (Book.Ch03.publicCoeffField Q a x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_cubeSet Q a) huGrad
  have hflux0 : MemVectorL2 (cubeSet Q)
      (fun x ↦ matVecMul a0.matrix (v.grad x)) := by
    simpa [constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll0 hvGrad
  have hGinternal : MemVectorL2 (cubeSet Q) Ginternal := by
    dsimp [Ginternal, fluxComparison]
    exact hfluxA.sub hflux0
  have hae :
      Book.Ch03.homogenizationComparisonFluxField Q a a0 u v
        =ᵐ[volumeMeasureOn (cubeSet Q)] Ginternal :=
    Book.Ch03.homogenizationComparisonFluxField_ae_eq_fluxComparison_publicCoeffField_cubeSet
      (Q := Q) (a := a) (a0 := a0) u v
  have hmem : MemVectorL2 (cubeSet Q)
      (Book.Ch03.homogenizationComparisonFluxField Q a a0 u v) :=
    MeasureTheory.MemLp.ae_eq hae.symm hGinternal
  have hmemNormalized :
      MeasureTheory.MemLp
        (Book.Ch03.homogenizationComparisonFluxField Q a a0 u v)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hmem
  exact cubeBesovNegativeVectorSeminormTwo_nonneg_of_memLp Q hs _ hmemNormalized

end

end HighContrast
end HCPolySupport
