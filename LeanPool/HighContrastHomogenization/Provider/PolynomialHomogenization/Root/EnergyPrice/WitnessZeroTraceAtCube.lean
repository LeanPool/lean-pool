/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.EnergyPrice.ForceBesovFromHsNormSq
public import LeanPool.HighContrastHomogenization.Analytic.AffineH1a0
public import LeanPool.HighContrastHomogenization.Analytic.H1a0ToH10
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.Translation

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.EnergyPrice.WitnessZeroTraceAtCube

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Gate R3, core: the witness zero-trace difference, at the gauge cube

`DirichletForcedCubeSolution` needs a `zeroTraceDifference` at the **triadic
cube**, while the frozen clause states it as `MemH1a0` on the **physical**
domain (`168:45-47`).  Every link of the transport is and public —

* `memH1a0_affinePullback` (`HCPoly.Analytic.AffineH1a0`) — the matrix
  gauge;
* `matImage_inv_affineImage` — the gauge image is a translate of the cube;
* `exists_h10Function_of_memH1a0` (`HCPoly.Analytic.H1a0ToH10`) — the
  `H¹₀` realization, with *literal* field equalities;
* `H10Function.untranslate` (CoarseGraining) — the translation half —

but **no declaration composes them**: every existing affine lemma is
either pure-matrix (`matImage L⁻¹`) or pure-translation (`translateSet z`).
This file supplies the composite.
-/

namespace HCPolySupport
namespace HighContrast
namespace EnergyPrice

open Book Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **Gate R3, core.**  The physical `MemH1a0` zero-trace datum of the frozen
clause becomes an honest `H¹₀` function on the gauge triadic cube, with its
value and gradient given by the gauge-and-translate pullback. -/
theorem exists_h10Function_gaugeCube_of_memH1a0 [NeZero d]
    {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hUmeas : MeasurableSet U) (hUfin : volume U ≠ ⊤)
    {b : CoeffField d} {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    {lamG LamG : ℝ} (hlamG : 0 < lamG)
    (hellG : ∀ᵐ x ∂volume,
      IsEllipticMatrix lamG LamG (affineCoefficient L hL b x))
    {Q : TriadicCube d} {c : Vec d}
    (hgauge : matImage L⁻¹ U = translateSet c (openCubeSet Q))
    (hconv : IsOpenBoundedConvexDomain (translateSet c (openCubeSet Q)))
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemH1a0 b U u Du) :
    ∃ w : H10Function (openCubeSet Q),
      (∀ y, w.toH1Function.toFun y = u (matVecMul L (y + c))) ∧
      (∀ y, w.toH1Function.grad y =
        matVecMul (matTranspose L) (Du (matVecMul L (y + c)))) := by
  have h1 := memH1a0_affinePullback hL hUmeas hlam hell hUfin hu
  rw [hgauge] at h1
  obtain ⟨w0, hw0f, hw0g⟩ :=
    exists_h10Function_of_memH1a0 hconv hlamG hellG h1
  refine ⟨H10Function.untranslate c w0, ?_, ?_⟩
  · intro y
    have hstep : (H10Function.untranslate c w0).toH1Function.toFun y =
        w0.toH1Function.toFun (y + c) := rfl
    rw [hstep, hw0f]
  · intro y
    have hstep : (H10Function.untranslate c w0).toH1Function.grad y =
        w0.toH1Function.grad (y + c) := rfl
    rw [hstep, hw0g]

/-- **Gate R3, packaged.**  Given the four pieces, the witness Dirichlet
cube solution exists with its `toH1` the prescribed (pulled-back) solution and
its `boundaryData` the prescribed (pulled-back) datum — the combination no
constructor provides. -/
@[expose]
def witnessDirichletForcedCubeSolution {Q : TriadicCube d}
    {aFam : CoeffFamily d}
    (uObs gObs : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d)))
    (hforced : IsForcedEquation Q aFam uObs (0 : Vec d → Vec d))
    (hzero : ∃ w : H10Function (Book.Ch02.cubeDomain Q : Set (Vec d)),
      w.toH1Function.toFun =ᵐ[volumeMeasureOn
          (Book.Ch02.cubeDomain Q : Set (Vec d))]
        fun x => uObs.toFun x - gObs.toFun x) :
    DirichletForcedCubeSolution Q aFam (0 : Vec d → Vec d) where
  toH1 := uObs
  boundaryData := gObs
  weakSolution := hforced
  zeroTraceDifference := hzero

end

end EnergyPrice
end HighContrast
end HCPolySupport
