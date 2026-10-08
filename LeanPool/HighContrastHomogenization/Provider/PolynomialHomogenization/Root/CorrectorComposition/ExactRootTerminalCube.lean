/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.ExactRootPullback
public import LeanPool.HighContrastHomogenization.Analytic.EllipsoidGeometry
public import LeanPool.HighContrastHomogenization.Analytic.CoefficientLocality
public import LeanPool.HighContrastHomogenization.Provider.Regularity.H1aOpenSubsetGradientRealization
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleCubeRestriction
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedCenteredCoeffFamily
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedEllipsoidTriadicGeometry
public import LeanPool.HighContrastHomogenization.Analytic.AffineWeakGradient
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineGradientQuotientInverse
public import LeanPool.HighContrastHomogenization.Provider.Selection.EnclosureGeometry
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedAffineFields
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedPhysicalDirichletAffineResponse
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedWeakSolutionPullback
public import LeanPool.HighContrastHomogenization.Support.Probability.LocalEllipticitySlices

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.ExactRootTerminalCube

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The exact-root terminal cube solution — the large-scale C¹ slope approximation clause residue (b1)

The large-scale C¹ slope approximation terminal `ExactRootGaugeTerminal` splits
into four items, of which exactly one, **(b1)**, is new content:

> a terminal `CubeSolution` on `originCube d m` for the exact-root reference
> family, from `MemH1a` + `IsWeakSolutionOn` on the ball
> [the exact-root analogue of the rounded ellipsoid terminal cube solution]

The obstruction is a strict negative consumer: the terminal's corrector-family premise is
`∀ Q, (aRounded.coeffOn Q).toCoeffField =ᵐ[volume] roundedCenteredCoefficient
abar hS ⇑a.1`, and the exact-root family satisfies the *exact-root* identity
instead.

**That mismatch is the whole of it.**  The proof never uses any
property of `baseRoundedGrid` beyond invertibility and symmetry, both of which
the exact root has (`CorrectorComposition.isUnit_det_exactRoot`,
`CorrectorComposition.matTranspose_exactRoot`).  This module runs the same proof at
`Selection.normalizedRoot (symmPart abar)` and yields the terminal cube solution for
the exact-root family, so **(b1) is discharged**.

Two deliberate differences from the statement:

* the terminal generation `m` is a **parameter** together with the geometric
  premise `matImage (Selection.normalizedRoot (symmPart abar)) (openCubeSet
  (originCube d m)) ⊆ ellipsoid abar R`, rather than the fixed
  `roundedEllipsoidTerminalGeneration`.  The large-scale C¹ slope approximation clause packaging
  needs to choose `m`
  against the *inner*-cube side of the volume comparison, so pinning the
  generation inside the constructor would be the wrong interface.  Nothing is
  weakened: the generation is one admissible choice.
* the corrector-family premise is stated against the exact-root coefficient
  `affineCoefficient (Selection.normalizedRoot (symmPart abar)) _
  ⇑(normalizedCenteredCoeff a abar hS).1`, which is *literally* the large-scale C¹ slope
  approximation clause
  terminal's `bRef`.

No estimate is used and no hypothesis is added: the premise list is the
one with `roundedCenteredCoefficient` replaced by `bRef` and the
generation exposed.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- **The exact-root terminal cube solution.**  A physical `MemH1a` weak
solution on the radius-`R` ellipsoid gives a Chapter 3 cube solution, for the
exact-root reference family, on any origin cube whose exact-root image sits
inside the ellipsoid; its gradient is the exact-root pullback of the physical
one. -/
theorem exists_exactRootTerminalCubeSolution [NeZero d] (a : CoeffSpace d)
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    (aRef : Book.Ch03.CoeffFamily d)
    (hRefAE : ∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField =ᵐ[volume]
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          (isUnit_det_exactRoot hS)
          (⇑(normalizedCenteredCoeff a abar hS).1))
    {R : ℝ} (m : ℤ)
    (hm : matImage (Selection.normalizedRoot (symmPart abar))
        (openCubeSet (originCube d m)) ⊆ ellipsoid abar R)
    (u : Vec d → ℝ) (Du : Vec d → Vec d)
    (hu : MemH1a (⇑a.1 : CoeffField d) (ellipsoid abar R) u Du)
    (hweak : IsWeakSolutionOn (⇑a.1 : CoeffField d)
      (ellipsoid abar R) Du) :
    ∃ w : Book.Ch03.CubeSolution (originCube d m) aRef,
      w.toH1.grad =
        fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar))
          (Du (matVecMul (Selection.normalizedRoot (symmPart abar)) y)) := by
  let Lmat : Mat d := Selection.normalizedRoot (symmPart abar)
  let Q : TriadicCube d := originCube d m
  let U : Set (Vec d) := matImage Lmat (openCubeSet Q)
  have hLmat : IsUnit Lmat.det := isUnit_det_exactRoot hS
  have hUdomain : IsOpenBoundedConvexDomain U :=
    isOpenBoundedConvexDomain_matImage hLmat
      (isOpenBoundedConvexDomain_openCubeSet Q)
  let : IsFiniteMeasure (volumeMeasureOn U) :=
    hUdomain.isFiniteMeasure_restrict_volume
  have hUsub : U ⊆ ellipsoid abar R := hm
  obtain ⟨lam, Lam, c, hlam, _hlamLam, hell, hac⟩ :=
    a.2.exists_ae_isEllipticMatrix_ae_eq_restrict (isBounded_ellipsoid hS R)
  obtain ⟨uPhysical, huPhysicalGrad⟩ :=
    isPotentialOn_grad_on_openSubset_of_memH1a hUdomain hUsub
      (isBounded_ellipsoid hS R) hlam hell ((memH1a_congr_coeff hac u Du).mp hu)
  have hweakU : IsWeakSolutionOn (⇑a.1 : CoeffField d) U uPhysical.grad := by
    have hrestricted := hweak.mono hUsub
    simpa only [huPhysicalGrad] using hrestricted
  have hdomain : matImage Lmat⁻¹ U = openCubeSet Q :=
    matImage_inv_matImage hLmat (openCubeSet Q)
  have hweakPullRaw :=
    (isWeakSolutionOn_exactRootCenteredPullback_iff
      (abar := abar) hS hUdomain.isOpen
      (⇑a.1 : CoeffField d) uPhysical.memL2 uPhysical.gradMemL2
      uPhysical.hasWeakGradient).mp hweakU
  have hPullback :
      ∃ uRoot : H1Function (openCubeSet Q),
        uRoot.grad = fun y ↦ matVecMul Lmat (Du (matVecMul Lmat y)) := by
    let uPull := exactRootH1Pullback abar hS
      hUdomain.isOpen.measurableSet uPhysical
    have hgrad := exactRootH1Pullback_grad abar hS
      hUdomain.isOpen.measurableSet uPhysical
    have hPullbackRaw :
        ∃ v : H1Function (matImage Lmat⁻¹ U),
          v.grad = fun y ↦ matVecMul Lmat (Du (matVecMul Lmat y)) := by
      refine ⟨uPull, ?_⟩
      rw [hgrad, huPhysicalGrad]
    rw [hdomain] at hPullbackRaw
    exact hPullbackRaw
  obtain ⟨uRoot, huRootGrad⟩ := hPullback
  have hweakRootRaw :
      IsWeakSolutionOn (exactRootCenteredCoefficient abar hS (⇑a.1))
        (openCubeSet Q) uRoot.grad := by
    rw [huRootGrad]
    simpa only [Lmat, hdomain, huPhysicalGrad] using hweakPullRaw
  have hcoeffAE :
      exactRootCenteredCoefficient abar hS (⇑a.1) =ᵐ[
        volume.restrict (openCubeSet Q)]
          (aRef.coeffOn Q).toCoeffField :=
    ae_restrict_of_ae
      ((exactRootCenteredCoefficient_ae a abar hS).trans (hRefAE Q).symm)
  have hweakRoot :
      IsWeakSolutionOn (aRef.coeffOn Q).toCoeffField
        (openCubeSet Q) uRoot.grad :=
    hweakRootRaw.congr_ae hcoeffAE _root_.Filter.EventuallyEq.rfl
  have hEll : IsAEEllipticFieldOn
      (aRef.coeffOn Q).lam (aRef.coeffOn Q).Lam
      (openCubeSet Q) (aRef.coeffOn Q).toCoeffField := by
    refine ⟨measurableSet_openCubeSet Q, ?_, ?_⟩
    · intro i j
      simpa only [Book.Ch02.cubeDomain_coe] using
        (aRef.coeffOn Q).aeStronglyMeasurable i j
    · simpa only [Book.Ch02.cubeDomain_coe] using
        (aRef.coeffOn Q).aeElliptic
  have hflux : MemVectorL2 (openCubeSet Q)
      (fun x ↦ matVecMul ((aRef.coeffOn Q).toCoeffField x)
        (uRoot.grad x)) :=
    hEll.memVectorL2_matVecMul uRoot.grad_memVectorL2
  have hsolenoidal : IsSolenoidalOn (openCubeSet Q)
      (fun x ↦ matVecMul ((aRef.coeffOn Q).toCoeffField x)
        (uRoot.grad x)) := by
    apply IsSolenoidalOn.of_test_of_contDiff_of_memVectorL2
      hflux (isOpen_openCubeSet Q)
    intro psi hsmooth hcompact hsupport
    have hzero := (hweakRoot psi ⟨hsmooth, hcompact, hsupport⟩).2
    change ∫ x in openCubeSet Q,
      vecDot (matVecMul ((aRef.coeffOn Q).toCoeffField x)
          (uRoot.grad x)) (smoothGrad psi x) ∂volume = 0
    simpa only [vecDot_comm] using hzero
  let w : Book.Ch03.CubeSolution Q aRef :=
    { toH1 := uRoot
      isHarmonic := ⟨uRoot.isPotentialOn, hsolenoidal⟩ }
  exact ⟨w, huRootGrad⟩

end

end CorrectorComposition
end HighContrast
end HCPolySupport
