/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineH10
public import LeanPool.HighContrastHomogenization.Analytic.AffineNegSobolevNorm
public import LeanPool.HighContrastHomogenization.Analytic.H1a0ToH10
public import LeanPool.HighContrastHomogenization.Provider.Initialization.IdentityGrid
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.AffineCoeffFamily
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedRootCoefficient
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledLocalizationAssembly
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.ABK26.FluxComparisonLocalization
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.CenteredCubeFractionalCZFullNorm
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Certificate.PrintOrderDecoupledTerminalSurface
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.L2RowAlgebra
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellDomain
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineTransfer
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalEquation
public import LeanPool.HighContrastHomogenization.Provider.Regularity.ObservationCoefficientTransport
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderIdentityCubeDualRegularity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarseFluxResponseRHS

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.CellFamilyAndFluxRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Cell-based physical forced families and the flux-response row

This module constructs a zero-forcing cube solution by restricting the
physical weak solution to each cell of an enlarged-margin ruled Whitney
system.  It then prices the resulting physical flux-defect row by the coarse
flux-response row.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open Book Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Almost-everywhere invariance -/

theorem cubeBesovDualFullNorm_congr_ae_on_ruledCell (Q : TriadicCube d) (s : ℝ)
    {f g : Vec d → ℝ}
    (hfg : f =ᵐ[volume.restrict (cubeSet Q)] g) :
    cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f =
      cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g := by
  have hpair : ∀ φ : Vec d → ℝ,
      cubeBesovPairing Q f φ = cubeBesovPairing Q g φ := by
    intro φ
    unfold cubeBesovPairing
    refine cubeAverage_eq_of_ae_eq_on_cubeSet ?_
    filter_upwards [hfg] with x hx
    rw [hx]
  unfold cubeBesovDualFullNorm
  congr 1
  ext r
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨φ, hφ, by rw [hpair φ]⟩
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨φ, hφ, by rw [hpair φ]⟩

theorem physicalFullDualBesovVectorNorm_congr_ae_on_ruledCell
    (Q : TriadicCube d) (s : ℝ) {F G : Vec d → Vec d}
    (hFG : F =ᵐ[volume.restrict (cubeSet Q)] G) :
    physicalFullDualBesovVectorNorm Q s F =
      physicalFullDualBesovVectorNorm Q s G := by
  unfold physicalFullDualBesovVectorNorm
  refine Finset.sum_congr rfl fun i _hi => ?_
  refine cubeBesovDualFullNorm_congr_ae_on_ruledCell Q s ?_
  filter_upwards [hFG] with x hx
  rw [hx]

/-- The full-dual Whitney cell energy is invariant under almost-everywhere
equality on an enlarged-margin ruled cell. -/
theorem physicalFullDualWhitneyFamilyCellEnergy_congr_ae_on_ruledCell
    {U : Set (Vec d)} {rho Rad s : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (F G : system.CellIndex → Vec d → Vec d)
    (hFG : ∀ i, F i =ᵐ[volume.restrict (system.cell i)] G i)
    (i : system.CellIndex) :
    physicalFullDualWhitneyFamilyCellEnergy system s F i =
      physicalFullDualWhitneyFamilyCellEnergy system s G i := by
  have hcube : F i =ᵐ[volume.restrict
      (cubeSet (whitneyCellCube system i))] G i := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    simpa only [openCubeSet_whitneyCellCube] using hFG i
  unfold physicalFullDualWhitneyFamilyCellEnergy
  exact congrArg (fun t : ℝ => ENNReal.ofReal t ^ 2)
    (physicalFullDualBesovVectorNorm_congr_ae_on_ruledCell
      (whitneyCellCube system i) s hcube)

/-! ## The forced equation on one cell -/

private theorem isForcedEquation_zero_of_isWeakSolutionOn_cube
    {Q : TriadicCube d} {a : CoeffFamily d}
    (u : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d)))
    (hu : IsWeakSolutionOn (a.coeffOn Q).toCoeffField
      (Book.Ch02.cubeDomain Q : Set (Vec d)) u.grad) :
    IsForcedEquation Q a u (0 : Vec d → Vec d) := by
  have hEll : IsAEEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
      (Book.Ch02.cubeDomain Q : Set (Vec d)) (a.coeffOn Q).toCoeffField :=
    ⟨(Book.Ch02.cubeDomain Q).measurableSet,
      (a.coeffOn Q).aeStronglyMeasurable, (a.coeffOn Q).aeElliptic⟩
  have hflux : MemVectorL2 (Book.Ch02.cubeDomain Q : Set (Vec d))
      (fun x => matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x)) :=
    hEll.memVectorL2_matVecMul u.grad_memVectorL2
  have hsol : IsSolenoidalOn (Book.Ch02.cubeDomain Q : Set (Vec d))
      (fun x => matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x)) := by
    refine IsSolenoidalOn.of_test_of_contDiff_of_memVectorL2 hflux
      (Book.Ch02.cubeDomain Q).isOpen ?_
    intro psi hpsi hsupp hsub
    have hzero := (hu psi ⟨hpsi, hsupp, hsub⟩).2
    have hfun :
        (fun x => vecDot
          (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
          (fun i => (fderiv ℝ psi x) (basisVec i))) =
        fun x => vecDot (smoothGrad psi x)
          (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x)) := by
      funext x
      rw [vecDot_comm]
      rfl
    rw [hfun]
    exact hzero
  have hweak : IsH1DirichletRhsWeakSolutionOn
      (a.coeffOn Q).toCoeffField
      (Book.Ch02.cubeDomain Q : Set (Vec d)) u (0 : Vec d → Vec d) :=
    IsH1DirichletRhsWeakSolutionOn.of_residual_solenoidal
      hflux MeasureTheory.MemLp.zero
      (by simpa only [Pi.zero_apply, sub_zero] using hsol)
  simpa only [IsForcedEquation] using! hweak

/-- A physical weak solution restricts to a zero-forcing solution on every
triadic cube contained in its domain. -/
theorem exists_cellCoeffFamily_and_forcedEquation [NeZero d]
    {U : Set (Vec d)}
    (aSource : Source.AKL.Field d)
    (haSource : AEUniformlyEllipticField aSource)
    (aPhysical : CoeffField d)
    (haeSource : (⇑aSource : CoeffField d) =ᵐ[volume] aPhysical)
    (u : H1Function U)
    (huPhysical : IsWeakSolutionOn aPhysical U u.grad)
    (Q : TriadicCube d) (hQ : openCubeSet Q ⊆ U) :
    ∃ (aCell : CoeffFamily d) (uCell : H1Function (openCubeSet Q)),
      ((aCell.coeffOn Q).toCoeffField
          =ᵐ[volumeMeasureOn (openCubeSet Q)] aPhysical) ∧
        (∀ x, uCell.grad x = u.grad x) ∧
        IsForcedEquation Q aCell uCell (0 : Vec d → Vec d) := by
  obtain ⟨f, hfm, hfa, hfp⟩ :=
    exists_locally_pointwise_elliptic_representative haSource
  let aReg : RegCoeffField d := regCoeffFieldOfBallPointwiseElliptic f hfm hfp
  have haReg : Book.Ch04.AELocallyUniformlyEllipticField aReg :=
    aeLocallyUniformlyEllipticField_of_ball_pointwise hfm hfp
  let aCell : CoeffFamily d :=
    Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField aReg haReg
  have hfaPhysical : f =ᵐ[volume] aPhysical := hfa.symm.trans haeSource
  have hcoeff : ((aCell.coeffOn Q).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet Q)] aPhysical) := by
    change f =ᵐ[volume.restrict (openCubeSet Q)] aPhysical
    exact ae_restrict_of_ae hfaPhysical
  let uCell : H1Function (openCubeSet Q) :=
    u.restrict (isOpen_openCubeSet Q) hQ
  have hPhysicalV : IsWeakSolutionOn aPhysical (openCubeSet Q) u.grad :=
    IsWeakSolutionOn.mono hQ huPhysical
  have hPhysicalF : IsWeakSolutionOn f (openCubeSet Q) u.grad :=
    IsWeakSolutionOn.congr_ae
      (ae_restrict_of_ae hfaPhysical.symm) _root_.Filter.EventuallyEq.rfl hPhysicalV
  have hForced : IsForcedEquation Q aCell uCell (0 : Vec d → Vec d) := by
    apply isForcedEquation_zero_of_isWeakSolutionOn_cube uCell
    simpa only [aCell, aReg,
      Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField_coeffOn_toCoeffField,
      regCoeffFieldOfBallPointwiseElliptic_toFun, uCell,
      H1Function.restrict] using! hPhysicalF
  exact ⟨aCell, uCell, hcoeff, fun _ => rfl, hForced⟩

/-! ## The family over the enlarged-margin ruled system -/

/-- On each ruled cell, the coefficient family agrees almost everywhere with
the physical coefficient and the forced solution has the physical gradient. -/
@[expose]
def RuledCellPhysicalForcedFamily
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (aPhysical : CoeffField d) (u : H1Function U)
    (aCell : system.CellIndex → CoeffFamily d)
    (wCell : ∀ i, ForcedCubeSolution (whitneyCellCube system i) (aCell i)
      (0 : Vec d → Vec d)) : Prop :=
  (∀ i, ((aCell i).coeffOn (whitneyCellCube system i)).toCoeffField
      =ᵐ[volume.restrict (system.cell i)] aPhysical) ∧
  (∀ i x, (wCell i).toH1.grad x = u.grad x)

/-- The cell-based physical forced family exists over every enlarged-margin
ruled Whitney system. -/
theorem exists_ruledCellPhysicalForcedFamily [NeZero d]
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (aSource : Source.AKL.Field d)
    (haSource : AEUniformlyEllipticField aSource)
    (aPhysical : CoeffField d)
    (haeSource : (⇑aSource : CoeffField d) =ᵐ[volume] aPhysical)
    (u : H1Function U)
    (huPhysical : IsWeakSolutionOn aPhysical U u.grad) :
    ∃ (aCell : system.CellIndex → CoeffFamily d)
      (wCell : ∀ i, ForcedCubeSolution (whitneyCellCube system i) (aCell i)
        (0 : Vec d → Vec d)),
      RuledCellPhysicalForcedFamily system aPhysical u aCell wCell := by
  classical
  have hpoint : ∀ i : system.CellIndex,
      ∃ (aC : CoeffFamily d)
        (uC : H1Function (openCubeSet (whitneyCellCube system i))),
        ((aC.coeffOn (whitneyCellCube system i)).toCoeffField
            =ᵐ[volumeMeasureOn (openCubeSet (whitneyCellCube system i))]
          aPhysical) ∧
          (∀ x, uC.grad x = u.grad x) ∧
          IsForcedEquation (whitneyCellCube system i) aC uC
            (0 : Vec d → Vec d) := by
    intro i
    refine exists_cellCoeffFamily_and_forcedEquation aSource haSource
      aPhysical haeSource u huPhysical (whitneyCellCube system i) ?_
    rw [openCubeSet_whitneyCellCube]
    exact system.cell_subset i
  choose aCell uCell hcoeff hgrad hforced using hpoint
  refine ⟨aCell, fun i => ⟨uCell i, hforced i⟩, ?_, ?_⟩
  · intro i
    have hcoeffCell := hcoeff i
    rwa [openCubeSet_whitneyCellCube] at hcoeffCell
  · intro i x
    exact hgrad i x

/-! ## The flux-response row -/

/-- The explicit constant in the coarse flux-response estimate. -/
@[expose]
def coarseFluxResponseConstant (d : ℕ) [NeZero d] : ℝ :=
  (d : ℝ) ^ 2 *
    max 1
      (((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) *
        (2 * ZeroTraceDirichletCorrectorData.zeroTraceFluxApexConstant d 1))

/-- The physical flux-defect row is bounded by the coarse flux-response row of
the cell-based forced family. -/
theorem physicalFluxDefectRow_le_coarseResponseRow [NeZero d]
    {U : Set (Vec d)} {rho Rad s : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hs : 0 < s) (hsOne : s < 1)
    (aPhysical : CoeffField d) (u : H1Function U)
    (a0 : system.CellIndex → ConstantCoeffMatrix d)
    (aCell : system.CellIndex → CoeffFamily d)
    (wCell : ∀ i, ForcedCubeSolution (whitneyCellCube system i) (aCell i)
      (0 : Vec d → Vec d))
    (hfamily : RuledCellPhysicalForcedFamily system aPhysical u aCell wCell) :
    normalizedWhitneyRowEnergy system
        (physicalFullDualWhitneyFamilyCellEnergy system s
          (ruledPhysicalFluxDefectOnCell system aPhysical a0 u)) ≤
      normalizedWhitneyRowEnergy system (fun i =>
        ENNReal.ofReal
          (physicalDualBesovScaleFactor
              (whitneyCellCube system i) s *
            coarseFluxResponseWithRHSRHS (coarseFluxResponseConstant d)
              (whitneyCellCube system i) (aCell i) (a0 i) s
                (0 : Vec d → Vec d) (wCell i)) ^ 2) := by
  obtain ⟨hcoeff, hgrad⟩ := hfamily
  have hcong : ∀ i,
      physicalFullDualWhitneyFamilyCellEnergy system s
          (ruledPhysicalFluxDefectOnCell system aPhysical a0 u) i =
        physicalFullDualWhitneyFamilyCellEnergy system s
          (fun j => forcedSolutionFluxDefectField (whitneyCellCube system j)
            (aCell j) (a0 j) (wCell j)) i := by
    refine physicalFullDualWhitneyFamilyCellEnergy_congr_ae_on_ruledCell system _ _ ?_
    intro j
    filter_upwards [hcoeff j] with x hx
    show matVecMul (aPhysical x - (a0 j).matrix) (u.grad x) =
      matVecMul (((aCell j).coeffOn (whitneyCellCube system j)).toCoeffField x -
        (a0 j).matrix) ((wCell j).toH1.grad x)
    rw [hx, hgrad j x]
  refine normalizedWhitneyRowEnergy_mono system fun i => ?_
  rw [hcong i]
  have hraw := coarseFluxResponseRHS_negativeDual_le
    (whitneyCellCube system i) (aCell i) (a0 i) (wCell i) hs hsOne
    (forceBesovRegularity_zero (whitneyCellCube system i) s)
  have hfactor : 0 ≤ physicalDualBesovScaleFactor
      (whitneyCellCube system i) s :=
    physicalDualBesovScaleFactor_nonneg _ _
  have hnorm : physicalFullDualBesovVectorNorm
      (whitneyCellCube system i) s
      (forcedSolutionFluxDefectField (whitneyCellCube system i)
        (aCell i) (a0 i) (wCell i)) ≤
      physicalDualBesovScaleFactor (whitneyCellCube system i) s *
        coarseFluxResponseWithRHSRHS (coarseFluxResponseConstant d)
          (whitneyCellCube system i) (aCell i) (a0 i) s
            (0 : Vec d → Vec d) (wCell i) := by
    rw [physicalFullDualBesovVectorNorm_eq_scaleFactor_mul_normalized]
    exact mul_le_mul_of_nonneg_left hraw hfactor
  show ENNReal.ofReal (physicalFullDualBesovVectorNorm
      (whitneyCellCube system i) s _) ^ 2 ≤ _
  exact pow_le_pow_left₀ (by positivity)
    (ENNReal.ofReal_le_ofReal hnorm) 2

end

end RowSupply
end HighContrast
end HCPolySupport
