/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.SubcellCoefficientGluing
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.AdjointHeadEnergyCarrier
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.CoarseBlockPerCellInput
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.DiagonalWeakNormAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.HeadEnergyCarrier
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ParentEnergyMapPort
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ScaleAverageSeminorm

/-!
# High-contrast homogenization: Entry.Response.Kernel.RecentredCarrierHypotheses

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The recentred per-cell hypotheses at the estimate's own carriers

For the recentred coefficient `a_- = a - g`, this file supplies the two per-cell hypotheses the
diagonal weak-norm estimate needs at its own carriers: the older-scale tail's per-cell bound,
controlling the metric square of a transported parent-cell average by the printed geometric square
times twice the subcell energy average, and the head's per-cell bound, obtained by carrying a
pointwise elliptic representative of the recentred coefficient since `IsEllipticFieldOn` is
pointwise while a point of `CoeffSpace` is only an almost-everywhere class. It then bounds the
finite-window head of the cell-average estimate `l.weaknorms.moreproto` by two finite defect sums,
using a per-cell metric bound for the recent parent/child optimizer difference together with an
averaged bound on the difference energies, both now available at the estimate's own grid.
-/

section
/-!
## The tail's per-cell hypothesis at the estimate's own carriers

`scaleTail_carrier` (`CentredVarianceTailRoute.lean`) is the per-scale older-scale bound
at the estimate's carriers.  Its only analytic input is `hcell`: for every aligned depth-`n`
subcell, the metric square of the transported cell average of the parent optimizer field is
bounded by the printed geometric square times twice the subcell energy average.

`parentEnergyMap_port` (`ParentEnergyMapPort.lean`) proves exactly that shape, but
at a pointwise elliptic representative of the recentred coefficient and with the subcell energy
written through the restricted Chapter-2 solution `z`.  This module supplies that data from the
parent harmonic optimizer and transports the port's conclusion back to the estimate's carrier.

The transport uses the pointwise elliptic representative of the recentred field on the parent
cell (`exists_globally_elliptic_representative_ae_eq_on`): it is the same field on every aligned
subcell, so the parent optimizer is harmonic against it there, and it is a.e. equal to
`respCoeffMinus F a` on the parent cell, so the cell average and the energy density are unchanged.
`Book.Ch02.Solution.ofAEEq` / `Response.aHarmonicOfAEEq` and the restriction
`exists_restrict_solution_adaptedCellAtCenter` produce the restricted Chapter-2 solution.  Finally
`weakOptimizerEnergy_sq` and a.e. invariance replace the port's energy square by the
estimate's volume average.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub coarseBlock
  exists_globally_elliptic_representative_ae_eq_on normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

private theorem coarseBlockMatrix_respCoeffMinus_of_ellipticRepresentative
    (jStar : ℕ) (F : BlockMat d) (hgrid : IsUnit (respGrid jStar F))
    (t : ℤ) (n : ℕ) (a : CoeffSpace d) (lam0 Lam' : ℝ)
    (hlam0 : 0 < lam0) (hle' : lam0 ≤ Lam')
    (f : CoeffField d) (hae : respCoeffMinus F a =ᵐ[volumeMeasureOn (respCell jStar F t)] f)
    (hEllOf : ∀ (S : Set (Vec d)) (_hS : MeasurableSet S),
      IsEllipticFieldOn lam0 Lam' S f) :
    ∀ w ∈ triadicIndexBox d n,
      Book.Ch02.coarseBlockMatrix
          (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (coeffOnOfIsEllipticFieldOn hlam0 hle'
            (hEllOf (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet))
        = blockCongr (respG F)
          (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a) := by
  intro w hw
  have hsub : adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w ⊆ respCell jStar F t :=
    adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw
  have hcell : respCoeffMinus F a =ᵐ[volumeMeasureOn
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hsub le_rfl) hae
  have hcellSymm : f =ᵐ[volumeMeasureOn
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)] respCoeffMinus F a := by
    filter_upwards [hcell] with x hx
    exact hx.symm
  have hae_w : Book.Ch02.CoeffOn.AEEq
      (coeffOnOfIsEllipticFieldOn hlam0 hle'
        (hEllOf (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet))
      (canonicalRespCoeffMinusOnAt (respGrid jStar F) hgrid (t - (n : ℤ)) w F a) := by
    change (coeffOnOfIsEllipticFieldOn hlam0 hle'
        (hEllOf (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet)).toCoeffField
      =ᵐ[volumeMeasureOn
        ((adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) : Set (Vec d))]
        (canonicalRespCoeffMinusOnAt (respGrid jStar F) hgrid (t - (n : ℤ)) w F a).toCoeffField
    rw [canonicalRespCoeffMinusOnAt_toFun]
    exact hcellSymm
  rw [Book.Ch02.coarseBlockMatrix_eq_ofAEEq hae_w]
  exact isCoarseBlockMatrix_respCoeffMinus (respGrid jStar F) hgrid (t - (n : ℤ)) w F a
    (canonicalRespCoeffMinusOnAt (respGrid jStar F) hgrid (t - (n : ℤ)) w F a)
    (canonicalRespCoeffMinusOnAt_toFun (respGrid jStar F) hgrid (t - (n : ℤ)) w F a)

omit [NeZero d] in
private theorem doubledFieldEnergy_average_congr_of_ae_eq
    (jStar : ℕ) (F : BlockMat d) (t : ℤ) (n : ℕ)
    (X X' : (w : Fin d → ℤ) → Vec d → BlockVec d)
    (hX : ∀ w ∈ triadicIndexBox d n,
      X w =ᵐ[volumeMeasureOn (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)] X' w) :
    ∀ w ∈ triadicIndexBox d n,
      2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (fun x => vecDot (X w x).1 (X w x).2)
        = 2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (fun x => vecDot (X' w x).1 (X' w x).2) := by
  intro w hw
  unfold volumeAverage
  congr 1
  congr 1
  exact MeasureTheory.integral_congr_ae
    ((hX w hw).fun_comp (fun z => vecDot z.1 z.2))

omit [NeZero d] in
private theorem cellAverage_congr_ae_on_recentCells
    (jStar : ℕ) (F : BlockMat d) (t : ℤ) (n : ℕ)
    (X X' : (w : Fin d → ℤ) → Vec d → BlockVec d)
    (hX : ∀ w ∈ triadicIndexBox d n,
      X w =ᵐ[volumeMeasureOn (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)] X' w) :
    ∀ w ∈ triadicIndexBox d n,
      cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (X w)
        = cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (X' w) := by
  intro w hw
  exact cellAverage_congr_ae (subset_refl _) (hX w hw)

omit [NeZero d] in
private theorem optimizerDifference_ae_eq_of_field_and_gradient
    (U V : Set (Vec d)) (f c : CoeffField d)
    (uRep : AHarmonicFunction f U) (u : AHarmonicFunction c U)
    (vRep : AHarmonicFunction f V) (v : AHarmonicFunction c V)
    (hcoef : f =ᵐ[volumeMeasureOn V] c)
    (hgrad_u : uRep.toH1.grad = u.toH1.grad)
    (hgrad_v : vRep.toH1.grad = v.toH1.grad) :
    (fun x => optimizerField f uRep x - optimizerField f vRep x)
      =ᵐ[volumeMeasureOn V]
    (fun x => optimizerField c u x - optimizerField c v x) := by
  filter_upwards [hcoef] with x hx
  have hfirst : (optimizerField f uRep x - optimizerField f vRep x).1
      = (optimizerField c u x - optimizerField c v x).1 := by
    simp only [optimizerField, Prod.fst_sub]
    rw [hgrad_u, hgrad_v]
  have hsecond : (optimizerField f uRep x - optimizerField f vRep x).2
      = (optimizerField c u x - optimizerField c v x).2 := by
    simp only [optimizerField, Prod.snd_sub, hx]
    rw [hgrad_u, hgrad_v]
  exact Prod.ext hfirst hsecond

/-- **The per-cell hypothesis of the older-scale tail.**  For an invertible selected grid, a
generation `t`, a depth `n`, and a parent harmonic optimizer attached to the recentred response
coefficient, every aligned depth-`n` subcell satisfies the per-cell metric bound of
`scaleTail_carrier`: the transported cell-average metric square of the parent optimizer field
is at most the printed geometric square times twice its energy average.  The bound is the
port `parentEnergyMap_port` at a pointwise elliptic representative, transported back along the
a.e. equality of the representative with `respCoeffMinus F a`; the cell-average step and the energy
step are both a.e. invariant. -/
theorem tailCell_of_bridge (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (n : ℕ)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hm : (explicitCanonicalMetric F).PosDef)
    (hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef)
    (hEhat : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))}) :
    ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffMinus F a) u)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffMinus F a) u)))
        ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
            * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2 *
          (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => vecDot (optimizerField (respCoeffMinus F a) u x).1
              (optimizerField (respCoeffMinus F a) u x).2)) := by
  classical
  -- A pointwise elliptic representative of the recentred field on the parent cell.
  have hParentConv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
    adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hgrid t
  obtain ⟨lam0, Lam0, fa, hlam0, _hle0, hmeas_fa, hEll_fa, hae_fa⟩ :=
    exists_globally_elliptic_representative_ae_eq_on (a := (a.1 : Source.AKL.Field d)) a.2
      hParentConv.isBoundedDomain.isBounded
  let f : CoeffField d := fun x => fa x - respg F
  let Lam' : ℝ := 2 * Lam0 + 2 * ‖respg F‖ ^ 2 / lam0
  have hle' : lam0 ≤ Lam' := by
    have hn : 0 ≤ 2 * ‖respg F‖ ^ 2 / lam0 := by positivity
    dsimp only [Lam']
    linarith only [hlam0, _hle0, hn]
  have hEllFaOf : ∀ (S : Set (Vec d)) (_hS : MeasurableSet S),
      IsEllipticFieldOn lam0 Lam0 S fa := by
    intro S hS
    refine ⟨?_, fun x _ => hEll_fa x⟩
    exact Measurable.of_eval fun i => Measurable.of_eval fun j =>
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hmeas_fa)).ite hS
        measurable_const
  have hEllOf : ∀ (S : Set (Vec d)) (hS : MeasurableSet S),
      IsEllipticFieldOn lam0 Lam' S f := by
    intro S hS
    have h := isEllipticFieldOn_sub_skew (hEllFaOf S hS) (respg F) (respg_isSkew F)
    simpa only [f, Lam'] using h
  have hae : respCoeffMinus F a =ᵐ[volumeMeasureOn (respCell jStar F t)] f := by
    filter_upwards [hae_fa] with x hx
    simp only [respCoeffMinus, f]
    rw [hx]
  have hEllParent : IsEllipticFieldOn lam0 Lam' (respCell jStar F t) f :=
    hEllOf (respCell jStar F t) hParentConv.isOpen.measurableSet
  let parentRepCoeff : Book.Ch02.CoeffOn (adaptedDomain (respGrid jStar F) hgrid t) :=
    coeffOnOfIsEllipticFieldOn hlam0 hle' hEllParent
  let aU : (w : Fin d → ℤ) → Book.Ch02.CoeffOn
      (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) :=
    fun w => coeffOnOfIsEllipticFieldOn hlam0 hle'
      (hEllOf (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet)
  let uRep : AHarmonicFunction f (respCell jStar F t) :=
    Response.aHarmonicOfAEEq hae u
  let zeroH : AHarmonicFunction f (respCell jStar F t) :=
    ⟨0, isAHarmonicGradient_zero⟩
  -- The parent optimizer on the representative; the branch outside the box is irrelevant and
  -- exists only so that the port's total hypotheses are supplied.
  let uFam : (w : Fin d → ℤ) → AHarmonicFunction (aU w).toCoeffField (respCell jStar F t) :=
    fun w => if hw : w ∈ triadicIndexBox d n then uRep else zeroH
  have hzExists : ∀ (w : Fin d → ℤ), w ∈ triadicIndexBox d n →
      ∃ z : Book.Ch02.Solution (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (aU w),
        z.toH1.grad = uRep.toH1.grad := by
    intro w hw
    exact exists_restrict_solution_adaptedCellAtCenter (respGrid jStar F) hgrid t n hw
      (lam := lam0) (Lam := Lam') (b := parentRepCoeff) (c := aU w) rfl
      (hEllOf (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet)
      uRep
  let zFam : (w : Fin d → ℤ) → Book.Ch02.Solution
      (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w) :=
    fun w => if hw : w ∈ triadicIndexBox d n then Classical.choose (hzExists w hw)
      else Book.Ch02.zeroSolution (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
        (aU w)
  have hzFam : ∀ w, (zFam w).toH1.grad = (uFam w).toH1.grad := by
    intro w
    by_cases hw : w ∈ triadicIndexBox d n
    · have hz : zFam w = Classical.choose (hzExists w hw) := dite_eq_left hw
      have hu : uFam w = uRep := dite_eq_left hw
      rw [hz, hu]
      exact Classical.choose_spec (hzExists w hw)
    · have hz : zFam w = Book.Ch02.zeroSolution
          (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w) := dite_eq_right hw
      have hu : uFam w = zeroH := dite_eq_right hw
      rw [hz, hu]
      rfl
  have hEllFam : ∀ w : Fin d → ℤ, IsEllipticFieldOn (aU w).lam (aU w).Lam
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (aU w).toCoeffField :=
    fun w => hEllOf (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
      (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet
  have hcoarseFam := coarseBlockMatrix_respCoeffMinus_of_ellipticRepresentative
    jStar F hgrid t n a lam0 Lam' hlam0 hle' f hae hEllOf
  have hport := parentEnergyMap_port (P := P) (γ := γ) (jStar := jStar) (F := F) (t := t)
    (hgrid := hgrid) (a := a) (n := n) (aU := aU) (V := respCell jStar F t)
    (u := uFam) (z := zFam) (hz := hzFam) (hEll := hEllFam)
    (hm := hm) (hEmean := hEmean) (hEhat := hEhat) (hM0 := hM0) (hbdd := hbdd)
    (hcoarse := hcoarseFam)
  intro w hw
  have h := hport w hw
  have huFam_w : uFam w = uRep := dite_eq_left hw
  have haU_w : (aU w).toCoeffField = f := rfl
  have huRep_grad : uRep.toH1.grad = u.toH1.grad := rfl
  have hgrad_z : (zFam w).toH1.grad = u.toH1.grad := by
    rw [hzFam w, huFam_w]
    exact huRep_grad
  have hcellAvg : cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (optimizerField (aU w).toCoeffField (uFam w))
      = cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (optimizerField (respCoeffMinus F a) u) := by
    refine cellAverage_congr_ae (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n
      hw) ?_
    filter_upwards [hae.symm] with x hx
    rw [huFam_w]
    simp only [optimizerField, huRep_grad, haU_w, hx]
  have haeSub : f =ᵐ[volumeMeasureOn (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)]
      respCoeffMinus F a := by
    filter_upwards [MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono
      (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw) le_rfl) hae] with x hx
    exact hx.symm
  have hnn : 0 ≤ volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
      (fun x => vecDot (optimizerField (aU w).toCoeffField (zFam w) x).1
        (optimizerField (aU w).toCoeffField (zFam w) x).2) :=
    volumeAverage_energyDensity_nonneg_of_aeEq
      (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet hlam0
      (hEllOf (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet)
      (Filter.EventuallyEq.rfl) (zFam w)
  have hEw : weakOptimizerEnergy (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (aU w).toCoeffField (zFam w) ^ 2
      = volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (fun x => vecDot (optimizerField (respCoeffMinus F a) u x).1
          (optimizerField (respCoeffMinus F a) u x).2) := by
    refine (weakOptimizerEnergy_sq (u := zFam w) hnn).trans ?_
    unfold volumeAverage
    congr 1
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [haeSub] with x hx
    simp only [optimizerField, hgrad_z, haU_w]
    rw [← hx]
  rw [hcellAvg, hEw] at h
  exact h

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The head's per-cell hypothesis at the estimate's own carriers

`tailCell_of_bridge` supplies the per-cell hypothesis of the older-scale tail by carrying a
**pointwise elliptic representative** of the recentred coefficient: `IsEllipticFieldOn` is
pointwise, while a point of `CoeffSpace d` is only an a.e. class, so the recentred field cannot be
fed to the port directly.  This module performs the same representative transport for the
**recent difference** instead of the parent state.

The port is `recentEnergyMap_port`, whose data are the parent optimizer restricted to each
aligned subcell and a child optimizer attached to the same coefficient there.  The difference of
the two optimizer fields is a single doubled state on the subcell, and on the subcell the
pointwise block identity `X · 𝐀 X = 2 ξ · a ξ` converts the port's Chapter-2 difference energy
into the estimate's `2 * volumeAverage` shape.  Both the cell average and the energy average are
a.e. invariant under the representative, so the conclusion returns to `respCoeffMinus F a`.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub coarseBlock
  exists_globally_elliptic_representative_ae_eq_on normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The per-cell hypothesis of the head's recent difference.**  For an invertible selected grid,
a generation `t`, a depth `n`, a parent harmonic optimizer attached to the recentred response
coefficient and a child optimizer on every aligned depth-`n` subcell, the transported cell-average
metric square of the difference of their optimizer fields is at most the printed geometric square
times twice the difference energy average there.

The bound is the recent-difference port `recentEnergyMap_port` at a pointwise elliptic
representative of `respCoeffMinus F a`, transported back along the a.e. equality of the
representative with `respCoeffMinus F a`.  The port's right-hand side, the Chapter-2 average of the
doubled block energy density of the difference, is converted to the estimate's `2 * volumeAverage`
through the pointwise identity for a doubled state `(ξ, a ξ)`; both the cell average and the energy
average are a.e. invariant, so the conclusion is stated at `respCoeffMinus F a`. -/
theorem headCell_of_bridge (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (n : ℕ)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (v : (w : Fin d → ℤ) → AHarmonicFunction (respCoeffMinus F a)
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w))
    (hm : (explicitCanonicalMetric F).PosDef)
    (hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef)
    (hEhat : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))}) :
    ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (fun x => optimizerField (respCoeffMinus F a) u x -
                optimizerField (respCoeffMinus F a) (v w) x)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (fun x => optimizerField (respCoeffMinus F a) u x -
                optimizerField (respCoeffMinus F a) (v w) x)))
        ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
            * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2 *
          (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => vecDot
              (optimizerField (respCoeffMinus F a) u x -
                optimizerField (respCoeffMinus F a) (v w) x).1
              (optimizerField (respCoeffMinus F a) u x -
                optimizerField (respCoeffMinus F a) (v w) x).2)) := by
  classical
  -- A pointwise elliptic representative of the recentred field on the parent cell.
  have hParentConv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
    adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hgrid t
  obtain ⟨lam0, Lam0, fa, hlam0, _hle0, hmeas_fa, hEll_fa, hae_fa⟩ :=
    exists_globally_elliptic_representative_ae_eq_on (a := (a.1 : Source.AKL.Field d)) a.2
      hParentConv.isBoundedDomain.isBounded
  let f : CoeffField d := fun x => fa x - respg F
  let Lam' : ℝ := 2 * Lam0 + 2 * ‖respg F‖ ^ 2 / lam0
  have hle' : lam0 ≤ Lam' := by
    have hn : 0 ≤ 2 * ‖respg F‖ ^ 2 / lam0 := by positivity
    dsimp only [Lam']
    linarith only [hlam0, _hle0, hn]
  have hEllFaOf : ∀ (S : Set (Vec d)) (_hS : MeasurableSet S),
      IsEllipticFieldOn lam0 Lam0 S fa := by
    intro S hS
    refine ⟨?_, fun x _ => hEll_fa x⟩
    exact Measurable.of_eval fun i => Measurable.of_eval fun j =>
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hmeas_fa)).ite hS
        measurable_const
  have hEllOf : ∀ (S : Set (Vec d)) (hS : MeasurableSet S),
      IsEllipticFieldOn lam0 Lam' S f := by
    intro S hS
    have h := isEllipticFieldOn_sub_skew (hEllFaOf S hS) (respg F) (respg_isSkew F)
    simpa only [f, Lam'] using h
  have hae : respCoeffMinus F a =ᵐ[volumeMeasureOn (respCell jStar F t)] f := by
    filter_upwards [hae_fa] with x hx
    simp only [respCoeffMinus, f]
    rw [hx]
  have hEllParent : IsEllipticFieldOn lam0 Lam' (respCell jStar F t) f :=
    hEllOf (respCell jStar F t) hParentConv.isOpen.measurableSet
  let parentRepCoeff : Book.Ch02.CoeffOn (adaptedDomain (respGrid jStar F) hgrid t) :=
    coeffOnOfIsEllipticFieldOn hlam0 hle' hEllParent
  let aU : (w : Fin d → ℤ) → Book.Ch02.CoeffOn
      (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) :=
    fun w => coeffOnOfIsEllipticFieldOn hlam0 hle'
      (hEllOf (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet)
  let uRep : AHarmonicFunction f (respCell jStar F t) :=
    Response.aHarmonicOfAEEq hae u
  -- The parent optimizer restricted to each aligned subcell.
  have hzExists : ∀ (w : Fin d → ℤ), w ∈ triadicIndexBox d n →
      ∃ z : Book.Ch02.Solution (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (aU w),
        z.toH1.grad = uRep.toH1.grad := by
    intro w hw
    exact exists_restrict_solution_adaptedCellAtCenter (respGrid jStar F) hgrid t n hw
      (lam := lam0) (Lam := Lam') (b := parentRepCoeff) (c := aU w) rfl
      (hEllOf (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet)
      uRep
  let zFam : (w : Fin d → ℤ) → Book.Ch02.Solution
      (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w) :=
    fun w => if hw : w ∈ triadicIndexBox d n then Classical.choose (hzExists w hw)
      else Book.Ch02.zeroSolution (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
        (aU w)
  have hzFam : ∀ w ∈ triadicIndexBox d n, (zFam w).toH1.grad = uRep.toH1.grad := by
    intro w hw
    dsimp only [zFam]
    rw [dite_eq_left hw]
    exact Classical.choose_spec (hzExists w hw)
  -- The child optimizer transported along the representative restricted to its subcell.
  have haeSub : ∀ w ∈ triadicIndexBox d n,
      respCoeffMinus F a =ᵐ[volumeMeasureOn
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)] f := by
    intro w hw
    exact MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono
      (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw) le_rfl) hae
  let vFam : (w : Fin d → ℤ) → Book.Ch02.Solution
      (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w) :=
    fun w => if hw : w ∈ triadicIndexBox d n then
        Response.aHarmonicOfAEEq (haeSub w hw) (v w)
      else Book.Ch02.zeroSolution (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
        (aU w)
  have hvFam : ∀ w ∈ triadicIndexBox d n, (vFam w).toH1.grad = (v w).toH1.grad := by
    intro w hw
    dsimp only [vFam]
    rw [dite_eq_left hw]
    rfl
  have hEllFam : ∀ w : Fin d → ℤ, IsEllipticFieldOn (aU w).lam (aU w).Lam
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (aU w).toCoeffField :=
    fun w => hEllOf (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
      (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet
  -- The coarse-block identification, exactly as in the tail module.
  have hcoarseFam := coarseBlockMatrix_respCoeffMinus_of_ellipticRepresentative
    jStar F hgrid t n a lam0 Lam' hlam0 hle' f hae hEllOf
  -- The two optimizer differences: on the representative, and at the estimate's coefficient.
  let Xf : (w : Fin d → ℤ) → Vec d → BlockVec d :=
    fun w x => optimizerField (aU w).toCoeffField (zFam w) x -
      optimizerField (aU w).toCoeffField (vFam w) x
  let Xr : (w : Fin d → ℤ) → Vec d → BlockVec d :=
    fun w x => optimizerField (respCoeffMinus F a) u x -
      optimizerField (respCoeffMinus F a) (v w) x
  -- The representative and the recentred coefficient agree a.e. on every aligned subcell.
  have hXae : ∀ w ∈ triadicIndexBox d n,
      Xf w =ᵐ[volumeMeasureOn (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)] Xr w := by
    intro w hw
    simpa only [Xf, Xr, optimizerField, aU, coeffOnOfIsEllipticFieldOn, hzFam w hw] using
      optimizerDifference_ae_eq_of_field_and_gradient
        (respCell jStar F t) (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        f (respCoeffMinus F a) uRep u (vFam w) (v w) (haeSub w hw).symm rfl (hvFam w hw)
  -- The Chapter-2 difference energy is the doubled pointwise energy on the representative.
  have hAve_f : ∀ w ∈ triadicIndexBox d n,
      Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (fun x => blockVecDot (Xf w x)
            (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x) (Xf w x)))
        = 2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => vecDot (Xf w x).1 (Xf w x).2) := by
    intro w hw
    have hpt : Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (fun x => blockVecDot (Xf w x)
            (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x) (Xf w x)))
        = Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (fun x => 2 * vecDot (Xf w x).1 (Xf w x).2) := by
      refine Book.Ch02.average_eq_of_ae_eq ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w).measurableSet] with x hx
      have hdet : IsUnit (symmPart ((aU w).toCoeffField x)).det :=
        isUnit_det_symmPart_of_isEllipticMatrix ((hEllFam w).2 x hx)
      have h2 : (Xf w x).2 = matVecMul ((aU w).toCoeffField x) (Xf w x).1 := by
        simp only [Xf, optimizerField, Prod.fst_sub, Prod.snd_sub]
        rw [matVecMul_sub_vec]
      have hX : Xf w x = ((Xf w x).1, matVecMul ((aU w).toCoeffField x) (Xf w x).1) :=
        Prod.ext rfl h2
      rw [hX, blockMatrixField_apply (aU w) x,
        blockEnergyDensity_primal hdet (Xf w x).1]
    rw [hpt]
    change
      (MeasureTheory.volume (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)).toReal⁻¹ *
        ∫ x in (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w),
          2 * vecDot (Xf w x).1 (Xf w x).2
      = 2 * ((MeasureTheory.volume (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ))
        w)).toReal⁻¹ *
        ∫ x in (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w),
          vecDot (Xf w x).1 (Xf w x).2)
    rw [MeasureTheory.integral_const_mul]
    ring
  -- The representative's difference energy is nonnegative; the difference is a doubled state.
  have hnonneg_f : ∀ w ∈ triadicIndexBox d n,
      0 ≤ volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (fun x => vecDot (Xf w x).1 (Xf w x).2) := by
    intro w hw
    unfold volumeAverage
    refine mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) ?_
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet] with x hx
    have hslot : (Xf w x).2 = matVecMul ((aU w).toCoeffField x) (Xf w x).1 := by
      simp only [Xf, optimizerField, Prod.fst_sub, Prod.snd_sub]
      rw [matVecMul_sub_vec]
    rw [hslot]
    exact le_trans (mul_nonneg hlam0.le (vecNormSq_nonneg _))
      (((hEllFam w).2 x hx).2.2.1 (Xf w x).1)
  -- The Chapter-2 difference energy at the recentred coefficient.
  have hAve_r : ∀ w ∈ triadicIndexBox d n,
      Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (fun x => blockVecDot (Xf w x)
            (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x) (Xf w x)))
        = 2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => vecDot (Xr w x).1 (Xr w x).2) := by
    intro w hw
    rw [hAve_f w hw]
    exact doubledFieldEnergy_average_congr_of_ae_eq jStar F t n Xf Xr hXae w hw
  -- The port's positivity input: the difference energy is nonnegative.
  have hG : ∀ w ∈ triadicIndexBox d n,
      0 ≤ Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (fun x => blockVecDot (Xf w x)
            (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x) (Xf w x))) := by
    intro w hw
    rw [hAve_f w hw]
    exact mul_nonneg (by norm_num) (hnonneg_f w hw)
  have hport := recentEnergyMap_port (P := P) (γ := γ) (jStar := jStar) (F := F) (t := t)
    (hgrid := hgrid) (a := a) (n := n) (aU := aU) (u := zFam) (v := vFam)
    (hEll := hEllFam) (hm := hm) (hEmean := hEmean) (hEhat := hEhat) (hM0 := hM0)
    (hbdd := hbdd) (hcoarse := hcoarseFam) (hG := hG)
  -- The cell average is a.e. invariant under the representative.
  have hcellAvg := cellAverage_congr_ae_on_recentCells jStar F t n Xf Xr hXae
  intro w hw
  have h := hport w hw
  rw [hcellAvg w hw, hAve_r w hw] at h
  exact h

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The finite-window head of the cell-average estimate, at the estimate's own carriers

The recent head of `l.weaknorms.moreproto` is bounded by the two finite defect sums once two
analytic facts are supplied at each depth: a per-cell metric bound for the recent difference of
the parent optimizer and a child optimizer, and an averaged bound for the difference energies.
Both are now available at the estimate's own grid, sample, metric and maximizer, so the head
carries no analytic hypothesis of its own: the coefficient's positive definiteness comes from the
law-integrability of the coarse block on the cell, and every geometric input from invertibility of
the selected grid.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock blockSub coarseBlock
  normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The finite-window head of the cell-average estimate, at the carriers.**  On the branch
where the all-scale maximum does not exceed `1`, the `3^{-n/2}`-weighted sum over the window
`n ≤ H` of the normalized `L²` averages of the recentred transported subcell averages is bounded
by `16 K L` times the sum of the two finite defect sums, where `K` is the square root of the
printed spectral bound of the normalized reference block and `L` the square root of the response
load. -/
theorem recentHead_carrier_minus (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) (a : CoeffSpace d)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1) :
    ∑ n ∈ Finset.range (H + 1),
        (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (optimizerField (respCoeffMinus F a) u) -
                    cellAverage (respCell jStar F t)
                      (optimizerField (respCoeffMinus F a) u)))
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (optimizerField (respCoeffMinus F a) u) -
                    cellAverage (respCell jStar F t)
                      (optimizerField (respCoeffMinus F a) u))))
      ≤ 16 *
          Real.sqrt
            (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
          Real.sqrt (respLsqMinus P jStar F t e) *
          (weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
              (respCoeffMinus F a) +
            weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ) (respEhatMinus P
              jStar F t)
              (respCoeffMinus F a)) := by
  classical
  have hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef :=
    respEhatMinus_posDef_of_integrable hgrid t hint
  have hM0 : (toFullBlockMat (respM0 F)).PosDef :=
    respM0_posDef_of_isUnit_respGrid hgrid
  have hm : (explicitCanonicalMetric F).PosDef :=
    explicitCanonicalMetric_posDef_of_isUnit_respGrid hgrid
  have hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    respMean_posDef_of_integrable hgrid t hint
  have h1u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).1 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) := fun n _ w hw j =>
    (integrableOn_optimizerField_respCoeffMinus_box (respGrid jStar F) hgrid t F a u n w
      hw j).1
  have h2u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).2 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) := fun n _ w hw j =>
    (integrableOn_optimizerField_respCoeffMinus_box (respGrid jStar F) hgrid t F a u n w
      hw j).2
  obtain ⟨V, hV⟩ :=
    recentHead_actual_of_analytic P γ hγ jStar H F t e hgrid a u hu hE hM0 hgood h1u h2u
  refine hV (fun n _ w _ j =>
      (integrableOn_optimizerField_respCoeffMinus_at (respGrid jStar F) hgrid
        (t - (n : ℤ)) w F a ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) j).1)
    (fun n _ w _ j =>
      (integrableOn_optimizerField_respCoeffMinus_at (respGrid jStar F) hgrid
        (t - (n : ℤ)) w F a ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) j).2)
    (fun n => ?_)
  refine ⟨fun w => 2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
    (fun x => vecDot
      (optimizerField (respCoeffMinus F a) u x -
        optimizerField (respCoeffMinus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).1
      (optimizerField (respCoeffMinus F a) u x -
        optimizerField (respCoeffMinus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).2), ?_, ?_⟩
  · exact headCell_of_bridge P γ jStar F t hgrid a n u
      (fun w => (V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) hm hEmean hE hM0 hbdd
  · exact headEnergy_carrier_minus P jStar F t e hgrid a n u hu
      (fun w => (V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)
      (fun w _ => (V n w).isMaximizer) hE

end

end HCPolySupport.HighContrast.Multiscale
end
