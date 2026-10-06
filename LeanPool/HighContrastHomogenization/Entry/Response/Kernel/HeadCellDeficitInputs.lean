/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.CoarseBlockPerCellInput
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ParentEnergyMapPort
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RecentScaleEnergyRoute
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ScaleAverageSeminorm

/-!
# High-contrast homogenization: Entry.Response.Kernel.HeadCellDeficitInputs

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The adjoint head-cell hypothesis and its algebraic inputs

For the adjoint sign, this file supplies the head's per-cell hypothesis at the diagonal weak-norm
estimate's own carriers — the estimate of `p.response.transfer` — by carrying a pointwise elliptic
representative of the recentred coefficient. It records that the normalized block commutes with a
finite average of cell defects, that the averaged response deficit and the response loads
`respLsq^∓`
are block quadratic forms linear in finite sums, and that the depth-`n` triadic subcells of an
adapted cell are pairwise disjoint and cover it up to a Lebesgue-null set.
-/

section
/-!
## The head's per-cell hypothesis at the estimate's own carriers, adjoint sign

`headCell_of_bridge` supplies the per-cell hypothesis of the recent difference by carrying a
**pointwise elliptic representative** of the recentred coefficient: `IsEllipticFieldOn` is
pointwise, while a point of `CoeffSpace d` is only an a.e. class, so the recentred field cannot be
fed to the port directly.  This module performs the same representative transport for the adjoint
recentred coefficient `a_+ = aᵀ + g`.

The port is `recentEnergyMap_port_plus`, whose data are the parent optimizer restricted to each
aligned subcell and a child optimizer attached to the same coefficient there.  The difference of
the two optimizer fields is a single doubled state on the subcell, and on the subcell the
pointwise block identity `X · 𝐀 X = 2 ξ · a ξ` converts the port's Chapter-2 difference energy
into the estimate's `2 * volumeAverage` shape.  Both the cell average and the energy average are
a.e. invariant under the representative, so the conclusion returns to `respCoeffPlus F a`.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub coarseBlock
  exists_globally_elliptic_representative_ae_eq_on normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The per-cell hypothesis of the head's recent difference, adjoint sign.**  For an invertible
selected grid, a generation `t`, a depth `n`, a parent harmonic optimizer attached to the
transposed recentred response coefficient and a child optimizer on every aligned depth-`n` subcell,
the transported cell-average metric square of the difference of their optimizer fields is at most
the printed geometric square times twice the difference energy average there.

The bound is the recent-difference port `recentEnergyMap_port_plus` at a pointwise elliptic
representative of `respCoeffPlus F a`, transported back along the a.e. equality of the
representative with `respCoeffPlus F a`.  The port's right-hand side, the Chapter-2 average of the
doubled block energy density of the difference, is converted to the estimate's `2 * volumeAverage`
through the pointwise identity for a doubled state `(ξ, a ξ)`; both the cell average and the energy
average are a.e. invariant, so the conclusion is stated at `respCoeffPlus F a`. -/
theorem headCell_of_bridge_plus (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (n : ℕ)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (v : (w : Fin d → ℤ) → AHarmonicFunction (respCoeffPlus F a)
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w))
    (hm : (explicitCanonicalMetric F).PosDef)
    (hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef)
    (hEhat : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
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
              (fun x => optimizerField (respCoeffPlus F a) u x -
                optimizerField (respCoeffPlus F a) (v w) x)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (fun x => optimizerField (respCoeffPlus F a) u x -
                optimizerField (respCoeffPlus F a) (v w) x)))
        ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))
            * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2 *
          (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => vecDot
              (optimizerField (respCoeffPlus F a) u x -
                optimizerField (respCoeffPlus F a) (v w) x).1
              (optimizerField (respCoeffPlus F a) u x -
                optimizerField (respCoeffPlus F a) (v w) x).2)) := by
  classical
  -- A pointwise elliptic representative of the adjoint recentred field on the parent cell.
  have hParentConv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
    adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hgrid t
  obtain ⟨lam0, Lam0, fa, hlam0, _hle0, hmeas_fa, hEll_fa, hae_fa⟩ :=
    exists_globally_elliptic_representative_ae_eq_on (a := (a.1 : Source.AKL.Field d)) a.2
      hParentConv.isBoundedDomain.isBounded
  let f : CoeffField d := fun x => matTranspose (fa x) + respg F
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
    have h := isEllipticFieldOn_transpose_add_skew (hEllFaOf S hS) (respg F) (respg_isSkew F)
    simpa only [f, Lam'] using h
  have hae : respCoeffPlus F a =ᵐ[volumeMeasureOn (respCell jStar F t)] f := by
    filter_upwards [hae_fa] with x hx
    simp only [respCoeffPlus, f]
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
      respCoeffPlus F a =ᵐ[volumeMeasureOn
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
  -- The coarse-block identification, exactly as in the adjoint tail module.
  have hcoarseFam : ∀ w ∈ triadicIndexBox d n,
      Book.Ch02.coarseBlockMatrix (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (aU w)
        = blockCongr (blockD d) (blockCongr (respG F)
            (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a)) := by
    intro w hw
    have hsub : adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w ⊆ respCell jStar F t :=
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw
    have hcell : respCoeffPlus F a =ᵐ[volumeMeasureOn
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)] f :=
      MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hsub le_rfl) hae
    have hcellSymm : f =ᵐ[volumeMeasureOn
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)] respCoeffPlus F a := by
      filter_upwards [hcell] with x hx
      exact hx.symm
    have hae_w : Book.Ch02.CoeffOn.AEEq (aU w)
        (canonicalRespCoeffPlusOnAt (respGrid jStar F) hgrid (t - (n : ℤ)) w F a) := by
      show (aU w).toCoeffField =ᵐ[volumeMeasureOn
        ((adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) : Set (Vec d))]
        (canonicalRespCoeffPlusOnAt (respGrid jStar F) hgrid (t - (n : ℤ)) w F a).toCoeffField
      rw [canonicalRespCoeffPlusOnAt_toFun]
      exact hcellSymm
    rw [Book.Ch02.coarseBlockMatrix_eq_ofAEEq hae_w]
    exact isCoarseBlockMatrix_respCoeffPlus (respGrid jStar F) hgrid (t - (n : ℤ)) w F a
      (canonicalRespCoeffPlusOnAt (respGrid jStar F) hgrid (t - (n : ℤ)) w F a)
      (canonicalRespCoeffPlusOnAt_toFun (respGrid jStar F) hgrid (t - (n : ℤ)) w F a)
  -- The two optimizer differences: on the representative, and at the estimate's coefficient.
  let Xf : (w : Fin d → ℤ) → Vec d → BlockVec d :=
    fun w x => optimizerField (aU w).toCoeffField (zFam w) x -
      optimizerField (aU w).toCoeffField (vFam w) x
  let Xr : (w : Fin d → ℤ) → Vec d → BlockVec d :=
    fun w x => optimizerField (respCoeffPlus F a) u x -
      optimizerField (respCoeffPlus F a) (v w) x
  -- The representative and the recentred coefficient agree a.e. on every aligned subcell.
  have hXae : ∀ w ∈ triadicIndexBox d n,
      Xf w =ᵐ[volumeMeasureOn (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)] Xr w := by
    intro w hw
    filter_upwards [haeSub w hw] with x hx
    have hg1 : (Xf w x).1 = (Xr w x).1 := by
      simp only [Xf, Xr, optimizerField, Prod.fst_sub]
      rw [hzFam w hw, hvFam w hw]
      rfl
    have hg2 : (Xf w x).2 = (Xr w x).2 := by
      simp only [Xf, Xr, optimizerField, Prod.snd_sub, hx]
      rw [hzFam w hw, hvFam w hw]
      rfl
    exact Prod.ext hg1 hg2
  -- The Chapter-2 difference energy is the doubled pointwise energy on the representative.
  have hXf : ∀ w x, (Xf w x).2 = matVecMul ((aU w).toCoeffField x) (Xf w x).1 := by
    intro w x
    simp only [Xf, optimizerField, Prod.fst_sub, Prod.snd_sub]
    rw [matVecMul_sub_vec]
  have hAve_f := blockEnergy_average_eq_twice_fieldEnergy (respGrid jStar F) hgrid t n
    aU Xf hEllFam hXf
  -- The representative's difference energy is nonnegative; the difference is a doubled state.
  have hnonneg_f := volumeAverage_nonneg_of_doubledField (respGrid jStar F) hgrid t n
    lam0 hlam0 aU Xf hEllFam hXf
  -- The Chapter-2 difference energy at the recentred coefficient.
  have hAve_r : ∀ w ∈ triadicIndexBox d n,
      Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (fun x => blockVecDot (Xf w x)
            (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x) (Xf w x)))
        = 2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => vecDot (Xr w x).1 (Xr w x).2) := by
    intro w hw
    rw [hAve_f w hw]
    unfold volumeAverage
    rw [show (∫ x in (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w),
            vecDot (Xf w x).1 (Xf w x).2)
          = ∫ x in (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w),
            vecDot (Xr w x).1 (Xr w x).2 from
        MeasureTheory.integral_congr_ae (by
          filter_upwards [hXae w hw] with x hx
          rw [hx])]
  -- The port's positivity input: the difference energy is nonnegative.
  have hG : ∀ w ∈ triadicIndexBox d n,
      0 ≤ Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (fun x => blockVecDot (Xf w x)
            (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x) (Xf w x))) := by
    intro w hw
    rw [hAve_f w hw]
    exact mul_nonneg (by norm_num) (hnonneg_f w hw)
  have hport := recentEnergyMap_port_plus (P := P) (γ := γ) (jStar := jStar) (F := F)
    (t := t) (hgrid := hgrid) (a := a) (n := n) (aU := aU) (u := zFam) (v := vFam)
    (hEll := hEllFam) (hm := hm) (hEmean := hEmean) (hEhat := hEhat) (hM0 := hM0)
    (hbdd := hbdd) (hcoarse := hcoarseFam) (hG := hG)
  -- The cell average is a.e. invariant under the representative.
  have hcellAvg : ∀ w ∈ triadicIndexBox d n,
      cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Xf w)
        = cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Xr w) := by
    intro w hw
    exact cellAverage_congr_ae (subset_refl _) (hXae w hw)
  intro w hw
  have h := hport w hw
  rw [hcellAvg w hw, hAve_r w hw] at h
  exact h

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The normalized block commutes with finite averages

`normalizedBlock H F = F^{-1/2} H F^{-1/2}` is linear in its first argument, so the flat
average of the normalized cell defects is the normalized block of the flat average of the
defects.  This file records that identity — in scalar, finite-set and recent-carrier form —
and then reads the resulting quadratic bound off the already proved Loewner comparison
`quadratic_le_norm_normalizedBlock`.

This is the algebraic half of the difference-energy step of the cell-average lemma: the
normalizing congruence is applied to the averaged defect rather than to each defect
separately.  Nothing here assumes a sign or a symmetry of the defect block, only that the
normalizing block is positive definite at the quadratic-bound consumer.
-/

open HCPolySupport.HighContrast (blockSub normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open scoped Matrix MatrixOrder
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem blockEnergy_average_eq_twice_fieldEnergy
    (q : Mat d) (hgrid : IsUnit q) (t : ℤ) (n : ℕ)
    (aU : (w : Fin d → ℤ) → Book.Ch02.CoeffOn
      (adaptedDomainAt q hgrid (t - (n : ℤ)) w))
    (X : (w : Fin d → ℤ) → Vec d → BlockVec d)
    (hEllFam : ∀ w : Fin d → ℤ,
      IsEllipticFieldOn (aU w).lam (aU w).Lam
        (adaptedCellAtCenter q (t - (n : ℤ)) w) (aU w).toCoeffField)
    (hX : ∀ w x, (X w x).2 = matVecMul ((aU w).toCoeffField x) (X w x).1) :
    ∀ w ∈ triadicIndexBox d n,
      Book.Ch02.average (adaptedDomainAt q hgrid (t - (n : ℤ)) w)
          (fun x => blockVecDot (X w x)
            (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x) (X w x)))
        = 2 * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (fun x => vecDot (X w x).1 (X w x).2) := by
  intro w hw
  have hpt : Book.Ch02.average (adaptedDomainAt q hgrid (t - (n : ℤ)) w)
        (fun x => blockVecDot (X w x)
          (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x) (X w x)))
      = Book.Ch02.average (adaptedDomainAt q hgrid (t - (n : ℤ)) w)
        (fun x => 2 * vecDot (X w x).1 (X w x).2) := by
    refine Book.Ch02.average_eq_of_ae_eq ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (adaptedDomainAt q hgrid (t - (n : ℤ)) w).measurableSet] with x hx
    have hdet : IsUnit (symmPart ((aU w).toCoeffField x)).det :=
      isUnit_det_symmPart_of_isEllipticMatrix ((hEllFam w).2 x hx)
    have h2 : (X w x).2 = matVecMul ((aU w).toCoeffField x) (X w x).1 := hX w x
    have hX : X w x = ((X w x).1, matVecMul ((aU w).toCoeffField x) (X w x).1) :=
      Prod.ext rfl h2
    rw [hX, blockMatrixField_apply (aU w) x,
      blockEnergyDensity_primal hdet (X w x).1]
  rw [hpt]
  show (MeasureTheory.volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal⁻¹ *
      ∫ x in (adaptedCellAtCenter q (t - (n : ℤ)) w),
        2 * vecDot (X w x).1 (X w x).2
    = 2 * ((MeasureTheory.volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal⁻¹ *
      ∫ x in (adaptedCellAtCenter q (t - (n : ℤ)) w),
        vecDot (X w x).1 (X w x).2)
  rw [MeasureTheory.integral_const_mul]
  ring

private theorem volumeAverage_nonneg_of_doubledField
    (q : Mat d) (hgrid : IsUnit q) (t : ℤ) (n : ℕ) (lam : ℝ) (hlam : 0 < lam)
    (aU : (w : Fin d → ℤ) → Book.Ch02.CoeffOn
      (adaptedDomainAt q hgrid (t - (n : ℤ)) w))
    (X : (w : Fin d → ℤ) → Vec d → BlockVec d)
    (hEllFam : ∀ w : Fin d → ℤ,
      IsEllipticFieldOn (aU w).lam (aU w).Lam
        (adaptedCellAtCenter q (t - (n : ℤ)) w) (aU w).toCoeffField)
    (hX : ∀ w x, (X w x).2 = matVecMul ((aU w).toCoeffField x) (X w x).1) :
    ∀ w ∈ triadicIndexBox d n,
      0 ≤ volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (fun x => vecDot (X w x).1 (X w x).2) := by
  intro w _
  unfold volumeAverage
  refine mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) ?_
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem
    (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet] with x hx
  rw [hX w x]
  exact le_trans (mul_nonneg hlam.le (vecNormSq_nonneg _))
    (((hEllFam w).2 x hx).2.2.1 (X w x).1)

/-- The normalization distributes over a finite weighted average: conjugating each summand by
the fixed root and then averaging is the same as conjugating the averaged defect.  The scalar
`c` is applied only to the output, so the identity holds for every finite set `Z`, including
the empty set and `c = 0`. -/
theorem normalizedBlock_finset_average {iota : Type*} (Z : Finset iota)
    (D : iota → BlockMat d) (F : BlockMat d) (c : ℝ) :
    c • ∑ w ∈ Z, toFullBlockMat (normalizedBlock (D w) F)
      = toFullBlockMat
          (normalizedBlock (ofFullBlockMat (c • ∑ w ∈ Z, toFullBlockMat (D w))) F) := by
  simp only [normalizedBlock, toFullBlockMat_ofFullBlockMat, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sum, Matrix.sum_mul]

/-- The recent averaged normalized defect of `weakAverageDefect` is the normalized block of
the flat average of the recent cell defects.  This is
`normalizedBlock_finset_average` at the triadic index box, the weight
`(card)⁻¹` and the recent coarse-block difference. -/
theorem weakAverageDefect_eq_normalizedBlock (q : Mat d) (t : ℤ) (n : ℕ) (E : BlockMat d)
    (b : CoeffField d) :
    weakAverageDefect q t n E b
      = normalizedBlock
          (ofFullBlockMat
            (((triadicIndexBox d n).card : ℝ)⁻¹ •
              ∑ w ∈ triadicIndexBox d n,
                toFullBlockMat
                  (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
                    (coarseBlockMatrix (HighContrast.adaptedCell q t) b))))
          E := by
  unfold weakAverageDefect
  rw [normalizedBlock_finset_average]
  rw [ofFullBlockMat_toFullBlockMat]

/-- The quadratic form of the flat recent average of the cell defects, read against a positive
definite metric `E`, is controlled by the operator norm of its `E`-normalized block times the
`E`-quadratic form of the test vector.  This is the difference-energy bound of the cell-average
lemma, obtained from `quadratic_le_norm_normalizedBlock` by identifying the normalized
block of the averaged defect with `weakAverageDefect`. -/
theorem average_defect_quadratic_le (q : Mat d) (t : ℤ) (n : ℕ) {E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) (b : CoeffField d) (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul
          (ofFullBlockMat
            (((triadicIndexBox d n).card : ℝ)⁻¹ •
              ∑ w ∈ triadicIndexBox d n,
                toFullBlockMat
                  (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
                    (coarseBlockMatrix (HighContrast.adaptedCell q t) b))))
          X)
      ≤ ‖toFullBlockMat (weakAverageDefect q t n E b)‖ * blockVecDot X (blockMatVecMul E X) := by
  have h := quadratic_le_norm_normalizedBlock E
    (ofFullBlockMat
      (((triadicIndexBox d n).card : ℝ)⁻¹ •
        ∑ w ∈ triadicIndexBox d n,
          toFullBlockMat
            (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
              (coarseBlockMatrix (HighContrast.adaptedCell q t) b))))
    hE X
  rw [← weakAverageDefect_eq_normalizedBlock q t n E b] at h
  exact h

end

end HCPolySupport.HighContrast.Multiscale
end

section
namespace HCPolySupport.HighContrast.Multiscale

open scoped Matrix MatrixOrder
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The doubled quadratic form of a finite sum of blocks is the sum of the quadratic forms: the
pairing `(X, Y) ↦ X · A Y` is linear in the flat representative `A`, and `ofFullBlockMat`
respects finite sums.  The identity holds for every finite index set, including the empty one. -/
theorem blockVecDot_finset_sum {iota : Type*} (Z : Finset iota) (D : iota → BlockMat d)
    (x : BlockVec d) :
    ∑ w ∈ Z, blockVecDot x (blockMatVecMul (D w) x)
      = blockVecDot x
          (blockMatVecMul (ofFullBlockMat (∑ w ∈ Z, toFullBlockMat (D w))) x) := by
  have h : ∀ A : BlockMat d,
      blockVecDot x (blockMatVecMul A x)
        = toFullBlockVec x ⬝ᵥ (toFullBlockMat A *ᵥ toFullBlockVec x) := by
    intro A
    rw [← dotProduct_toFullBlockVec x (blockMatVecMul A x), toFullBlockVec_blockMatVecMul]
  simp only [h, toFullBlockMat_ofFullBlockMat, Matrix.sum_mulVec, dotProduct_sum]

/-- The doubled quadratic form is homogeneous in the flat representative `A`: dilating a block by
a scalar dilates the quadratic form by the same scalar. -/
theorem blockVecDot_smul (c : ℝ) (D : BlockMat d) (x : BlockVec d) :
    blockVecDot x (blockMatVecMul (ofFullBlockMat (c • toFullBlockMat D)) x)
      = c * blockVecDot x (blockMatVecMul D x) := by
  have h : ∀ A : BlockMat d,
      blockVecDot x (blockMatVecMul A x)
        = toFullBlockVec x ⬝ᵥ (toFullBlockMat A *ᵥ toFullBlockVec x) := by
    intro A
    rw [← dotProduct_toFullBlockVec x (blockMatVecMul A x), toFullBlockVec_blockMatVecMul]
  simp only [h, toFullBlockMat_ofFullBlockMat, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The averaged response deficit as a block quadratic form

The averaged difference of the response functional between the child cells of a triadic box and
the parent cell is the block quadratic form of the response load against the averaged
coarse-block difference.  The two cell values enter only through the hypotheses `hJ` and `hJ₀`,
so the identity is purely algebraic in the coarse blocks; identifying those values with the
response functional is a separate step.

The identity holds for every triadic index box, including the empty one.  On each child the
difference of the two quadratic forms is the quadratic form of the block defect
`blockSub (child block) (parent block)`, so the parent term cancels and the outer normalization
never needs the box to be nonempty.
-/

open HCPolySupport.HighContrast (blockSub)
namespace HCPolySupport.HighContrast.Multiscale

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The averaged response deficit is the block quadratic form of the averaged coarse-block
defect.  With `J w` the response value on the child cell `adaptedCellAtCenter q (t - n) w` and `J₀`
the response value on the parent cell `adaptedCell q t`, each written as the quadratic form of
its coarse block against the load `x`, the normalized average of the child-to-parent differences
is the quadratic form of the normalized average of the block defects
`blockSub (child block) (parent block)`. -/
theorem response_deficit_eq_blockQuadratic (q : Mat d) (t : ℤ) (n : ℕ)
    (b : CoeffField d) (x : BlockVec d)
    (J : (Fin d → ℤ) → ℝ) (J₀ : ℝ)
    (hJ : ∀ w ∈ triadicIndexBox d n,
      J w = blockVecDot x
        (blockMatVecMul (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b) x))
    (hJ₀ : J₀ = blockVecDot x
      (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell q t) b) x)) :
    ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n, (J w - J₀)
      = blockVecDot x
          (blockMatVecMul
            (ofFullBlockMat
              (((triadicIndexBox d n).card : ℝ)⁻¹ •
                ∑ w ∈ triadicIndexBox d n,
                  toFullBlockMat
                    (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
                      (coarseBlockMatrix (HighContrast.adaptedCell q t) b)))) x) := by
  let Z : Finset (Fin d → ℤ) := triadicIndexBox d n
  let C : (Fin d → ℤ) → BlockMat d := fun w =>
    coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b
  let At : BlockMat d := coarseBlockMatrix (HighContrast.adaptedCell q t) b
  let A : (Fin d → ℤ) → BlockMat d := fun w => blockSub (C w) At
  have hsum : ∑ w ∈ Z, (J w - J₀) = ∑ w ∈ Z, blockVecDot x (blockMatVecMul (A w) x) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [hJ w hw, hJ₀]
    rw [show A w = ofFullBlockMat (toFullBlockMat (C w) - toFullBlockMat At) from rfl,
      blockVecDot_blockMatVecMul_ofFullBlockMat_sub]
  calc
    (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (J w - J₀)
        = (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot x (blockMatVecMul (A w) x) := by
          rw [hsum]
    _ = (Z.card : ℝ)⁻¹ *
          blockVecDot x (blockMatVecMul (ofFullBlockMat (∑ w ∈ Z, toFullBlockMat (A w))) x) := by
          rw [blockVecDot_finset_sum Z A x]
    _ = blockVecDot x
          (blockMatVecMul
            (ofFullBlockMat ((Z.card : ℝ)⁻¹ • ∑ w ∈ Z, toFullBlockMat (A w))) x) := by
          rw [← blockVecDot_smul (Z.card : ℝ)⁻¹
            (ofFullBlockMat (∑ w ∈ Z, toFullBlockMat (A w))) x]
          simp only [toFullBlockMat_ofFullBlockMat]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The depth-`n` subcells cover their parent adapted cell up to a null set

The cells `adaptedCellAtCenter q (t - n) w` over the index box `triadicIndexBox d n` are `3^{nd}`
pairwise disjoint open subcells of the parent `HighContrast.adaptedCell q t`.  They omit the
interior seams, so they are not literally a cover, but the omitted set is Lebesgue-null.
The three facts proved here are the volume bookkeeping (`card` times a subcell volume equals
the parent volume), the equality of the union with the parent at the level of measures, and
the nullity of the difference.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The volume of any depth-`n` subcell, multiplied by the number of subcells, is the volume
of the parent cell.  The identity is purely translation invariance of Lebesgue measure plus
the scale arithmetic `3^{nd} · 3^{(t-n)d} = 3^{td}`. -/
theorem volume_adaptedCellAtCenter_card_eq (q : Mat d) (hq : IsUnit q) (t : ℤ) (n : ℕ)
    (w : Fin d → ℤ) :
    ((triadicIndexBox d n).card : ℝ) * (volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal
      = (volume (HighContrast.adaptedCell q t)).toReal := by
  have hdet : |q.det| ≠ 0 :=
    abs_ne_zero.mpr (IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det q).mp hq))
  have h3 : (3 : ℝ) ^ n * (3 : ℝ) ^ (t - (n : ℤ)) = (3 : ℝ) ^ t := by
    rw [show ((3 : ℝ) ^ n) = (3 : ℝ) ^ ((n : ℤ)) from (zpow_natCast (3 : ℝ) n).symm,
      ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring_nf
  have hmain : ((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ (t - (n : ℤ))) ^ d = ((3 : ℝ) ^ t) ^ d := by
    rw [← mul_pow, h3]
  have hVreal : (volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal
      = |q.det| * ((3 : ℝ) ^ (t - (n : ℤ))) ^ d := by
    rw [Geometry.volume_adaptedCellAtCenter, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (t - (n : ℤ)))]
  rw [card_triadicIndexBox, hVreal, Geometry.volume_adaptedCell_toReal]
  exact mul_left_cancel₀ hdet (by rw [← hmain]; ring)

/-- The union of the depth-`n` subcells has the same volume as the parent cell.  The union is
an a.e. cover, and the equality follows from finite additivity over the pairwise disjoint
measurable subcells together with the per-cell volume identity. -/
theorem volume_biUnion_adaptedCellAtCenter (q : Mat d) (hq : IsUnit q) (t : ℤ) (n : ℕ) :
    volume (⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w)
      = volume (HighContrast.adaptedCell q t) := by
  classical
  have hmeas : ∀ w ∈ triadicIndexBox d n,
      MeasurableSet (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    fun w _ => (isOpen_adaptedCellAtCenter_of_isUnit hq _ w).measurableSet
  have hdisj : Set.PairwiseDisjoint (↑(triadicIndexBox d n) : Set (Fin d → ℤ))
      (fun w => adaptedCellAtCenter q (t - (n : ℤ)) w) := by
    intro a _ b _ hab
    exact Geometry.adaptedCellAtCenter_disjoint_of_ne hq _ hab
  have hUfin : volume (HighContrast.adaptedCell q t) ≠ ⊤ := by
    rw [Geometry.volume_adaptedCell]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hconst : ∀ w, volume (adaptedCellAtCenter q (t - (n : ℤ)) w)
      = volume (adaptedCellAtCenter q (t - (n : ℤ)) 0) := by
    intro w
    simp only [Geometry.volume_adaptedCellAtCenter]
  have hsum : ∑ w ∈ triadicIndexBox d n, volume (adaptedCellAtCenter q (t - (n : ℤ)) w)
      = ((triadicIndexBox d n).card : ℝ≥0∞)
          * volume (adaptedCellAtCenter q (t - (n : ℤ)) 0) := by
    calc ∑ w ∈ triadicIndexBox d n, volume (adaptedCellAtCenter q (t - (n : ℤ)) w)
        = ∑ _w ∈ triadicIndexBox d n, volume (adaptedCellAtCenter q (t - (n : ℤ)) 0) :=
          Finset.sum_congr rfl (fun w _ => hconst w)
      _ = ((triadicIndexBox d n).card : ℝ≥0∞)
            * volume (adaptedCellAtCenter q (t - (n : ℤ)) 0) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard := volume_adaptedCellAtCenter_card_eq q hq t n 0
  have hEnn : ((triadicIndexBox d n).card : ℝ≥0∞)
        * volume (adaptedCellAtCenter q (t - (n : ℤ)) 0)
      = volume (HighContrast.adaptedCell q t) := by
    refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
    · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (Geometry.volume_adaptedCellAtCenter_ne_top q (t - (n : ℤ)) 0)
    · exact hUfin
    · rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
      exact hcard
  calc volume (⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w)
      = ∑ w ∈ triadicIndexBox d n, volume (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
        measure_biUnion_finset hdisj hmeas
    _ = ((triadicIndexBox d n).card : ℝ≥0∞)
          * volume (adaptedCellAtCenter q (t - (n : ℤ)) 0) := hsum
    _ = volume (HighContrast.adaptedCell q t) := hEnn

/-- The parent cell differs from the union of its depth-`n` subcells by a null set.  This is
the a.e. covering statement: the union is measurable, contained in the parent, and has the
same (finite) measure, so the difference is null. -/
theorem adaptedCell_diff_biUnion_null (q : Mat d) (hq : IsUnit q) (t : ℤ) (n : ℕ) :
    volume (HighContrast.adaptedCell q t \
        ⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w) = 0 := by
  classical
  have hsub : (⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w)
      ⊆ HighContrast.adaptedCell q t := by
    refine Set.iUnion₂_subset ?_
    intro w hw
    exact adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hOpen : IsOpen (⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    isOpen_iUnion fun w => isOpen_iUnion fun _ => isOpen_adaptedCellAtCenter_of_isUnit hq _ w
  have hUfin : volume (HighContrast.adaptedCell q t) ≠ ⊤ := by
    rw [Geometry.volume_adaptedCell]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hVeq : volume (⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w)
      = volume (HighContrast.adaptedCell q t) :=
    volume_biUnion_adaptedCellAtCenter q hq t n
  have hVfin : volume (⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w) ≠ ⊤ := by
    rw [hVeq]
    exact hUfin
  rw [measure_sdiff hsub hOpen.measurableSet.nullMeasurableSet hVfin, hVeq]
  simp

end

end HCPolySupport.HighContrast.Multiscale
end
