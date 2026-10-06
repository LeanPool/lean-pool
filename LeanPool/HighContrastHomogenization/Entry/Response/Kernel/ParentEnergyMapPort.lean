/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.SubcellCoefficientGluing
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.CoarseBlockPerCellInput
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs

/-!
# High-contrast homogenization: Entry.Response.Kernel.ParentEnergyMapPort

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The parent-optimizer energy map, and the adjoint tail-cell hypothesis

This file proves the per-cell bookkeeping of the diagonal weak-norm estimate for a single parent
optimizer field: the metric square of the cell average of the parent state is bounded by the
square of the printed geometric factor times the Chapter-2 block energy of the aligned subcell,
first for the recentred sample and then, tracking the extra congruence the flux flip introduces,
for its adjoint twin. It then records the resulting per-scale older-scale bound at the estimate's
own carriers, adjoint sign: for every aligned depth-`n` subcell, the metric square of the
transported cell average of the parent optimizer field is bounded by the printed geometric square
times twice the subcell's response size.  It serves the weak-norm estimate
`e.response.weak.estimate`.
-/

section
/-!
## The parent-optimizer energy map on an aligned cell

This is the per-cell bookkeeping of the weak-norm estimate for the single parent optimizer field
instead of a difference.  The metric square of the cell average of the parent state is bounded by
the square of the printed geometric factor times the Chapter-2 block energy of the aligned
subcell, the energy carried by the restricted solution whose gradient agrees with the parent's.

The proof is the recent-difference bookkeeping with the recent-difference metric input replaced by
the cell energy bound for the parent optimizer on an aligned subcell.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub coarseBlock normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The parent-optimizer energy map on an aligned cell.  For every index `w` in the triadic box,
the metric square of the cell average of the parent optimizer field on the aligned subcell is
bounded by the printed geometric square times twice the Chapter-2 block energy of the restricted
solution there; that energy is the actual state energy on the subcell, not a difference energy.

The hypothesis `hcoarse` identifies the Chapter-2 coarse block of the recentred coefficient with
the shear congruence of the subcell's coarse block, exactly as in the recent-difference map. -/
theorem parentEnergyMap_port
    (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hgrid : IsUnit (respGrid jStar F))
    (a : CoeffSpace d) (n : ℕ)
    (aU : (w : Fin d → ℤ) →
      Book.Ch02.CoeffOn (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w))
    {V : Set (Vec d)}
    (u : (w : Fin d → ℤ) → AHarmonicFunction (aU w).toCoeffField V)
    (z : (w : Fin d → ℤ) →
      Book.Ch02.Solution (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w))
    (hz : ∀ w, (z w).toH1.grad = (u w).toH1.grad)
    (hEll : ∀ w : Fin d → ℤ, IsEllipticFieldOn (aU w).lam (aU w).Lam
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (aU w).toCoeffField)
    (hm : (explicitCanonicalMetric F).PosDef)
    (hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef)
    (hEhat : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (hcoarse : ∀ w ∈ triadicIndexBox d n,
      Book.Ch02.coarseBlockMatrix (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU
        w) =
        blockCongr (respG F) (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ))
          w) a)) :
    ∀ w ∈ triadicIndexBox d n,
      blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (aU w).toCoeffField (u w))))
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (aU w).toCoeffField (u w))))
      ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
          * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
              * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2
        * (2 * weakOptimizerEnergy (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (aU w).toCoeffField (z w) ^ 2) := by
  have hNpd : (toFullBlockMat
      (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))).PosDef :=
    Annealed.normalizedBlock_posDef _ _ hEhat hM0
  have hnorm_pos : 0 < ‖toFullBlockMat
      (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖ :=
    norm_pos_iff.mpr hNpd.isUnit.ne_zero
  have hBpos : 0 < 1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
      * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2) :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
  have hsize : ‖toFullBlockMat
        (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖
        * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
            * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) ^ 2
      ≤ (Real.sqrt
            (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
          * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
              * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2 := by
    rw [blockSpecBound_eq_norm_of_posSemidef _ hNpd.posSemidef, mul_pow,
      Real.sq_sqrt (norm_nonneg _)]
  refine perCellHypothesis_of_metric_and_size (P := P) (γ := γ) (jStar := jStar) (F := F) (t := t)
    (a := a) (n := n)
    (Y := fun w x => optimizerField (aU w).toCoeffField (u w) x)
    (G := fun w => 2 * weakOptimizerEnergy (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
      (aU w).toCoeffField (z w) ^ 2)
    (k := ‖toFullBlockMat (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖)
    (e := (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
        * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) ^ 2)
    (hk := hnorm_pos.le) (he := (pow_pos hBpos 2).le) (hG := fun _ _ => by positivity)
    (hsize := hsize) (hmetric := ?_)
  intro w hw
  have hAE : toFullBlockMat
        (Book.Ch02.coarseBlockMatrix (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (aU w))
      ≤ (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
          * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) ^ 2
        • toFullBlockMat (respEhatMinus P jStar F t) := by
    rw [hcoarse w hw]
    exact coarseBlock_congr_le_sq_smul_respEhatMinus P γ jStar F t a n hw hbdd hEmean
  have hEM : toFullBlockMat (respEhatMinus P jStar F t)
      ≤ ‖toFullBlockMat (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖
        • toFullBlockMat (respM0 F) :=
    le_smul_of_normalizedBlock hEhat.posSemidef hM0
  have hmain := blockSq_cellAverage_optimizerField_adaptedCellAtCenter_le
    (q := respGrid jStar F) (hq := hgrid) (k := t - (n : ℤ)) (w := w)
    (E := respEhatMinus P jStar F t)
    (aU w) (hEll w) (u w) (z w) (hz w) hm hEhat hnorm_pos (pow_pos hBpos 2) hEM hAE
  simpa only using hmain

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The parent-optimizer energy map, adjoint sign

The parent-optimizer energy map of `ParentEnergyMapPort` is stated for the recentred
sample `respEhatMinus`.  The adjoint copy is needed for the `a_+` per-scale input, whose sample is
`respEhatPlus = blockAdjoint (respEhatMinus …)`.  Because the adjoint adds one congruence by the
flux flip `D`, the response-size input is no longer a bound for the shear factor `respG F` alone:
it is the composed factor `D ∘ respG F`.

As in the recent-difference adjoint twin, the map is split so that the large block terms are
elaborated once each: the per-cell step carries the two Loewner constants abstract and is the
aligned-subcell instance of the Chapter-2 block energy bound for the parent optimizer, and the
second theorem feeds it the adjoint size inputs.  The remaining input of the second theorem is the
identification of the Chapter-2 coarse block of the recentred adjoint field with the composed
congruence of the cell's coarse block; the two coarse-block carriers used here — the Chapter-2
`coarseBlockMatrix` on a `Domain` and the set-level `coarseBlock` on the cell — are not identified
by any declaration in this module's import closure, so that identification is carried as an
explicit hypothesis, exactly as for the minus sign.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub coarseBlock normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The per-cell step of the parent-optimizer energy map for the adjoint sample, with the two
Loewner constants abstract.  This is the aligned-subcell Chapter-2 block energy bound for the
parent optimizer `u`, whose gradient agrees with the restricted solution `z`: the metric square of
the cell average of the parent state is bounded by the product `k * e` of the two Loewner sizes
times twice the actual state energy carried by `z`.  The reference sample is `respEhatPlus`, the
root is `blockSqrt (respM0 F)`, and the response sample and the two Loewner hypotheses are those of
the weak-norm estimate (`e.response.weak.estimate`). -/
theorem parentEnergyMap_cell_plus
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hgrid : IsUnit (respGrid jStar F))
    (n : ℕ)
    (aU : (w : Fin d → ℤ) →
      Book.Ch02.CoeffOn (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w))
    {V : Set (Vec d)}
    (u : (w : Fin d → ℤ) → AHarmonicFunction (aU w).toCoeffField V)
    (z : (w : Fin d → ℤ) →
      Book.Ch02.Solution (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w))
    (hz : ∀ w, (z w).toH1.grad = (u w).toH1.grad)
    (hEll : ∀ w : Fin d → ℤ, IsEllipticFieldOn (aU w).lam (aU w).Lam
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (aU w).toCoeffField)
    (hm : (explicitCanonicalMetric F).PosDef)
    (hEhat : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (k e : ℝ) (hk : 0 < k) (he : 0 < e)
    (hEM : toFullBlockMat (respEhatPlus P jStar F t) ≤ k • toFullBlockMat (respM0 F))
    (hAE : ∀ w ∈ triadicIndexBox d n,
      toFullBlockMat (Book.Ch02.coarseBlockMatrix
          (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w))
        ≤ e • toFullBlockMat (respEhatPlus P jStar F t)) :
    ∀ w ∈ triadicIndexBox d n,
      blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (aU w).toCoeffField (u w))))
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (aU w).toCoeffField (u w))))
      ≤ (k * e) * (2 * weakOptimizerEnergy (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (aU w).toCoeffField (z w) ^ 2) := by
  intro w hw
  simpa only using blockSq_cellAverage_optimizerField_adaptedCellAtCenter_le
    (q := respGrid jStar F) (hq := hgrid) (k := t - (n : ℤ)) (w := w)
    (E := respEhatPlus P jStar F t)
    (aU w) (hEll w) (u w) (z w) (hz w) hm hEhat hk he hEM (hAE w hw)

/-- The parent-optimizer energy map on an aligned cell for the adjoint sample.  This is the adjoint
twin of `parentEnergyMap_port` (`ParentEnergyMapPort.lean`): the sample is
`respEhatPlus`, and the response-size input `hcoarse` identifies the Chapter-2 coarse block of the
recentred field with the composed congruence `D ∘ respG F`, the factor the adjoint carries.  The
per-cell step is `parentEnergyMap_cell_plus` above. -/
theorem parentEnergyMap_port_plus
    (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hgrid : IsUnit (respGrid jStar F))
    (a : CoeffSpace d) (n : ℕ)
    (aU : (w : Fin d → ℤ) →
      Book.Ch02.CoeffOn (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w))
    {V : Set (Vec d)}
    (u : (w : Fin d → ℤ) → AHarmonicFunction (aU w).toCoeffField V)
    (z : (w : Fin d → ℤ) →
      Book.Ch02.Solution (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w))
    (hz : ∀ w, (z w).toH1.grad = (u w).toH1.grad)
    (hEll : ∀ w : Fin d → ℤ, IsEllipticFieldOn (aU w).lam (aU w).Lam
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (aU w).toCoeffField)
    (hm : (explicitCanonicalMetric F).PosDef)
    (hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef)
    (hEhat : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (hcoarse : ∀ w ∈ triadicIndexBox d n,
      Book.Ch02.coarseBlockMatrix (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU
        w) =
        blockCongr (blockD d)
          (blockCongr (respG F) (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n :
            ℤ)) w) a))) :
    ∀ w ∈ triadicIndexBox d n,
      blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (aU w).toCoeffField (u w))))
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (aU w).toCoeffField (u w))))
      ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))
          * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
              * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2
        * (2 * weakOptimizerEnergy (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (aU w).toCoeffField (z w) ^ 2) := by
  have hNpd : (toFullBlockMat
      (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))).PosDef :=
    Annealed.normalizedBlock_posDef _ _ hEhat hM0
  have hnorm_pos : 0 < ‖toFullBlockMat
      (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖ :=
    norm_pos_iff.mpr hNpd.isUnit.ne_zero
  have hBpos : 0 < 1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
      * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2) :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
  have hsize : ‖toFullBlockMat
        (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖
        * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
            * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) ^ 2
      ≤ (Real.sqrt
            (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))
          * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
              * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2 := by
    rw [blockSpecBound_eq_norm_of_posSemidef _ hNpd.posSemidef, mul_pow,
      Real.sq_sqrt (norm_nonneg _)]
  refine perCellHypothesis_of_constants (triadicIndexBox d n)
    (fun w => blockVecDot
      (blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (optimizerField (aU w).toCoeffField (u w))))
      (blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (optimizerField (aU w).toCoeffField (u w)))))
    (fun w => 2 * weakOptimizerEnergy (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
      (aU w).toCoeffField (z w) ^ 2)
    (‖toFullBlockMat (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖
      * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
          * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) ^ 2)
    ((Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))
        * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
            * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2)
    (mul_nonneg hnorm_pos.le (pow_pos hBpos 2).le) (fun _ _ => by positivity) hsize ?_
  exact parentEnergyMap_cell_plus P jStar F t hgrid n aU u z hz hEll hm hEhat
    ‖toFullBlockMat (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖
    ((1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
        * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) ^ 2)
    hnorm_pos (pow_pos hBpos 2)
    (le_smul_of_normalizedBlock hEhat.posSemidef hM0)
    (fun w hw => by
      rw [hcoarse w hw]
      exact blockCongr_le_smul (blockD d)
        (coarseBlock_congr_le_sq_smul_respEhatMinus P γ jStar F t a n hw hbdd hEmean))

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The tail's per-cell hypothesis at the estimate's own carriers, adjoint sign

`scaleTail_carrier` (`CentredVarianceTailRoute.lean`) is the per-scale older-scale bound
at the estimate's carriers.  Its only analytic input is `hcell`: for every aligned depth-`n`
subcell, the metric square of the transported cell average of the parent optimizer field is
bounded by the printed geometric square times twice the subcell energy average.

This module is the adjoint twin of `tailCell_of_bridge`: the parent optimizer is attached to
the transposed recentred response coefficient `a_+ = aᵀ + g`, and the reference sample is the
adjoint block `respEhatPlus`.  The adjoint parent energy map
`parentEnergyMap_port_plus` proves the per-cell shape at a pointwise elliptic representative of
the adjoint recentred coefficient and with the subcell energy written through the restricted
Chapter-2 solution.  This module supplies that data from the parent harmonic optimizer and
transports the port's conclusion back to the estimate's carrier.

The transport uses the pointwise elliptic representative of the adjoint recentred field on the
parent cell (`exists_globally_elliptic_representative_ae_eq_on`, which is transposed and shifted by
the skew Schur coefficient): it is the same field on every aligned subcell, so the parent optimizer
is harmonic against it there, and it is a.e. equal to `respCoeffPlus F a` on the parent cell, so the
cell average and the energy density are unchanged.  `Book.Ch02.Solution.ofAEEq` /
`Response.aHarmonicOfAEEq` and the restriction `exists_restrict_solution_adaptedCellAtCenter`
produce the restricted Chapter-2 solution.  Finally `weakOptimizerEnergy_sq` and a.e. invariance
replace the port's energy square by the estimate's volume average.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub coarseBlock
  exists_globally_elliptic_representative_ae_eq_on normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The per-cell hypothesis of the older-scale tail, adjoint sign.**  For an invertible selected
grid, a generation `t`, a depth `n`, and a parent harmonic optimizer attached to the transposed
recentred response coefficient, every aligned depth-`n` subcell satisfies the per-cell metric bound
of `scaleTail_carrier`: the transported cell-average metric square of the parent optimizer field
is at most the printed geometric square times twice its energy average.  The bound is the adjoint
port `parentEnergyMap_port_plus` at a pointwise elliptic representative, transported back along
the a.e. equality of the representative with `respCoeffPlus F a`; the cell-average step and the
energy step are both a.e. invariant. -/
theorem tailCell_of_bridge_plus (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (n : ℕ)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
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
              (optimizerField (respCoeffPlus F a) u)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffPlus F a) u)))
        ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))
            * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2 *
          (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => vecDot (optimizerField (respCoeffPlus F a) u x).1
              (optimizerField (respCoeffPlus F a) u x).2)) := by
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
  have hport := parentEnergyMap_port_plus (P := P) (γ := γ) (jStar := jStar) (F := F) (t := t)
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
        (optimizerField (respCoeffPlus F a) u) := by
    refine cellAverage_congr_ae (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n
      hw) ?_
    filter_upwards [hae.symm] with x hx
    rw [huFam_w]
    simp only [optimizerField, huRep_grad, haU_w, hx]
  have haeSub : f =ᵐ[volumeMeasureOn (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)]
      respCoeffPlus F a := by
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
        (fun x => vecDot (optimizerField (respCoeffPlus F a) u x).1
          (optimizerField (respCoeffPlus F a) u x).2) := by
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
