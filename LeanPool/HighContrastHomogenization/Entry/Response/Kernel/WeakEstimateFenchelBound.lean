/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.ResponseTransferHelpers
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.BesovScaleSummationToolkit
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RecentCellDefectBound
public import LeanPool.HighContrastHomogenization.Entry.Setup.ProjectiveDistance
public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import LeanPool.HighContrastHomogenization.Support.Ambient.CoefficientField
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Foundations.Algebra
public import LeanPool.HighContrastHomogenization.Support.PDE.Harmonic

/-!
# High-contrast homogenization: Entry.Response.Kernel.WeakEstimateFenchelBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The pathwise Fenchel and Loewner bounds for the weak quantity

Restricting the cell-average half of AK.HC (2.15) to an arbitrary triadic subcell of the response
cell, this file bounds the squared doubled cell average of the optimizer state there by the same
Fenchel-derived quadratic form, and combines it with the coarse-block envelope of the all-scale
maximum to bound the per-scale terms entering the scale-average seminorm of AK.HC (2.130). It
assembles the resulting per-scale bounds into the pathwise estimate `e.response.weak.estimate` of
the squared seminorm of the doubled optimizer state. It closes with the all-scale Loewner bound
`p.response.transfer` - the operator-norm envelope that dominates the response grid's terminal cell
also dominates every triadic subcell, with the depth-dependent contrast weight made explicit - and
the elementary quadratic-form algebra (congruence, scaling, a Loewner comparison, a block sum) that
transports it.
-/

section
/-!
## The Fenchel bound on a triadic subcell of the response cell

The cell-average half of AK.HC (2.15) restricted to a triadic subcell `adaptedCellAtCenter q (t -
n) w`
of the response cell `U_t = adaptedCell q t`: a field harmonic on the whole cell restricts to the
subcell, its gradient — hence its optimizer field and scalar variation energy integrand — is
unchanged, and the squared doubled cell average of the optimizer field over the subcell is
controlled by the pathwise symmetric energy of the field times any positive constant `K` that
bounds above the quadratic form of the coarse block of `b` on the subcell augmented by the swap
block `𝐑`.
-/

open HCPolySupport.HighContrast.CG

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The cell-average energy bound on a triadic subcell of the response cell: for `v` harmonic on
the response cell `U_t`, the squared doubled cell average over the depth-`n` subcell
`adaptedCellAtCenter q (t - n) w` of its optimizer field is bounded by the pathwise symmetric
energy of
the field over that subcell times any positive constant `K` that bounds above the quadratic form of
the coarse block of `b` on the subcell augmented by the swap block `𝐑`.  This is the cell-average
half of AK.HC (2.15) on a subcell of `U_t`; the proof restricts `v` to the subcell and applies the
cell-average bound there. -/
theorem blockVecDot_cellAverage_subcell_le {d : ℕ} [NeZero d]
    {q : Mat d} (hq : IsUnit q) (t : ℤ) (n : ℕ) {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n)
    {lam Lam : ℝ} {b : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) b)
    (v : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (K : ℝ) (hK : 0 < K)
    (hB : ∀ X : BlockVec d, blockVecDot X (blockMatVecMul
          (ofFullBlockMat (toFullBlockMat (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
            + toFullBlockMat (blockSwap d))) X) ≤ K * blockVecDot X X) :
    blockVecDot (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
        (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
      ≤ K * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand b v) := by
  have hConv : IsOpenBoundedConvexDomain (adaptedCellAtCenter q (t - (n : ℤ)) w) := by
    rw [adaptedCellAtCenter, Annealed.adaptedCellTranslate_eq_cg_affine]
    exact isOpenBoundedConvexDomain_affine_openCube q hq (t - (n : ℤ)) _
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)) :=
    hConv.isFiniteMeasure_restrict_volume
  have hVU : adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hUopen : IsOpen (HighContrast.adaptedCell q t) :=
    (adaptedCell_isOpenBoundedConvexDomain q hq t).isOpen
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) b :=
    hEll.mono hConv.isOpen.measurableSet hVU
  have hvol : 0 < (volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal := by
    rw [Geometry.volume_adaptedCellAtCenter, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (t - (n : ℤ)))]
    exact mul_pos
      (abs_pos.mpr (IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det q).mp hq)))
      (pow_pos (by positivity : (0 : ℝ) < (3 : ℝ) ^ (t - (n : ℤ))) d)
  have hgrad :
      (v.restrictOfIsEllipticFieldOn hUopen hConv.isOpen hVU hEllV).toH1.grad =
        v.toH1.grad := by
    rw [AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn]
    simp only [H1Function.restrict]
  simpa only [optimizerField, scalarVariationEnergyIntegrand, hgrad] using!
    (blockVecDot_cellAverage_optimizerField_self_le hConv hEllV hvol
      (v.restrictOfIsEllipticFieldOn hUopen hConv.isOpen hVU hEllV) K hK hB)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The pathwise per-scale bound for the weak-quantity integrand

The scale-average seminorm `[·]` of AK.HC (2.130) is built from the squared `L²` cell means of the
optimizer state on the depth-`n` triadic subcells of the response cell.  This file records the
pathwise bound those subcell terms satisfy: after the test block `S` and the shift `Y` are applied,
the normalized sum over the subcells is controlled by the pathwise symmetric energy of the
harmonic field on the response cell.  The estimate chains the cell-average half of the Fenchel
bound (2.15) on each subcell with the exact partition identity of the subcell energy averages.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The pathwise per-scale bound for the weak-quantity integrand `e.response.weak.estimate`: for a
`b`-harmonic field `v` on the response cell `U_t = adaptedCell q t`, a test block `S` with
`|S X|² ≤ kS |X|²`, a shift `Y`, and a constant `K` that bounds the coarse block of `b` augmented
by the swap block `𝐑` on every depth-`n` triadic subcell, the normalized sum over the `3 ^ (n d)`
subcells of the squared length of `S` applied to the shifted subcell average of the optimizer
field of `v` is at most `kS (2 K ⟨∇v ⬝ symm(b) ∇v⟩_{U_t} + 2 |Y|²)`.  The proof applies the
cell-average half of the Fenchel bound (2.15) on each subcell, averages the subcell energy over the
exact partition of `U_t`, and expands the shift; this is the pathwise input of the scale-average
seminorm bound AK.HC (2.130). -/
theorem avsum_optimizerState_sq_le_of_inputs {d : ℕ} [NeZero d]
    {q : Mat d} (hq : IsUnit q) (t : ℤ) (n : ℕ)
    {lam Lam : ℝ} {b : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) b)
    (v : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (S : BlockMat d) (Y : BlockVec d) (kS : ℝ) (hkS : 0 ≤ kS)
    (hS : ∀ X : BlockVec d, blockVecDot (blockMatVecMul S X) (blockMatVecMul S X)
        ≤ kS * blockVecDot X X)
    (K : ℝ) (hK : 0 < K)
    (hB : ∀ w ∈ triadicIndexBox d n, ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul
        (ofFullBlockMat (toFullBlockMat (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
          + toFullBlockMat (blockSwap d))) X) ≤ K * blockVecDot X X)
    (hint : IntegrableOn (scalarVariationEnergyIntegrand b v) (HighContrast.adaptedCell q t)) :
    (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
        blockVecDot
          (blockMatVecMul S (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y))
          (blockMatVecMul S (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y))
      ≤ kS * (2 * (K * volumeAverage (HighContrast.adaptedCell q t) (scalarVariationEnergyIntegrand b v))
              + 2 * blockVecDot Y Y) := by
  classical
  have hNpos : (0 : ℝ) < ((triadicIndexBox d n).card : ℝ) := by
    rw [card_triadicIndexBox n]
    positivity
  have hNne : ((triadicIndexBox d n).card : ℝ) ≠ 0 := ne_of_gt hNpos
  have hInvNN : (0 : ℝ) ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  -- The pointwise bound: `S` does not increase the squared length, and the shift is expanded.
  have hpt : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul S
            (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y))
          (blockMatVecMul S
            (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y))
        ≤ kS * (2 * (blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            + blockVecDot Y Y)) := by
    intro w _
    have h1 := hS (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y)
    have h2 := blockVecDot_sub_self_le
      (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v)) Y
    have h3 : kS * blockVecDot
          (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y)
          (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y)
        ≤ kS * (2 * (blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            + blockVecDot Y Y)) := by
      refine mul_le_mul_of_nonneg_left ?_ hkS
      linarith only [h2]
    linarith only [h1, h3]
  -- Fenchel on every subcell, then the exact partition average over the subcells.
  have hfen : (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
      ≤ K * volumeAverage (HighContrast.adaptedCell q t) (scalarVariationEnergyIntegrand b v) := by
    have hcell : ∀ w ∈ triadicIndexBox d n,
        blockVecDot
            (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
          ≤ K * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (scalarVariationEnergyIntegrand b v) := by
      intro w hw
      exact blockVecDot_cellAverage_subcell_le (d := d) hq t n hw hEll v K hK (hB w hw)
    calc
      (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
          ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                K * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                  (scalarVariationEnergyIntegrand b v) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) hInvNN
      _ = K * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                  (scalarVariationEnergyIntegrand b v)) := by
            rw [← Finset.mul_sum]
            ring
      _ = K * volumeAverage (HighContrast.adaptedCell q t)
              (scalarVariationEnergyIntegrand b v) := by
            rw [avsum_volumeAverage_eq q hq t n hint]
  -- The normalized sum of the shifted squares.
  have hFk : (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          kS * (2 * (blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            + blockVecDot Y Y))
      = kS * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          (2 * (blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            + blockVecDot Y Y))) := by
    rw [← Finset.mul_sum]
    ring
  have hFshift : (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          (2 * (blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            + blockVecDot Y Y))
      = 2 * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v)))
        + 2 * blockVecDot Y Y := by
    have hsummand : ∑ w ∈ triadicIndexBox d n,
          (2 * (blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            + blockVecDot Y Y))
        = ∑ w ∈ triadicIndexBox d n,
          (2 * blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            + 2 * blockVecDot Y Y) :=
      Finset.sum_congr rfl (fun w _ => by ring)
    have hsum_eval : ∑ w ∈ triadicIndexBox d n,
          (2 * (blockVecDot
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
            + blockVecDot Y Y))
        = 2 * (∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v)))
          + ((triadicIndexBox d n).card : ℝ) * (2 * blockVecDot Y Y) := by
      rw [hsummand, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have hc2 : (((triadicIndexBox d n).card : ℝ))⁻¹ *
          (((triadicIndexBox d n).card : ℝ) * (2 * blockVecDot Y Y)) = 2 * blockVecDot Y Y := by
      calc (((triadicIndexBox d n).card : ℝ))⁻¹ *
            (((triadicIndexBox d n).card : ℝ) * (2 * blockVecDot Y Y))
          = ((((triadicIndexBox d n).card : ℝ))⁻¹ * ((triadicIndexBox d n).card : ℝ))
              * (2 * blockVecDot Y Y) := by ring
        _ = 1 * (2 * blockVecDot Y Y) := by rw [inv_mul_cancel₀ hNne]
        _ = 2 * blockVecDot Y Y := by ring
    calc (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            (2 * (blockVecDot
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              + blockVecDot Y Y))
        = (((triadicIndexBox d n).card : ℝ))⁻¹ *
            (2 * (∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                  (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v)))
              + ((triadicIndexBox d n).card : ℝ) * (2 * blockVecDot Y Y)) := by
          rw [hsum_eval]
      _ = 2 * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v)))
          + 2 * blockVecDot Y Y := by
          rw [mul_add, hc2]
          ring
  -- Assemble.
  calc
    (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
        blockVecDot
          (blockMatVecMul S (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y))
          (blockMatVecMul S (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y))
        ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              kS * (2 * (blockVecDot
                  (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                  (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                + blockVecDot Y Y)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) hInvNN
    _ = kS * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            (2 * (blockVecDot
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
              + blockVecDot Y Y))) := hFk
    _ = kS * (2 * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v)))
          + 2 * blockVecDot Y Y) := by rw [hFshift]
    _ ≤ kS * (2 * (K * volumeAverage (HighContrast.adaptedCell q t)
              (scalarVariationEnergyIntegrand b v))
          + 2 * blockVecDot Y Y) := by
          refine mul_le_mul_of_nonneg_left ?_ hkS
          linarith only [hfen]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The pathwise seminorm bound by the cell energy

The scale-average seminorm `[·]` of AK.HC (2.130) is a sum of per-scale cell averages.  The
per-scale bound `avsum_optimizerState_sq_le_of_inputs` controls each scale by the pathwise cell
energy with a coarse-block envelope `K = K₀ · 3 ^ (ρ n)`, while the summation
`besovSeminorm_sq_le_of_scale_bound` accepts any per-scale majorant `A · 3 ^ (ρ n)` with `ρ < 1`.
This file chains the two: the envelope and the shift are monotone in the geometric factor
`3 ^ (ρ n) ≥ 1`, so the per-scale bound can be rewritten in the majorant shape with the geometric
loss absorbed into the coefficient `A`.  This is the pathwise input `e.response.weak.estimate`
into the squared scale-average seminorm bound AK.HC (2.130).
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The pathwise bound of the squared scale-average seminorm AK.HC (2.130) by the cell energy,
with the geometric loss absorbed.  For a `b`-harmonic field `v` on the response cell
`U_t = adaptedCell q t`, a test block `S` with `|S X|² ≤ kS |X|²`, a shift `Y`, and a coarse-block
envelope of the augmented block on every depth-`n` triadic subcell of the form
`K₀ · 3 ^ (ρ n)` with `ρ < 1`, the squared scale-average seminorm of the applied, shifted cell
averages of the optimizer field is at most `((1 - 3 ^ ((ρ - 1) / 2))⁻¹)²` times
`3 ^ t (kS (2 K₀ ⟨∇v ⬝ symm(b) ∇v⟩_{U_t} + 2 |Y|²))`.  The proof applies the per-scale pathwise
bound at envelope `K₀ · 3 ^ (ρ n)`, then uses `3 ^ (ρ n) ≥ 1` and the nonnegativity of the energy,
the shift and `kS` to move the geometric factor onto the whole per-scale majorant, so that the
scale-weighted summation `e.response.weak.estimate` of AK.HC (2.130) applies. -/
theorem besovSeminorm_sq_optimizerState_le_of_scale_bounds {d : ℕ} [NeZero d]
    {q : Mat d} (hq : IsUnit q) (t : ℤ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {lam Lam : ℝ} {b : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) b)
    (v : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (S : BlockMat d) (Y : BlockVec d) (kS : ℝ) (hkS : 0 ≤ kS)
    (hS : ∀ X : BlockVec d, blockVecDot (blockMatVecMul S X) (blockMatVecMul S X)
        ≤ kS * blockVecDot X X)
    (K₀ : ℝ) (hK₀ : 0 < K₀)
    (hB : ∀ (n : ℕ), ∀ w ∈ triadicIndexBox d n, ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul
        (ofFullBlockMat (toFullBlockMat (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
          + toFullBlockMat (blockSwap d))) X)
        ≤ (K₀ * (3 : ℝ) ^ (ρ * (n : ℝ))) * blockVecDot X X)
    (hint : IntegrableOn (scalarVariationEnergyIntegrand b v) (HighContrast.adaptedCell q t))
    (hEnn : 0 ≤ volumeAverage (HighContrast.adaptedCell q t) (scalarVariationEnergyIntegrand b v)) :
    besovSeminorm t (fun n z => blockMatVecMul S
        (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) z) (optimizerField b v) - Y)) ^ 2
      ≤ ((1 - (3 : ℝ) ^ ((ρ - 1) / 2))⁻¹) ^ 2 *
          ((3 : ℝ) ^ (t : ℝ) *
            (kS * (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
                  (scalarVariationEnergyIntegrand b v))
                + 2 * blockVecDot Y Y))) := by
  classical
  have hBnn : 0 ≤ blockVecDot Y Y := blockVecDot_nonneg Y
  have hE0 : 0 ≤ volumeAverage (HighContrast.adaptedCell q t)
      (scalarVariationEnergyIntegrand b v) := hEnn
  have hA0 : 0 ≤ kS * (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
        (scalarVariationEnergyIntegrand b v)) + 2 * blockVecDot Y Y) := by
    refine mul_nonneg hkS (add_nonneg ?_ ?_)
    · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg (le_of_lt hK₀) hE0)
    · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hBnn
  -- The per-scale majorant `A * 3 ^ (ρ * n)` with `A` the absorbed coefficient.
  have hper : ∀ n : ℕ,
      (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            blockVecDot
              (blockMatVecMul S
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y))
              (blockMatVecMul S
                (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) - Y))
        ≤ (kS * (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
              (scalarVariationEnergyIntegrand b v)) + 2 * blockVecDot Y Y))
            * (3 : ℝ) ^ (ρ * (n : ℝ)) := by
    intro n
    have hp0le : (0 : ℝ) ≤ ρ * (n : ℝ) := mul_nonneg hρ0 (Nat.cast_nonneg n)
    have hp1 : (1 : ℝ) ≤ (3 : ℝ) ^ (ρ * (n : ℝ)) :=
      Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) hp0le
    have hp0 : (0 : ℝ) < (3 : ℝ) ^ (ρ * (n : ℝ)) := lt_of_lt_of_le zero_lt_one hp1
    have hKpos : 0 < K₀ * (3 : ℝ) ^ (ρ * (n : ℝ)) := mul_pos hK₀ hp0
    have hbase := avsum_optimizerState_sq_le_of_inputs (d := d) hq t n hEll v S Y kS hkS hS
      (K₀ * (3 : ℝ) ^ (ρ * (n : ℝ))) hKpos (hB n) hint
    -- Absorb the geometric factor `3 ^ (ρ * n) ≥ 1` into the constant coefficient.
    have h2B : 2 * blockVecDot Y Y
        ≤ (2 * blockVecDot Y Y) * (3 : ℝ) ^ (ρ * (n : ℝ)) := by
      simpa using mul_le_mul_of_nonneg_left hp1
        (show (0 : ℝ) ≤ 2 * blockVecDot Y Y by linarith only [hBnn])
    have hstep : 2 * (K₀ * (3 : ℝ) ^ (ρ * (n : ℝ))
            * volumeAverage (HighContrast.adaptedCell q t) (scalarVariationEnergyIntegrand b v))
          + 2 * blockVecDot Y Y
        ≤ (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
              (scalarVariationEnergyIntegrand b v)) + 2 * blockVecDot Y Y)
            * (3 : ℝ) ^ (ρ * (n : ℝ)) := by
      have hKterm : 2 * (K₀ * (3 : ℝ) ^ (ρ * (n : ℝ))
            * volumeAverage (HighContrast.adaptedCell q t) (scalarVariationEnergyIntegrand b v))
          = (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
                (scalarVariationEnergyIntegrand b v))) * (3 : ℝ) ^ (ρ * (n : ℝ)) := by
        ring
      have hsplit : (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
              (scalarVariationEnergyIntegrand b v)) + 2 * blockVecDot Y Y)
            * (3 : ℝ) ^ (ρ * (n : ℝ))
          = (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
                (scalarVariationEnergyIntegrand b v))) * (3 : ℝ) ^ (ρ * (n : ℝ))
            + (2 * blockVecDot Y Y) * (3 : ℝ) ^ (ρ * (n : ℝ)) := by
        ring
      rw [hKterm, hsplit]
      exact add_le_add (le_refl _) h2B
    have hle1 : kS * (2 * (K₀ * (3 : ℝ) ^ (ρ * (n : ℝ))
            * volumeAverage (HighContrast.adaptedCell q t) (scalarVariationEnergyIntegrand b v))
          + 2 * blockVecDot Y Y)
        ≤ kS * ((2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
              (scalarVariationEnergyIntegrand b v)) + 2 * blockVecDot Y Y)
            * (3 : ℝ) ^ (ρ * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hstep hkS
    have hle2 : kS * ((2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
              (scalarVariationEnergyIntegrand b v)) + 2 * blockVecDot Y Y)
            * (3 : ℝ) ^ (ρ * (n : ℝ)))
        = (kS * (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
              (scalarVariationEnergyIntegrand b v)) + 2 * blockVecDot Y Y))
            * (3 : ℝ) ^ (ρ * (n : ℝ)) := by
      ring
    rw [hle2] at hle1
    exact le_trans hbase hle1
  exact besovSeminorm_sq_le_of_scale_bound t ρ
    (kS * (2 * (K₀ * volumeAverage (HighContrast.adaptedCell q t)
          (scalarVariationEnergyIntegrand b v)) + 2 * blockVecDot Y Y))
    hρ1 hρ0 hA0
    (fun n z => blockMatVecMul S
      (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) z) (optimizerField b v) - Y))
    hper

end

end HCPolySupport.HighContrast.Multiscale
end

section
open HCPolySupport.HighContrast (CoeffSpace blockScale blockSub coarseBlock normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

/-! ## The all-scale Loewner bound on every triadic subcell

`coarseBlock_le_one_add_respAllScaleMax` bounds only the terminal cell of the response grid
by `(1 + respAllScaleMax) E_t`.  The all-scale maximum (`p.response.transfer`) is a
supremum over every depth, so the same Loewner bound holds on every triadic subcell, with the
depth-`n` weight `3 ^ (Quenched.contrastRho γ * n)` made explicit: the weighted normalized
recentred block of
the depth-`n` cell enters the defining set of the maximum, so the depth-`n` spectral bound is
`3 ^ (Quenched.contrastRho γ * n) * respAllScaleMax`. -/

/-- Cauchy--Schwarz against the L2 operator norm: for any real square matrix `N` and real vector
`v`, the quadratic form `v ⬝ᵥ (N *ᵥ v)` is dominated by `‖N‖ * (v ⬝ᵥ v)`. -/
private theorem dotProduct_mulVec_le_opNorm_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℝ) (v : n → ℝ) : v ⬝ᵥ (N *ᵥ v) ≤ ‖N‖ * (v ⬝ᵥ v) := by
  have hsq := vecSq_mulVec_le N v
  have hvv : (0 : ℝ) ≤ v ⬝ᵥ v := dotProduct_self_nonneg v
  rcases eq_or_lt_of_le (norm_nonneg N) with h0 | hpos
  · have hN : N = 0 := norm_eq_zero.mp h0.symm
    subst hN
    simp
  · have hexp : (0 : ℝ) ≤ (‖N‖ • v - N *ᵥ v) ⬝ᵥ (‖N‖ • v - N *ᵥ v) :=
      dotProduct_self_nonneg _
    have hexpand : (‖N‖ • v - N *ᵥ v) ⬝ᵥ (‖N‖ • v - N *ᵥ v) =
        ‖N‖ * ‖N‖ * (v ⬝ᵥ v) - 2 * ‖N‖ * (v ⬝ᵥ (N *ᵥ v)) + (N *ᵥ v) ⬝ᵥ (N *ᵥ v) := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, dotProduct_comm (N *ᵥ v) v]
      ring
    rw [hexpand] at hexp
    nlinarith only [hexp, hsq, hpos]

/-- The operator-norm Loewner envelope of an arbitrary doubled block: every doubled block is
dominated by its L2 operator norm times the doubled identity.  This is the nonemptiness witness
that reads the infimum defining `blockSpecBound` as a Loewner upper bound. -/
private theorem blockMatLoewnerLE_blockScale_opNorm {d : ℕ} (N : BlockMat d) :
    BlockMatLoewnerLE N (blockScale (blockOpNorm N) (Book.Ch02.blockIdentity d)) := by
  intro X
  have h := dotProduct_mulVec_le_opNorm_mul_self (toFullBlockMat N) (toFullBlockVec X)
  have hL : blockVecDot X (blockMatVecMul N X) =
      toFullBlockVec X ⬝ᵥ (toFullBlockMat N *ᵥ toFullBlockVec X) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  have hR : blockVecDot X (blockMatVecMul (blockScale (blockOpNorm N)
      (Book.Ch02.blockIdentity d)) X) =
      blockOpNorm N * (toFullBlockVec X ⬝ᵥ toFullBlockVec X) := by
    rw [qform_blockScale_smul, qform_identity]
  rw [hL, hR]
  unfold blockOpNorm at h ⊢
  linarith only [h]

/-- The all-scale Loewner bound on every triadic subcell (`p.response.transfer`):
for `P`-a.e. sample `a`, every depth-`n` cell of the response grid is Loewner-dominated by
`(1 + 3 ^ (Quenched.contrastRho γ * n) * respAllScaleMax) · respMean`, with the depth weight
explicit. -/
theorem coarseBlock_subcell_le_one_add_scaled_respAllScaleMax (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) :
    ∀ᵐ a ∂P, ∀ (n : ℕ), ∀ z ∈ triadicIndexBox d n,
      BlockMatLoewnerLE
        (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
        (blockScale (1 + (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) * respAllScaleMax P γ jStar F t a)
          (respMean P jStar F t)) := by
  let : NeZero d := ⟨by omega⟩
  have _hγ := hγ
  have hEt : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src hstat hdag jStar hj (explicitCanonicalMetric F) hm t
  filter_upwards [pathwise_envelope hd γ P E Ψ Kg Src hstat hdag jStar hj F hm t]
    with a ha
  obtain ⟨C, _hC0, _hL0, hterms⟩ := ha
  intro n z hz
  -- the defining set of the all-scale maximum is bounded above by the envelope constant `C`
  have hbdd : BddAbove {y : ℝ | ∃ n : ℕ, ∃ z ∈ triadicIndexBox d n, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))} := by
    refine ⟨C, ?_⟩
    rintro y ⟨m, w, hw, rfl⟩
    exact hterms m w hw
  -- the depth-`n`, cell-`z` weighted term is a member of that set
  have hmem : (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d)) ∈
      {y : ℝ | ∃ n : ℕ, ∃ z ∈ triadicIndexBox d n, y =
        (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
          blockSpecBound (blockSub
            (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
              (respMean P jStar F t)) (Book.Ch02.blockIdentity d))} :=
    ⟨n, z, hz, rfl⟩
  have hle : (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d)) ≤
      respAllScaleMax P γ jStar F t a :=
    le_csSup hbdd hmem
  -- multiply by the positive depth weight `3 ^ (Quenched.contrastRho γ * n)`
  have hspec : blockSpecBound (blockSub
        (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
          (respMean P jStar F t)) (Book.Ch02.blockIdentity d)) ≤
      (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) * respAllScaleMax P γ jStar F t a := by
    have hpos : 0 < (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hcancel : (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) *
        (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      have hexp : Quenched.contrastRho γ * (n : ℝ) + -(Quenched.contrastRho γ * (n : ℝ)) = 0 := by ring
      rw [hexp, Real.rpow_zero]
    calc blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))
        = (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) *
            ((3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
              blockSpecBound (blockSub
                (normalizedBlock
                  (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
                  (respMean P jStar F t)) (Book.Ch02.blockIdentity d))) := by
          rw [← mul_assoc, hcancel, one_mul]
      _ ≤ (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) * respAllScaleMax P γ jStar F t a :=
          mul_le_mul_of_nonneg_left hle hpos.le
  -- back to a Loewner bound, then un-normalize
  have hwit : BlockMatLoewnerLE (blockSub
        (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
          (respMean P jStar F t)) (Book.Ch02.blockIdentity d))
      (blockScale (blockOpNorm (blockSub
        (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
          (respMean P jStar F t)) (Book.Ch02.blockIdentity d)))
        (Book.Ch02.blockIdentity d)) :=
    blockMatLoewnerLE_blockScale_opNorm _
  have hfin : BlockMatLoewnerLE
      (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
        (respMean P jStar F t))
      (blockScale (1 + (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) * respAllScaleMax P γ jStar F t a)
        (Book.Ch02.blockIdentity d)) :=
    le_one_add_specBound _ _ _ (norm_nonneg _) hwit hspec
  exact le_scale_of_normalizedBlock_le hEt hfin

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Deterministic glue facts for the weak-quantity bound

Four independent algebraic facts used to propagate the quadratic-form bounds of the coarse
blocks through the recentring and normalization steps of the weak-quantity bound.

* `qform_blockCongr_le` transports a quadratic-form bound through the congruence
  `Gᵀ A G`, using that the flattened quadratic form of `blockCongr G A` is the form of `A`
  evaluated on `G X`.
* `qform_le_of_loewner` turns a Loewner comparison against a scalar multiple `c E` into a
  scalar multiple of the quadratic-form bound of `E`.
* `qform_add_blockSwap_le` adds the swap block `𝐑` to a bounded block and pays exactly one
  unit of the identity form, by the arithmetic-geometric inequality `2 x · y ≤ x · x + y · y`.
* `volumeAverage_vecDot_optimizerField_eq` identifies the doubled energy of the optimizer
  state with the symmetric part of the coefficient: `ξ · (M ξ) = ξ · (symmPart M) ξ`.

Paper: the response quadratic form `AK.HC (2.15)`.
-/

open HCPolySupport.HighContrast (blockScale)
namespace HCPolySupport.HighContrast.Multiscale

noncomputable section

/-- The quadratic form of a scalar dilation of a doubled block:
`X ⬝ (c A) X = c (X ⬝ A X)`. -/
private theorem qform_blockScale {d : ℕ} (c : ℝ) (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockScale c A) X) =
      c * blockVecDot X (blockMatVecMul A X) := by
  simp only [blockScale, blockMatVecMul, smul_matVecMul, vecDot_add_right,
    vecDot_smul_right, blockVecDot]
  ring

/-- The quadratic form of a sum of two blocks presented through `ofFullBlockMat` splits into
the sum of the two quadratic forms. -/
private theorem qform_ofFullBlockMat_add {d : ℕ} (A B : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (ofFullBlockMat (toFullBlockMat A + toFullBlockMat B)) X) =
      blockVecDot X (blockMatVecMul A X) + blockVecDot X (blockMatVecMul B X) := by
  rw [← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec,
    toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul,
    toFullBlockMat_ofFullBlockMat, Matrix.add_mulVec, dotProduct_add]

/-- A congruence `Gᵀ A G` transports a quadratic-form bound: if `A` is bounded by `K` and `G`
is bounded by `kG`, then `blockCongr G A` is bounded by `K kG`.  The proof evaluates the
congruence form on `G X` and composes the two bounds.  Paper: `AK.HC (2.15)`. -/
theorem qform_blockCongr_le {d : ℕ} (G A : BlockMat d) (K kG : ℝ) (hK : 0 ≤ K)
    (hA : ∀ X : BlockVec d, blockVecDot X (blockMatVecMul A X) ≤ K * blockVecDot X X)
    (hG : ∀ X : BlockVec d, blockVecDot (blockMatVecMul G X) (blockMatVecMul G X)
        ≤ kG * blockVecDot X X) :
    ∀ X : BlockVec d, blockVecDot X (blockMatVecMul (blockCongr G A) X)
      ≤ (K * kG) * blockVecDot X X := by
  intro X
  rw [blockVecDot_blockCongr]
  calc
    blockVecDot (blockMatVecMul G X) (blockMatVecMul A (blockMatVecMul G X))
        ≤ K * blockVecDot (blockMatVecMul G X) (blockMatVecMul G X) := hA (blockMatVecMul G X)
    _ ≤ K * (kG * blockVecDot X X) :=
          mul_le_mul_of_nonneg_left (hG X) hK
    _ = (K * kG) * blockVecDot X X := by ring

/-- A Loewner comparison `A ≤ c E` combines with a quadratic-form bound `E ≤ kE` on `E` into
the bound `A ≤ c kE` on the identity form.  Paper: `AK.HC (2.15)`. -/
theorem qform_le_of_loewner {d : ℕ} {A E : BlockMat d} {c kE : ℝ} (hc : 0 ≤ c)
    (hA : BlockMatLoewnerLE A (blockScale c E))
    (hE : ∀ X : BlockVec d, blockVecDot X (blockMatVecMul E X) ≤ kE * blockVecDot X X) :
    ∀ X : BlockVec d, blockVecDot X (blockMatVecMul A X) ≤ (c * kE) * blockVecDot X X := by
  intro X
  have hX := hA X
  rw [qform_blockScale] at hX
  calc
    blockVecDot X (blockMatVecMul A X) ≤ c * blockVecDot X (blockMatVecMul E X) := by
          linarith only [hX]
    _ ≤ c * (kE * blockVecDot X X) := mul_le_mul_of_nonneg_left (hE X) hc
    _ = (c * kE) * blockVecDot X X := by ring

/-- Adding the swap block `𝐑` to a quadratically bounded block costs exactly one unit of the
identity form: `X ⬝ (A + 𝐑) X ≤ (K + 1) (X ⬝ X)`.  The swap contributes the off-diagonal
pairing `2 x · y`, which the arithmetic-geometric inequality bounds by `x · x + y · y`.
Paper: `AK.HC (2.15)`. -/
theorem qform_add_blockSwap_le {d : ℕ} {A : BlockMat d} {K : ℝ}
    (hA : ∀ X : BlockVec d, blockVecDot X (blockMatVecMul A X) ≤ K * blockVecDot X X) :
    ∀ X : BlockVec d, blockVecDot X (blockMatVecMul
        (ofFullBlockMat (toFullBlockMat A + toFullBlockMat (blockSwap d))) X)
      ≤ (K + 1) * blockVecDot X X := by
  intro X
  rw [qform_ofFullBlockMat_add]
  have hswap : blockVecDot X (blockMatVecMul (blockSwap d) X) ≤ blockVecDot X X := by
    have hb := abs_vecDot_le_add_halves_vecNormSq X.1 X.2
    have h1 : vecDot X.1 X.2 ≤ vecDot X.1 X.1 / 2 + vecDot X.2 X.2 / 2 := by
      simpa only [vecNormSq] using le_trans (le_abs_self (vecDot X.1 X.2)) hb
    have h2 : vecDot X.2 X.1 ≤ vecDot X.1 X.1 / 2 + vecDot X.2 X.2 / 2 := by
      rw [vecDot_comm]
      simpa only [vecNormSq] using le_trans (le_abs_self (vecDot X.1 X.2)) hb
    simp only [blockVecDot, blockMatVecMul_blockSwap_fst, blockMatVecMul_blockSwap_snd]
    linarith only [h1, h2]
  calc
    blockVecDot X (blockMatVecMul A X) + blockVecDot X (blockMatVecMul (blockSwap d) X)
        ≤ K * blockVecDot X X + blockVecDot X X := add_le_add (hA X) hswap
    _ = (K + 1) * blockVecDot X X := by ring

/-- The doubled energy of the optimizer state is the symmetric energy: pointwise,
`ξ · (b x ξ) = ξ · (symmPart (b x) ξ)` because the antisymmetric part contributes nothing to
the quadratic form.  The optimizer field is `(∇v, b ∇v)` and the variation energy integrand
is `∇v · (symmPart b) ∇v`, so the two volume averages agree. -/
theorem volumeAverage_vecDot_optimizerField_eq {d : ℕ} [NeZero d] (V : Set (Vec d))
    (b : CoeffField d) (v : AHarmonicFunction b V) :
    volumeAverage V (fun x => vecDot (optimizerField b v x).1 (optimizerField b v x).2)
      = volumeAverage V (scalarVariationEnergyIntegrand b v) := by
  have _ : NeZero d := ‹NeZero d›
  have h : (fun x => vecDot (optimizerField b v x).1 (optimizerField b v x).2)
      = scalarVariationEnergyIntegrand b v := by
    funext x
    simp only [optimizerField, scalarVariationEnergyIntegrand]
    exact (vecDot_matVecMul_symmPart (b x) (v.toH1.grad x)).symm
  rw [h]

end

end HCPolySupport.HighContrast.Multiscale
end
