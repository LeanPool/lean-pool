/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.ResponseTransferHelpers
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.SelectionExponentBounds
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.CanonicalCutoffPairingMeasurability
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.DualityBoundHypotheses
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.BesovScaleSummationToolkit
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.OptimizerEnergyIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RecentCellDefectBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.WeakEstimateFenchelBound
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# High-contrast homogenization: Entry.Response.Kernel.WeakIntegrandDomination

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Almost-Sure Domination of the Weak-Quantity Integrand

This file shows that, for an arbitrary family of response maximizers and either sign of the
recentring, the square of the scale-average seminorm of the recentred, canonically metric-scaled
cell averages of the doubled optimizer state is almost-surely dominated by the all-scale envelope
entering the weak quantity `W^\pm` of `e.response.weak.estimate`. It records the elementary
measure-theoretic fact that a measurable nonnegative function almost-surely dominated by an
integrable envelope is itself integrable, and applies it to the squared seminorm. It assembles
these into the integrability of the weak-quantity integrand directly from the standing law
premises, for both signs.
-/

section
/-!
## Almost-sure domination of the weak-quantity integrand by the all-scale envelope

The weak quantity `W^\pm` of `e.response.weak.estimate` is the sample expectation of the square of
the scale-average seminorm `besovSeminorm` of the recentred, canonically-metric-scaled cell averages
of the doubled optimizer state `X_t^\pm`.  This file bounds that integrand, for an arbitrary family
of response maximizers, almost surely by an explicit multiple of the all-scale envelope
`1 + respAllScaleMax` times the recentred response `J` of AK.HC (2.15), plus one.

The bound is the almost-sure consequence of the pathwise scale-average seminorm bound of
AK.HC (2.130): the optimizer field is replaced, cell average by cell average, by the Chapter-2
canonical maximizer of an elliptic representative of the recentred coefficient; the pathwise bound
is applied to that representative with the subcell quadratic-form envelope read off the all-scale
Loewner bound; and the energy--response identity of `e.response.weak.estimate` converts the cell
energy into twice the recentred response.  The constant is allowed to depend on the sample law and
the fixed data, but not on the sample.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace coarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The squared norm of `A X` is bounded by the square of the operator norm of `A` times the
squared norm of `X`, `|A X| ^ 2 ≤ |A| ^ 2 |X| ^ 2`.  This is the quadratic-form bound of the
canonical metric square root and of the recentring shear. -/
private theorem qform_blockMatVecMul_self_le_opNorm_sq_mul_self {d : ℕ} (A : BlockMat d) :
    ∀ X : BlockVec d, blockVecDot (blockMatVecMul A X) (blockMatVecMul A X)
      ≤ blockOpNorm A ^ 2 * blockVecDot X X := by
  intro X
  have h := vecSq_mulVec_le (toFullBlockMat A) (toFullBlockVec X)
  rw [← toFullBlockVec_blockMatVecMul A X] at h
  simpa only [dotProduct_toFullBlockVec, blockOpNorm] using h

/-- The quadratic form of a positive semidefinite block is bounded by its operator norm:
`X ⬝ (A X) ≤ |A| (X ⬝ X)`.  This is the deterministic quadratic-form bound for the annealed
mean `respMean` of the weak-quantity estimate `e.response.weak.estimate`. -/
private theorem qform_le_opNorm_mul_self_of_posSemidef {d : ℕ} {A : BlockMat d}
    (hA : (toFullBlockMat A).PosSemidef) :
    ∀ X : BlockVec d, blockVecDot X (blockMatVecMul A X)
      ≤ blockOpNorm A * blockVecDot X X := by
  intro X
  have h := psd_dot_le_opNorm hA (toFullBlockVec X)
  rw [← toFullBlockVec_blockMatVecMul A X] at h
  simpa only [dotProduct_toFullBlockVec, blockOpNorm] using h

/-- **The a.e. domination of the weak-quantity integrand.**  For a recentred coefficient family
`c` whose samplewise field admits an elliptic representative and whose coarse block is the fixed
congruence `Gᵀ (coarseBlock a) G`, and for an arbitrary family `u` of response maximizers, the
squared scale-average seminorm of the `M_0 ^ (1/2)`-transported recentred optimizer state is
dominated almost surely by an explicit constant times `(1 + ℳ) J + 1`, with `ℳ` the all-scale
envelope of `e.response.weak.estimate` and `J` the recentred pathwise response of AK.HC (2.15).

The constant is built from the metric operator bound `|M_0 ^ (1/2)| ^ 2`, the congruence operator
bound `|G| ^ 2`, the annealed-mean operator bound `|E_t|`, the geometric factor `3 ^ t`,
`Y ⬝ Y`, and the `ρ`-summation gain of the scale-average seminorm AK.HC (2.130); it depends on the
sample law and the fixed data only, never on the sample. -/
private theorem ae_besovSeminorm_sq_le_envelope_of_recentring {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (p q' : Vec d) (Y : BlockVec d)
    (G : BlockMat d) (c : CoeffSpace d → CoeffField d)
    (hrep : ∀ a : CoeffSpace d, ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
        c a =ᵐ[volumeMeasureOn (respCell jStar F t)] f)
    (hcoarse : ∀ (a : CoeffSpace d) (j : ℤ) (w : Fin d → ℤ),
      coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w) (c a)
        = blockCongr G (coarseBlock (adaptedCellAtCenter (respGrid jStar F) j w) a))
    (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (c a) (u a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ a ∂P,
      besovSeminorm t (fun n z => blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
            (optimizerField (c a) (u a)) - Y)) ^ 2
        ≤ C * ((1 + respAllScaleMax P γ jStar F t a) *
              respJ (respGrid jStar F) t p q' (c a) + 1) := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hj hm
  have hEt : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src hstat hdag jStar hj (explicitCanonicalMetric F) hm t
  have hEt_psd : (toFullBlockMat (respMean P jStar F t)).PosSemidef := hEt.posSemidef
  have hρ0 : 0 ≤ Quenched.contrastRho γ := by
    simp only [Quenched.contrastRho]; linarith only [hγ.1]
  have hρ1 : Quenched.contrastRho γ < 1 := by
    simp only [Quenched.contrastRho]; linarith only [hγ.2]
  -- the deterministic operator constants
  let kE : ℝ := blockOpNorm (respMean P jStar F t)
  let kG : ℝ := blockOpNorm G ^ 2
  let kS : ℝ := blockOpNorm (blockSqrt (respM0 F)) ^ 2
  have hkE : 0 ≤ kE := by simp only [kE]; exact norm_nonneg _
  have hkG : 0 ≤ kG := by simp only [kG]; exact sq_nonneg _
  have hkS : 0 ≤ kS := by simp only [kS]; exact sq_nonneg _
  have hEbound : ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul (respMean P jStar F t) X) ≤ kE * blockVecDot X X := by
    intro X; exact qform_le_opNorm_mul_self_of_posSemidef hEt_psd X
  have hGbound : ∀ X : BlockVec d,
      blockVecDot (blockMatVecMul G X) (blockMatVecMul G X) ≤ kG * blockVecDot X X := by
    intro X; exact qform_blockMatVecMul_self_le_opNorm_sq_mul_self G X
  have hSbound : ∀ X : BlockVec d,
      blockVecDot (blockMatVecMul (blockSqrt (respM0 F)) X)
          (blockMatVecMul (blockSqrt (respM0 F)) X) ≤ kS * blockVecDot X X := by
    intro X; exact qform_blockMatVecMul_self_le_opNorm_sq_mul_self (blockSqrt (respM0 F)) X
  -- the final constant: the pathwise gain, the metric bound, and the envelope coefficients
  let Cst : ℝ := ((1 - (3 : ℝ) ^ ((Quenched.contrastRho γ - 1) / 2))⁻¹) ^ 2 * (3 : ℝ) ^ (t : ℝ) * kS
      * (4 * kE * kG + 4 + 2 * blockVecDot Y Y)
  have hCst : 0 ≤ Cst := by
    simp only [Cst]
    refine mul_nonneg ?_ ?_
    · refine mul_nonneg ?_ hkS
      exact mul_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
    · have h1 : 0 ≤ kE * kG := mul_nonneg hkE hkG
      have h2 : 0 ≤ blockVecDot Y Y := Response.blockVecDot_self_nonneg Y
      linarith only [h1, h2]
  refine ⟨Cst, hCst, ?_⟩
  filter_upwards [coarseBlock_subcell_le_one_add_scaled_respAllScaleMax d hd γ hγ P E Ψ Kg Src
    hstat hdag jStar hj F hm t] with a hLo
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ := hrep a
  let A : Book.Ch02.CoeffOn (adaptedDomain (respGrid jStar F) hq t) :=
    coeffOnOfIsEllipticFieldOn (U := adaptedDomain (respGrid jStar F) hq t) hlam hle hEll
  let v : AHarmonicFunction f (respCell jStar F t) := canonicalAHarmonicFunctionOfCoeffOn A p q'
  -- the arbitrary maximizer family is replaced by the canonical maximizer of the representative
  have hsemi : besovSeminorm t (fun n z => blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y))
      = besovSeminorm t (fun n z => blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField f v) - Y)) := by
    refine besovSeminorm_congr (fun n w hw => ?_)
    have hVU : adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w ⊆ respCell jStar F t :=
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw
    have hcell := cellAverage_optimizerField_eq_canonical (U := adaptedDomain (respGrid jStar F) hq t)
      hVU hlam hle hEll hae p q' (u a) (hu a)
    have hcellv : cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (optimizerField (c a) (u a))
        = cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (optimizerField f v) := hcell
    rw [hcellv]
  have hvmax : IsResponseMaximizer (respCell jStar F t) p q' f v := by
    simpa only [v, canonicalAHarmonicFunctionOfCoeffOn] using!
      (scalarCanonicalMaximizerOfCoeffOn A p q').isResponseMaximizer
  -- the energy--response identity
  have hUmeas : MeasurableSet (respCell jStar F t) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isOpen.measurableSet
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) := by
    simpa only [volumeMeasureOn, respCell] using
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
  have hEnn : 0 ≤ volumeAverage (respCell jStar F t) (scalarVariationEnergyIntegrand f v) :=
    volumeAverage_nonneg_of_nonneg_on hUmeas
      (scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn (respCell jStar F t) f hEll v)
  have hIntf : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hint : IntegrableOn (scalarVariationEnergyIntegrand f v) (respCell jStar F t) :=
    hIntf.energy v
  have hweak : weakOptimizerEnergy (respCell jStar F t) f v ^ 2 =
      2 * ResponseJ (respCell jStar F t) p q' f :=
    weakOptimizerEnergy_sq_eq_two_responseJ hUmeas hEll p q' v hvmax
  have hvec_nn : 0 ≤ volumeAverage (respCell jStar F t)
      (fun x => vecDot (optimizerField f v x).1 (optimizerField f v x).2) := by
    rw [volumeAverage_vecDot_optimizerField_eq (respCell jStar F t) f v]
    exact hEnn
  have hsq : weakOptimizerEnergy (respCell jStar F t) f v ^ 2 =
      volumeAverage (respCell jStar F t)
        (fun x => vecDot (optimizerField f v x).1 (optimizerField f v x).2) := by
    unfold weakOptimizerEnergy
    exact Real.sq_sqrt hvec_nn
  have hE2 : volumeAverage (respCell jStar F t) (scalarVariationEnergyIntegrand f v) =
      2 * respJ (respGrid jStar F) t p q' (c a) := by
    rw [← volumeAverage_vecDot_optimizerField_eq (respCell jStar F t) f v]
    rw [← hsq, hweak, ← responseJ_congr_of_ae_eq hae p q']
    rfl
  have hJnn : 0 ≤ respJ (respGrid jStar F) t p q' (c a) := by
    linarith only [hEnn, hE2]
  have hMnn : 0 ≤ respAllScaleMax P γ jStar F t a := respAllScaleMax_nonneg P γ jStar F t a
  -- the subcell quadratic-form envelope read off the all-scale Loewner bound
  let K₀ : ℝ := kE * kG * (1 + respAllScaleMax P γ jStar F t a) + 1
  have hK₀ : 0 < K₀ := by
    have hnonneg : 0 ≤ kE * kG * (1 + respAllScaleMax P γ jStar F t a) :=
      mul_nonneg (mul_nonneg hkE hkG) (by linarith only [hMnn])
    simp only [K₀]
    linarith only [hnonneg]
  have hBf : ∀ (n : ℕ), ∀ w ∈ triadicIndexBox d n, ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul (ofFullBlockMat (toFullBlockMat
          (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) f)
        + toFullBlockMat (blockSwap d))) X)
        ≤ (K₀ * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ))) * blockVecDot X X := by
    intro n w hw X
    have hVU : adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w ⊆ respCell jStar F t :=
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw
    have hsub : c a =ᵐ[volumeMeasureOn (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)] f :=
      MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
    have hcongr : coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) f
        = blockCongr G (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a) := by
      rw [← coarseBlockMatrix_congr_of_ae_eq hsub, hcoarse a (t - (n : ℤ)) w]
    have hLo' := hLo n w hw
    have hc : 0 ≤ 1 + (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) * respAllScaleMax P γ jStar F t a := by
      have hp : 0 ≤ (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) * respAllScaleMax P γ jStar F t a :=
        mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) hMnn
      linarith only [hp]
    have hqA : ∀ X : BlockVec d, blockVecDot X (blockMatVecMul
        (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a) X)
        ≤ ((1 + (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) * respAllScaleMax P γ jStar F t a) * kE)
            * blockVecDot X X :=
      qform_le_of_loewner hc hLo' hEbound
    have hqcon : ∀ X : BlockVec d, blockVecDot X (blockMatVecMul
        (blockCongr G (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a)) X)
        ≤ (((1 + (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) * respAllScaleMax P γ jStar F t a) * kE) * kG)
            * blockVecDot X X :=
      qform_blockCongr_le G (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a)
        ((1 + (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) * respAllScaleMax P γ jStar F t a) * kE) kG
        (mul_nonneg hc hkE) hqA hGbound
    have hqadd := qform_add_blockSwap_le hqcon X
    rw [hcongr]
    refine le_trans hqadd ?_
    have hp1 : (1 : ℝ) ≤ (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg hρ0 (Nat.cast_nonneg n))
    have hcoef : (((1 + (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ))
            * respAllScaleMax P γ jStar F t a) * kE) * kG + 1)
        ≤ K₀ * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) := by
      have hkEG : 0 ≤ kE * kG := mul_nonneg hkE hkG
      have hkey : (kE * kG * (1 + respAllScaleMax P γ jStar F t a) + 1)
            * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ))
          - ((((1 + (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ))
              * respAllScaleMax P γ jStar F t a) * kE) * kG) + 1)
          = (kE * kG + 1) * ((3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) - 1) := by ring
      have hnn : 0 ≤ (kE * kG + 1) * ((3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) - 1) :=
        mul_nonneg (by linarith only [hkEG]) (by linarith only [hp1])
      simp only [K₀]
      linarith only [hkey, hnn]
    exact mul_le_mul_of_nonneg_right hcoef (Response.blockVecDot_self_nonneg X)
  -- the pathwise scale-average seminorm bound at the elliptic representative
  have hpath := besovSeminorm_sq_optimizerState_le_of_scale_bounds (q := respGrid jStar F)
    hq t (Quenched.contrastRho γ) hρ0 hρ1 hEll v (blockSqrt (respM0 F)) Y kS hkS hSbound K₀ hK₀ hBf hint hEnn
  -- absorb the energy into the response and the constant into the envelope
  have hinner : 2 * (2 * ((kE * kG * (1 + respAllScaleMax P γ jStar F t a) + 1)
        * respJ (respGrid jStar F) t p q' (c a))) + 2 * blockVecDot Y Y
      ≤ (4 * kE * kG + 4 + 2 * blockVecDot Y Y)
          * ((1 + respAllScaleMax P γ jStar F t a) * respJ (respGrid jStar F) t p q' (c a) + 1) := by
    have hYnn : 0 ≤ blockVecDot Y Y := Response.blockVecDot_self_nonneg Y
    have hkEG : 0 ≤ kE * kG := mul_nonneg hkE hkG
    have hQ1 : 1 ≤ (1 + respAllScaleMax P γ jStar F t a)
        * respJ (respGrid jStar F) t p q' (c a) + 1 := by
      have hprod : 0 ≤ (1 + respAllScaleMax P γ jStar F t a)
          * respJ (respGrid jStar F) t p q' (c a) :=
        mul_nonneg (by linarith only [hMnn]) hJnn
      linarith only [hprod]
    have hMJ : (1 + respAllScaleMax P γ jStar F t a) * respJ (respGrid jStar F) t p q' (c a)
        ≤ (1 + respAllScaleMax P γ jStar F t a)
          * respJ (respGrid jStar F) t p q' (c a) + 1 := by linarith only []
    have hQJ : respJ (respGrid jStar F) t p q' (c a)
        ≤ (1 + respAllScaleMax P γ jStar F t a)
          * respJ (respGrid jStar F) t p q' (c a) + 1 := by
      have h1 : (1 : ℝ) ≤ 1 + respAllScaleMax P γ jStar F t a := by linarith only [hMnn]
      have hJMJ : respJ (respGrid jStar F) t p q' (c a)
          ≤ (1 + respAllScaleMax P γ jStar F t a) * respJ (respGrid jStar F) t p q' (c a) := by
        simpa using mul_le_mul_of_nonneg_right h1 hJnn
      linarith only [hJMJ]
    calc
      2 * (2 * ((kE * kG * (1 + respAllScaleMax P γ jStar F t a) + 1)
            * respJ (respGrid jStar F) t p q' (c a))) + 2 * blockVecDot Y Y
          = 4 * (kE * kG)
              * ((1 + respAllScaleMax P γ jStar F t a)
                * respJ (respGrid jStar F) t p q' (c a))
            + 4 * respJ (respGrid jStar F) t p q' (c a) + 2 * blockVecDot Y Y := by ring
      _ ≤ 4 * (kE * kG)
              * ((1 + respAllScaleMax P γ jStar F t a)
                * respJ (respGrid jStar F) t p q' (c a) + 1)
            + 4 * ((1 + respAllScaleMax P γ jStar F t a)
                * respJ (respGrid jStar F) t p q' (c a) + 1)
            + 2 * blockVecDot Y Y
              * ((1 + respAllScaleMax P γ jStar F t a)
                * respJ (respGrid jStar F) t p q' (c a) + 1) := by
          have h1 : 4 * (kE * kG)
                * ((1 + respAllScaleMax P γ jStar F t a)
                  * respJ (respGrid jStar F) t p q' (c a))
              ≤ 4 * (kE * kG)
                * ((1 + respAllScaleMax P γ jStar F t a)
                  * respJ (respGrid jStar F) t p q' (c a) + 1) :=
            mul_le_mul_of_nonneg_left hMJ (by positivity)
          have h2 : 4 * respJ (respGrid jStar F) t p q' (c a)
              ≤ 4 * ((1 + respAllScaleMax P γ jStar F t a)
                  * respJ (respGrid jStar F) t p q' (c a) + 1) := by linarith only [hQJ]
          have h3 : 2 * blockVecDot Y Y
              ≤ 2 * blockVecDot Y Y
                * ((1 + respAllScaleMax P γ jStar F t a)
                  * respJ (respGrid jStar F) t p q' (c a) + 1) := by
            have h := mul_le_mul_of_nonneg_left hQ1 hYnn
            linarith only [h]
          linarith only [h1, h2, h3]
      _ = (4 * kE * kG + 4 + 2 * blockVecDot Y Y)
            * ((1 + respAllScaleMax P γ jStar F t a)
              * respJ (respGrid jStar F) t p q' (c a) + 1) := by ring
  have hpath' : ((1 - (3 : ℝ) ^ ((Quenched.contrastRho γ - 1) / 2))⁻¹) ^ 2
        * ((3 : ℝ) ^ (t : ℝ) * (kS * (2 * (K₀ * volumeAverage (respCell jStar F t)
              (scalarVariationEnergyIntegrand f v)) + 2 * blockVecDot Y Y)))
      ≤ Cst * ((1 + respAllScaleMax P γ jStar F t a)
          * respJ (respGrid jStar F) t p q' (c a) + 1) := by
    have hkey : ((1 - (3 : ℝ) ^ ((Quenched.contrastRho γ - 1) / 2))⁻¹) ^ 2
          * ((3 : ℝ) ^ (t : ℝ) * (kS * (2 * (K₀ * volumeAverage (respCell jStar F t)
                (scalarVariationEnergyIntegrand f v)) + 2 * blockVecDot Y Y)))
        = ((1 - (3 : ℝ) ^ ((Quenched.contrastRho γ - 1) / 2))⁻¹) ^ 2 * (3 : ℝ) ^ (t : ℝ) * kS
            * (2 * (2 * ((kE * kG * (1 + respAllScaleMax P γ jStar F t a) + 1)
                * respJ (respGrid jStar F) t p q' (c a))) + 2 * blockVecDot Y Y) := by
      rw [hE2]
      simp only [K₀]
      ring
    rw [hkey]
    have hkey2 : Cst * ((1 + respAllScaleMax P γ jStar F t a)
          * respJ (respGrid jStar F) t p q' (c a) + 1)
        = ((1 - (3 : ℝ) ^ ((Quenched.contrastRho γ - 1) / 2))⁻¹) ^ 2 * (3 : ℝ) ^ (t : ℝ) * kS
            * ((4 * kE * kG + 4 + 2 * blockVecDot Y Y)
              * ((1 + respAllScaleMax P γ jStar F t a)
                * respJ (respGrid jStar F) t p q' (c a) + 1)) := by
      simp only [Cst]; ring
    rw [hkey2]
    exact mul_le_mul_of_nonneg_left hinner
      (mul_nonneg (mul_nonneg (sq_nonneg _)
        (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))) hkS)
  rw [hsemi]
  exact le_trans hpath hpath'

/-- **The a.e. domination of the weak-quantity integrand, recentred sign.**  For the recentred
coefficient family `a_- = a - g` and an arbitrary family of response maximizers, the squared
scale-average seminorm of the `M_0 ^ (1/2)`-transported recentred optimizer state is dominated
almost surely by an explicit constant times `(1 + ℳ) J^- + 1`, with `ℳ` the all-scale envelope and
`J^-` the recentred pathwise response of AK.HC (2.15).  This is the almost-sure input of the weak
quantity `W^-` of `e.response.weak.estimate`. -/
theorem ae_besovSeminorm_sq_le_envelope_minus {d : ℕ} [NeZero d] (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (p q' : Vec d) (Y : BlockVec d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (respCoeffMinus F a) (u a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ a ∂P,
      besovSeminorm t (fun n z => blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
            (optimizerField (respCoeffMinus F a) (u a)) - Y)) ^ 2
        ≤ C * ((1 + respAllScaleMax P γ jStar F t a) *
              respJ (respGrid jStar F) t p q' (respCoeffMinus F a) + 1) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hj hm
  exact ae_besovSeminorm_sq_le_envelope_of_recentring hd γ hγ P E Ψ Kg Src hstat hdag jStar hj F hm
    t p q' Y (respG F) (respCoeffMinus F)
    (fun a => exists_elliptic_representative_respCell_respCoeffMinus hj hm t a)
    (fun a j w => coarseBlockMatrix_respCoeffMinus_at hq j w F a) u hu

/-- **The a.e. domination of the weak-quantity integrand, adjoint sign.**  The adjoint twin of
`ae_besovSeminorm_sq_le_envelope_minus`: for the adjoint recentred coefficient family
`a_+ = aᵀ + g` and an arbitrary family of response maximizers, the squared scale-average seminorm
of the `M_0 ^ (1/2)`-transported recentred optimizer state is dominated almost surely by an
explicit constant times `(1 + ℳ) J^+ + 1`, with `J^+` the adjoint recentred pathwise response of
AK.HC (2.15).  This is the almost-sure input of the weak quantity `W^+` of
`e.response.weak.estimate`. -/
theorem ae_besovSeminorm_sq_le_envelope_plus {d : ℕ} [NeZero d] (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (p q' : Vec d) (Y : BlockVec d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (respCoeffPlus F a) (u a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ a ∂P,
      besovSeminorm t (fun n z => blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
            (optimizerField (respCoeffPlus F a) (u a)) - Y)) ^ 2
        ≤ C * ((1 + respAllScaleMax P γ jStar F t a) *
              respJ (respGrid jStar F) t p q' (respCoeffPlus F a) + 1) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hj hm
  exact ae_besovSeminorm_sq_le_envelope_of_recentring hd γ hγ P E Ψ Kg Src hstat hdag jStar hj F hm
    t p q' Y (respGPlus F) (respCoeffPlus F)
    (fun a => exists_elliptic_representative_respCell_respCoeffPlus hj hm t a)
    (fun a j w => coarseBlockMatrix_respCoeffPlus_at hq j w F a) u hu

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Integrability of the squared weak-quantity seminorm

The weak-quantity estimate `e.response.weak.estimate` bounds the squared scale-average Besov
seminorm of the `M_0 ^ (1/2)`-transported recentred optimizer state by a sample-dependent
envelope.  This file records the elementary measure-theoretic consequence used to discharge the
integrability premise of the cutoff rows: a measurable nonnegative function dominated almost
everywhere by an integrable function is integrable.

The generic domination statement is specialised to the all-scale envelope
`respAllScaleMax` of `HCPoly.Entry.Response.Core.ResponseBlockObjects`, whose
`Q`-th moment is controlled by `e.response.weak.estimate`; because the law is a probability
measure, the additive constant `1` in the envelope is integrable and the envelope itself is
integrable whenever its response factor is.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Integrability of the squared weak-quantity seminorm by domination.**  Let `P` be a
probability law on the coefficient space and let

`f a = besovSeminorm t (fun n z => M_0 ^ (1/2) (cellAverage U_{t-n,z} (optimizerField (c a) (u a))
- Y)) ^ 2`

be the squared scale-average seminorm of the `M_0 ^ (1/2)`-transported recentred optimizer state,
as in `e.response.weak.estimate`.  If `f` is `P`-a.e.-strongly measurable and is dominated
`P`-a.e. by an integrable function `g`, then `f` is `P`-integrable: the finite-integral half of
`Integrable` follows from `HasFiniteIntegral.mono'` after replacing `‖f a‖` by `f a` through the
nonnegativity of the square, and the measurability half is the hypothesis. -/
theorem integrable_besovSeminorm_sq_of_domination {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (jStar : ℕ) (F : BlockMat d) (t : ℤ) (Y : BlockVec d)
    (c : CoeffSpace d → CoeffField d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (g : CoeffSpace d → ℝ) (hg : Integrable g P)
    (hmeas : AEStronglyMeasurable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2) P)
    (hdom : ∀ᵐ a ∂P, besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2 ≤ g a) :
    Integrable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2) P := by
  refine Integrable.mono' hg hmeas ?_
  filter_upwards [hdom] with a ha
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact ha

/-- **Integrability of the squared weak-quantity seminorm from the recentred all-scale envelope.**
The generic domination statement with `g a = C * ((1 + respAllScaleMax P γ jStar F t a) *
respJ (respGrid jStar F) t p q' (respCoeffMinus F a) + 1)`.  The response factor
`(1 + respAllScaleMax) * respJ` is `P`-integrable by `hint` and the constant `1` is `P`-integrable
because `P` is a probability measure, so `C` times their sum is integrable and the squared
seminorm inherits integrability from the domination hypothesis. -/
theorem integrable_besovSeminorm_sq_of_ae_envelope {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (p q' : Vec d) (Y : BlockVec d)
    (c : CoeffSpace d → CoeffField d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (C : ℝ) (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2) P)
    (hint : Integrable (fun a => (1 + respAllScaleMax P γ jStar F t a) *
        respJ (respGrid jStar F) t p q' (respCoeffMinus F a)) P)
    (hdom : ∀ᵐ a ∂P, besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2 ≤
      C * ((1 + respAllScaleMax P γ jStar F t a) *
        respJ (respGrid jStar F) t p q' (respCoeffMinus F a) + 1)) :
    Integrable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2) P := by
  have _ := hC
  refine integrable_besovSeminorm_sq_of_domination P jStar F t Y c u
    (fun a => C * ((1 + respAllScaleMax P γ jStar F t a) *
      respJ (respGrid jStar F) t p q' (respCoeffMinus F a) + 1)) ?_ hmeas hdom
  exact (hint.add (integrable_const (1 : ℝ))).const_mul C

/-- **Integrability of the squared weak-quantity seminorm from the adjoint all-scale envelope.**
The adjoint twin of `integrable_besovSeminorm_sq_of_ae_envelope`: the same domination argument
applies with the adjoint recentred response `respJ (respGrid jStar F) t p q' (respCoeffPlus F a)`
in place of the recentred response. -/
theorem integrable_besovSeminorm_sq_of_ae_envelope_plus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (p q' : Vec d) (Y : BlockVec d)
    (c : CoeffSpace d → CoeffField d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (C : ℝ) (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2) P)
    (hint : Integrable (fun a => (1 + respAllScaleMax P γ jStar F t a) *
        respJ (respGrid jStar F) t p q' (respCoeffPlus F a)) P)
    (hdom : ∀ᵐ a ∂P, besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2 ≤
      C * ((1 + respAllScaleMax P γ jStar F t a) *
        respJ (respGrid jStar F) t p q' (respCoeffPlus F a) + 1)) :
    Integrable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2) P := by
  have _ := hC
  refine integrable_besovSeminorm_sq_of_domination P jStar F t Y c u
    (fun a => C * ((1 + respAllScaleMax P γ jStar F t a) *
      respJ (respGrid jStar F) t p q' (respCoeffPlus F a) + 1)) ?_ hmeas hdom
  exact (hint.add (integrable_const (1 : ℝ))).const_mul C

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Integrability of the weak-quantity integrand from the standing law premises

The weak quantity `W^\pm` of `e.response.weak.estimate` is the sample expectation of the square of
the scale-average seminorm `besovSeminorm` of the recentred, canonically-metric-scaled cell averages
of the doubled optimizer state `X_t^\pm`, for an arbitrary family of response maximizers.  This file
assembles the three landed ingredients into the integrability of that integrand, starting from the
standing law premises `IsStationaryLaw` and the coarse-ellipticity dagger.

The ingredients are:

* almost-everywhere strong measurability of the integrand, from the measurable canonical selection
  and the countable sum defining the seminorm;
* almost-sure domination of the integrand by a constant multiple of the all-scale envelope
  `(1 + respAllScaleMax) * respJ + 1`, from the pathwise scale-average seminorm bound AK.HC (2.130)
  and the energy--response identity of `e.response.weak.estimate`;
* integrability of that envelope, from the `Q`-th envelope moment with `2 ≤ Q` supplied by
  `e.response.weak.estimate` and Hölder's inequality, together with the elementary domination
  argument closing the square.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Integrability of the squared weak-quantity seminorm from the standing law premises, recentred
sign.**  Let `P` be a stationary probability law with coarse-ellipticity dagger, let `F` be a block
with positive-definite canonical metric, and let `u` be an arbitrary family of response maximizers
for the recentred coefficient `a_-`.  Assume the all-scale envelope `ℳ = respAllScaleMax` is
measurable with `Q`-th moment `P`-integrable and `J^- ^ 2` is `P`-integrable.  Then the squared
scale-average seminorm of the `M_0 ^ (1/2)`-transported recentred optimizer state is `P`-integrable.
This is the integrability of the integrand of the weak quantity `W^-` of
`e.response.weak.estimate`; the a.e. domination is supplied by AK.HC (2.130) and the closing
domination argument by Hölder. -/
theorem integrable_besovSeminorm_sq_of_raw_minus {d : ℕ} [NeZero d] (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (p q' : Vec d) (Y : BlockVec d)
    (hMint : Integrable (fun a => respAllScaleMax P γ jStar F t a ^ bigQ d γ) P)
    (hMmeas : AEStronglyMeasurable (respAllScaleMax P γ jStar F t) P)
    (hJsq : Integrable (fun a =>
      respJ (respGrid jStar F) t p q' (respCoeffMinus F a) ^ 2) P)
    (u : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (respCoeffMinus F a) (u a)) :
    Integrable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (respCoeffMinus F a) (u a)) - Y)) ^ 2) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hj hm
  have hJmeas : AEStronglyMeasurable
      (fun a => respJ (respGrid jStar F) t p q' (respCoeffMinus F a)) P :=
    (measurable_respJ_respCoeffMinus (respGrid jStar F) hq t F p q').aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (respCoeffMinus F a) (u a)) - Y)) ^ 2) P :=
    aestronglyMeasurable_besovSeminorm_sq_of_maximizer P jStar F t hj hm
      (respCoeffMinus F) (Or.inl rfl) p q' Y u hu
  have hint : Integrable (fun a => (1 + respAllScaleMax P γ jStar F t a) *
      respJ (respGrid jStar F) t p q' (respCoeffMinus F a)) P :=
    integrable_one_add_respAllScaleMax_mul_respJ hd γ hγ P jStar F t p q'
      hMmeas hMint (bigQ_two_le d γ hγ) hJsq hJmeas
  obtain ⟨C, hC, hdom⟩ := ae_besovSeminorm_sq_le_envelope_minus hd γ hγ P E Ψ Kg Src
    hstat hdag jStar hj F hm t p q' Y u hu
  exact integrable_besovSeminorm_sq_of_ae_envelope P γ jStar F t p q' Y
    (respCoeffMinus F) u C hC hmeas hint hdom

/-- **Integrability of the squared weak-quantity seminorm from the standing law premises, adjoint
sign.**  The adjoint twin of `integrable_besovSeminorm_sq_of_raw_minus`: with the adjoint recentred
coefficient `a_+` and an arbitrary family `u` of response maximizers for it, the same hypotheses on
the all-scale envelope and on `J^+ ^ 2` give `P`-integrability of the squared scale-average seminorm
of the `M_0 ^ (1/2)`-transported adjoint optimizer state.  This is the integrability of the
integrand of the weak quantity `W^+` of `e.response.weak.estimate`. -/
theorem integrable_besovSeminorm_sq_of_raw_plus {d : ℕ} [NeZero d] (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (p q' : Vec d) (Y : BlockVec d)
    (hMint : Integrable (fun a => respAllScaleMax P γ jStar F t a ^ bigQ d γ) P)
    (hMmeas : AEStronglyMeasurable (respAllScaleMax P γ jStar F t) P)
    (hJsq : Integrable (fun a =>
      respJ (respGrid jStar F) t p q' (respCoeffPlus F a) ^ 2) P)
    (u : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (respCoeffPlus F a) (u a)) :
    Integrable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (respCoeffPlus F a) (u a)) - Y)) ^ 2) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hj hm
  have hJmeas : AEStronglyMeasurable
      (fun a => respJ (respGrid jStar F) t p q' (respCoeffPlus F a)) P :=
    (measurable_respJ_respCoeffPlus (respGrid jStar F) hq t F p q').aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (respCoeffPlus F a) (u a)) - Y)) ^ 2) P :=
    aestronglyMeasurable_besovSeminorm_sq_of_maximizer P jStar F t hj hm
      (respCoeffPlus F) (Or.inr rfl) p q' Y u hu
  have hint : Integrable (fun a => (1 + respAllScaleMax P γ jStar F t a) *
      respJ (respGrid jStar F) t p q' (respCoeffPlus F a)) P :=
    integrable_one_add_respAllScaleMax_mul_respJPlus hd γ hγ P jStar F t p q'
      hMmeas hMint (bigQ_two_le d γ hγ) hJsq hJmeas
  obtain ⟨C, hC, hdom⟩ := ae_besovSeminorm_sq_le_envelope_plus hd γ hγ P E Ψ Kg Src
    hstat hdag jStar hj F hm t p q' Y u hu
  exact integrable_besovSeminorm_sq_of_ae_envelope_plus P γ jStar F t p q' Y
    (respCoeffPlus F) u C hC hmeas hint hdom

end

end HCPolySupport.HighContrast.Multiscale
end
