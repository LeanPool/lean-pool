/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootPayloadDataB
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenLambdaSlots
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccFinalDisplay
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourCollapseWeights

/-!
# RootPayloadDataM

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-- **The `dataM` constant** `C_dM = √(4·F·(64/7)·C_Bc)·K_d(d)`. -/
def rootClauseBDataMConst (d : ℕ) (CBc : ℝ) : ℝ :=
  Real.sqrt (4 * stepSevenCaccForcingFactor * (64 / 7 * CBc)) * rootClauseBDataBConst d

theorem rootClauseBDataMConst_nonneg (d : ℕ) (CBc : ℝ) :
    0 ≤ rootClauseBDataMConst d CBc :=
  mul_nonneg (Real.sqrt_nonneg _) (rootClauseBDataBConst_nonneg d)

/-- `√(3^e) = 3^{e/2}`. -/
theorem sqrt_rpow_three (e : ℝ) :
    Real.sqrt (Real.rpow (3 : ℝ) e) = Real.rpow (3 : ℝ) (e / 2) := by
  have h1 : Real.sqrt (Real.rpow (3 : ℝ) e) =
      Real.rpow (Real.rpow (3 : ℝ) e) (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have h2 : Real.rpow (3 : ℝ) (e * (1 / 2 : ℝ)) =
      Real.rpow (Real.rpow (3 : ℝ) e) (1 / 2 : ℝ) :=
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) e (1 / 2)
  have h3 : e * (1 / 2 : ℝ) = e / 2 := by ring
  rw [h1, ← h2, h3]

/-- A Besov bound and forcing regularity supply the common Caccioppoli data estimate. -/
theorem rootClauseB_dataM_of_besov_bound [NeZero d] {M : ABKModel d} {m0 : ℤ}
    {Ecap : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap)
    (hgamma : M.gamma < 1 / 2) {m n' : ℤ} {a : CoeffFamily d}
    {f : Vec d → Vec d} {Khol CBc : ℝ} (hmm0 : m ≤ m0) (hn' : n' ≤ m - 1)
    (hKhol : 0 ≤ Khol) (hCBc : 0 ≤ CBc)
    (hcaps : StepSevenLambdaCaps (originCube d (n' + 1)) a
      ((Annealed.sigmaBar M (n' + 1) : ℝ)) CBc)
    (hBes : scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n')
      stepOneS f ≤ rootClauseBDataBConst d * (Real.rpow (3 : ℝ) ((n' : ℝ) / 2) * Khol))
    (hforce : ForceBesovRegularity (originCube d n') stepOneS f) :
    stepSevenCaccDataM (originCube d n') a f ≤
      rootClauseBDataMConst d CBc *
        (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ * edFinalDataOscG Khol m) := by
  have hFnn : (0 : ℝ) ≤ stepSevenCaccForcingFactor := stepSevenCaccForcingFactor_nonneg
  have hKnn : (0 : ℝ) ≤ 4 * stepSevenCaccForcingFactor * (64 / 7 * CBc) := by
    have h := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hFnn)
      (by linarith only [hCBc] : (0 : ℝ) ≤ 64 / 7 * CBc)
    exact h
  -- the `λ` slot, from the payload's own `capsCacc`
  have hidx : (n' + 1 - 1 : ℤ) = n' := by ring
  have hlam : (Ch02.lambdaS (originCube d n') stepSevenCaccT a)⁻¹ ≤
      (64 / 7 * CBc) * ((Annealed.sigmaBar M (n' + 1) : ℝ))⁻¹ := by
    have h := stepSevenLambdaS_inv_le_of_caps (k := n' + 1) a hcaps
    rwa [hidx] at h
  -- the `σ` reconciliation
  set E : ℝ := M.gamma * ((m : ℝ) - ((n' + 1 : ℤ) : ℝ)) with hEdef
  have hsig : ((Annealed.sigmaBar M (n' + 1) : ℝ))⁻¹ ≤
      4 * Real.rpow (3 : ℝ) E * ((Annealed.sigmaBar M m : ℝ))⁻¹ :=
    inv_sigmaBar_le_mul_inv_sigmaBar_of_inductionState hS (by omega) hmm0
  -- the combined bound inside the square root
  have hlamF : stepSevenCaccForcingFactor *
        (Ch02.lambdaS (originCube d n') stepSevenCaccT a)⁻¹ ≤
      (4 * stepSevenCaccForcingFactor * (64 / 7 * CBc)) *
        (Real.rpow (3 : ℝ) E * ((Annealed.sigmaBar M m : ℝ))⁻¹) := by
    have h1 : (Ch02.lambdaS (originCube d n') stepSevenCaccT a)⁻¹ ≤
        (64 / 7 * CBc) *
          (4 * Real.rpow (3 : ℝ) E * ((Annealed.sigmaBar M m : ℝ))⁻¹) :=
      le_trans hlam
        (mul_le_mul_of_nonneg_left hsig (by linarith only [hCBc]))
    have h2 := mul_le_mul_of_nonneg_left h1 hFnn
    exact le_trans h2 (le_of_eq (by ring))
  have hA : Real.sqrt (stepSevenCaccForcingFactor *
        (Ch02.lambdaS (originCube d n') stepSevenCaccT a)⁻¹) ≤
      Real.sqrt (4 * stepSevenCaccForcingFactor * (64 / 7 * CBc)) *
        (Real.rpow (3 : ℝ) (E / 2) *
          Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹) := by
    have hRnn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) E := Real.rpow_nonneg (by norm_num) E
    refine le_trans (Real.sqrt_le_sqrt hlamF) (le_of_eq ?_)
    rw [Real.sqrt_mul hKnn, Real.sqrt_mul hRnn, sqrt_rpow_three]
  have hBesnn : (0 : ℝ) ≤ scaleNormalizedPositiveBesovVectorSeminormTwo
      (originCube d n') stepOneS f :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove _ stepOneS _
      hforce.partialSeminorms_bddAbove
  have hAnn : (0 : ℝ) ≤ Real.sqrt (4 * stepSevenCaccForcingFactor * (64 / 7 * CBc)) *
      (Real.rpow (3 : ℝ) (E / 2) *
        Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹) :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _))
  -- the exponent budget
  have hcast : ((n' + 1 : ℤ) : ℝ) = (n' : ℝ) + 1 := by push_cast; ring
  have hX : (0 : ℝ) ≤ (m : ℝ) - ((n' : ℝ) + 1) := by
    have h : ((n' + 1 : ℤ) : ℝ) ≤ ((m : ℤ) : ℝ) := by exact_mod_cast (by omega : n' + 1 ≤ m)
    rw [hcast] at h
    linarith only [h]
  have hEle : E ≤ (m : ℝ) - (n' : ℝ) := by
    rw [hEdef, hcast]
    have hprod : M.gamma * ((m : ℝ) - ((n' : ℝ) + 1)) ≤
        (1 / 2 : ℝ) * ((m : ℝ) - ((n' : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (le_of_lt hgamma) hX
    linarith only [hprod, hX]
  have hexp : Real.rpow (3 : ℝ) (E / 2) * Real.rpow (3 : ℝ) ((n' : ℝ) / 2) ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) := by
    have hadd : Real.rpow (3 : ℝ) (E / 2 + (n' : ℝ) / 2) =
        Real.rpow (3 : ℝ) (E / 2) * Real.rpow (3 : ℝ) ((n' : ℝ) / 2) :=
      Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _
    rw [← hadd]
    have hmono : Real.rpow (3 : ℝ) (E / 2 + (n' : ℝ) / 2) ≤
        Real.rpow (3 : ℝ) ((m : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hEle])
    exact hmono
  -- assemble
  have hcoef : (0 : ℝ) ≤ Real.sqrt (4 * stepSevenCaccForcingFactor * (64 / 7 * CBc)) *
      rootClauseBDataBConst d * Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (rootClauseBDataBConst_nonneg d))
      (Real.sqrt_nonneg _)
  have hstep : (Real.rpow (3 : ℝ) (E / 2) * Real.rpow (3 : ℝ) ((n' : ℝ) / 2)) * Khol ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol :=
    mul_le_mul_of_nonneg_right hexp hKhol
  rw [stepSevenCaccDataM, rootClauseBDataMConst, edFinalDataOscG]
  refine le_trans (mul_le_mul hA hBes hBesnn hAnn) ?_
  calc Real.sqrt (4 * stepSevenCaccForcingFactor * (64 / 7 * CBc)) *
        (Real.rpow (3 : ℝ) (E / 2) * Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹) *
        (rootClauseBDataBConst d * (Real.rpow (3 : ℝ) ((n' : ℝ) / 2) * Khol))
      = Real.sqrt (4 * stepSevenCaccForcingFactor * (64 / 7 * CBc)) *
          rootClauseBDataBConst d * Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
          ((Real.rpow (3 : ℝ) (E / 2) * Real.rpow (3 : ℝ) ((n' : ℝ) / 2)) * Khol) := by
        ring
    _ ≤ Real.sqrt (4 * stepSevenCaccForcingFactor * (64 / 7 * CBc)) *
          rootClauseBDataBConst d * Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
          (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol) :=
        mul_le_mul_of_nonneg_left hstep hcoef
    _ = Real.sqrt (4 * stepSevenCaccForcingFactor * (64 / 7 * CBc)) *
          rootClauseBDataBConst d *
          (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
            (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Khol)) := by ring


/-- **The clause-(B) `dataM` leg, produced**: the Caccioppoli's own data leg
against the printed `K_g`-leg. -/
theorem rootClauseB_dataM [NeZero d] {M : ABKModel d} {m0 : ℤ}
    {Ecap : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap)
    (hgamma : M.gamma < 1 / 2) {m n' : ℤ} {z : Vec d} {a : CoeffFamily d}
    {gsrc : Vec d → Vec d} {Khol CBc : ℝ} (hmm0 : m ≤ m0) (hn' : n' ≤ m - 1)
    (hz : z ∈ openCubeSet (originCube d (m - 1))) (hKhol : 0 ≤ Khol)
    (hCBc : 0 ≤ CBc)
    (hgHol : Support.HolderSeminormBoundOn (openCubeSet (originCube d m))
      (1 / 2) Khol gsrc)
    (hgL2 : MemLp gsrc 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
    (hgW : MemLp (Gagliardo.gagliardoKernel stepOneS 2 gsrc) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))))
    (hcaps : StepSevenLambdaCaps (originCube d (n' + 1)) a
      ((Annealed.sigmaBar M (n' + 1) : ℝ)) CBc) :
    stepSevenCaccDataM (originCube d n') a (fun y => -gsrc (y + z)) ≤
      rootClauseBDataMConst d CBc *
        (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ * edFinalDataOscG Khol m) := by
  exact rootClauseB_dataM_of_besov_bound hS hgamma hmm0 hn' hKhol hCBc hcaps
    (besovTranslated_neg_le_holder (m := m) (j := n') hz hn' hKhol hgHol hgL2 hgW)
    (forceBesovRegularity_stepSevenCacc_interior hz hn' hgL2 hgW)

end

end Algsuperdiff.Section4.Provider.Regularity
