/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLowerLtTwo

/-!
# SuperposedFluxLowerInfinity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The sharp lower endpoint branch

This file sums the sharp pointwise remainder against the exact endpoint
weight and supplies the conditional infinity-exponent payload.  Its scalar
output-constant inequalities remain caller-supplied obligations; these
Provider helpers assert no source-node status.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- Fixed prefactor in the infinity-exponent final Orlicz budget. -/
def superposedFluxInfinityBudgetConst (d : ℕ) : ℝ :=
  superposedFluxTriangleConst * superposedFluxDepthAmpConst d *
    superposedFluxLowerPoleConst

theorem superposedFluxInfinityBudgetConst_pos (hd : 2 ≤ d) :
    0 < superposedFluxInfinityBudgetConst d := by
  unfold superposedFluxInfinityBudgetConst
  have htri : 0 < superposedFluxTriangleConst := by
    unfold superposedFluxTriangleConst
    positivity
  exact mul_pos (mul_pos htri (superposedFluxDepthAmpConst_pos hd))
    superposedFluxLowerPoleConst_pos

/-- A payload-valued helper for the conditional infinity-exponent A. -/
theorem superposedFlux_lower_branchPayload_infinity [NeZero d]
    (hd : 2 ≤ d) {Clow : ℝ} (hClow : 0 < Clow)
    (haux : profileAuxiliaryConst d ≤ Clow)
    (hdet : 2 * superposedFluxSharpDetConst d ≤ Clow)
    (hbudgetChoice : superposedFluxInfinityBudgetConst d + 6 ≤
      superposedFluxBfaRate d * Clow) :
    ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
      Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
      ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
        max (Real.exp (Clow / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
          ∀ s : ℝ,
            ∀ hsWindow : s ∈ Set.Icc
              (M.gamma / 2 + Real.exp
                (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1,
              ∃ Ydet Y : CutoffSample d → ℝ,
                (∀ omega, ∀ L : ℤ, m - 1 ≤ L →
                    Observable.cutoffLowerEllipticityInv M m L s
                        (by
                          exact (add_pos
                            (div_pos M.shellPrefix.gamma_pos (by norm_num))
                            (Real.exp_pos _)).trans_le hsWindow.1)
                        CoarseEllipticityExponent.infinity omega *
                      (Annealed.sigmaBar M (m - 1) : ℝ) ≤
                    Ydet omega + Y omega) ∧
                (∀ omega, Ydet omega ≤ Clow) ∧
                Measurable Y ∧
                IsBigOWith (cutoffSampleLaw M).toMeasure
                  (gammaSigma ((1 - sigma) / 2)) Y
                  (Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
  intro M m E hstate sigma hsigma hE1 hE2 s hsWindow
  have hs : 0 < s := by
    linarith [M.shellPrefix.gamma_pos, hsWindow.1, Real.exp_pos
      (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))]
  have hgap : 0 < 2 * s - M.gamma := by
    linarith [hsWindow.1, Real.exp_pos
      (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))]
  have hExpClow : Real.exp (Clow / sigma) ≤ (E : ℝ) :=
    (le_max_left _ _).trans hE1
  have hExpAux : Real.exp (profileAuxiliaryConst d / sigma) ≤
      Real.exp (Clow / sigma) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right haux hsigma.1.le)
  have hmaxAux : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    max_le (hExpAux.trans hExpClow) ((le_max_right _ _).trans hE1)
  obtain ⟨U, hUnonneg, hUmeas, hUOraw, hdepth, hUcap⟩ :=
    exists_superposedFluxLowerPointwiseRepresentative hd M m E hstate
      hsigma.1 hsigma.2 hmaxAux hE2
  let a : ℕ → ℝ := fun n => superposedFluxDepthAmpProfile M E n
  let w : ℕ → ℝ := fun n => endpointWeight (2 * s) n
  let H : ℝ := superposedFluxCutoffCap M m
  let Cdet : ℝ := 2 * superposedFluxSharpDetConst d
  have ha : ∀ n, 0 < a n := fun n => superposedFluxDepthAmpProfile_pos hd M E n
  have hw : ∀ n, 0 < w n := fun n => endpointWeight_pos _ n
  have hHpos : 0 < H := superposedFluxCutoffCap_pos hd M m
  have hwsum : Summable w := by
    have hgrid : Summable fun n : ℕ => gridWeight (2 * s) n * (1 : ℝ) := by
      simpa using (gridWeight_summable (by linarith : 0 < 2 * s)).mul_right (1 : ℝ)
    simpa [w] using summable_endpointWeight_mul hgrid
  have hUsum : ∀ omega, Summable fun n : ℕ => w n * U n omega := by
    intro omega
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hw n).le (hUnonneg n omega))
      (fun n => mul_le_mul_of_nonneg_left (hUcap n omega) (hw n).le)
      (hwsum.mul_right H)
  have hasum : Summable fun n : ℕ => w n * a n := by
    simpa [w, a] using summable_endpointWeight_mul_depthAmp M (E : ℝ) hgap
  have hUO : ∀ n, IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma ((1 - sigma) / 2)) (U n) (a n) := by
    intro n
    exact (hUOraw n).mono_scale
      (superposedFluxSharpDepthAmp_le_profile hd M m E hsigma.1 hsigma.2
        hmaxAux hE2 n)
  let rare : ℝ := Real.exp
    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))
  let X : ℝ := ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹
  let A : ℝ := Real.exp (-(superposedFluxBfaRate d * X))
  let K : ℝ := superposedFluxInfinityBudgetConst d
  have hrare : 0 < rare := Real.exp_pos _
  have hrareOne : rare ≤ 1 := by
    simpa [rare, X, mul_assoc] using
      exp_neg_frozen_le_one (Clow := Clow) (E := (E : ℝ))
        (gamma := M.gamma) hClow M.shellPrefix.gamma_pos
  have hgammaZ : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) :=
    gamma_le_zpow_neg_five_of_frozenGate E.property M.shellPrefix.gamma_pos hE2
  have hXlarge : Clow ≤ X := by
    simpa [X] using outputConst_le_invSq_mul_gammaInv_of_gate M hClow.le
      hsigma.1 hsigma.2 E.property hExpClow hgammaZ
  have hgate : K * A ≤ rare ^ (6 : ℕ) := by
    simpa [K, A, rare, X, mul_assoc] using
      prefactor_mul_exp_le_frozenRare_pow
        (superposedFluxInfinityBudgetConst_pos hd).le hClow hXlarge hbudgetChoice
  have hseries : (∑' n : ℕ, w n * a n) ≤
      superposedFluxDepthAmpConst d * superposedFluxLowerPoleConst *
        A * rare⁻¹ ^ (5 : ℕ) := by
    simpa [w, a, A, rare, X, mul_assoc] using
      tsum_endpointWeight_mul_depthAmp_le hd M (E : ℝ) hsWindow.2
        hrare hrareOne hsWindow.1
  have htri : gammaTriangleConst ((1 - sigma) / 2) ≤
      superposedFluxTriangleConst :=
    gammaTriangleConst_le_superposedFluxTriangleConst (by linarith [hsigma.2])
  have hbudget : gammaTriangleConst ((1 - sigma) / 2) *
      (∑' n : ℕ, w n * a n) ≤ rare := by
    have hsum0 : 0 ≤ ∑' n : ℕ, w n * a n :=
      tsum_nonneg fun n => mul_nonneg (hw n).le (ha n).le
    have hright0 : 0 ≤ superposedFluxDepthAmpConst d *
        superposedFluxLowerPoleConst * A * rare⁻¹ ^ (5 : ℕ) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (superposedFluxDepthAmpConst_pos hd).le
            superposedFluxLowerPoleConst_pos.le)
          (by dsimp [A]; exact (Real.exp_pos _).le))
        (by positivity)
    have hfirst : gammaTriangleConst ((1 - sigma) / 2) *
        (∑' n : ℕ, w n * a n) ≤ K * A * rare⁻¹ ^ (5 : ℕ) := by
      calc
        _ ≤ gammaTriangleConst ((1 - sigma) / 2) *
            (superposedFluxDepthAmpConst d * superposedFluxLowerPoleConst *
              A * rare⁻¹ ^ (5 : ℕ)) :=
          mul_le_mul_of_nonneg_left hseries gammaTriangleConst_pos.le
        _ ≤ superposedFluxTriangleConst *
            (superposedFluxDepthAmpConst d * superposedFluxLowerPoleConst *
              A * rare⁻¹ ^ (5 : ℕ)) :=
          mul_le_mul_of_nonneg_right htri hright0
        _ = K * A * rare⁻¹ ^ (5 : ℕ) := by
          unfold K superposedFluxInfinityBudgetConst
          ring
    exact hfirst.trans (mul_le_of_pow_inv_gate
      (mul_nonneg (superposedFluxInfinityBudgetConst_pos hd).le
        (by dsimp [A]; exact (Real.exp_pos _).le))
      hrare le_rfl hgate)
  have hdom : ∀ omega, ∀ L : ℤ, m - 1 ≤ L →
      Observable.cutoffLowerEllipticityInv M m L s hs
          CoarseEllipticityExponent.infinity omega *
        (Annealed.sigmaBar M (m - 1) : ℝ) ≤
      Cdet + ∑' n : ℕ, w n * U n omega := by
    refine cutoffLowerEllipticityInv_infinity_mul_forall_le M m hs rfl
      (Annealed.sigmaBar M (m - 1)).2.le ?_
    intro n omega L hL
    have hbase := hdepth omega L hL n
    have hraw0 : 0 ≤ (3 : ℝ) ^ (-2 * s * (n : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hcollar := rpow_collar_eq_endpointWeight s M.gamma n
    have hraw : (3 : ℝ) ^ (-2 * s * (n : ℝ)) = w n := by
      dsimp [w]
      rw [endpointWeight_eq_rpow]
      congr 1
      ring
    have hCdet0 : 0 ≤ Cdet := by
      dsimp [Cdet]
      exact mul_nonneg (by norm_num) (superposedFluxSharpDetConst_pos hd).le
    have hdetWeight : endpointWeight (2 * s - M.gamma) n * Cdet ≤ Cdet :=
      by
        simpa using (mul_le_mul_of_nonneg_right (endpointWeight_le_one hgap n)
          hCdet0)
    have hterm : w n * U n omega ≤ ∑' j : ℕ, w j * U j omega :=
      endpointTerm_le_tsum (fun j => (hw j).le) hUnonneg hUsum n omega
    calc
      (Annealed.sigmaBar M (m - 1) : ℝ) *
          ((3 : ℝ) ^ (-2 * s * (n : ℝ)) *
            Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
              (originCube d m) (m - (n : ℤ))
              (coefficientCutoff M.nu L omega)) =
        (3 : ℝ) ^ (-2 * s * (n : ℝ)) *
          ((Annealed.sigmaBar M (m - 1) : ℝ) *
            Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
              (originCube d m) (m - (n : ℤ))
              (coefficientCutoff M.nu L omega)) := by ring
      _ ≤ (3 : ℝ) ^ (-2 * s * (n : ℝ)) *
          (finiteQGeometricProfile Cdet M.gamma n + U n omega) :=
        mul_le_mul_of_nonneg_left (by simpa [Cdet] using hbase) hraw0
      _ = endpointWeight (2 * s - M.gamma) n * Cdet + w n * U n omega := by
        unfold finiteQGeometricProfile
        rw [← hcollar, hraw]
        ring
      _ ≤ Cdet + ∑' j : ℕ, w j * U j omega := add_le_add hdetWeight hterm
  obtain ⟨Ydet, Y, hYdom, hYdet, hYmeas, hYO⟩ :=
    twoTermFamilySplit_of_endpointMajorant
      (by linarith [hsigma.2] : 0 < (1 - sigma) / 2) hw hUnonneg hUmeas
      ha hasum hUO hbudget hdom
  exact ⟨Ydet, Y, hYdom, fun omega => (hYdet omega).trans hdet, hYmeas,
    by simpa [rare] using hYO⟩

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
