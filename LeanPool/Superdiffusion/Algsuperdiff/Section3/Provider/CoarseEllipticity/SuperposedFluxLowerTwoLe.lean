/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLowerSeries

/-!
# SuperposedFluxLowerTwoLe

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The sharp lower branch for finite exponents at least two

This file feeds the pointwise sharp representative into the finite-`q`
pre-split theorem.  Scale summability, amplitude absorption, and parameter
gates are local proof steps.  The output-constant inequalities on the main
theorem remain caller-supplied conditional A obligations; this Provider module
asserts no source-node status.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- Fixed multiplicative budget prefactor for the `2 ≤ q < ∞` random
lane. -/
def superposedFluxTwoLeBudgetConst (d : ℕ) : ℝ :=
  2 * superposedFluxTriangleConst * superposedFluxDepthAmpConst d *
    superposedFluxLowerPoleConst

theorem superposedFluxTwoLeBudgetConst_pos (hd : 2 ≤ d) :
    0 < superposedFluxTwoLeBudgetConst d := by
  unfold superposedFluxTwoLeBudgetConst
  have htri : 0 < superposedFluxTriangleConst := by
    unfold superposedFluxTriangleConst
    positivity
  exact mul_pos
    (mul_pos (mul_pos (by norm_num) htri) (superposedFluxDepthAmpConst_pos hd))
    superposedFluxLowerPoleConst_pos

/-- The model-facing finite-`q` producer consumed by
`coarse_ellipticity_lower_branchPayload_two_le_of_finiteQPresplit`. -/
theorem exists_superposedFluxFiniteQPresplit_two_le [NeZero d]
    (hd : 2 ≤ d) {Clow : ℝ} (hClow : 0 < Clow)
    (haux : profileAuxiliaryConst d ≤ Clow)
    (hbudgetChoice : superposedFluxTwoLeBudgetConst d + 6 ≤
      superposedFluxBfaRate d * Clow)
    (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E})
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc 0 (1 / 2))
    (hE1 : max (Real.exp (Clow / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hE2 : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (r : {r : ℝ // 1 ≤ r}) (hr : 2 ≤ (r : ℝ))
    (s : ℝ)
    (hsWindow : s ∈ Set.Icc
      (M.gamma / 2 + Real.exp
        (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1) :
    ∃ (U : ℕ → CutoffSample d → ℝ) (a : ℕ → ℝ),
      (∀ n omega, 0 ≤ U n omega) ∧
      (∀ n, Measurable (U n)) ∧
      (∀ omega, Summable fun n : ℕ =>
        Book.Ch02.geometricWeight s (r : ℝ) n *
          U n omega ^ ((r : ℝ) / 2)) ∧
      (∀ omega, Summable fun n : ℕ =>
        Book.Ch02.geometricWeight s (r : ℝ) n ^ (2 / (r : ℝ)) *
          U n omega) ∧
      (∀ n, 0 < a n) ∧
      (Summable fun n : ℕ =>
        Book.Ch02.geometricWeight s (r : ℝ) n ^ (2 / (r : ℝ)) * a n) ∧
      (∀ n, IsBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma ((1 - sigma) / 2)) (U n) (a n)) ∧
      (2 * gammaTriangleConst ((1 - sigma) / 2) *
          (∑' n : ℕ,
            Book.Ch02.geometricWeight s (r : ℝ) n ^ (2 / (r : ℝ)) *
              a n) ≤
        Real.exp (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) ∧
      (∀ omega, ∀ L : ℤ, m - 1 ≤ L → ∀ n : ℕ,
        (Annealed.sigmaBar M (m - 1) : ℝ) *
            Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
              (originCube d m) (m - (n : ℤ))
              (coefficientCutoff M.nu L omega) ≤
          finiteQGeometricProfile (2 * superposedFluxSharpDetConst d)
            M.gamma n + U n omega) := by
  have hr0 : 0 < (r : ℝ) := by linarith [r.property]
  have hexpWindow : 0 < Real.exp
      (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) := Real.exp_pos _
  have hs : 0 < s := by
    linarith [M.shellPrefix.gamma_pos, hsWindow.1]
  have hgap : 0 < 2 * s - M.gamma := by
    linarith [hsWindow.1]
  have hExpClow : Real.exp (Clow / sigma) ≤ (E : ℝ) :=
    (le_max_left _ _).trans hE1
  have hExpAux : Real.exp (profileAuxiliaryConst d / sigma) ≤
      Real.exp (Clow / sigma) := by
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right haux hsigma.1.le)
  have hmaxAux : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    max_le (hExpAux.trans hExpClow) ((le_max_right _ _).trans hE1)
  obtain ⟨U, hUnonneg, hUmeas, hUOraw, hdepth, hUcap⟩ :=
    exists_superposedFluxLowerPointwiseRepresentative hd M m E hstate
      hsigma.1 hsigma.2 hmaxAux hE2
  let a : ℕ → ℝ := fun n => superposedFluxDepthAmpProfile M E n
  let H : ℝ := superposedFluxCutoffCap M m
  have hHpos : 0 < H := superposedFluxCutoffCap_pos hd M m
  have hUqsum : ∀ omega, Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n *
        U n omega ^ ((r : ℝ) / 2) := by
    intro omega
    refine HCPolySupport.summable_geometricWeight_mul_of_nonneg_of_le
      (C := H ^ ((r : ℝ) / 2)) (mul_pos hs hr0) ?_ ?_
    · intro n
      exact Real.rpow_nonneg (hUnonneg n omega) _
    · intro n
      exact Real.rpow_le_rpow (hUnonneg n omega) (hUcap n omega) (by positivity)
  have hUlinsum : ∀ omega, Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n ^ (2 / (r : ℝ)) *
        U n omega := by
    intro omega
    have hweight := summable_geometricWeight_rpow_two_div hs hr0
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Real.rpow_nonneg
        (HCPolySupport.geometricWeight_nonneg n (mul_pos hs hr0).le) _)
          (hUnonneg n omega))
      (fun n => mul_le_mul_of_nonneg_left (hUcap n omega)
        (Real.rpow_nonneg
          (HCPolySupport.geometricWeight_nonneg n (mul_pos hs hr0).le) _))
      (hweight.mul_right H)
  have ha : ∀ n, 0 < a n := fun n => by
    exact superposedFluxDepthAmpProfile_pos hd M E n
  have hasum : Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n ^ (2 / (r : ℝ)) * a n := by
    simpa [a] using summable_rootedWeight_mul_depthAmp M (E : ℝ) hs hr0
      hgap
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
  let K : ℝ := superposedFluxTwoLeBudgetConst d
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
        (superposedFluxTwoLeBudgetConst_pos hd).le hClow hXlarge hbudgetChoice
  have hseries :
      (∑' n : ℕ,
        Book.Ch02.geometricWeight s (r : ℝ) n ^ (2 / (r : ℝ)) * a n) ≤
        superposedFluxDepthAmpConst d * superposedFluxLowerPoleConst *
          A * rare⁻¹ ^ (5 : ℕ) := by
    simpa [a, A, rare, X, mul_assoc] using
      tsum_rootedWeight_mul_depthAmp_le hd M (E : ℝ) hs hsWindow.2 hr0
        hrare hrareOne hsWindow.1
  have htri : gammaTriangleConst ((1 - sigma) / 2) ≤
      superposedFluxTriangleConst :=
    gammaTriangleConst_le_superposedFluxTriangleConst (by linarith [hsigma.2])
  have hbudget : 2 * gammaTriangleConst ((1 - sigma) / 2) *
      (∑' n : ℕ,
        Book.Ch02.geometricWeight s (r : ℝ) n ^ (2 / (r : ℝ)) * a n) ≤
      rare := by
    have hsum0 : 0 ≤ ∑' n : ℕ,
        Book.Ch02.geometricWeight s (r : ℝ) n ^ (2 / (r : ℝ)) * a n :=
      tsum_nonneg fun n => mul_nonneg (Real.rpow_nonneg
        (HCPolySupport.geometricWeight_nonneg n (mul_pos hs hr0).le) _) (ha n).le
    have hcoef0 : 0 ≤ 2 * gammaTriangleConst ((1 - sigma) / 2) :=
      mul_nonneg (by norm_num) gammaTriangleConst_pos.le
    have hright0 : 0 ≤ superposedFluxDepthAmpConst d *
        superposedFluxLowerPoleConst * A * rare⁻¹ ^ (5 : ℕ) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (superposedFluxDepthAmpConst_pos hd).le
            superposedFluxLowerPoleConst_pos.le)
          (by dsimp [A]; exact (Real.exp_pos _).le))
        (by positivity)
    have hfirst : 2 * gammaTriangleConst ((1 - sigma) / 2) *
        (∑' n : ℕ,
          Book.Ch02.geometricWeight s (r : ℝ) n ^ (2 / (r : ℝ)) * a n) ≤
        K * A * rare⁻¹ ^ (5 : ℕ) := by
      calc
        _ ≤ (2 * gammaTriangleConst ((1 - sigma) / 2)) *
            (superposedFluxDepthAmpConst d * superposedFluxLowerPoleConst *
              A * rare⁻¹ ^ (5 : ℕ)) :=
          mul_le_mul_of_nonneg_left hseries hcoef0
        _ ≤ (2 * superposedFluxTriangleConst) *
            (superposedFluxDepthAmpConst d * superposedFluxLowerPoleConst *
              A * rare⁻¹ ^ (5 : ℕ)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left htri (by norm_num)) hright0
        _ = K * A * rare⁻¹ ^ (5 : ℕ) := by
          unfold K superposedFluxTwoLeBudgetConst
          ring
    exact hfirst.trans (mul_le_of_pow_inv_gate
      (mul_nonneg (superposedFluxTwoLeBudgetConst_pos hd).le (Real.exp_pos _).le)
      hrare le_rfl hgate)
  exact ⟨U, a, hUnonneg, hUmeas, hUqsum, hUlinsum, ha, hasum, hUO,
    by simpa [rare] using hbudget, hdepth⟩

/-- A payload-valued helper for the conditional `2 ≤ q < ∞` A. -/
theorem superposedFlux_lower_branchPayload_two_le [NeZero d]
    (hd : 2 ≤ d) {Clow : ℝ} (hClow : 0 < Clow)
    (haux : profileAuxiliaryConst d ≤ Clow)
    (hdet : 8 * superposedFluxSharpDetConst d ≤ Clow)
    (hbudgetChoice : superposedFluxTwoLeBudgetConst d + 6 ≤
      superposedFluxBfaRate d * Clow) :
    ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
      Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
      ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
        max (Real.exp (Clow / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
        ∀ r : {r : ℝ // 1 ≤ r}, 2 ≤ (r : ℝ) →
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
                        (CoarseEllipticityExponent.finite r) omega *
                      (Annealed.sigmaBar M (m - 1) : ℝ) ≤
                    Ydet omega + Y omega) ∧
                (∀ omega, Ydet omega ≤
                  Clow * s * (2 * s - M.gamma)⁻¹) ∧
                Measurable Y ∧
                IsBigOWith (cutoffSampleLaw M).toMeasure
                  (gammaSigma ((1 - sigma) / 2)) Y
                  (Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
  have habsorb : 4 * (2 * superposedFluxSharpDetConst d) ≤ Clow := by
    convert hdet using 1
    all_goals ring
  refine coarse_ellipticity_lower_branchPayload_two_le_of_finiteQPresplit d
    (Clow := Clow) (Cprof := 2 * superposedFluxSharpDetConst d)
    (mul_nonneg (by norm_num) (superposedFluxSharpDetConst_pos hd).le) habsorb ?_
  intro M m E hstate sigma hsigma hE1 hE2 r hr s hsWindow
  exact exists_superposedFluxFiniteQPresplit_two_le hd hClow haux hbudgetChoice
    M m E hstate sigma hsigma hE1 hE2 r hr s hsWindow

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
