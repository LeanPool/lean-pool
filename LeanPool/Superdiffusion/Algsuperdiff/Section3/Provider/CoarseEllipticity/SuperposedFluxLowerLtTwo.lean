/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLowerLtTwoSeries

/-!
# SuperposedFluxLowerLtTwo

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The sharp lower branch for finite exponents below two

This file normalizes the pointwise sharp representative by its deterministic
depth amplitude and supplies the conditional finite-`q < 2` pre-split A.  The
output-constant inequalities remain caller-supplied obligations; these Provider
helpers assert no source-node status.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- The model-facing normalized finite-`q < 2` producer consumed by
`coarse_ellipticity_lower_branchPayload_lt_two_of_finiteQPresplit`. -/
theorem exists_superposedFluxFiniteQPresplit_lt_two [NeZero d]
    (hd : 2 ≤ d) {Clow : ℝ} (hClow : 0 < Clow)
    (haux : profileAuxiliaryConst d ≤ Clow)
    (hbudgetChoice : superposedFluxLtTwoBudgetConst d + 6 ≤
      (superposedFluxBfaRate d / 2) * Clow)
    (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E})
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc 0 (1 / 2))
    (hE1 : max (Real.exp (Clow / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hE2 : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (r : {r : ℝ // 1 ≤ r}) (hr : (r : ℝ) < 2)
    (s : ℝ)
    (hsWindow : s ∈ Set.Icc
      (M.gamma / 2 + Real.exp
        (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1) :
    ∃ (V : ℕ → CutoffSample d → ℝ) (a : ℕ → ℝ),
      (∀ n omega, 0 ≤ V n omega) ∧
      (∀ n, Measurable (V n)) ∧
      (∀ n, 0 < a n) ∧
      (Summable fun n : ℕ =>
        Book.Ch02.geometricWeight s (r : ℝ) n *
          a n ^ ((r : ℝ) / 2)) ∧
      (∀ omega, Summable fun n : ℕ =>
        Book.Ch02.geometricWeight s (r : ℝ) n *
          a n ^ ((r : ℝ) / 2) * V n omega) ∧
      (∀ n, IsBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma ((1 - sigma) / 2)) (V n) 1) ∧
      ((2 * (∑' n : ℕ,
          Book.Ch02.geometricWeight s (r : ℝ) n *
            a n ^ ((r : ℝ) / 2)) ^ (2 / (r : ℝ))) *
          gammaTriangleConst ((1 - sigma) / 2) ≤
        Real.exp (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) ∧
      (∀ omega, ∀ L : ℤ, m - 1 ≤ L → ∀ n : ℕ,
        (Annealed.sigmaBar M (m - 1) : ℝ) *
            Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
              (originCube d m) (m - (n : ℤ))
              (coefficientCutoff M.nu L omega) ≤
          finiteQGeometricProfile (2 * superposedFluxSharpDetConst d)
            M.gamma n + a n * V n omega) := by
  have hr0 : 0 < (r : ℝ) := by linarith [r.property]
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
  let V : ℕ → CutoffSample d → ℝ := fun n omega => (a n)⁻¹ * U n omega
  let H : ℝ := superposedFluxCutoffCap M m
  let X : ℝ := ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹
  let Ahalf : ℝ := Real.exp (-(superposedFluxBfaRate d / 2 * X))
  let a0 : ℝ := superposedFluxDepthAmpConst d *
    Real.exp (-(superposedFluxBfaRate d * X))
  have ha : ∀ n, 0 < a n := fun n => superposedFluxDepthAmpProfile_pos hd M E n
  have hVnonneg : ∀ n omega, 0 ≤ V n omega := by
    intro n omega
    exact mul_nonneg (inv_nonneg.mpr (ha n).le) (hUnonneg n omega)
  have hVmeas : ∀ n, Measurable (V n) := by
    intro n
    exact (hUmeas n).const_mul (a n)⁻¹
  have hasum : Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n * a n ^ ((r : ℝ) / 2) := by
    simpa [a] using summable_geometricWeight_mul_depthAmp_rpow_lt_two
      hd M (E : ℝ) hs r.property hr hgap
  have hHpos : 0 < H := superposedFluxCutoffCap_pos hd M m
  have ha0pos : 0 < a0 := by
    dsimp [a0]
    exact mul_pos (superposedFluxDepthAmpConst_pos hd) (Real.exp_pos _)
  have ha0le : ∀ n, a0 ≤ a n := by
    intro n
    have hP : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ (4 : ℕ) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      apply one_le_pow₀
      linarith
    have hG : (1 : ℝ) ≤ (3 : ℝ) ^ (M.gamma * (n : ℝ)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg M.shellPrefix.gamma_pos.le
        (Nat.cast_nonneg n))
    have hPG : (1 : ℝ) ≤
        ((n : ℝ) + 1) ^ (4 : ℕ) *
          (3 : ℝ) ^ (M.gamma * (n : ℝ)) := by
      nlinarith [mul_le_mul hP hG (by norm_num : (0 : ℝ) ≤ 1) (by positivity)]
    calc
      a0 = (superposedFluxDepthAmpConst d * 1) *
          Real.exp (-(superposedFluxBfaRate d * X)) := by simp [a0]
      _ ≤ (superposedFluxDepthAmpConst d *
          (((n : ℝ) + 1) ^ (4 : ℕ) *
            (3 : ℝ) ^ (M.gamma * (n : ℝ)))) *
          Real.exp (-(superposedFluxBfaRate d * X)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPG (superposedFluxDepthAmpConst_pos hd).le)
          (Real.exp_pos _).le
      _ = a n := by
        dsimp [a, superposedFluxDepthAmpProfile, X]
        ring
  have hVlinsum : ∀ omega, Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s (r : ℝ) n *
        a n ^ ((r : ℝ) / 2) * V n omega := by
    intro omega
    let C : ℝ := a0 ^ ((r : ℝ) / 2 - 1) * H
    have hweight := (HCPolySupport.summable_geometricWeight
      (mul_pos hs hr0)).mul_right C
    refine Summable.of_nonneg_of_le ?_ ?_ hweight
    · intro n
      exact mul_nonneg
        (mul_nonneg
          (HCPolySupport.geometricWeight_nonneg n (mul_pos hs hr0).le)
          (Real.rpow_nonneg (ha n).le _))
        (hVnonneg n omega)
    · intro n
      have hexp : (r : ℝ) / 2 - 1 ≤ 0 := by linarith
      have hcoeff : a n ^ ((r : ℝ) / 2 - 1) ≤
          a0 ^ ((r : ℝ) / 2 - 1) :=
        Real.rpow_le_rpow_of_nonpos ha0pos (ha0le n) hexp
      have hnormalize : a n ^ ((r : ℝ) / 2) * V n omega =
          a n ^ ((r : ℝ) / 2 - 1) * U n omega := by
        rw [Real.rpow_sub_one (ha n).ne']
        dsimp [V]
        field_simp
      have hnormalized : a n ^ ((r : ℝ) / 2) * V n omega ≤ C := by
        rw [hnormalize]
        dsimp [C]
        exact mul_le_mul hcoeff (hUcap n omega) (hUnonneg n omega)
          (Real.rpow_nonneg ha0pos.le _)
      simpa only [mul_assoc] using! mul_le_mul_of_nonneg_left hnormalized
        (HCPolySupport.geometricWeight_nonneg n (mul_pos hs hr0).le)
  have hVO : ∀ n, IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma ((1 - sigma) / 2)) (V n) 1 := by
    intro n
    have hscaled := (hUOraw n).mono_scale
      (superposedFluxSharpDepthAmp_le_profile hd M m E hsigma.1 hsigma.2
        hmaxAux hE2 n)
    have hnorm := hscaled.const_mul (inv_nonneg.mpr (ha n).le)
    simpa [V, a, inv_mul_cancel₀ (ha n).ne'] using hnorm
  let rare : ℝ := Real.exp
    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))
  let K : ℝ := superposedFluxLtTwoBudgetConst d
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
  have hgate : K * Ahalf ≤ rare ^ (6 : ℕ) := by
    simpa [K, Ahalf, rare, X, mul_assoc] using
      prefactor_mul_exp_le_frozenRare_pow
        (superposedFluxLtTwoBudgetConst_pos d).le hClow hXlarge hbudgetChoice
  have hseries :
      (∑' n : ℕ, Book.Ch02.geometricWeight s (r : ℝ) n *
        a n ^ ((r : ℝ) / 2)) ≤
        superposedFluxLtTwoSeriesConst d * Ahalf * rare⁻¹ ^ (5 : ℕ) := by
    simpa [a, Ahalf, rare, X, mul_assoc] using
      tsum_geometricWeight_mul_depthAmp_rpow_lt_two_le hd M (E : ℝ)
        hs hsWindow.2 r.property hr hrare hrareOne hsWindow.1
  have htri : gammaTriangleConst ((1 - sigma) / 2) ≤
      superposedFluxTriangleConst :=
    gammaTriangleConst_le_superposedFluxTriangleConst (by linarith [hsigma.2])
  have htriOne : (1 : ℝ) ≤ superposedFluxTriangleConst := by
    unfold superposedFluxTriangleConst
    have hp : (1 : ℝ) ≤ (625 : ℝ) ^ (12 : ℝ) :=
      Real.one_le_rpow (by norm_num) (by norm_num)
    nlinarith
  let S : ℝ := ∑' n : ℕ, Book.Ch02.geometricWeight s (r : ℝ) n *
    a n ^ ((r : ℝ) / 2)
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg fun n => mul_nonneg
      (HCPolySupport.geometricWeight_nonneg n (mul_pos hs hr0).le)
      (Real.rpow_nonneg (ha n).le _)
  have hSTrare : (2 * S) * superposedFluxTriangleConst ≤ rare := by
    have hright0 : 0 ≤ superposedFluxLtTwoSeriesConst d *
        Ahalf * rare⁻¹ ^ (5 : ℕ) := by
      exact mul_nonneg
        (mul_nonneg (superposedFluxLtTwoSeriesConst_pos d).le
          (by dsimp [Ahalf]; exact (Real.exp_pos _).le))
        (by positivity)
    have hfirst : (2 * S) * superposedFluxTriangleConst ≤
        K * Ahalf * rare⁻¹ ^ (5 : ℕ) := by
      calc
        _ ≤ (2 * (superposedFluxLtTwoSeriesConst d * Ahalf *
              rare⁻¹ ^ (5 : ℕ))) * superposedFluxTriangleConst :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by simpa [S] using hseries) (by norm_num))
            (by unfold superposedFluxTriangleConst; positivity)
        _ = K * Ahalf * rare⁻¹ ^ (5 : ℕ) := by
          unfold K superposedFluxLtTwoBudgetConst
          ring
    exact hfirst.trans (mul_le_of_pow_inv_gate
      (mul_nonneg (superposedFluxLtTwoBudgetConst_pos d).le
        (by dsimp [Ahalf]; exact (Real.exp_pos _).le))
      hrare le_rfl hgate)
  have hxOne : 2 * S ≤ 1 := by
    have hxTri : 2 * S ≤ (2 * S) * superposedFluxTriangleConst := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left htriOne
        (mul_nonneg (by norm_num) hS0)
    exact hxTri.trans (hSTrare.trans hrareOne)
  have hroot : (2 * S) ^ (2 / (r : ℝ)) ≤ 2 * S := by
    apply Real.rpow_le_self_of_le_one (mul_nonneg (by norm_num) hS0) hxOne
    rw [le_div_iff₀ hr0]
    simpa using hr.le
  have htwoRoot : 2 * S ^ (2 / (r : ℝ)) ≤
      (2 * S) ^ (2 / (r : ℝ)) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hS0]
    have hu : (1 : ℝ) ≤ 2 / (r : ℝ) := by
      rw [le_div_iff₀ hr0]
      simpa using hr.le
    have htwoPow : (2 : ℝ) ≤ (2 : ℝ) ^ (2 / (r : ℝ)) := by
      calc
        (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hu
    exact mul_le_mul_of_nonneg_right htwoPow
      (Real.rpow_nonneg hS0 _)
  have hbudget : (2 * S ^ (2 / (r : ℝ))) *
      gammaTriangleConst ((1 - sigma) / 2) ≤ rare := by
    calc
      _ ≤ (2 * S) ^ (2 / (r : ℝ)) *
          gammaTriangleConst ((1 - sigma) / 2) :=
        mul_le_mul_of_nonneg_right htwoRoot gammaTriangleConst_pos.le
      _ ≤ (2 * S) * gammaTriangleConst ((1 - sigma) / 2) :=
        mul_le_mul_of_nonneg_right hroot gammaTriangleConst_pos.le
      _ ≤ (2 * S) * superposedFluxTriangleConst :=
        mul_le_mul_of_nonneg_left htri (mul_nonneg (by norm_num) hS0)
      _ ≤ rare := hSTrare
  have hdepth' : ∀ omega, ∀ L : ℤ, m - 1 ≤ L → ∀ n : ℕ,
      (Annealed.sigmaBar M (m - 1) : ℝ) *
          Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
            (originCube d m) (m - (n : ℤ))
            (coefficientCutoff M.nu L omega) ≤
        finiteQGeometricProfile (2 * superposedFluxSharpDetConst d)
          M.gamma n + a n * V n omega := by
    intro omega L hL n
    have h := hdepth omega L hL n
    have hav : a n * V n omega = U n omega := by
      dsimp [V]
      rw [← mul_assoc, mul_inv_cancel₀ (ha n).ne', one_mul]
    simpa only [hav] using h
  exact ⟨V, a, hVnonneg, hVmeas, ha, hasum, hVlinsum, hVO,
    by simpa [S, rare] using hbudget, hdepth'⟩

/-- A payload-valued helper for the conditional `1 ≤ q < 2` A. -/
theorem superposedFlux_lower_branchPayload_lt_two [NeZero d]
    (hd : 2 ≤ d) {Clow : ℝ} (hClow : 0 < Clow)
    (haux : profileAuxiliaryConst d ≤ Clow)
    (hdet : 16 * superposedFluxSharpDetConst d ≤ Clow)
    (hbudgetChoice : superposedFluxLtTwoBudgetConst d + 6 ≤
      (superposedFluxBfaRate d / 2) * Clow) :
    ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
      Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
      ∀ sigma : ℝ, sigma ∈ Set.Ioc 0 (1 / 2) →
        max (Real.exp (Clow / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
        ∀ r : {r : ℝ // 1 ≤ r}, (r : ℝ) < 2 →
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
                  Clow * (s / (2 * s - M.gamma)) ^ (2 / (r : ℝ))) ∧
                Measurable Y ∧
                IsBigOWith (cutoffSampleLaw M).toMeasure
                  (gammaSigma ((1 - sigma) / 2)) Y
                  (Real.exp
                    (-(Clow⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
  have habsorb : 8 * (2 * superposedFluxSharpDetConst d) ≤ Clow := by
    convert hdet using 1
    all_goals ring
  refine coarse_ellipticity_lower_branchPayload_lt_two_of_finiteQPresplit d
    (Clow := Clow) (Cprof := 2 * superposedFluxSharpDetConst d)
    (mul_nonneg (by norm_num) (superposedFluxSharpDetConst_pos hd).le) habsorb ?_
  intro M m E hstate sigma hsigma hE1 hE2 r hr s hsWindow
  exact exists_superposedFluxFiniteQPresplit_lt_two hd hClow haux hbudgetChoice
    M m E hstate sigma hsigma hE1 hE2 r hr s hsWindow

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
