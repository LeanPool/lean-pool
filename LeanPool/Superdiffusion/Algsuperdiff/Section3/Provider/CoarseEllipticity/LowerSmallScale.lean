/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffMultiscaleEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.CutoffCoarseNormBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.PlateauLandmarks
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.GridDominationEndpoint
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.LambdaGridBridge
import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.OneSidedOrlicz

/-!
# LowerSmallScale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The deterministic small-scale branch of the lower coarse-ellipticity bound

This file proves the `m <= mStar M` branch used inside the proof of the lower
half of `Frozen.Section3.coarse_ellipticity_bounds`.  It is an internal branch
theorem, not a replacement for that frozen theorem and not a closed source
node.  In the eventual source-facing proof, `m <= mStar M` is introduced by a
case split and `8 <= C` is discharged by the dimension-only choice of the
single outer constant; neither becomes a premise of the frozen declaration.

The argument is deterministic.  Uniform ellipticity bounds every inverse
starred descendant norm by `nu^-1`.  The normalized geometric depth weights
then give the same bound for every finite exponent, while the infinity
endpoint follows from its decaying weights.  Below `mStar`, the annealed
plateau is at most `2 * nu`, so the whole lower observable is at most `2`.
The frozen lower profile is at least `2` once its common constant is at least
`8`; hence the zero random witness supplies the exact lower-family carrier.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

private theorem neZero_of_model (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- A uniform bound on all inverse starred descendant norms bounds the finite
multiscale inverse ellipticity by the same constant. -/
theorem lambdaSqFinite_inv_le_of_forall_maxDescendant_le
    [NeZero d] (Q : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    {s q B : ℝ} (hs : 0 < s) (hq : 0 < q) (hB : 0 ≤ B)
    (hmax : ∀ n : ℕ,
      Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
        (Q.scale - (n : ℤ)) a ≤ B) :
    (Book.Ch02.lambdaSqFinite Q s q a)⁻¹ ≤ B := by
  have hsq : 0 < s * q := mul_pos hs hq
  have hleft : Summable (fun n : ℕ =>
      Book.Ch02.geometricWeight s q n *
        Real.rpow
          (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) a) (q / 2)) :=
    Book.Ch02.summable_sigmaStarInv_series_pointwiseCoeffField Q a hs hq
  have hright : Summable (fun n : ℕ =>
      Book.Ch02.geometricWeight s q n * Real.rpow B (q / 2)) :=
    (HCPolySupport.summable_geometricWeight hsq).mul_right _
  have hterm : ∀ n : ℕ,
      Book.Ch02.geometricWeight s q n *
          Real.rpow
            (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) a) (q / 2) ≤
        Book.Ch02.geometricWeight s q n * Real.rpow B (q / 2) := by
    intro n
    refine mul_le_mul_of_nonneg_left ?_ ?_
    · exact Real.rpow_le_rpow
        (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
          (sub_le_self Q.scale (by exact_mod_cast Nat.zero_le n)) a)
        (hmax n) (div_nonneg hq.le (by norm_num))
    · exact HCPolySupport.geometricWeight_nonneg n hsq.le
  have hseries :
      (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        Real.rpow
          (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) a) (q / 2)) ≤
      Real.rpow B (q / 2) := by
    calc
      (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
          Real.rpow
            (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) a) (q / 2)) ≤
          ∑' n : ℕ, Book.Ch02.geometricWeight s q n * Real.rpow B (q / 2) :=
        Summable.tsum_le_tsum hterm hleft hright
      _ = Real.rpow B (q / 2) := by
        rw [tsum_mul_right]
        have hweightOne : (∑' n : ℕ, Book.Ch02.geometricWeight s q n) = 1 := by
          simpa only [Book.Ch02.geometricWeight_eq_old] using
            HCPolySupport.tsum_geometricWeight_eq_one hsq
        rw [hweightOne, one_mul]
  rw [lambdaSqFinite_inv_eq_rpow Q hsq.le a]
  calc
    Real.rpow
        (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
          Real.rpow
            (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) a) (q / 2)) (2 / q) ≤
        Real.rpow (Real.rpow B (q / 2)) (2 / q) :=
      Real.rpow_le_rpow (tsum_nonneg fun n => mul_nonneg
        (HCPolySupport.geometricWeight_nonneg n hsq.le)
        (Real.rpow_nonneg
          (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
            (sub_le_self Q.scale (by exact_mod_cast Nat.zero_le n)) a) _))
        hseries (div_nonneg (by norm_num) hq.le)
    _ = Real.rpow B ((q / 2) * (2 / q)) :=
      (Real.rpow_mul hB (q / 2) (2 / q)).symm
    _ = B := by
      have hprod : (q / 2) * (2 / q) = 1 := by field_simp [hq.ne']
      rw [hprod]
      exact Real.rpow_one B

/-- Every lower coarse-ellipticity observable of the cutoff is bounded by
`nu^-1`, uniformly in both admissible exponent endpoints and both scales. -/
theorem cutoffLowerEllipticityInv_le_nu_inv
    (M : ABKModel d) (domainScale cutoffScale : ℤ) {s : ℝ} (hs : 0 < s)
    (q : CoarseEllipticityExponent) (omega : Cutoff.CutoffSample d) :
    Observable.cutoffLowerEllipticityInv M domainScale cutoffScale s hs q omega ≤
      M.nu⁻¹ := by
  let : NeZero d := neZero_of_model M
  rw [Observable.cutoffLowerEllipticityInv_eq_literal]
  unfold Observable.cutoffLowerEllipticityInvLiteral
  rcases q with ⟨q, hq⟩
  cases q with
  | finite r =>
      change 1 ≤ r at hq
      rw [Book.Ch04.lambdaSqCoeffField]
      simp only [Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField,
        dite_eq_left, Book.Ch02.lambdaSq_finite]
      exact lambdaSqFinite_inv_le_of_forall_maxDescendant_le
        (originCube d domainScale) _ hs (lt_of_lt_of_le zero_lt_one hq)
          (inv_nonneg.mpr M.nu_pos.le)
          (fun n => Provider.Base.maxDescendantSigmaStarInvMatrixNormAtScale_coefficientCutoff_le
            M (originCube d domainScale) cutoffScale n omega)
  | infinity =>
      apply lambdaSqCoeffField_inv_infinity_le_of_forall
      intro n
      rw [Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale]
      simp only [Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField, dite_eq_left]
      calc
        Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
            Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
              (originCube d domainScale) (domainScale - (n : ℤ))
                (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
                  (Cutoff.coefficientCutoff M.nu cutoffScale omega)
                  (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField
                    M cutoffScale omega)) ≤
          1 * M.nu⁻¹ := by
            exact mul_le_mul
              (Book.Ch02.infinityWeight_le_one hs.le n)
              (Provider.Base.maxDescendantSigmaStarInvMatrixNormAtScale_coefficientCutoff_le
                M (originCube d domainScale) cutoffScale n omega)
              (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg
                (originCube d domainScale)
                (sub_le_self (originCube d domainScale).scale
                  (by exact_mod_cast Nat.zero_le n)) _)
              zero_le_one
        _ = M.nu⁻¹ := one_mul _

/-- Below `mStar`, the lower observable normalized by the previous annealed
diffusivity is bounded pointwise by `2`, uniformly in the cutoff level. -/
theorem cutoffLowerEllipticityInv_mul_sigmaBar_le_two_of_le_mStar
    (M : ABKModel d) (m : ℤ) (hm : m ≤ mStar M)
    {s : ℝ} (hs : 0 < s) (q : CoarseEllipticityExponent) (L : ℤ)
    (omega : Cutoff.CutoffSample d) :
    Observable.cutoffLowerEllipticityInv M m L s hs q omega *
        (Annealed.sigmaBar M (m - 1) : ℝ) ≤ 2 := by
  have hobservable := cutoffLowerEllipticityInv_le_nu_inv M m L hs q omega
  have hmPred : m - 1 ≤ mStar M := by omega
  have hplateau := (Provider.Base.annealedPlateau_le_mStar M (m - 1) hmPred).2
  calc
    Observable.cutoffLowerEllipticityInv M m L s hs q omega *
          (Annealed.sigmaBar M (m - 1) : ℝ) ≤
        M.nu⁻¹ * (Annealed.sigmaBar M (m - 1) : ℝ) :=
      mul_le_mul_of_nonneg_right hobservable (Annealed.sigmaBar M (m - 1)).2.le
    _ ≤ M.nu⁻¹ * (2 * M.nu) :=
      mul_le_mul_of_nonneg_left hplateau (inv_pos.mpr M.nu_pos).le
    _ = 2 := by field_simp [M.nu_pos.ne']

/-- On the frozen source window, the lower deterministic profile is at least
`2` whenever its common constant is at least `8`. -/
theorem two_le_lowerEllipticityProfile_of_eight_le
    {C gamma s : ℝ} (hC : 8 ≤ C) (hgamma : 0 < gamma)
    (hhalf : gamma / 2 < s) (q : CoarseEllipticityExponent) :
    2 ≤ lowerEllipticityProfile C gamma s q := by
  have hs : 0 < s := by linarith
  have hgap : 0 < 2 * s - gamma := by linarith
  have hratio : (1 / 2 : ℝ) ≤ s / (2 * s - gamma) := by
    rw [le_div_iff₀ hgap]
    nlinarith [hgamma.le]
  rcases q with ⟨q, hq⟩
  cases q with
  | finite r =>
      change 1 ≤ r at hq
      have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hq
      by_cases hr : r < 2
      · simp only [lowerEllipticityProfile, hr, ↓reduceIte]
        have hexp : 2 / r ≤ 2 := by
          rw [div_le_iff₀ hrpos]
          nlinarith
        have hquarter : (1 / 4 : ℝ) ≤
            Real.rpow (s / (2 * s - gamma)) (2 / r) := by
          calc
            (1 / 4 : ℝ) = Real.rpow (1 / 2 : ℝ) 2 := by
              norm_num [Real.rpow_two]
            _ ≤ Real.rpow (1 / 2 : ℝ) (2 / r) :=
              Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hexp
            _ ≤ Real.rpow (s / (2 * s - gamma)) (2 / r) :=
              Real.rpow_le_rpow (by norm_num) hratio (div_nonneg (by norm_num) hrpos.le)
        have hmul := mul_le_mul hC hquarter (by norm_num : (0 : ℝ) ≤ 1 / 4)
          (by linarith : (0 : ℝ) ≤ C)
        norm_num at hmul ⊢
        exact hmul
      · have hr2 : 2 ≤ r := not_lt.mp hr
        simp only [lowerEllipticityProfile, hr, ↓reduceIte]
        have hmul := mul_le_mul hC hratio (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by linarith : (0 : ℝ) ≤ C)
        have htwo : 2 ≤ C * (s / (2 * s - gamma)) := by
          linarith
        simpa [div_eq_mul_inv, mul_assoc] using htwo
  | infinity =>
      simp only [lowerEllipticityProfile]
      linarith

private theorem isBigOWith_gammaSigma_zero {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {sigma A : ℝ} (hA : 0 ≤ A) :
    HCPolySupport.IndependentSums.IsBigOWith μ
      (HCPolySupport.IndependentSums.gammaSigma sigma) (fun _ : Ω => 0) A :=
  Algsuperdiff.Section3.Probability.isBigOWith_gammaSigma_of_eq_zero hA (fun _ => rfl)

/-- The exact lower-family conclusion in the `m <= mStar M` branch.  The
witness is identically zero; no induction-state or gate proposition is assumed
or hidden in this result. -/
theorem coarse_ellipticity_lower_of_le_mStar_of_eight_le
    (M : ABKModel d) (m : ℤ) (hm : m ≤ mStar M) {C : ℝ} (hC : 8 ≤ C)
    (E : {E : ℝ // 1 ≤ E}) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioc 0 (1 / 2))
    (q : CoarseEllipticityExponent) (s : ℝ)
    (hsWindow : s ∈ Set.Icc
      (M.gamma / 2 + Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) 1) :
    Probability.IsLowerIntegerFamilyOrlicz
      (Cutoff.cutoffSampleLaw M).toMeasure
      (HCPolySupport.IndependentSums.gammaSigma ((1 - sigma) / 2))
      (fun L : ℤ => fun omega =>
        Observable.cutoffLowerEllipticityInv M m L s
          (by
            exact (add_pos
              (div_pos M.shellPrefix.gamma_pos (by norm_num))
              (Real.exp_pos
                (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)))).trans_le hsWindow.1)
          q omega * (Annealed.sigmaBar M (m - 1) : ℝ))
      (m - 1) (lowerEllipticityProfile C M.gamma s q)
      (Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
  have hrare : 0 < Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) :=
    Real.exp_pos _
  have hhalf : M.gamma / 2 < s := by linarith [hsWindow.1]
  have hs : 0 < s := by linarith [M.shellPrefix.gamma_pos]
  have htailExp : 0 < (1 - sigma) / 2 := by linarith [hsigma.2]
  refine ⟨fun _ => 0,
    Probability.isAdmissibleTail_gammaSigma htailExp,
    hrare, ?_, measurable_const, ?_, isBigOWith_gammaSigma_zero hrare.le⟩
  · intro L _hL
    exact (Observable.measurable_cutoffLowerEllipticityInv M m L s hs q).mul_const _
  · intro omega L _hL
    have htwo := cutoffLowerEllipticityInv_mul_sigmaBar_le_two_of_le_mStar
      M m hm hs q L omega
    have hprofile := two_le_lowerEllipticityProfile_of_eight_le
      hC M.shellPrefix.gamma_pos hhalf q
    simpa only [add_zero] using htwo.trans hprofile

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
