/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.LowScaleExpectation

/-!
# Coarse-graining support:
Support.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.PairedSquares

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

/-!
# Paired weak-norm square conversion

This proof-internal file assembles the square estimates coming from the
weak-norm maximizer theorem for the third Section 5.3 lemma.
-/

noncomputable section

attribute [local irreducible] coarseFluctuationScalarWeightAtScale
  coarseFluctuationTauSumAtScale coarseFluctuationUnitMomentWeightAtScale
  coarseFluctuationResponseMomentAtScale

private theorem positivePart_split_le (x base : ℝ) :
    x ≤ base + max (x - base) 0 := by
  by_cases h : x ≤ base
  · exact h.trans (le_add_of_nonneg_right (le_max_right _ _))
  · have hx : base ≤ x := le_of_lt (lt_of_not_ge h)
    have hmax : max (x - base) 0 = x - base := max_eq_left (sub_nonneg.mpr hx)
    linarith

/-- Pointwise decomposition of the response-defect mismatch-square pair in
the weak-norm maximizer RHS.  The endpoint ellipticity factors are split into
their scale-zero baseline plus the shifted positive excess. -/
theorem paired_mismatchTermSquares_special_le_baseline_add_positiveExcess
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Vec d) (a : RegCoeffField d) :
    let β := section53CoarseFluctuationBeta hP4
    let s := hP4.sLower + 2 * β
    let s' := hP4.sLower + β
    let t := hP4.sUpper + 2 * β
    let t' := hP4.sUpper + β
    let Q : TriadicCube d := originCube d (m : ℤ)
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let σ := sigmaHatAtScale hP hStruct (m : ℤ)
    let defectSum : ℝ :=
      ∑ n ∈ Finset.Icc (((k : ℤ) + 1)) (m : ℤ),
        Real.rpow (3 : ℝ)
            (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.sqrt
            (WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e a)
    let lowerExcess : ℝ :=
      max
        ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct 0)⁻¹)
        0
    let upperExcess : ℝ :=
      max
        (Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct 0)
        0
    σ *
        (WeakNormsMaximizer.gradientMismatchTermAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxMismatchTermAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
      ≤
        (coarseFluctuationScalarWeightAtScale hP hStruct m +
            (σ * lowerExcess + σ⁻¹ * upperExcess)) *
          defectSum ^ 2 := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let D : ℝ :=
    ∑ n ∈ Finset.Icc (((k : ℤ) + 1)) (m : ℤ),
      Real.rpow (3 : ℝ)
          (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        Real.sqrt
          (WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  let lowerCoeff : ℝ := (Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹
  let upperCoeff : ℝ := Ch04.LambdaSqCoeffField Q t' (.finite 1) a
  let lowerBase : ℝ := (hP.barSigmaStarAtScale hStruct 0)⁻¹
  let upperBase : ℝ := hP.barSigmaAtScale hStruct 0
  let lowerExcess : ℝ := max (lowerCoeff - lowerBase) 0
  let upperExcess : ℝ := max (upperCoeff - upperBase) 0
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hs'_pos : 0 < s' := by
    dsimp [s', β]
    linarith [hP4.sLower_pos, hβ_pos]
  have ht'_pos : 0 < t' := by
    dsimp [t', β]
    linarith [hP4.sUpper_pos, hβ_pos]
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hlowerCoeff_nonneg : 0 ≤ lowerCoeff := by
    dsimp [lowerCoeff]
    exact inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg Q a hs'_pos (by norm_num))
  have hupperCoeff_nonneg : 0 ≤ upperCoeff := by
    dsimp [upperCoeff]
    exact Ch04.LambdaSqCoeffField_finite_nonneg Q a ht'_pos (by norm_num)
  have hGradSq :
      (WeakNormsMaximizer.gradientMismatchTermAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 =
        lowerCoeff * D ^ 2 := by
    have hgap : s - s' = β := by
      dsimp [s, s']
      ring
    dsimp [WeakNormsMaximizer.gradientMismatchTermAtScale, D, lowerCoeff, Q]
    rw [hgap]
    rw [mul_pow, Real.sq_sqrt hlowerCoeff_nonneg]
  have hFluxSq :
      (WeakNormsMaximizer.fluxMismatchTermAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2 =
        upperCoeff * D ^ 2 := by
    have hgap : t - t' = β := by
      dsimp [t, t']
      ring
    dsimp [WeakNormsMaximizer.fluxMismatchTermAtScale, D, upperCoeff, Q]
    rw [hgap]
    rw [mul_pow, Real.sq_sqrt hupperCoeff_nonneg]
  have hlower_le : lowerCoeff ≤ lowerBase + lowerExcess := by
    simpa [lowerExcess] using positivePart_split_le lowerCoeff lowerBase
  have hupper_le : upperCoeff ≤ upperBase + upperExcess := by
    simpa [upperExcess] using positivePart_split_le upperCoeff upperBase
  have hDsq_nonneg : 0 ≤ D ^ 2 := sq_nonneg _
  have hScalarWeight :
      coarseFluctuationScalarWeightAtScale hP hStruct m =
        σ * lowerBase + σ⁻¹ * upperBase := by
    unfold coarseFluctuationScalarWeightAtScale
    simp [σ, lowerBase, upperBase]
  calc
    σ *
        (WeakNormsMaximizer.gradientMismatchTermAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
      σ⁻¹ *
        (WeakNormsMaximizer.fluxMismatchTermAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
        =
      (σ * lowerCoeff + σ⁻¹ * upperCoeff) * D ^ 2 := by
        rw [hGradSq, hFluxSq]
        ring
    _ ≤
      (σ * (lowerBase + lowerExcess) +
          σ⁻¹ * (upperBase + upperExcess)) * D ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (add_le_add
            (mul_le_mul_of_nonneg_left hlower_le hσ_nonneg)
            (mul_le_mul_of_nonneg_left hupper_le hσ_inv_nonneg))
          hDsq_nonneg
    _ =
      (coarseFluctuationScalarWeightAtScale hP hStruct m +
          (σ * lowerExcess + σ⁻¹ * upperExcess)) * D ^ 2 := by
        rw [hScalarWeight]
        ring

private theorem integrable_weightedResponseDefectSquare
    {d : ℕ}
    [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k : ℕ)
    (m : ℕ)
    (e : Vec d)
    :
    let β := section53CoarseFluctuationBeta hP4
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let S : Finset ℤ := Finset.Icc (((k : ℤ) + 1)) (m : ℤ)
    let w : ℤ → ℝ :=
      fun n => Real.rpow (3 : ℝ)
        (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
    let defectSum : RegCoeffField d → ℝ :=
      fun a =>
        ∑ n ∈ S, w n *
          Real.sqrt
            (WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e a)
    ∀ (_hk_nonneg : (0 : ℤ) ≤ (k : ℤ)),
    Integrable (fun a : RegCoeffField d => (defectSum a) ^ 2) P := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let S : Finset ℤ := Finset.Icc (((k : ℤ) + 1)) (m : ℤ)
  let w : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ)
      (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
  let defectSum : RegCoeffField d → ℝ :=
    fun a =>
      ∑ n ∈ S, w n *
        Real.sqrt
          (WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  intro hk_nonneg
  have hBlockM :
      Integrable
        (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have hParent :
      Integrable
        (Ch04.restrictionResponseJObservableCubeSet (originCube d (m : ℤ)) p_e q_e) P :=
    hP.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
      (originCube d (m : ℤ)) p_e q_e hBlockM
  have hDesc :
      ∀ n ∈ S,
        ∀ R, R ∈ descendantsAtScale (originCube d (m : ℤ)) n →
          Integrable (Ch04.restrictionResponseJObservableCubeSet R p_e q_e) P := by
    intro n hn R hR
    have hn_bounds := Finset.mem_Icc.mp hn
    have hn_nonneg : 0 ≤ n := by
      have hk0 : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
      linarith
    have hnm : n ≤ (m : ℤ) := hn_bounds.2
    have hOrigin_nat :
        Integrable
          (Ch04.coarseFullBlockMatrixAtCube
            (originCube d ((Int.toNat n : ℕ) : ℤ))) P :=
      Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 (Int.toNat n)
    have hOrigin :
        Integrable
          (Ch04.coarseFullBlockMatrixAtCube (originCube d n)) P := by
      simpa [Int.toNat_of_nonneg hn_nonneg] using hOrigin_nat
    have hBlockR :
        Integrable (Ch04.coarseFullBlockMatrixAtCube R) P :=
      hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
        hstat hn_nonneg hnm hR hOrigin
    exact
      hP.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
        R p_e q_e hBlockR
  have hw : ∀ n ∈ S, 0 ≤ w n := by
    intro n _hn
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  simpa [defectSum, S, w, p_e, q_e] using
    integrable_sq_weighted_sqrt_responseDefectAverageAtScale
      hP hk_nonneg w p_e q_e
      (by intro n hn; exact hw n (by simpa [S] using hn))
      hParent hDesc

private theorem shiftedPositiveEllipticityExcesses_memLp
    {d : ℕ}
    [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ)
    :
    let β := section53CoarseFluctuationBeta hP4
    let s' := hP4.sLower + β
    let t' := hP4.sUpper + β
    let Q : TriadicCube d := originCube d (m : ℤ)
    let lowerExcess : RegCoeffField d → ℝ :=
      fun a =>
        max
          ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
            (hP.barSigmaStarAtScale hStruct 0)⁻¹)
          0
    let upperExcess : RegCoeffField d → ℝ :=
      fun a =>
        max
          (Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
            hP.barSigmaAtScale hStruct 0)
          0
    ∀ (_hβ_pos : 0 < β),
    ∀ (_hs'_pos : 0 < s'),
    ∀ (_ht'_pos : 0 < t'),
    (MemLp lowerExcess (ENNReal.ofReal (hP4.xi : ℝ)) P) ∧
      (MemLp upperExcess (ENNReal.ofReal (hP4.xi : ℝ)) P) := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let lowerExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct 0)⁻¹)
        0
  let upperExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        (Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct 0)
        0
  intro hβ_pos hs'_pos ht'_pos
  have hLowerAE : AEMeasurable lowerExcess P := by
    simpa [lowerExcess, Q] using
      ((hP.aemeasurable_lambdaSqCoeffField_finite_one_inv Q hs'_pos).sub
        aemeasurable_const).max aemeasurable_const
  have hUpperAE : AEMeasurable upperExcess P := by
    simpa [upperExcess, Q] using
      ((hP.aemeasurable_LambdaSqCoeffField_finite_one Q ht'_pos).sub
        aemeasurable_const).max aemeasurable_const
  have hLower_nonneg : ∀ᵐ a ∂P, 0 ≤ lowerExcess a := by
    filter_upwards with a
    exact le_max_right _ _
  have hUpper_nonneg : ∀ᵐ a ∂P, 0 ≤ upperExcess a := by
    filter_upwards with a
    exact le_max_right _ _
  have hs'_gt : hP4.sLower < s' := by
    dsimp [s', β]
    linarith
  have ht'_gt : hP4.sUpper < t' := by
    dsimp [t', β]
    linarith
  have hs'_lt_one : s' < 1 := by
    have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
    dsimp [s', β]
    nlinarith [hP4.sUpper_pos, hβ_pos]
  have ht'_lt_one : t' < 1 := by
    have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
    dsimp [t', β]
    nlinarith [hP4.sLower_pos, hβ_pos]
  have hLowerPowInt :
      Integrable (fun a : RegCoeffField d => lowerExcess a ^ hP4.xi) P := by
    simpa [lowerExcess, Q, s', β] using
      Section52.lowerPositiveExcessPowIntegrableAtScale_from_P4_twoExponent
        hP hStruct hP4 hs'_gt hs'_lt_one m
  have hUpperPowInt :
      Integrable (fun a : RegCoeffField d => upperExcess a ^ hP4.xi) P := by
    simpa [upperExcess, Q, t', β] using
      Section52.upperPositiveExcessPowIntegrableAtScale_from_P4_twoExponent
        hP hStruct hP4 ht'_gt ht'_lt_one m
  have hLowerMem :
      MemLp lowerExcess (ENNReal.ofReal (hP4.xi : ℝ)) P :=
    memLp_of_integrable_nonneg_nat_pow hP4.xi_pos hLowerAE
      hLower_nonneg hLowerPowInt
  have hUpperMem :
      MemLp upperExcess (ENNReal.ofReal (hP4.xi : ℝ)) P :=
    memLp_of_integrable_nonneg_nat_pow hP4.xi_pos hUpperAE
      hUpper_nonneg hUpperPowInt
  exact ⟨hLowerMem, hUpperMem⟩

private theorem aemeasurable_pairedMismatchSquares
    {d : ℕ}
    [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k : ℕ)
    (m : ℕ)
    (e : Vec d)
    :
    let β := section53CoarseFluctuationBeta hP4
    let s := hP4.sLower + 2 * β
    let s' := hP4.sLower + β
    let t := hP4.sUpper + 2 * β
    let t' := hP4.sUpper + β
    let _Q : TriadicCube d := originCube d (m : ℤ)
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let σ := sigmaHatAtScale hP hStruct (m : ℤ)
    let _S : Finset ℤ := Finset.Icc (((k : ℤ) + 1)) (m : ℤ)
    let X : RegCoeffField d → ℝ :=
      fun a =>
        σ *
            (WeakNormsMaximizer.gradientMismatchTermAtScale
              (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
          σ⁻¹ *
            (WeakNormsMaximizer.fluxMismatchTermAtScale
              (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
    ∀ (_hs'_pos : 0 < s'),
    ∀ (_ht'_pos : 0 < t'),
    AEMeasurable X P := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let S : Finset ℤ := Finset.Icc (((k : ℤ) + 1)) (m : ℤ)
  let X : RegCoeffField d → ℝ :=
    fun a =>
      σ *
          (WeakNormsMaximizer.gradientMismatchTermAtScale
            (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
        σ⁻¹ *
          (WeakNormsMaximizer.fluxMismatchTermAtScale
            (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
  intro hs'_pos ht'_pos
  have hDefAE (n : ℤ) :
      AEMeasurable
        (fun a : RegCoeffField d =>
          WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a) P := by
    change AEMeasurable
      (fun a : RegCoeffField d =>
        descendantsAverage Q (Int.toNat ((m : ℤ) - n))
            (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a) -
          Ch04.restrictionResponseJObservableCubeSet Q p_e q_e a) P
    simpa only [Pi.sub_def] using
      (hP.aemeasurable_descendantsAverage_restrictionResponseJObservableCubeSet
        Q (Int.toNat ((m : ℤ) - n)) p_e q_e).sub
        (hP.aemeasurable_restrictionResponseJObservableCubeSet Q p_e q_e)
  have hSumAE (v v' : ℝ) :
      AEMeasurable
        (fun a : RegCoeffField d =>
          ∑ n ∈ S,
            Real.rpow (3 : ℝ) (-(v - v') * (Int.toNat ((m : ℤ) - n) : ℝ)) *
              Real.sqrt
                (WeakNormsMaximizer.responseDefectAverageAtScale
                  (m : ℤ) n p_e q_e a)) P := by
    refine S.aemeasurable_fun_sum (μ := P) ?_
    intro n _hn
    exact (hDefAE n).sqrt.const_mul _
  have hGradMismatchAE :
      AEMeasurable
        (fun a : RegCoeffField d =>
          WeakNormsMaximizer.gradientMismatchTermAtScale
            (m : ℤ) (k : ℤ) s s' p_e q_e a) P := by
    change AEMeasurable
      (fun a : RegCoeffField d =>
        Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹) *
          ∑ n ∈ S,
            Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat ((m : ℤ) - n) : ℝ)) *
              Real.sqrt
                (WeakNormsMaximizer.responseDefectAverageAtScale
                  (m : ℤ) n p_e q_e a)) P
    simpa only [Pi.mul_def] using
      (hP.aemeasurable_lambdaSqCoeffField_finite_one_inv Q hs'_pos).sqrt.mul
        (hSumAE s s')
  have hFluxMismatchAE :
      AEMeasurable
        (fun a : RegCoeffField d =>
          WeakNormsMaximizer.fluxMismatchTermAtScale
            (m : ℤ) (k : ℤ) t t' p_e q_e a) P := by
    change AEMeasurable
      (fun a : RegCoeffField d =>
        Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a) *
          ∑ n ∈ S,
            Real.rpow (3 : ℝ) (-(t - t') * (Int.toNat ((m : ℤ) - n) : ℝ)) *
              Real.sqrt
                (WeakNormsMaximizer.responseDefectAverageAtScale
                  (m : ℤ) n p_e q_e a)) P
    simpa only [Pi.mul_def] using
      (hP.aemeasurable_LambdaSqCoeffField_finite_one Q ht'_pos).sqrt.mul
        (hSumAE t t')
  have hGradSquareAE :
      AEMeasurable
        (fun a : RegCoeffField d => σ *
          (WeakNormsMaximizer.gradientMismatchTermAtScale
            (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2) P :=
    (hGradMismatchAE.pow_const (2 : ℕ)).const_mul σ
  have hFluxSquareAE :
      AEMeasurable
        (fun a : RegCoeffField d => σ⁻¹ *
          (WeakNormsMaximizer.fluxMismatchTermAtScale
            (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) P :=
    (hFluxMismatchAE.pow_const (2 : ℕ)).const_mul σ⁻¹
  change AEMeasurable X P
  simpa only [X, Pi.add_def] using hGradSquareAE.add hFluxSquareAE

private theorem pairedMismatchSquares_le_defectResponseMajorant
    {d : ℕ}
    [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k : ℕ)
    (m : ℕ)
    (e : Vec d)
    :
    let β := section53CoarseFluctuationBeta hP4
    let s := hP4.sLower + 2 * β
    let s' := hP4.sLower + β
    let t := hP4.sUpper + 2 * β
    let t' := hP4.sUpper + β
    let Q : TriadicCube d := originCube d (m : ℤ)
    let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let σ := sigmaHatAtScale hP hStruct (m : ℤ)
    let S : Finset ℤ := Finset.Icc (((k : ℤ) + 1)) (m : ℤ)
    let w : ℤ → ℝ :=
      fun n => Real.rpow (3 : ℝ)
        (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
    let defectSum : RegCoeffField d → ℝ :=
      fun a =>
        ∑ n ∈ S, w n *
          Real.sqrt
            (WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e a)
    let childAvg : RegCoeffField d → ℝ :=
      fun a => descendantsAverage Q j
        (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
    let lowerExcess : RegCoeffField d → ℝ :=
      fun a =>
        max
          ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
            (hP.barSigmaStarAtScale hStruct 0)⁻¹)
          0
    let upperExcess : RegCoeffField d → ℝ :=
      fun a =>
        max
          (Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
            hP.barSigmaAtScale hStruct 0)
          0
    let X : RegCoeffField d → ℝ :=
      fun a =>
        σ *
            (WeakNormsMaximizer.gradientMismatchTermAtScale
              (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
          σ⁻¹ *
            (WeakNormsMaximizer.fluxMismatchTermAtScale
              (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
    let coeff : ℝ := (5 * β⁻¹) ^ 2
    let Y : RegCoeffField d → ℝ :=
      fun a =>
        coarseFluctuationScalarWeightAtScale hP hStruct m * (defectSum a) ^ 2 +
          coeff * ((σ * lowerExcess a + σ⁻¹ * upperExcess a) * childAvg a)
    ∀ (_hσ_nonneg : 0 ≤ σ),
    ∀ (_hσ_inv_nonneg : 0 ≤ σ⁻¹),
    ∀ (_hDefect_le : ∀ᵐ a ∂P, (defectSum a) ^ 2 ≤ coeff * childAvg a),
    X ≤ᵐ[P] Y := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let S : Finset ℤ := Finset.Icc (((k : ℤ) + 1)) (m : ℤ)
  let w : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ)
      (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
  let defectSum : RegCoeffField d → ℝ :=
    fun a =>
      ∑ n ∈ S, w n *
        Real.sqrt
          (WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  let childAvg : RegCoeffField d → ℝ :=
    fun a => descendantsAverage Q j
      (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
  let lowerExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct 0)⁻¹)
        0
  let upperExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        (Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct 0)
        0
  let X : RegCoeffField d → ℝ :=
    fun a =>
      σ *
          (WeakNormsMaximizer.gradientMismatchTermAtScale
            (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
        σ⁻¹ *
          (WeakNormsMaximizer.fluxMismatchTermAtScale
            (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
  let coeff : ℝ := (5 * β⁻¹) ^ 2
  let Y : RegCoeffField d → ℝ :=
    fun a =>
      coarseFluctuationScalarWeightAtScale hP hStruct m * (defectSum a) ^ 2 +
        coeff * ((σ * lowerExcess a + σ⁻¹ * upperExcess a) * childAvg a)
  intro hσ_nonneg hσ_inv_nonneg hDefect_le
  filter_upwards [hDefect_le] with a hdef
  have hsplit :=
    paired_mismatchTermSquares_special_le_baseline_add_positiveExcess
      hP hStruct hP4 k m e a
  have hpos_nonneg :
      0 ≤ σ * lowerExcess a + σ⁻¹ * upperExcess a := by
    exact add_nonneg
      (mul_nonneg hσ_nonneg (le_max_right _ _))
      (mul_nonneg hσ_inv_nonneg (le_max_right _ _))
  calc
    X a ≤
        (coarseFluctuationScalarWeightAtScale hP hStruct m +
            (σ * lowerExcess a + σ⁻¹ * upperExcess a)) *
          (defectSum a) ^ 2 := by
          simpa [X, defectSum, lowerExcess, upperExcess, S, w, σ, s, s', t,
            t', Q, p_e, q_e, β] using hsplit
    _ =
        coarseFluctuationScalarWeightAtScale hP hStruct m *
            (defectSum a) ^ 2 +
          (σ * lowerExcess a + σ⁻¹ * upperExcess a) *
            (defectSum a) ^ 2 := by ring
    _ ≤
        coarseFluctuationScalarWeightAtScale hP hStruct m *
            (defectSum a) ^ 2 +
          coeff * ((σ * lowerExcess a + σ⁻¹ * upperExcess a) * childAvg a) := by
          refine add_le_add le_rfl ?_
          calc
            (σ * lowerExcess a + σ⁻¹ * upperExcess a) * (defectSum a) ^ 2
                ≤
              (σ * lowerExcess a + σ⁻¹ * upperExcess a) *
                (coeff * childAvg a) :=
                mul_le_mul_of_nonneg_left hdef hpos_nonneg
            _ = coeff * ((σ * lowerExcess a + σ⁻¹ * upperExcess a) *
                  childAvg a) := by ring
    _ = Y a := by simp [Y]

private theorem integral_mismatchMajorant_eq_baseline_add_excess
    {d : ℕ}
    [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k : ℕ)
    (m : ℕ)
    (e : Vec d)
    :
    let β := section53CoarseFluctuationBeta hP4
    let s' := hP4.sLower + β
    let t' := hP4.sUpper + β
    let Q : TriadicCube d := originCube d (m : ℤ)
    let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let σ := sigmaHatAtScale hP hStruct (m : ℤ)
    let S : Finset ℤ := Finset.Icc (((k : ℤ) + 1)) (m : ℤ)
    let w : ℤ → ℝ :=
      fun n => Real.rpow (3 : ℝ)
        (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
    let defectSum : RegCoeffField d → ℝ :=
      fun a =>
        ∑ n ∈ S, w n *
          Real.sqrt
            (WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e a)
    let childAvg : RegCoeffField d → ℝ :=
      fun a => descendantsAverage Q j
        (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
    let lowerExcess : RegCoeffField d → ℝ :=
      fun a =>
        max
          ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
            (hP.barSigmaStarAtScale hStruct 0)⁻¹)
          0
    let upperExcess : RegCoeffField d → ℝ :=
      fun a =>
        max
          (Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
            hP.barSigmaAtScale hStruct 0)
          0
    let coeff : ℝ := (5 * β⁻¹) ^ 2
    let Y : RegCoeffField d → ℝ :=
      fun a =>
        coarseFluctuationScalarWeightAtScale hP hStruct m * (defectSum a) ^ 2 +
          coeff * ((σ * lowerExcess a + σ⁻¹ * upperExcess a) * childAvg a)
    ∀ (_hDsqInt : Integrable (fun a : RegCoeffField d => (defectSum a) ^ 2) P),
    ∀ (_hLowerChildInt : Integrable (fun a : RegCoeffField d => lowerExcess a * childAvg a) P),
    ∀ (_hUpperChildInt : Integrable (fun a : RegCoeffField d => upperExcess a * childAvg a) P),
    ∀ (_hPosInt : Integrable
        (fun a : RegCoeffField d =>
          (σ * lowerExcess a + σ⁻¹ * upperExcess a) * childAvg a) P),
    ∫ a, Y a ∂P =
        coarseFluctuationScalarWeightAtScale hP hStruct m *
            ∫ a, (defectSum a) ^ 2 ∂P +
          coeff *
            (σ * (∫ a, lowerExcess a * childAvg a ∂P) +
              σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P)) := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let S : Finset ℤ := Finset.Icc (((k : ℤ) + 1)) (m : ℤ)
  let w : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ)
      (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
  let defectSum : RegCoeffField d → ℝ :=
    fun a =>
      ∑ n ∈ S, w n *
        Real.sqrt
          (WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  let childAvg : RegCoeffField d → ℝ :=
    fun a => descendantsAverage Q j
      (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
  let lowerExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct 0)⁻¹)
        0
  let upperExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        (Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct 0)
        0
  let coeff : ℝ := (5 * β⁻¹) ^ 2
  let Y : RegCoeffField d → ℝ :=
    fun a =>
      coarseFluctuationScalarWeightAtScale hP hStruct m * (defectSum a) ^ 2 +
        coeff * ((σ * lowerExcess a + σ⁻¹ * upperExcess a) * childAvg a)
  intro hDsqInt hLowerChildInt hUpperChildInt hPosInt
  calc
    ∫ a, Y a ∂P =
        ∫ a,
          coarseFluctuationScalarWeightAtScale hP hStruct m *
              (defectSum a) ^ 2 +
            coeff * ((σ * lowerExcess a + σ⁻¹ * upperExcess a) *
              childAvg a) ∂P := by simp [Y]
    _ =
        ∫ a,
          coarseFluctuationScalarWeightAtScale hP hStruct m *
            (defectSum a) ^ 2 ∂P +
          ∫ a,
            coeff * ((σ * lowerExcess a + σ⁻¹ * upperExcess a) *
              childAvg a) ∂P := by
          rw [integral_add
            (hDsqInt.const_mul (coarseFluctuationScalarWeightAtScale hP hStruct m))
            (hPosInt.const_mul coeff)]
    _ =
        coarseFluctuationScalarWeightAtScale hP hStruct m *
            ∫ a, (defectSum a) ^ 2 ∂P +
          coeff *
            ∫ a, (σ * lowerExcess a + σ⁻¹ * upperExcess a) *
              childAvg a ∂P := by
          rw [integral_const_mul, integral_const_mul]
    _ =
        coarseFluctuationScalarWeightAtScale hP hStruct m *
            ∫ a, (defectSum a) ^ 2 ∂P +
          coeff *
            (σ * (∫ a, lowerExcess a * childAvg a ∂P) +
              σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P)) := by
          congr 1
          have hsplit :
              ∫ a, (σ * lowerExcess a + σ⁻¹ * upperExcess a) *
                  childAvg a ∂P =
                ∫ a, σ * (lowerExcess a * childAvg a) +
                  σ⁻¹ * (upperExcess a * childAvg a) ∂P := by
              refine integral_congr_ae ?_
              filter_upwards with a
              ring
          rw [hsplit]
          rw [integral_add (hLowerChildInt.const_mul σ)
            (hUpperChildInt.const_mul σ⁻¹)]
          rw [integral_const_mul, integral_const_mul]

private theorem integral_mismatchBaseline_le_weightedTau
    {d : ℕ}
    [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k : ℕ)
    (m : ℕ)
    (hkm : k < m)
    (e : Vec d)
    (Cpos : ℝ)
    :
    let C : ℝ := max 10 (25 * Cpos + 10)
    let β := section53CoarseFluctuationBeta hP4
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let S : Finset ℤ := Finset.Icc (((k : ℤ) + 1)) (m : ℤ)
    let w : ℤ → ℝ :=
      fun n => Real.rpow (3 : ℝ)
        (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
    let defectSum : RegCoeffField d → ℝ :=
      fun a =>
        ∑ n ∈ S, w n *
          Real.sqrt
            (WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e a)
    ∀ (_hC_ge_ten : 10 ≤ C),
    ∀ (_hβ_pos : 0 < β),
    ∀ (_hβ_le_one : β ≤ 1),
    ∀ (_hscalar_nonneg : 0 ≤ coarseFluctuationScalarWeightAtScale hP hStruct m),
    ∀ (_hTau_nonneg : 0 ≤ coarseFluctuationTauSumAtScale hP hStruct hP4 k m e),
    ∀ (_hβ2_inv_nonneg : 0 ≤ (β ^ 2)⁻¹),
    coarseFluctuationScalarWeightAtScale hP hStruct m *
          ∫ a, (defectSum a) ^ 2 ∂P
        ≤
          C * ((β ^ 2)⁻¹ *
            coarseFluctuationScalarWeightAtScale hP hStruct m *
              coarseFluctuationTauSumAtScale hP hStruct hP4 k m e) := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let C : ℝ := max 10 (25 * Cpos + 10)
  let β := section53CoarseFluctuationBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let S : Finset ℤ := Finset.Icc (((k : ℤ) + 1)) (m : ℤ)
  let w : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ)
      (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
  let defectSum : RegCoeffField d → ℝ :=
    fun a =>
      ∑ n ∈ S, w n *
        Real.sqrt
          (WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  intro hC_ge_ten hβ_pos hβ_le_one hscalar_nonneg hTau_nonneg hβ2_inv_nonneg
  have htauBase :=
    integral_sq_beta_weighted_sqrt_responseDefectAverageAtScale_special_le_tauSum
      hP hstat hStruct hP4 hkm e
  have hβinv_le_beta2 :
      β⁻¹ ≤ (β ^ 2)⁻¹ := by
    have hβ2_le : β ^ 2 ≤ β := by nlinarith [hβ_pos, hβ_le_one]
    exact (inv_le_inv₀ hβ_pos (sq_pos_of_pos hβ_pos)).mpr hβ2_le
  have hbase :
      ∫ a, (defectSum a) ^ 2 ∂P
        ≤ (5 * β⁻¹) *
            coarseFluctuationTauSumAtScale hP hStruct hP4 k m e := by
    simpa [defectSum, S, w, β, p_e, q_e] using htauBase
  calc
    coarseFluctuationScalarWeightAtScale hP hStruct m *
        ∫ a, (defectSum a) ^ 2 ∂P
        ≤
      coarseFluctuationScalarWeightAtScale hP hStruct m *
        ((5 * β⁻¹) *
          coarseFluctuationTauSumAtScale hP hStruct hP4 k m e) :=
        mul_le_mul_of_nonneg_left hbase hscalar_nonneg
    _ =
      5 * β⁻¹ *
        (coarseFluctuationScalarWeightAtScale hP hStruct m *
          coarseFluctuationTauSumAtScale hP hStruct hP4 k m e) := by ring
    _ ≤
      5 * (β ^ 2)⁻¹ *
        (coarseFluctuationScalarWeightAtScale hP hStruct m *
          coarseFluctuationTauSumAtScale hP hStruct hP4 k m e) := by
        gcongr
    _ ≤
      C * ((β ^ 2)⁻¹ *
        coarseFluctuationScalarWeightAtScale hP hStruct m *
          coarseFluctuationTauSumAtScale hP hStruct hP4 k m e) := by
        have htail_nonneg :
            0 ≤ (β ^ 2)⁻¹ *
              coarseFluctuationScalarWeightAtScale hP hStruct m *
                coarseFluctuationTauSumAtScale hP hStruct hP4 k m e := by
          exact mul_nonneg (mul_nonneg hβ2_inv_nonneg hscalar_nonneg) hTau_nonneg
        have hC_ge_five : 5 ≤ C := by linarith
        nlinarith

private theorem mismatchExcessCoefficient_le_inverseBetaCube
    {d : ℕ}
    [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    :
    let β := section53CoarseFluctuationBeta hP4
    let coeff : ℝ := (5 * β⁻¹) ^ 2
    ∀ (_hβ_pos : 0 < β),
    ∀ (_hβ_le_one : β ≤ 1),
    coeff ≤ 25 * (β ^ 3)⁻¹ := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let coeff : ℝ := (5 * β⁻¹) ^ 2
  intro hβ_pos hβ_le_one
  have hcoeff_eq : coeff = 25 * (β ^ 2)⁻¹ := by
    dsimp [coeff]
    field_simp [hβ_pos.ne']
    ring
  have hβ3_le_β2 : β ^ 3 ≤ β ^ 2 := by
    calc
      β ^ 3 = β ^ 2 * β := by ring
      _ ≤ β ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hβ_le_one (sq_nonneg β)
      _ = β ^ 2 := by ring
  have hinv_le : (β ^ 2)⁻¹ ≤ (β ^ 3)⁻¹ :=
    (inv_le_inv₀ (sq_pos_of_pos hβ_pos) (by positivity : 0 < β ^ 3)).mpr
      hβ3_le_β2
  calc
    coeff = 25 * (β ^ 2)⁻¹ := hcoeff_eq
    _ ≤ 25 * (β ^ 3)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv_le (by norm_num)

private theorem integral_mismatchPositiveExcess_le_responseMoment
    {d : ℕ}
    [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k : ℕ)
    (m : ℕ)
    (e : Vec d)
    (Cpos : ℝ)
    (hCpos_nonneg : 0 ≤ Cpos)
    :
    let C : ℝ := max 10 (25 * Cpos + 10)
    let β := section53CoarseFluctuationBeta hP4
    let s' := hP4.sLower + β
    let t' := hP4.sUpper + β
    let Q : TriadicCube d := originCube d (m : ℤ)
    let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let σ := sigmaHatAtScale hP hStruct (m : ℤ)
    let childAvg : RegCoeffField d → ℝ :=
      fun a => descendantsAverage Q j
        (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
    let lowerExcess : RegCoeffField d → ℝ :=
      fun a =>
        max
          ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
            (hP.barSigmaStarAtScale hStruct 0)⁻¹)
          0
    let upperExcess : RegCoeffField d → ℝ :=
      fun a =>
        max
          (Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
            hP.barSigmaAtScale hStruct 0)
          0
    let coeff : ℝ := (5 * β⁻¹) ^ 2
    ∀ (_hC_ge_pos : 25 * Cpos ≤ C),
    ∀ (_hpositiveChild : σ * (∫ a, lowerExcess a * childAvg a ∂P) +
          σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P)
        ≤
          Cpos * (hP4.xi : ℝ) *
            Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
              coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e),
    ∀ (_hUnit_nonneg : 0 ≤ coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m),
    ∀ (_hResp_nonneg : 0 ≤ coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e),
    ∀ (_hPosCore_nonneg : 0 ≤
        (hP4.xi : ℝ) *
          Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
            coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
              coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e),
    ∀ (_hβ3_inv_nonneg : 0 ≤ (β ^ 3)⁻¹),
    ∀ (_hCoeff_le_beta3 : coeff ≤ 25 * (β ^ 3)⁻¹),
    coeff *
          (σ * (∫ a, lowerExcess a * childAvg a ∂P) +
            σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P))
        ≤
          C * ((hP4.xi : ℝ) * (β ^ 3)⁻¹ *
            Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
            coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
              coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let C : ℝ := max 10 (25 * Cpos + 10)
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let childAvg : RegCoeffField d → ℝ :=
    fun a => descendantsAverage Q j
      (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
  let lowerExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct 0)⁻¹)
        0
  let upperExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        (Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct 0)
        0
  let coeff : ℝ := (5 * β⁻¹) ^ 2
  intro hC_ge_pos hpositiveChild hUnit_nonneg hResp_nonneg hPosCore_nonneg hβ3_inv_nonneg
    hCoeff_le_beta3
  calc
    coeff *
        (σ * (∫ a, lowerExcess a * childAvg a ∂P) +
          σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P))
        ≤
      coeff *
        (Cpos * (hP4.xi : ℝ) *
          Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
            coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
              coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) :=
        mul_le_mul_of_nonneg_left hpositiveChild
          (by dsimp [coeff]; positivity)
    _ =
      (coeff * Cpos) *
        ((hP4.xi : ℝ) *
          Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
            coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
              coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) := by ring
    _ ≤
      (25 * (β ^ 3)⁻¹ * Cpos) *
        ((hP4.xi : ℝ) *
          Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
            coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
              coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCoeff_le_beta3 hCpos_nonneg)
          hPosCore_nonneg
    _ =
      (25 * Cpos) *
        ((hP4.xi : ℝ) * (β ^ 3)⁻¹ *
          Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
            coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
              coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) := by ring
    _ ≤
      C * ((hP4.xi : ℝ) * (β ^ 3)⁻¹ *
        Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
        coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
          coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) := by
        have htail_nonneg :
            0 ≤ (hP4.xi : ℝ) * (β ^ 3)⁻¹ *
              Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
              coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
          exact mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (by exact_mod_cast Nat.zero_le hP4.xi)
                  hβ3_inv_nonneg)
                (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
              hUnit_nonneg)
            hResp_nonneg
        exact mul_le_mul_of_nonneg_right hC_ge_pos htail_nonneg

private theorem integrable_weightedExcessResponseProducts
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {lowerExcess upperExcess response : Ω → ℝ} {exponent order weight : ℝ}
    (hConjugate : exponent.HolderConjugate order)
    (hResponse : MemLp response (ENNReal.ofReal exponent) μ)
    (hLower : MemLp lowerExcess (ENNReal.ofReal order) μ)
    (hUpper : MemLp upperExcess (ENNReal.ofReal order) μ) :
    Integrable (fun a => lowerExcess a * response a) μ ∧
      Integrable (fun a => upperExcess a * response a) μ ∧
        Integrable (fun a =>
          (weight * lowerExcess a + weight⁻¹ * upperExcess a) * response a) μ := by
  let : ENNReal.HolderTriple (ENNReal.ofReal exponent) (ENNReal.ofReal order) 1 := by
    simpa using Real.HolderTriple.ennrealOfReal hConjugate
  have hLowerProduct : Integrable (fun a => lowerExcess a * response a) μ := by
    simpa [mul_comm] using! hResponse.integrable_mul hLower
  have hUpperProduct : Integrable (fun a => upperExcess a * response a) μ := by
    simpa [mul_comm] using! hResponse.integrable_mul hUpper
  refine ⟨hLowerProduct, hUpperProduct, ?_⟩
  refine ((hLowerProduct.const_mul weight).add
    (hUpperProduct.const_mul weight⁻¹)).congr ?_
  filter_upwards with a
  simp only [Pi.add_apply]
  ring

private theorem bound_le_commonMultiple_of_twoComponentBounds
    {value majorant baseline positive baselineBound positiveBound boundCoefficient : ℝ}
    (hMajorant : value ≤ majorant) (hSplit : majorant = baseline + positive)
    (hBaseline : baseline ≤ boundCoefficient * baselineBound)
    (hPositive : positive ≤ boundCoefficient * positiveBound) :
    value ≤ boundCoefficient * (baselineBound + positiveBound) := by
  calc
    value ≤ majorant := hMajorant
    _ = baseline + positive := hSplit
    _ ≤ boundCoefficient * baselineBound + boundCoefficient * positiveBound :=
      add_le_add hBaseline hPositive
    _ = boundCoefficient * (baselineBound + positiveBound) := by ring

private theorem mismatchManuscriptContributions_nonnegative
    {d : ℕ}
    [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k : ℕ)
    (m : ℕ)
    (e : Vec d)
    :
    let β := section53CoarseFluctuationBeta hP4
    ∀ (_hβ_pos : 0 < β),
    (0 ≤ coarseFluctuationTauSumAtScale hP hStruct hP4 k m e) ∧
      (0 ≤ coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m) ∧
      (0 ≤ coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) ∧
      (0 ≤
        (hP4.xi : ℝ) *
          Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
            coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
              coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) ∧
      (0 ≤ (β ^ 2)⁻¹) ∧
      (0 ≤ (β ^ 3)⁻¹) := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  intro hβ_pos
  have hTau_nonneg :
      0 ≤ coarseFluctuationTauSumAtScale hP hStruct hP4 k m e :=
    coarseFluctuationTauSumAtScale_nonneg hP hstat hStruct hP4 k m e
  have hUnit_nonneg :
      0 ≤ coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m :=
    coarseFluctuationUnitMomentWeightAtScale_nonneg hP hStruct hP4 m
  have hResp_nonneg :
      0 ≤ coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e :=
    coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4 k m e
  have hPosCore_nonneg :
      0 ≤
        (hP4.xi : ℝ) *
          Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
            coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
              coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by exact_mod_cast Nat.zero_le hP4.xi)
          (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
        hUnit_nonneg)
      hResp_nonneg
  have hβ2_inv_nonneg : 0 ≤ (β ^ 2)⁻¹ :=
    inv_nonneg.mpr (sq_nonneg β)
  have hβ3_inv_nonneg : 0 ≤ (β ^ 3)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg hβ_pos.le 3)
  exact ⟨hTau_nonneg, hUnit_nonneg, hResp_nonneg, hPosCore_nonneg, hβ2_inv_nonneg, hβ3_inv_nonneg⟩

private theorem weightedResponseDefectSquare_le_childResponse
    {d : ℕ}
    [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k : ℕ)
    (m : ℕ)
    (e : Vec d)
    :
    let β := section53CoarseFluctuationBeta hP4
    let Q : TriadicCube d := originCube d (m : ℤ)
    let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let S : Finset ℤ := Finset.Icc (((k : ℤ) + 1)) (m : ℤ)
    let w : ℤ → ℝ :=
      fun n => Real.rpow (3 : ℝ)
        (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
    let defectSum : RegCoeffField d → ℝ :=
      fun a =>
        ∑ n ∈ S, w n *
          Real.sqrt
            (WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e a)
    let childAvg : RegCoeffField d → ℝ :=
      fun a => descendantsAverage Q j
        (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
    let coeff : ℝ := (5 * β⁻¹) ^ 2
    ∀ (_hβ_pos : 0 < β),
    ∀ (_hβ_le_one : β ≤ 1),
    ∀ (_hk_nonneg : (0 : ℤ) ≤ (k : ℤ)),
    ∀ (_hkm_int : (k : ℤ) ≤ (m : ℤ)),
    ∀ᵐ a ∂P, (defectSum a) ^ 2 ≤ coeff * childAvg a := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let Q : TriadicCube d := originCube d (m : ℤ)
  let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let S : Finset ℤ := Finset.Icc (((k : ℤ) + 1)) (m : ℤ)
  let w : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ)
      (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
  let defectSum : RegCoeffField d → ℝ :=
    fun a =>
      ∑ n ∈ S, w n *
        Real.sqrt
          (WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  let childAvg : RegCoeffField d → ℝ :=
    fun a => descendantsAverage Q j
      (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
  let coeff : ℝ := (5 * β⁻¹) ^ 2
  intro hβ_pos hβ_le_one hk_nonneg hkm_int
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  simpa [defectSum, childAvg, coeff, S, w, Q, j, β, p_e, q_e] using
    sq_beta_weighted_sqrt_responseDefectAverageAtScale_le_childResponseAverageAtScale
      ha hk_nonneg hkm_int hβ_pos hβ_le_one p_e q_e

/-- Expectation-level conversion for the paired response-defect mismatch
squares in the weak-norm maximizer RHS. -/
theorem integral_paired_mismatchTermSquares_special_le_coarseFluctuationTerms_uniform
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (_hstat : Ch04.RestrictionStationaryLaw P)
      (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ {k m : ℕ}, k < m → ∀ e : Vec d,
        let β := section53CoarseFluctuationBeta hP4
        let s := hP4.sLower + 2 * β
        let s' := hP4.sLower + β
        let t := hP4.sUpper + 2 * β
        let t' := hP4.sUpper + β
        let p_e := specialPAtScale hP hStruct (m : ℤ) e
        let q_e := specialQAtScale hP hStruct (m : ℤ) e
        let σ := sigmaHatAtScale hP hStruct (m : ℤ)
        Integrable
            (fun a : RegCoeffField d =>
              σ *
                  (WeakNormsMaximizer.gradientMismatchTermAtScale
                    (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
                σ⁻¹ *
                  (WeakNormsMaximizer.fluxMismatchTermAtScale
                    (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) P ∧
          ∫ a,
                (σ *
                    (WeakNormsMaximizer.gradientMismatchTermAtScale
                      (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
                  σ⁻¹ *
                    (WeakNormsMaximizer.fluxMismatchTermAtScale
                      (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P
              ≤
                C *
                  ((β ^ 2)⁻¹ *
                      coarseFluctuationScalarWeightAtScale hP hStruct m *
                        coarseFluctuationTauSumAtScale hP hStruct hP4 k m e +
                    (hP4.xi : ℝ) * (β ^ 3)⁻¹ *
                      Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
                      coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                        coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) := by
  classical
  rcases ellipticityPositiveExcess_childResponseAverage_expectation_le_uniform
      params with ⟨Cpos, hCpos_nonneg, hCpos_all⟩
  let C : ℝ := max 10 (25 * Cpos + 10)
  refine ⟨C, by
    dsimp [C]
    exact le_trans (by norm_num : (0 : ℝ) ≤ 10) (le_max_left _ _), ?_⟩
  intro P hP hstat hStruct hP4 hparams k m hkm e
  subst params
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let S : Finset ℤ := Finset.Icc (((k : ℤ) + 1)) (m : ℤ)
  let w : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ)
      (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
  let defectSum : RegCoeffField d → ℝ :=
    fun a =>
      ∑ n ∈ S, w n *
        Real.sqrt
          (WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  let childAvg : RegCoeffField d → ℝ :=
    fun a => descendantsAverage Q j
      (fun R => Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
  let lowerExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct 0)⁻¹)
        0
  let upperExcess : RegCoeffField d → ℝ :=
    fun a =>
      max
        (Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct 0)
        0
  let X : RegCoeffField d → ℝ :=
    fun a =>
      σ *
          (WeakNormsMaximizer.gradientMismatchTermAtScale
            (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
        σ⁻¹ *
          (WeakNormsMaximizer.fluxMismatchTermAtScale
            (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
  let coeff : ℝ := (5 * β⁻¹) ^ 2
  let Y : RegCoeffField d → ℝ :=
    fun a =>
      coarseFluctuationScalarWeightAtScale hP hStruct m * (defectSum a) ^ 2 +
        coeff * ((σ * lowerExcess a + σ⁻¹ * upperExcess a) * childAvg a)
  have hCpos := hCpos_all hP hstat hStruct hP4 rfl hkm e
  have hC_ge_ten : 10 ≤ C := by dsimp [C]; exact le_max_left _ _
  have hC_ge_pos : 25 * Cpos ≤ C := by
    dsimp [C]
    have hle : 25 * Cpos ≤ 25 * Cpos + 10 := by linarith
    exact hle.trans (le_max_right _ _)
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hβ_le_one : β ≤ 1 := by
    have hle := sLower_add_beta_le_one hP4
    dsimp [β] at hle ⊢
    linarith [hP4.sLower_pos]
  have hs'_pos : 0 < s' := by
    dsimp [s', β]
    linarith [hP4.sLower_pos, hβ_pos]
  have ht'_pos : 0 < t' := by
    dsimp [t', β]
    linarith [hP4.sUpper_pos, hβ_pos]
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm.le
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hscalar_nonneg :
      0 ≤ coarseFluctuationScalarWeightAtScale hP hStruct m :=
    coarseFluctuationScalarWeightAtScale_nonneg hP hStruct hP4 m
  have hDsqInt := integrable_weightedResponseDefectSquare (d := d) (P := P) (hP := hP) (hstat :=
    hstat)
    (hStruct := hStruct) (hP4 := hP4) (k := k) (m := m) (e := e) hk_nonneg
  have hChildMem :
      MemLp childAvg (ENNReal.ofReal (section53CoarseFluctuationZeta hP4)) P := by
    simpa [childAvg, Q, j, p_e, q_e] using
      zeta_descendantResponseObservable_memLp_from_P4_of_stationarity
        hP hstat hStruct hP4 hk_nonneg hkm_int p_e q_e
  have hExtractedConclusion := shiftedPositiveEllipticityExcesses_memLp (d := d) (P := P) (hP := hP)
    (hStruct := hStruct) (hP4 := hP4) (m := m) hβ_pos hs'_pos ht'_pos
  rcases hExtractedConclusion with ⟨hLowerMem, hUpperMem⟩
  rcases integrable_weightedExcessResponseProducts (weight := σ)
      (holderConjugate_xi_section53CoarseFluctuationZeta hP4).symm
      hChildMem hLowerMem hUpperMem with ⟨hLowerChildInt, hUpperChildInt, hPosInt⟩
  have hYInt : Integrable Y P := by
    exact
      (hDsqInt.const_mul (coarseFluctuationScalarWeightAtScale hP hStruct m)).add
        (hPosInt.const_mul coeff)
  have hXAE := aemeasurable_pairedMismatchSquares (d := d) (P := P) (hP := hP) (hStruct := hStruct)
    (hP4 := hP4) (k := k) (m := m) (e := e) hs'_pos ht'_pos
  have hXNonneg : ∀ᵐ a ∂P, 0 ≤ X a := by
    filter_upwards with a
    dsimp [X]
    exact add_nonneg
      (mul_nonneg hσ_nonneg (sq_nonneg _))
      (mul_nonneg hσ_inv_nonneg (sq_nonneg _))
  have hDefect_le := weightedResponseDefectSquare_le_childResponse (d := d) (P := P) (hP := hP)
    (hStruct := hStruct) (hP4 := hP4) (k := k) (m := m) (e := e) hβ_pos hβ_le_one hk_nonneg
    hkm_int
  have hPoint := pairedMismatchSquares_le_defectResponseMajorant (d := d) (P := P) (hP := hP)
    (hStruct := hStruct) (hP4 := hP4) (k := k) (m := m) (e := e) hσ_nonneg hσ_inv_nonneg
    hDefect_le
  have hXInt : Integrable X P := by
    refine Integrable.mono' hYInt hXAE.aestronglyMeasurable ?_
    filter_upwards [hPoint, hXNonneg] with a hle hnonneg
    have hleXY : X a ≤ Y a := hle
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hleXY
  have hmono :
      ∫ a, X a ∂P ≤ ∫ a, Y a ∂P :=
    integral_mono_ae hXInt hYInt hPoint
  have hY_eq := integral_mismatchMajorant_eq_baseline_add_excess (d := d) (P := P) (hP := hP)
    (hStruct := hStruct) (hP4 := hP4) (k := k) (m := m) (e := e) hDsqInt hLowerChildInt
    hUpperChildInt hPosInt
  have hpositiveChild :
      σ * (∫ a, lowerExcess a * childAvg a ∂P) +
          σ⁻¹ * (∫ a, upperExcess a * childAvg a ∂P)
        ≤
          Cpos * (hP4.xi : ℝ) *
            Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
              coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
    simpa [β, s', t', Q, j, p_e, q_e, σ, childAvg, lowerExcess, upperExcess] using
      hCpos
  have hNonnegativeContributions := mismatchManuscriptContributions_nonnegative (d := d) (P :=
    P) (hP := hP)
    (hstat := hstat) (hStruct := hStruct) (hP4 := hP4) (k := k) (m := m) (e := e) hβ_pos
  rcases hNonnegativeContributions with
    ⟨hTau_nonneg, hUnit_nonneg, hResp_nonneg, hPosCore_nonneg, hβ2_inv_nonneg,
      hβ3_inv_nonneg⟩
  have hBaseline_le := integral_mismatchBaseline_le_weightedTau (d := d) (P := P) (hP := hP)
    (hstat := hstat)
    (hStruct := hStruct) (hP4 := hP4) (k := k) (m := m) (hkm := hkm) (e := e) (Cpos := Cpos)
    hC_ge_ten hβ_pos hβ_le_one hscalar_nonneg hTau_nonneg hβ2_inv_nonneg
  have hCoeff_le_beta3 := mismatchExcessCoefficient_le_inverseBetaCube (d := d) (P := P) (hP :=
    hP) (hP4 := hP4)
    hβ_pos hβ_le_one
  have hPositive_le := integral_mismatchPositiveExcess_le_responseMoment (d := d) (P := P) (hP
    := hP)
    (hStruct := hStruct) (hP4 := hP4) (k := k) (m := m) (e := e) (Cpos := Cpos)
    (hCpos_nonneg := hCpos_nonneg) hC_ge_pos hpositiveChild hUnit_nonneg hResp_nonneg
    hPosCore_nonneg hβ3_inv_nonneg hCoeff_le_beta3
  have hmain := bound_le_commonMultiple_of_twoComponentBounds
    hmono hY_eq hBaseline_le hPositive_le
  refine ⟨by exact hXInt, ?_⟩
  simpa [X, β, s, s', t, t', p_e, q_e, σ] using hmain

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end HCPolySupport
