/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.CombineFiniteQuantitative
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section56.SmallContrastAssembly.MatrixAveragePackaging
public import LeanPool.Superdiffusion.Support.HighContrast.Variance.BlockVarianceBound

/-!
# CombineFiniteTwoChannel

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open _root_.HCPolySupport.Book.Ch05.Section56.SmallContrastAssembly
  (descendantsAverageFluctuationOperatorNormSqWithNormalizer_le_probeSqBudget_ae)

/-!
# Quantitative descendant channel

This module assembles the finite quadratic probes of the relative descendant
fluctuation matrix.  The observation cube is at physical scale `n`, while its
relative centre is `n - L - c` and its children end at the fixed relative scale
`-c`.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.Book.Ch02
open _root_.HCPolySupport.Book.Ch05.Section54.VarianceBoundGoodScale
open _root_.HCPolySupport.IndependentSums
open scoped MatrixOrder

noncomputable section



/-- The finite-coordinate reconstruction of the relative descendant operator
norm.  Its right side records the exact probe bounds used by the downstream
quantitative variance assembly. -/
theorem two_mul_integral_relativeStarredDescendantOperatorNormSq_le
    {d : ℕ} [NeZero d] (M : ABKModel d) (L n : ℤ) (hLn : L ≤ n)
    {s A D : ℝ} (hs : 0 < s)
    (hLower : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L ⟨s, hs⟩) A D) :
    let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
    let P := Cutoff.relativeNormalizedCutoffLaw M L
    let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
    let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
    let center : ℤ := n - L - c
    let Q : TriadicCube d := originCube d center
    let j : ℕ := (n - L).toNat
    let sigma := Annealed.sigmaBar M L
    let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
    let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
    let Cn : BlockMat d :=
      Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
    let N : ℝ := ((descendantsAtScale Q (-c)).card : ℝ)
    let card : ℝ := Fintype.card (BlockCoord d)
    let budget : ℝ :=
      2 *
          ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
            (gammaMomentConst (1 / 2) *
              (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ)) +
        8 *
          ((gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (4 : ℕ) +
            (gammaMomentConst (1 / 2) *
              (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (4 : ℕ))
    let secondBudget : ℝ :=
      2 *
        ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
          (gammaMomentConst (1 / 2) *
            (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ))
    let probeRhs : FullBlockVec d → ℝ := fun q =>
      let probeBudget : ℝ := 6 * (dotProduct q q) ^ (2 : ℕ) * budget
      let meanBudget : ℝ :=
        4 * (dotProduct q q) ^ (2 : ℕ) * secondBudget ^ (2 : ℕ)
      let K : ℝ := Real.sqrt probeBudget
      let rootBound : ℝ :=
        N⁻¹ *
          (Book.Ch04.rosenthalDescendantsAtScaleLpConst d (-c) 2 *
                N ^ (1 / (2 : ℝ)) * K +
            Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d (-c) 2 *
                Real.sqrt N * K)
      2 * rootBound ^ (2 : ℕ) + 2 * meanBudget
    Integrable
        (starredDescendantsAverageFluctuationOperatorNormSq B Cn Q j) P ∧
      2 * ∫ a, starredDescendantsAverageFluctuationOperatorNormSq B Cn Q j a ∂P ≤
        2 * card ^ (2 : ℕ) *
          (card *
            ∑ alpha : BlockCoord d, card *
              ∑ beta : BlockCoord d, 3 *
                (probeRhs (fullBlockCoordinateProbe alpha) +
                  probeRhs (fullBlockPlusProbe alpha beta) +
                  probeRhs (fullBlockMinusProbe alpha beta))) := by
  classical
  let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
  let P := Cutoff.relativeNormalizedCutoffLaw M L
  let hP := Cutoff.relativeNormalizedCutoffLaw_lawCarrier M L
  let hStruct := Cutoff.relativeNormalizedCutoffLaw_structuralLaw M L
  let center : ℤ := n - L - c
  let Q : TriadicCube d := originCube d center
  let j : ℕ := (n - L).toNat
  let sigma := Annealed.sigmaBar M L
  let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
  let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
  let Cn : BlockMat d :=
    Book.Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
  let N : ℝ := ((descendantsAtScale Q (-c)).card : ℝ)
  let card : ℝ := Fintype.card (BlockCoord d)
  let budget : ℝ :=
    2 *
        ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
          (gammaMomentConst (1 / 2) *
            (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ)) +
      8 *
        ((gammaMomentConst 2 * (4 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (4 : ℕ) +
          (gammaMomentConst (1 / 2) *
            (4 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (4 : ℕ))
  let secondBudget : ℝ :=
    2 *
      ((gammaMomentConst 2 * (2 : ℝ) ^ ((2 : ℝ)⁻¹) * A) ^ (2 : ℕ) +
        (gammaMomentConst (1 / 2) *
          (2 : ℝ) ^ (((1 / 2 : ℝ))⁻¹) * D) ^ (2 : ℕ))
  let probeRhs : FullBlockVec d → ℝ := fun q =>
    let probeBudget : ℝ := 6 * (dotProduct q q) ^ (2 : ℕ) * budget
    let meanBudget : ℝ :=
      4 * (dotProduct q q) ^ (2 : ℕ) * secondBudget ^ (2 : ℕ)
    let K : ℝ := Real.sqrt probeBudget
    let rootBound : ℝ :=
      N⁻¹ *
        (Book.Ch04.rosenthalDescendantsAtScaleLpConst d (-c) 2 *
              N ^ (1 / (2 : ℝ)) * K +
          Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d (-c) 2 *
              Real.sqrt N * K)
    2 * rootBound ^ (2 : ℕ) + 2 * meanBudget
  dsimp only
  let S : FullBlockMat d := blockSwapMat d * CFC.sqrt B
  let Mdesc : RegCoeffField d → FullBlockMat d := fun a =>
    starredDescendantsAverageFluctuationMatrix B Cn Q j a
  have hint : ∀ q : FullBlockVec d,
      Integrable (fun a => (fullBlockQuadratic (Mdesc a) q) ^ (2 : ℕ)) P := by
    intro q
    simpa only [Mdesc, c, P, hP, hStruct, center, Q, j, sigma, a0, B,
      Cn, N, budget, secondBudget, probeRhs] using
      (relativeStarredDescendantProbe_sq_integrable_and_le
        M L n hLn hs hLower q).1
  have hbd : ∀ q : FullBlockVec d,
      (∫ a, (fullBlockQuadratic (Mdesc a) q) ^ (2 : ℕ) ∂P) ≤ probeRhs q := by
    intro q
    simpa only [Mdesc, c, P, hP, hStruct, center, Q, j, sigma, a0, B,
      Cn, N, budget, secondBudget, probeRhs] using
      (relativeStarredDescendantProbe_sq_integrable_and_le
        M L n hLn hs hLower q).2
  have hbudgetInt :=
    _root_.HCPolySupport.integrable_fullBlockProbeSqBudget
      (P := P) (M := Mdesc) hint
  have hpointRaw :=
    descendantsAverageFluctuationOperatorNormSqWithNormalizer_le_probeSqBudget_ae
        hP hStruct center S Q j
  have hpoint :
      (fun a => starredDescendantsAverageFluctuationOperatorNormSq
        B Cn Q j a) ≤ᵐ[P]
      fun a => card ^ (2 : ℕ) * fullBlockProbeSqBudget (Mdesc a) := by
    filter_upwards [hpointRaw] with a ha
    rw [starredDescendantsAverageFluctuationOperatorNormSq_eq
      hP hStruct center B Q j a]
    rw [show Mdesc a =
      Book.Ch05.Section56.descendantsAverageFluctuationMatrixWithNormalizer
        hP hStruct center S Q j a by
      exact
        starredFluctuationMatrix_eq_normalizedDescendantAverage
        hP hStruct center B Q j a]
    exact ha
  have hnonneg :
      (0 : RegCoeffField d → ℝ) ≤ᵐ[P]
        fun a => starredDescendantsAverageFluctuationOperatorNormSq
          B Cn Q j a :=
    Filter.Eventually.of_forall fun _ => pow_nonneg (norm_nonneg _) 2
  have hopMeasRaw :=
    Book.Ch05.Section56.aemeasurable_descendantsAverageFluctuationOperatorNormSqWithNormalizer
      hP hStruct center S Q j
  have hopMeas : AEMeasurable
      (starredDescendantsAverageFluctuationOperatorNormSq B Cn Q j) P := by
    refine hopMeasRaw.congr ?_
    filter_upwards with a
    exact (starredDescendantsAverageFluctuationOperatorNormSq_eq
      hP hStruct center B Q j a).symm
  have hdescInt : Integrable
      (starredDescendantsAverageFluctuationOperatorNormSq B Cn Q j) P := by
    refine Integrable.mono' (hbudgetInt.const_mul (card ^ (2 : ℕ)))
      hopMeas.aestronglyMeasurable ?_
    filter_upwards [hpoint] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact ha
    · exact pow_nonneg (norm_nonneg _) 2
  have hop :
      (∫ a, starredDescendantsAverageFluctuationOperatorNormSq B Cn Q j a ∂P) ≤
        ∫ a, card ^ (2 : ℕ) * fullBlockProbeSqBudget (Mdesc a) ∂P :=
    integral_mono_of_nonneg hnonneg (hbudgetInt.const_mul _) hpoint
  have hbudget :
      (∫ a, fullBlockProbeSqBudget (Mdesc a) ∂P) ≤
        card *
          ∑ alpha : BlockCoord d, card *
            ∑ beta : BlockCoord d, 3 *
              (probeRhs (fullBlockCoordinateProbe alpha) +
                probeRhs (fullBlockPlusProbe alpha beta) +
                probeRhs (fullBlockMinusProbe alpha beta)) := by
    rw [_root_.HCPolySupport.integral_fullBlockProbeSqBudget_eq hint]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine Finset.sum_le_sum fun alpha _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine Finset.sum_le_sum fun beta _ => ?_
    exact mul_le_mul_of_nonneg_left
      (add_le_add
        (add_le_add
          (hbd (fullBlockCoordinateProbe alpha))
          (hbd (fullBlockPlusProbe alpha beta)))
        (hbd (fullBlockMinusProbe alpha beta)))
      (by norm_num)
  refine ⟨hdescInt, ?_⟩
  calc
    2 * ∫ a, starredDescendantsAverageFluctuationOperatorNormSq B Cn Q j a ∂P
        ≤ 2 * ∫ a, card ^ (2 : ℕ) *
            fullBlockProbeSqBudget (Mdesc a) ∂P :=
          mul_le_mul_of_nonneg_left hop (by norm_num)
    _ = 2 * card ^ (2 : ℕ) *
          ∫ a, fullBlockProbeSqBudget (Mdesc a) ∂P := by
          rw [integral_const_mul]
          ring
    _ ≤ 2 * card ^ (2 : ℕ) *
          (card *
            ∑ alpha : BlockCoord d, card *
              ∑ beta : BlockCoord d, 3 *
                (probeRhs (fullBlockCoordinateProbe alpha) +
                  probeRhs (fullBlockPlusProbe alpha beta) +
                  probeRhs (fullBlockMinusProbe alpha beta))) :=
          mul_le_mul_of_nonneg_left hbudget
            (mul_nonneg (by norm_num) (sq_nonneg _))

end

end Algsuperdiff.Section3.Provider.Homogenization
