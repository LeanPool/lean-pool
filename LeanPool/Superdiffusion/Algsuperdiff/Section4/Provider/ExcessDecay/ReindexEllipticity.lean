/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ReindexSlot

/-!
# ReindexEllipticity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The child-frame coarse-graining objects at the slot `n+3`

`InteriorEllipticity` caps the two coarse-graining objects the interior chain
carries at the child cube `□_n` — the `q = 1` error at depth `0` and the
ellipticity factors inside CoarseGraining's forcing bracket — at the **proved**
slot `n+2`.  The frozen statement reads them at the slot `n+3`, so this
module re-runs the same three-step composition one scale up:

* the **frame bridge** (`InteriorGlueFrame`) is `k`-generic:
  `homogenizationErrorOnCube_parentRebasedFamily_eq_offGrid` takes the slot as
  a parameter and is an identity;
* the **off-grid cap** is `ReindexSlot`'s, at the depth-`3` factor `3^{3s/8}`
  in place of the proved depth-`2` factor `3^{s/4}` — the *only* quantitative
  cost of this file, one extra `3^{s/8} ≤ 3^{1/8}`;
* the **good event** is the `n+3` slot's own `𝒢(n+3, z; s/8, 1/2)`.

The last section re-runs the `x`-frame composition
(`InteriorEllipticitySlot.eLpNorm_sub_weaklyHarmonic_le_coarseGraining_rebased`)
at the re-based family of the **`n+3`** flux increment.

## References

* ABK26, `e.mathcalE.stability.applied`; `e.bound.Lambdas.by.Es.v2`;
  `e.homogenization.L2.interior`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 0. The comparator, in the two spellings -/

private theorem isotropicComparator_eq_scalarMatrix (sigma : PositiveScalar) :
    isotropicComparatorMatrix (d := d) sigma = scalarMatrix (d := d) (sigma : ℝ) := rfl

/-! ## 1. The frame bridge at the `n+3` re-based family -/

/-- **The child-frame `𝓔_{s/6,∞,2}` at the `n+3` family, against the anchor's
representative.** -/
theorem ae_homogenizationErrorOnCube_rebased_le_representative_addThree [NeZero d]
    (M : ABKModel d) (L n : ℤ) (z : Vec d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d, ∀ m : ℤ,
        (fun y => x + y) '' openCubeSet (originCube d n) ⊆
            ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
              openCubeSet (originCube d m) →
        Ch02.HomogenizationErrorOnCube (originCube d n) (s / 6) .infinity (.finite 2)
            (parentRebasedFamily M L (n + 3) x z omega)
            (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) ≤
          Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
            ((3 : ℝ) ^ (3 * (s / 8)) *
              fluxCorrectedErrorRepresentative M L (n + 3)
                ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega)) := by
  filter_upwards [ae_offGridChildError_le_representative_harmonicSlot_addThree M L n z hs hs1]
    with omega hall
  intro x m hgeom
  have hbase := hall x m hgeom
  rwa [homogenizationErrorOnCube_parentRebasedFamily_eq_offGrid M L (n + 3) n x z omega
    (by linarith only [hs] : (0 : ℝ) < s / 6)
    (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3)))]

/-! ## 2. The energy leg's `𝓔` factor, at the `n+3` slot -/

/-- **The `q = 1` error at depth `0` of the re-cut slot, at the anchor's
representative.** -/
theorem ae_coarseGrainingErrorAtDepth_rebased_le_representative_addThree [NeZero d]
    (M : ABKModel d) (L n : ℤ) (z : Vec d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d, ∀ m : ℤ,
        (fun y => x + y) '' openCubeSet (originCube d n) ⊆
            ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
              openCubeSet (originCube d m) →
        Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n)
            (parentRebasedFamily M L (n + 3) x z omega)
            (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) 0 ≤
          Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
            ((3 : ℝ) ^ (3 * (s / 8)) *
              fluxCorrectedErrorRepresentative M L (n + 3)
                ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega)) := by
  filter_upwards [ae_homogenizationErrorOnCube_rebased_le_representative_addThree M L n z hs hs1]
    with omega hall
  intro x m hgeom
  have hdepth := coarseGrainingHomogenizationErrorAtDepth_le (originCube d n)
    (parentRebasedFamily M L (n + 3) x z omega)
    (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (r := s / 3) (t := s / 6) 0
    (by linarith only [hs]) (by linarith only [hs])
  have hone : Real.rpow (3 : ℝ) (s / 6 * ((0 : ℕ) : ℝ)) = 1 := by
    norm_num
  rw [hone, one_mul] at hdepth
  have hmat : (scalarComparator (d := d) (Annealed.sigmaBar M (n + 3)).2).matrix =
      isotropicComparatorMatrix (d := d) (Annealed.sigmaBar M (n + 3)) := by
    rw [scalarComparator_matrix, isotropicComparator_eq_scalarMatrix]
  rw [hmat] at hdepth
  exact hdepth.trans (hall x m hgeom)

/-! ## 3. The ellipticity ratio at the child frame, `n+3` slot -/

/-- **`e.bound.Lambdas.by.Es.v2` at the child cube, in the child's own frame, at
the `n+3` slot.** -/
theorem ae_ellipticityRatio_rebased_le_representative_addThree [NeZero d] (M : ABKModel d)
    (L n : ℤ) (z : Vec d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d, ∀ m : ℤ,
        (fun y => x + y) '' openCubeSet (originCube d n) ⊆
            ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
              openCubeSet (originCube d m) →
        max (((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
              Ch02.LambdaSq (originCube d n) (s / 6) (.finite 2)
                (parentRebasedFamily M L (n + 3) x z omega))
            ((Annealed.sigmaBar M (n + 3) : ℝ) *
              (Ch02.lambdaSq (originCube d n) (s / 6) (.finite 2)
                (parentRebasedFamily M L (n + 3) x z omega))⁻¹) ≤
          2 * (d : ℝ) *
            ((Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
                ((3 : ℝ) ^ (3 * (s / 8)) *
                  fluxCorrectedErrorRepresentative M L (n + 3)
                    ⟨s / 8, by linarith only [hs]⟩
                    (Cutoff.translateCutoffSample z omega))) ^ 2 + 1) := by
  filter_upwards [ae_homogenizationErrorOnCube_rebased_le_representative_addThree M L n z hs hs1]
    with omega hall
  intro x m hgeom
  have hs6 : (0 : ℝ) < s / 6 := by linarith only [hs]
  have hratio := max_ellipticityRatio_le_homogenizationError (d := d) (originCube d n)
    (parentRebasedFamily M L (n + 3) x z omega) hs6 (Annealed.sigmaBar M (n + 3)).2
  rw [← isotropicComparator_eq_scalarMatrix] at hratio
  have hnn : 0 ≤ Ch02.HomogenizationErrorOnCube (originCube d n) (s / 6) .infinity
      (.finite 2) (parentRebasedFamily M L (n + 3) x z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) :=
    homogenizationErrorOnCube_infinity_two_nonneg (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) hs6
  exact hratio.trans (two_mul_dim_mul_sq_add_one_le_of_le hnn (hall x m hgeom))

/-! ## 4. CoarseGraining's forcing bracket at the child frame, `n+3` slot -/

/-- **The forcing bracket at the child frame, in terms of the anchor's
representative.**  The comparator's scale `σ_{n+3}` cancels between the
ellipticity factors and the matrix norm, exactly as at the proved slot. -/
theorem ae_forceBracket_rebased_le_addThree [NeZero d] (M : ABKModel d) (L n : ℤ) (z : Vec d)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d, ∀ m : ℤ,
        (fun y => x + y) '' openCubeSet (originCube d n) ⊆
            ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
              openCubeSet (originCube d m) →
        coarseGrainingForceBracket (originCube d n)
            (parentRebasedFamily M L (n + 3) x z omega)
            (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) ≤
          Real.sqrt (2 * (d : ℝ) *
                ((Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
                    ((3 : ℝ) ^ (3 * (s / 8)) *
                      fluxCorrectedErrorRepresentative M L (n + 3)
                        ⟨s / 8, by linarith only [hs]⟩
                        (Cutoff.translateCutoffSample z omega))) ^ 2 + 1)) *
              (Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
                ((3 : ℝ) ^ (3 * (s / 8)) *
                  fluxCorrectedErrorRepresentative M L (n + 3)
                    ⟨s / 8, by linarith only [hs]⟩
                    (Cutoff.translateCutoffSample z omega))) +
            2 * (2 * (d : ℝ) *
                ((Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
                    ((3 : ℝ) ^ (3 * (s / 8)) *
                      fluxCorrectedErrorRepresentative M L (n + 3)
                        ⟨s / 8, by linarith only [hs]⟩
                        (Cutoff.translateCutoffSample z omega))) ^ 2 + 1)) := by
  filter_upwards [ae_coarseGrainingErrorAtDepth_rebased_le_representative_addThree M L n z hs hs1,
    ae_ellipticityRatio_rebased_le_representative_addThree M L n z hs hs1] with omega herr hratio
  intro x m hgeom
  have hs6 : (0 : ℝ) < s / 6 := by linarith only [hs]
  set A : Ch03.CoeffFamily d := parentRebasedFamily M L (n + 3) x z omega with hAdef
  set sig : ℝ := (Annealed.sigmaBar M (n + 3) : ℝ) with hsigdef
  have hsig : 0 < sig := (Annealed.sigmaBar M (n + 3)).2
  set Eb : ℝ := Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
      ((3 : ℝ) ^ (3 * (s / 8)) *
        fluxCorrectedErrorRepresentative M L (n + 3) ⟨s / 8, by linarith only [hs]⟩
          (Cutoff.translateCutoffSample z omega)) with hEbdef
  set Kb : ℝ := 2 * (d : ℝ) * (Eb ^ 2 + 1) with hKbdef
  have hKb : 0 ≤ Kb := by
    rw [hKbdef]
    have h1 : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ Eb ^ 2 + 1 := by positivity
    exact mul_nonneg h1 h2
  have hlam : 0 < Ch02.lambdaSq (originCube d n) (s / 6) (.finite 2) A :=
    Ch02.lambdaSq_finite_pos (originCube d n) A hs6 (by norm_num)
  have hLam : 0 < Ch02.LambdaSq (originCube d n) (s / 6) (.finite 2) A :=
    Ch02.LambdaSq_finite_pos (originCube d n) A hs6 (by norm_num)
  have hrat := hratio x m hgeom
  have h1 : sig⁻¹ * Ch02.LambdaSq (originCube d n) (s / 6) (.finite 2) A ≤ Kb :=
    le_trans (le_max_left _ _) hrat
  have h2 : sig * (Ch02.lambdaSq (originCube d n) (s / 6) (.finite 2) A)⁻¹ ≤ Kb :=
    le_trans (le_max_right _ _) hrat
  have hErrDepth := herr x m hgeom
  have hErrDepthNn : 0 ≤ Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n) A
      (scalarComparator (d := d) hsig) (s / 3) 0 :=
    coarseGrainingHomogenizationErrorAtDepth_nonneg (originCube d n) A _
      (by linarith only [hs]) 0
  have hprodInv : Ch02.LambdaSq (originCube d n) (s / 6) (.finite 2) A *
      (Ch02.lambdaSq (originCube d n) (s / 6) (.finite 2) A)⁻¹ ≤ Kb * Kb := by
    have heq : Ch02.LambdaSq (originCube d n) (s / 6) (.finite 2) A *
        (Ch02.lambdaSq (originCube d n) (s / 6) (.finite 2) A)⁻¹ =
        (sig⁻¹ * Ch02.LambdaSq (originCube d n) (s / 6) (.finite 2) A) *
          (sig * (Ch02.lambdaSq (originCube d n) (s / 6) (.finite 2) A)⁻¹) := by
      field_simp
    rw [heq]
    exact mul_le_mul h1 h2 (mul_nonneg hsig.le (inv_pos.mpr hlam).le)
      (le_trans (mul_nonneg (inv_pos.mpr hsig).le hLam.le) h1)
  have hT2 : Ch03.poincareUpperEllipticityFactor (originCube d n) A (s / 6) (.finite 2) *
      Ch03.poincareLowerEllipticityFactor (originCube d n) A (s / 6) (.finite 2) ≤ Kb := by
    rw [Ch03.poincareUpperEllipticityFactor, Ch03.poincareLowerEllipticityFactor,
      rpow_half_eq_sqrt, rpow_neg_half_eq_sqrt_inv hlam,
      ← Real.sqrt_mul hLam.le]
    refine le_trans (Real.sqrt_le_sqrt hprodInv) ?_
    rw [show Kb * Kb = Kb ^ (2 : ℕ) by ring, Real.sqrt_sq hKb]
  have hT3 : Ch03.constantCoeffMatrixNorm (scalarComparator (d := d) hsig) *
      Real.rpow (Ch02.lambdaSq (originCube d n) (s / 6) (.finite 2) A) (-1 : ℝ) ≤ Kb := by
    rw [constantCoeffMatrixNorm_scalarComparator hsig, rpow_neg_one_eq_inv hlam]
    exact h2
  have hT1 : Ch03.constantCoeffMatrixNormHalf (scalarComparator (d := d) hsig) *
      Ch03.poincareLowerEllipticityFactor (originCube d n) A (s / 6) (.finite 2) *
      Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n) A
        (scalarComparator (d := d) hsig) (s / 3) 0 ≤
      Real.sqrt Kb * Eb := by
    have hhalf : Ch03.constantCoeffMatrixNormHalf (scalarComparator (d := d) hsig) *
        Ch03.poincareLowerEllipticityFactor (originCube d n) A (s / 6) (.finite 2) ≤
        Real.sqrt Kb := by
      rw [constantCoeffMatrixNormHalf_scalarComparator hsig,
        Ch03.poincareLowerEllipticityFactor, rpow_half_eq_sqrt,
        rpow_neg_half_eq_sqrt_inv hlam, ← Real.sqrt_mul hsig.le]
      exact Real.sqrt_le_sqrt h2
    exact mul_le_mul hhalf hErrDepth hErrDepthNn (Real.sqrt_nonneg _)
  rw [coarseGrainingForceBracket, show s / 3 / 2 = s / 6 by ring]
  linarith only [hT1, hT2, hT3]

/-! ## 5. The `x`-frame composition at the `n+3` re-based family -/

/-- **The `x`-frame composition at the `n+3` re-based family and the re-cut
slot.**

`InteriorEllipticitySlot.eLpNorm_sub_weaklyHarmonic_le_coarseGraining_rebased`
with the family's slot moved from `n+2` to `n+3`. -/
theorem eLpNorm_sub_weaklyHarmonic_le_coarseGraining_rebased_addThree [NeZero d]
    (M : ABKModel d) (L : ℤ) (omega : Cutoff.CutoffSample d) {s : ℝ} (hs : 0 < s)
    (hs1 : s ≤ 1) {n m : ℤ} {x z : Vec d}
    (hsub : translateSet x (openCubeSet (originCube d n)) ⊆
      openCubeSet (originCube d m))
    (u hdat : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
    (hsol : Support.IsDirichletSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m) u hdat g)
    (hgL2 : MemLp g 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
    (hgW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))))
    (v : H1Function ((fun y => x + y) '' openCubeSet (originCube d n)))
    (w : H10Function ((fun y => x + y) '' openCubeSet (originCube d n)))
    (hharm : Support.IsWeaklyHarmonicOn
      ((fun y => x + y) '' openCubeSet (originCube d n)) v)
    (hval : ∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y)
    (hgrad : ∀ y, v.grad y = u.grad y - w.toH1Function.grad y)
    {sigma0 : ℝ} (hsigma0 : 0 < sigma0) :
    sigma0 * (cubeBesovScaleWeight (1 : ℝ) (originCube d n) *
        (eLpNorm (fun y => u.toFun y - v.toFun y) 2
          (Support.normalizedVolumeMeasureOn
            ((fun y => x + y) '' openCubeSet (originCube d n)))).toReal) ≤
      3 * negNormBaseConst d * coarseGrainingP2Const d *
          (216 * (s⁻¹) ^ (4 : ℕ) *
              coarseGrainingEnergyTerm (originCube d n)
                (parentRebasedFamily M L (n + 3) x z omega) (scalarComparator hsigma0)
                (s / 3)
                (H1Function.untranslate x
                  (u.restrict (isOpen_translateSet_openCubeSet x n) hsub)) +
            1944 * (s⁻¹) ^ (6 : ℕ) *
              coarseGrainingForceTerm (originCube d n)
                (parentRebasedFamily M L (n + 3) x z omega) (scalarComparator hsigma0)
                (s / 3) s (fun y => -g (y + x))) +
        interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) *
          Real.rpow (3 : ℝ) (s * (n : ℝ)) *
          (Support.normalizedGagliardoESeminormOn
            ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal := by
  have hsubimg : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      openCubeSet (originCube d m) := by
    rw [image_add_eq_translateSet x (openCubeSet (originCube d n))]
    exact hsub
  have hgL2child := memLp_two_child_of_clause_iv hsubimg hgL2
  have hgWchild := memLp_two_gagliardo_child_of_clause_iv hsubimg hgW
  have hforce : Ch03.ForceBesovRegularity (originCube d n) s (fun y => -g (y + x)) :=
    forceBesovRegularity_translated_neg (originCube d n) hs hs1 hgL2child hgWchild
  have heq := isForcedEquation_parentRebasedFamily (k := n + 3) M L x z omega hsub hsol.2
  have hmain := coarseGraining_l2_thirdSlot_harmonic_le hsigma0 heq hs hs1 hforce
  have hlhs : cubeLpNorm (originCube d n) (2 : ℝ≥0∞)
      (fun y =>
        (harmonicCorrector (scalarComparator hsigma0)
          (H1Function.untranslate x
            (u.restrict (isOpen_translateSet_openCubeSet x n) hsub))).toH1Function.toFun
          y) =
      (eLpNorm (fun y => u.toFun y - v.toFun y) 2
        (Support.normalizedVolumeMeasureOn
          ((fun y => x + y) '' openCubeSet (originCube d n)))).toReal := by
    show (eLpNorm _ (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d n))).toReal = _
    exact congrArg ENNReal.toReal
      (eLpNorm_sub_weaklyHarmonic_eq_harmonicCorrector hsigma0
        (image_add_eq_translateSet x (openCubeSet (originCube d n))) hsub u v w hharm
        hval hgrad).symm
  have hmain' := hlhs ▸ hmain
  refine hmain'.trans (add_le_add le_rfl ?_)
  exact correctionLeg_le_anchorGagliardo n hs hs1 hgL2child hgWchild

end

end Algsuperdiff.Section4.Provider.ExcessDecay
