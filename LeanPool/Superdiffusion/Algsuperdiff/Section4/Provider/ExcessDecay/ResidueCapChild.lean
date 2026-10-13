/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ReindexEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueCapGeometry

/-!
# ResidueCapChild

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The child cube's cap family, re-cut at hinge (C)

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## What is proved

`ReindexSlot.ae_offGridChildError_le_representative_harmonicSlot_addThree` and the
four caps built on it in `ReindexEllipticity` (§1--§4) are stated at the
anchor's geometry binder `x + □_n ⊆ (z+□_{n+1}) ∩ □_m`.  Their proofs use that
binder for exactly one thing: the half-open containment

```text
  (C)   translateSet (x − z) (cubeSet □_n) ⊆ cubeSet □_{n+3} .
```

This module restates the five caps with `(C)` itself as the binder.  Each is a
*strict generalization* of the proved statement — the proved one is recovered
by `translateSet_cubeSet_subset_of_anchorGeometry` composed with the half-open
nesting `cubeSet_originCube_add_two_subset` — and each proof is the proved
proof with the hinge supplied rather than derived.  The point is
`ResidueCapGeometry.translateSet_cubeSet_flushSubCube_subset_anchorParent`:
the flush sub-cube `K'`, which provably fails the anchor's binder
(`ResidueAbsorption`), satisfies `(C)`.

## References

* ABK26, `e.mathcalE.stability.applied`; `e.bound.Lambdas.by.Es.v2`;
  `p.general.coarse.graining`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem isotropicComparator_eq_scalarMatrix_child (sigma : PositiveScalar) :
    isotropicComparatorMatrix (d := d) sigma = scalarMatrix (d := d) (sigma : ℝ) := rfl

/-- The scale gap of the `(n+3)`/`n` parent/child pair. -/
private theorem originCube_scale_gap_three_child (n : ℤ) :
    ((originCube d (n + 3)).scale - (originCube d n).scale).toNat = 3 := by
  have h : (originCube d (n + 3)).scale - (originCube d n).scale = 3 := by
    simp only [originCube]
    ring
  rw [h]
  rfl

/-! ## 1. The off-grid child error, at hinge (C) -/

/-- **The off-grid child error against the `(n+3)` representative, at hinge
(C).**

`ReindexSlot.ae_offGridChildError_le_representative_harmonicSlot_addThree`, with the
anchor's geometry binder replaced by the half-open containment it is used to
prove.  Nothing else changes; the depth factor is still `3^{3s/8}`. -/
theorem ae_offGridChildError_le_representative_gapThree [NeZero d]
    (M : ABKModel d) (L n : ℤ) (z : Vec d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d,
        translateSet (x - z) (cubeSet (originCube d n)) ⊆
            cubeSet (originCube d (n + 3)) →
        offGridErrorFunctional (x - z) (originCube d n) (s / 6)
            (fluxCorrectedRegField M L (n + 3) (originCube d (n + 3))
              (Cutoff.translateCutoffSample z omega)).toFun
            (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) ≤
          Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
            ((3 : ℝ) ^ (3 * (s / 8)) *
              fluxCorrectedErrorRepresentative M L (n + 3)
                ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega)) := by
  have hbase := (GoodEvents.measurePreserving_translateCutoffSample M
      z).quasiMeasurePreserving.ae
    (ae_offGridErrorFunctional_le_fluxCorrectedErrorFunctionalAtRoot
      M L (n + 3) (originCube d (n + 3))
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3)))
      (by linarith only [hs] : (0 : ℝ) < s / 8)
      (by linarith only [hs] : s / 8 < s / 6)
      (by linarith only [hs1] : s / 6 ≤ 1 / 2))
  filter_upwards [hbase] with omega hall
  intro x hcontain
  have hstep := hall (x - z) (originCube d n) (originCube d (n + 3)) hcontain
  rw [originCube_scale_gap_three_child (d := d) n,
    fluxCorrectedErrorFunctionalAtRoot_eq_representative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩] at hstep
  have hexp : (s / 8 * ((3 : ℕ) : ℝ)) = 3 * (s / 8) := by
    push_cast
    ring
  rwa [hexp] at hstep

/-! ## 2. The frame bridge at hinge (C) -/

/-- **The child-frame `𝓔_{s/6,∞,2}` at the `n+3` family, at hinge (C).** -/
theorem ae_homogenizationErrorOnCube_rebased_le_representative_gapThree [NeZero d]
    (M : ABKModel d) (L n : ℤ) (z : Vec d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d,
        translateSet (x - z) (cubeSet (originCube d n)) ⊆
            cubeSet (originCube d (n + 3)) →
        Ch02.HomogenizationErrorOnCube (originCube d n) (s / 6) .infinity (.finite 2)
            (parentRebasedFamily M L (n + 3) x z omega)
            (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) ≤
          Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
            ((3 : ℝ) ^ (3 * (s / 8)) *
              fluxCorrectedErrorRepresentative M L (n + 3)
                ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega)) := by
  filter_upwards [ae_offGridChildError_le_representative_gapThree M L n z hs hs1]
    with omega hall
  intro x hcontain
  have hbase := hall x hcontain
  rwa [homogenizationErrorOnCube_parentRebasedFamily_eq_offGrid M L (n + 3) n x z omega
    (by linarith only [hs] : (0 : ℝ) < s / 6)
    (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3)))]

/-! ## 3. The energy leg's `𝓔` factor at hinge (C) -/

/-- **The `q = 1` error at depth `0` of the re-cut slot, at hinge (C).** -/
theorem ae_coarseGrainingErrorAtDepth_rebased_le_representative_gapThree [NeZero d]
    (M : ABKModel d) (L n : ℤ) (z : Vec d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d,
        translateSet (x - z) (cubeSet (originCube d n)) ⊆
            cubeSet (originCube d (n + 3)) →
        Ch03.coarseGrainingHomogenizationErrorAtDepth (originCube d n)
            (parentRebasedFamily M L (n + 3) x z omega)
            (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) 0 ≤
          Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
            ((3 : ℝ) ^ (3 * (s / 8)) *
              fluxCorrectedErrorRepresentative M L (n + 3)
                ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega)) := by
  filter_upwards [ae_homogenizationErrorOnCube_rebased_le_representative_gapThree
    M L n z hs hs1] with omega hall
  intro x hcontain
  have hdepth := coarseGrainingHomogenizationErrorAtDepth_le (originCube d n)
    (parentRebasedFamily M L (n + 3) x z omega)
    (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (r := s / 3) (t := s / 6) 0
    (by linarith only [hs]) (by linarith only [hs])
  have hone : Real.rpow (3 : ℝ) (s / 6 * ((0 : ℕ) : ℝ)) = 1 := by
    norm_num
  rw [hone, one_mul] at hdepth
  have hmat : (scalarComparator (d := d) (Annealed.sigmaBar M (n + 3)).2).matrix =
      isotropicComparatorMatrix (d := d) (Annealed.sigmaBar M (n + 3)) := by
    rw [scalarComparator_matrix, isotropicComparator_eq_scalarMatrix_child]
  rw [hmat] at hdepth
  exact hdepth.trans (hall x hcontain)

/-! ## 4. The ellipticity ratio at hinge (C) -/

/-- **`e.bound.Lambdas.by.Es.v2` at the child cube, in the child's own frame, at
hinge (C).** -/
theorem ae_ellipticityRatio_rebased_le_representative_gapThree [NeZero d]
    (M : ABKModel d) (L n : ℤ) (z : Vec d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d,
        translateSet (x - z) (cubeSet (originCube d n)) ⊆
            cubeSet (originCube d (n + 3)) →
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
  filter_upwards [ae_homogenizationErrorOnCube_rebased_le_representative_gapThree
    M L n z hs hs1] with omega hall
  intro x hcontain
  have hs6 : (0 : ℝ) < s / 6 := by linarith only [hs]
  have hratio := max_ellipticityRatio_le_homogenizationError (d := d) (originCube d n)
    (parentRebasedFamily M L (n + 3) x z omega) hs6 (Annealed.sigmaBar M (n + 3)).2
  rw [← isotropicComparator_eq_scalarMatrix_child] at hratio
  have hnn : 0 ≤ Ch02.HomogenizationErrorOnCube (originCube d n) (s / 6) .infinity
      (.finite 2) (parentRebasedFamily M L (n + 3) x z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) :=
    homogenizationErrorOnCube_infinity_two_nonneg (originCube d n)
      (parentRebasedFamily M L (n + 3) x z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) hs6
  exact hratio.trans (two_mul_dim_mul_sq_add_one_le_of_le hnn (hall x hcontain))

/-! ## 5. CoarseGraining's forcing bracket at hinge (C) -/

/-- **The forcing bracket at the child frame, at hinge (C).**  The comparator's
scale `σ_{n+3}` cancels between the ellipticity factors and the matrix norm,
exactly as at the proved slot. -/
theorem ae_forceBracket_rebased_le_gapThree [NeZero d] (M : ABKModel d) (L n : ℤ)
    (z : Vec d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d,
        translateSet (x - z) (cubeSet (originCube d n)) ⊆
            cubeSet (originCube d (n + 3)) →
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
  filter_upwards [ae_coarseGrainingErrorAtDepth_rebased_le_representative_gapThree
      M L n z hs hs1,
    ae_ellipticityRatio_rebased_le_representative_gapThree M L n z hs hs1]
    with omega herr hratio
  intro x hcontain
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
  have hrat := hratio x hcontain
  have h1 : sig⁻¹ * Ch02.LambdaSq (originCube d n) (s / 6) (.finite 2) A ≤ Kb :=
    le_trans (le_max_left _ _) hrat
  have h2 : sig * (Ch02.lambdaSq (originCube d n) (s / 6) (.finite 2) A)⁻¹ ≤ Kb :=
    le_trans (le_max_right _ _) hrat
  have hErrDepth := herr x hcontain
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

/-! ## 6. The proved statements, recovered -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
