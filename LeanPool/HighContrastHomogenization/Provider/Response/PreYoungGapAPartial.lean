/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedFiveTermProfile
public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffEnergyObservables
public import LeanPool.HighContrastHomogenization.Provider.Response.RecentDifferenceEnergyMeasurability

/-!
# High-contrast homogenization: Provider.Response.PreYoungGapAPartial

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Integrability from measurable response observables

The optimizer-energy and optimizer-readout observables used by the adapted
pre-Young decomposition are strongly measurable in the random coefficient.
This module combines those facts with explicit response domination.  The
terminal and recent-energy families build their integrable response majorants
from finite adapted means; the localized split readouts retain an abstract
integrable majorant until their quantitative weak-norm bounds are supplied.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem integrable_responseJ_of_integrableCoarseBlock
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {U : Domain d}
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d))) (p r : Vec d) :
    Integrable (fun a ↦ responseJ U (a.coeffOn U) p r) P := by
  let X : BlockVec d := (-p, r)
  have hquad := (integrable_coarseBlock_quadratic hint X).const_mul (1 / 2 : ℝ)
  have hsub := hquad.sub (integrable_const (vecDot p r))
  refine hsub.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  simpa only [X] using! (responseJ_eq_coarseBlock U a p r).symm

private theorem integrable_adjointResponseJ_of_integrableCoarseBlock
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {U : Domain d}
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d))) (p r : Vec d) :
    Integrable (fun a ↦ responseJ U (a.transpose.coeffOn U) p r) P := by
  let X : BlockVec d := (-p, r)
  let D := blockMatVecMul (blockDiag (1 : Mat d) (-1)) X
  have hquad : Integrable (fun a ↦ blockVecDot X
      (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)) P := by
    have hbase := integrable_coarseBlock_quadratic hint D
    refine hbase.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
    change blockVecDot D (blockMatVecMul (coarseBlock (U : Set (Vec d)) a) D) =
      blockVecDot X (blockMatVecMul (coarseBlock (U : Set (Vec d)) a.transpose) X)
    rw [coarseBlock_transpose a U, blockQuadratic_adjointSign_congr]
  have hsub := (hquad.const_mul (1 / 2 : ℝ)).sub (integrable_const (vecDot p r))
  refine hsub.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  simpa only [X] using! (responseJ_eq_coarseBlock U a.transpose p r).symm

private theorem integrable_responseJ_subSkew_of_integrableCoarseBlock
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {U : Domain d}
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    Integrable (fun a ↦ responseJ U ((a.subSkew g hg).coeffOn U) p r) P := by
  refine (integrable_responseJ_of_integrableCoarseBlock hint p
    (r - matVecMul g p)).congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  exact (responseJ_subSkew U a g hg p r).symm

private theorem integrable_responseJ_adjointSubSkew_of_integrableCoarseBlock
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {U : Domain d}
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    Integrable (fun a ↦ responseJ U
      ((a.subSkew g hg).transpose.coeffOn U) p r) P := by
  refine (integrable_adjointResponseJ_of_integrableCoarseBlock hint p
    (r + matVecMul g p)).congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  change responseJ U (a.transpose.coeffOn U) p (r + matVecMul g p) =
    responseJ U ((a.subSkew g hg).transpose.coeffOn U) p r
  rw [CoeffSpace.transpose_subSkew]
  have h := responseJ_subSkew U a.transpose (-g) (isSkewMat_neg hg) p r
  have hload : r - matVecMul (-g) p = r + matVecMul g p := by
    rw [neg_matVecMul, sub_neg_eq_add]
  rw [hload] at h
  exact h.symm

/-! ## Terminal cutoff-energy defects -/

/-- Measurability of the primal terminal cutoff defect and its pointwise
response domination give the literal integrability premise of the terminal
component. -/
theorem integrable_affineSubSkewCutoffEnergyDefect_of_responseJ_domination
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (hint : HasFiniteAdaptedMean P q t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (hdom : ∀ a : CoeffSpace d,
      0 ≤ average (adaptedDomain hq t) (fun x ↦
          adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
            vecDot
              ((centeredResponseOptimizer (adaptedDomain hq t)
                (a.subSkew g hg) p r).toH1.grad x)
              (matVecMul (((a.subSkew g hg).coeffOn
                (adaptedDomain hq t)).toCoeffField x)
                ((centeredResponseOptimizer (adaptedDomain hq t)
                  (a.subSkew g hg) p r).toH1.grad x)))) ∧
        average (adaptedDomain hq t) (fun x ↦
          adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
            vecDot
              ((centeredResponseOptimizer (adaptedDomain hq t)
                (a.subSkew g hg) p r).toH1.grad x)
              (matVecMul (((a.subSkew g hg).coeffOn
                (adaptedDomain hq t)).toCoeffField x)
                ((centeredResponseOptimizer (adaptedDomain hq t)
                  (a.subSkew g hg) p r).toH1.grad x)))) ≤
          2 * responseJ (adaptedDomain hq t)
            ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r) :
    Integrable (fun a ↦
      average (adaptedDomain hq t) (fun x ↦
        adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((centeredResponseOptimizer (adaptedDomain hq t)
              (a.subSkew g hg) p r).toH1.grad x)
            (matVecMul (((a.subSkew g hg).coeffOn
              (adaptedDomain hq t)).toCoeffField x)
              ((centeredResponseOptimizer (adaptedDomain hq t)
                (a.subSkew g hg) p r).toH1.grad x)))) -
        responseJ (adaptedDomain hq t)
          ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r) P := by
  let W : CoeffSpace d → ℝ := fun a ↦
    average (adaptedDomain hq t) (fun x ↦
      adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
        vecDot
          ((centeredResponseOptimizer (adaptedDomain hq t)
            (a.subSkew g hg) p r).toH1.grad x)
          (matVecMul (((a.subSkew g hg).coeffOn
            (adaptedDomain hq t)).toCoeffField x)
            ((centeredResponseOptimizer (adaptedDomain hq t)
              (a.subSkew g hg) p r).toH1.grad x))))
  let J : CoeffSpace d → ℝ := fun a ↦ responseJ (adaptedDomain hq t)
    ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r
  change Integrable (fun a ↦ W a - J a) P
  have hJ : Integrable J P :=
    integrable_responseJ_subSkew_of_integrableCoarseBlock
      (P := P) (U := adaptedDomain hq t) hint g hg p r
  have hmeas : AEStronglyMeasurable (fun a ↦ W a - J a) P := by
    simpa only [W, J] using
      Selection.aestronglyMeasurable_affineSubSkewCutoffEnergyDefect hq t P g hg p r
  refine Integrable.mono' (f := fun a ↦ W a - J a) (g := J) hJ hmeas ?_
  filter_upwards with a
  change |W a - J a| ≤ J a
  have ha := hdom a
  change 0 ≤ W a ∧ W a ≤ 2 * J a at ha
  exact abs_le.mpr
    ⟨by linarith only [ha.1], by linarith only [ha.2]⟩

/-- Measurability and response domination give the independently transposed
terminal cutoff-defect integrability premise. -/
theorem integrable_affineAdjointSubSkewCutoffEnergyDefect_of_responseJ_domination
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (hint : HasFiniteAdaptedMean P q t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (hdom : ∀ a : CoeffSpace d,
      0 ≤ average (adaptedDomain hq t) (fun x ↦
          adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
            vecDot
              ((centeredAdjointOptimizer (adaptedDomain hq t)
                (a.subSkew g hg) p r).toH1.grad x)
              (matVecMul (((a.subSkew g hg).transpose.coeffOn
                (adaptedDomain hq t)).toCoeffField x)
                ((centeredAdjointOptimizer (adaptedDomain hq t)
                  (a.subSkew g hg) p r).toH1.grad x)))) ∧
        average (adaptedDomain hq t) (fun x ↦
          adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
            vecDot
              ((centeredAdjointOptimizer (adaptedDomain hq t)
                (a.subSkew g hg) p r).toH1.grad x)
              (matVecMul (((a.subSkew g hg).transpose.coeffOn
                (adaptedDomain hq t)).toCoeffField x)
                ((centeredAdjointOptimizer (adaptedDomain hq t)
                  (a.subSkew g hg) p r).toH1.grad x)))) ≤
          2 * responseJ (adaptedDomain hq t)
            ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r) :
    Integrable (fun a ↦
      average (adaptedDomain hq t) (fun x ↦
        adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((centeredAdjointOptimizer (adaptedDomain hq t)
              (a.subSkew g hg) p r).toH1.grad x)
            (matVecMul (((a.subSkew g hg).transpose.coeffOn
              (adaptedDomain hq t)).toCoeffField x)
              ((centeredAdjointOptimizer (adaptedDomain hq t)
                (a.subSkew g hg) p r).toH1.grad x)))) -
        responseJ (adaptedDomain hq t)
          ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r) P := by
  let W : CoeffSpace d → ℝ := fun a ↦
    average (adaptedDomain hq t) (fun x ↦
      adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
        vecDot
          ((centeredAdjointOptimizer (adaptedDomain hq t)
            (a.subSkew g hg) p r).toH1.grad x)
          (matVecMul (((a.subSkew g hg).transpose.coeffOn
            (adaptedDomain hq t)).toCoeffField x)
            ((centeredAdjointOptimizer (adaptedDomain hq t)
              (a.subSkew g hg) p r).toH1.grad x))))
  let J : CoeffSpace d → ℝ := fun a ↦ responseJ (adaptedDomain hq t)
    ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r
  change Integrable (fun a ↦ W a - J a) P
  have hJ : Integrable J P :=
    integrable_responseJ_adjointSubSkew_of_integrableCoarseBlock
      (P := P) (U := adaptedDomain hq t) hint g hg p r
  have hmeas : AEStronglyMeasurable (fun a ↦ W a - J a) P := by
    simpa only [W, J] using
      Selection.aestronglyMeasurable_affineAdjointSubSkewCutoffEnergyDefect
        hq t P g hg p r
  refine Integrable.mono' (f := fun a ↦ W a - J a) (g := J) hJ hmeas ?_
  filter_upwards with a
  change |W a - J a| ≤ J a
  have ha := hdom a
  change 0 ≤ W a ∧ W a ≤ 2 * J a at ha
  exact abs_le.mpr
    ⟨by linarith only [ha.1], by linarith only [ha.2]⟩

/-! ## Recent difference energies -/

/-! ## Localized cutoff-split readouts -/

end

end HCPolySupport.HighContrast.Response
