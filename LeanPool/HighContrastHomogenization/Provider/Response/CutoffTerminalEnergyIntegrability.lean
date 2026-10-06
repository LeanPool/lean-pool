/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseAdjointAnnealed
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewResponse
public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffEnergyObservables
public import LeanPool.HighContrastHomogenization.Provider.Response.VariationalIdentities

/-!
# High-contrast homogenization: Provider.Response.CutoffTerminalEnergyIntegrability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Integrability of the terminal cutoff energy

The adapted cutoff lies between zero and two.  Its weighted optimizer energy
is therefore bounded by twice the full optimizer energy, whose value is the
response functional.  A finite terminal coarse-block moment then supplies the
integrable majorant for both the primal and independently transposed problems.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory
open Book.Ch05.Section53.JUpperBoundWeakNorms

noncomputable section

variable {d : ℕ}

private theorem cutoffWeightedHalfEnergy_nonneg_le_two_responseJ
    {U : Domain d} (a : CoeffOn U) (p r : Vec d) (v : Solution U a)
    (hv : Book.Ch02.IsResponseMaximizer U a p r v) (phi : Vec d → ℝ)
    (hphiMeas : AEStronglyMeasurable phi
      (volumeMeasureOn (U : Set (Vec d))))
    (hphiNonneg : ∀ x, 0 ≤ phi x) (hphiLe : ∀ x, phi x ≤ 2) :
    0 ≤ average U (fun x ↦ phi x * ((1 / 2 : ℝ) *
        vecDot (v.toH1.grad x)
          (matVecMul (a.toCoeffField x) (v.toH1.grad x)))) ∧
      average U (fun x ↦ phi x * ((1 / 2 : ℝ) *
        vecDot (v.toH1.grad x)
          (matVecMul (a.toCoeffField x) (v.toH1.grad x)))) ≤
        2 * responseJ U a p r := by
  let F : Vec d → ℝ := fun x ↦ (1 / 2 : ℝ) *
    vecDot (v.toH1.grad x) (matVecMul (a.toCoeffField x) (v.toH1.grad x))
  have hFIntegrable : IntegrableOn F (U : Set (Vec d)) volume := by
    have henergy :=
      (ch02_variationEnergyIntegrand_integrableOn U a v).const_mul (1 / 2 : ℝ)
    refine IntegrableOn.congr_fun henergy ?_ U.measurableSet
    intro x _
    dsimp only [F, variationEnergyIntegrand]
    rw [vecDot_matVecMul_symmPart]
  have hFNonneg : 0 ≤ᵐ[volumeMeasureOn (U : Set (Vec d))] F := by
    filter_upwards [a.aeElliptic] with x hx
    have hlower := lowerBound_symmPart_of_isEllipticMatrix hx (v.toH1.grad x)
    have hbase : 0 ≤ a.lam * vecNormSq (v.toH1.grad x) :=
      mul_nonneg hx.1.le (vecNormSq_nonneg _)
    have hsymm : 0 ≤ vecDot (v.toH1.grad x)
        (matVecMul (symmPart (a.toCoeffField x)) (v.toH1.grad x)) :=
      hbase.trans hlower
    have hraw : 0 ≤ vecDot (v.toH1.grad x)
        (matVecMul (a.toCoeffField x) (v.toH1.grad x)) := by
      rwa [vecDot_matVecMul_symmPart] at hsymm
    exact mul_nonneg (by norm_num) hraw
  have hphiBound : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)), ‖phi x‖ ≤ 2 :=
    _root_.Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_of_nonneg (hphiNonneg x)]
      exact hphiLe x
  have hweightedIntegrable :
      IntegrableOn (fun x ↦ phi x * F x) (U : Set (Vec d)) volume :=
    hFIntegrable.bdd_mul hphiMeas hphiBound
  have hweightedNonneg :
      0 ≤ᵐ[volumeMeasureOn (U : Set (Vec d))] fun x ↦ phi x * F x :=
    hFNonneg.mono fun x hx ↦ mul_nonneg (hphiNonneg x) hx
  have hweightedLe :
      (fun x ↦ phi x * F x) ≤ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x ↦ 2 * F x :=
    hFNonneg.mono fun x hx ↦ mul_le_mul_of_nonneg_right (hphiLe x) hx
  have hvolumeNonneg :
      0 ≤ (volume (U : Set (Vec d))).toReal⁻¹ :=
    inv_nonneg.mpr ENNReal.toReal_nonneg
  have haverageNonneg : 0 ≤ average U (fun x ↦ phi x * F x) := by
    unfold Book.Ch02.average
    exact mul_nonneg hvolumeNonneg (integral_nonneg_of_ae hweightedNonneg)
  have hintegral := integral_mono_ae hweightedIntegrable
    (hFIntegrable.const_mul 2) hweightedLe
  have haverageLe : average U (fun x ↦ phi x * F x) ≤ 2 * average U F := by
    unfold Book.Ch02.average
    calc
      (volume (U : Set (Vec d))).toReal⁻¹ *
            ∫ x in (U : Set (Vec d)), phi x * F x ∂volume ≤
          (volume (U : Set (Vec d))).toReal⁻¹ *
            ∫ x in (U : Set (Vec d)), 2 * F x ∂volume :=
        mul_le_mul_of_nonneg_left hintegral hvolumeNonneg
      _ = 2 * ((volume (U : Set (Vec d))).toReal⁻¹ *
            ∫ x in (U : Set (Vec d)), F x ∂volume) := by
        rw [integral_const_mul]
        ring
  have hFFormula : F = fun x ↦
      (1 / 2 : ℝ) * variationEnergyIntegrand U a v x := by
    funext x
    dsimp only [F, variationEnergyIntegrand]
    rw [vecDot_matVecMul_symmPart]
  have haverageF : average U F = (1 / 2 : ℝ) * variationEnergyValue U a v := by
    rw [hFFormula]
    unfold variationEnergyValue Book.Ch02.average
    rw [integral_const_mul]
    ring
  have haverageResponse : average U F = responseJ U a p r :=
    haverageF.trans (responseJ_eq_energy a hv).symm
  change 0 ≤ average U (fun x ↦ phi x * F x) ∧
    average U (fun x ↦ phi x * F x) ≤ 2 * responseJ U a p r
  exact ⟨haverageNonneg, haverageLe.trans_eq (congrArg (2 * ·) haverageResponse)⟩

/-- The cutoff-weighted primal terminal energy lies between zero and twice
the terminal response value. -/
theorem cutoffWeightedTerminalEnergy_nonneg_le_two_responseJ [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d) (p r : Vec d) :
    0 ≤ average (adaptedDomain hq t) (fun x ↦
        adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((centeredResponseOptimizer (adaptedDomain hq t) a p r).toH1.grad x)
            (matVecMul ((a.coeffOn (adaptedDomain hq t)).toCoeffField x)
              ((centeredResponseOptimizer
                (adaptedDomain hq t) a p r).toH1.grad x)))) ∧
      average (adaptedDomain hq t) (fun x ↦
        adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((centeredResponseOptimizer (adaptedDomain hq t) a p r).toH1.grad x)
            (matVecMul ((a.coeffOn (adaptedDomain hq t)).toCoeffField x)
              ((centeredResponseOptimizer
                (adaptedDomain hq t) a p r).toH1.grad x)))) ≤
        2 * responseJ (adaptedDomain hq t) (a.coeffOn (adaptedDomain hq t)) p r := by
  exact cutoffWeightedHalfEnergy_nonneg_le_two_responseJ
    (a.coeffOn (adaptedDomain hq t)) p r
    (centeredResponseOptimizer (adaptedDomain hq t) a p r)
    (centeredResponseOptimizer_isMaximizer (adaptedDomain hq t) a p r)
    (adaptedPreYoungCutoff q hq t)
    (adaptedPreYoungCutoff_smooth hq t).continuous.aestronglyMeasurable
    (adaptedPreYoungCutoff_nonneg hq t)
    (adaptedPreYoungCutoff_le_two hq t)

/-- The independently transposed cutoff-weighted terminal energy has the same
response-value domination. -/
theorem cutoffWeightedTerminalAdjointEnergy_nonneg_le_two_responseJ [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d) (p r : Vec d) :
    0 ≤ average (adaptedDomain hq t) (fun x ↦
        adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((centeredAdjointOptimizer (adaptedDomain hq t) a p r).toH1.grad x)
            (matVecMul ((a.transpose.coeffOn (adaptedDomain hq t)).toCoeffField x)
              ((centeredAdjointOptimizer
                (adaptedDomain hq t) a p r).toH1.grad x)))) ∧
      average (adaptedDomain hq t) (fun x ↦
        adaptedPreYoungCutoff q hq t x * ((1 / 2 : ℝ) *
          vecDot
            ((centeredAdjointOptimizer (adaptedDomain hq t) a p r).toH1.grad x)
            (matVecMul ((a.transpose.coeffOn (adaptedDomain hq t)).toCoeffField x)
              ((centeredAdjointOptimizer
                (adaptedDomain hq t) a p r).toH1.grad x)))) ≤
        2 * responseJ (adaptedDomain hq t)
          (a.transpose.coeffOn (adaptedDomain hq t)) p r := by
  exact cutoffWeightedHalfEnergy_nonneg_le_two_responseJ
    (a.transpose.coeffOn (adaptedDomain hq t)) p r
    (centeredAdjointOptimizer (adaptedDomain hq t) a p r)
    (centeredAdjointOptimizer_isMaximizer (adaptedDomain hq t) a p r)
    (adaptedPreYoungCutoff q hq t)
    (adaptedPreYoungCutoff_smooth hq t).continuous.aestronglyMeasurable
    (adaptedPreYoungCutoff_nonneg hq t)
    (adaptedPreYoungCutoff_le_two hq t)

private theorem integrable_responseJ_of_finiteAdaptedMean
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (hint : HasFiniteAdaptedMean P q t)
    (p r : Vec d) :
    Integrable (fun a ↦ responseJ (adaptedDomain hq t)
      (a.coeffOn (adaptedDomain hq t)) p r) P := by
  let X : BlockVec d := (-p, r)
  have hquad := (integrable_coarseBlock_quadratic hint X).const_mul (1 / 2 : ℝ)
  have hsub := hquad.sub (integrable_const (vecDot p r))
  refine hsub.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  simpa only [X, adaptedDomain_carrier, Pi.sub_apply] using
    (responseJ_eq_coarseBlock (adaptedDomain hq t) a p r).symm

private theorem integrable_adjointResponseJ_of_finiteAdaptedMean
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (hint : HasFiniteAdaptedMean P q t)
    (p r : Vec d) :
    Integrable (fun a ↦ responseJ (adaptedDomain hq t)
      (a.transpose.coeffOn (adaptedDomain hq t)) p r) P := by
  let X : BlockVec d := (-p, r)
  let D := blockMatVecMul (blockDiag (1 : Mat d) (-1)) X
  have hquad : Integrable (fun a ↦ blockVecDot X
      (blockMatVecMul (coarseBlock (adaptedCell q t) a.transpose) X)) P := by
    have hbase := integrable_coarseBlock_quadratic hint D
    refine hbase.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
    change blockVecDot D (blockMatVecMul (coarseBlock (adaptedCell q t) a) D) =
      blockVecDot X (blockMatVecMul (coarseBlock (adaptedCell q t) a.transpose) X)
    rw [← adaptedDomain_carrier hq t, coarseBlock_transpose a,
      blockQuadratic_adjointSign_congr]
  have hsub := (hquad.const_mul (1 / 2 : ℝ)).sub
    (integrable_const (vecDot p r))
  refine hsub.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  simpa only [X, adaptedDomain_carrier, Pi.sub_apply] using
    (responseJ_eq_coarseBlock (adaptedDomain hq t) a.transpose p r).symm

private theorem integrable_responseJ_subSkew_of_finiteAdaptedMean
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (hint : HasFiniteAdaptedMean P q t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    Integrable (fun a ↦ responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r) P := by
  refine (integrable_responseJ_of_finiteAdaptedMean hq t hint p
    (r - matVecMul g p)).congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  exact (responseJ_subSkew (adaptedDomain hq t) a g hg p r).symm

private theorem integrable_adjointResponseJ_subSkew_of_finiteAdaptedMean
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (hint : HasFiniteAdaptedMean P q t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
    Integrable (fun a ↦ responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r) P := by
  refine (integrable_adjointResponseJ_of_finiteAdaptedMean hq t hint p
    (r + matVecMul g p)).congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  change responseJ (adaptedDomain hq t) (a.transpose.coeffOn (adaptedDomain hq t))
      p (r + matVecMul g p) = responseJ (adaptedDomain hq t)
        ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r
  rw [CoeffSpace.transpose_subSkew]
  have h := responseJ_subSkew (adaptedDomain hq t) a.transpose (-g)
    (isSkewMat_neg hg) p r
  have hload : r - matVecMul (-g) p = r + matVecMul g p := by
    rw [neg_matVecMul, sub_neg_eq_add]
  rw [hload] at h
  exact h.symm

/-- A terminal coarse-block moment gives the exact primal cutoff-defect
integrability premise of the cutoff component. -/
theorem integrable_cutoffWeightedTerminalEnergyDefect_subSkew [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (hint : HasFiniteAdaptedMean P q t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
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
  apply (integrable_responseJ_subSkew_of_finiteAdaptedMean
    hq t hint g hg p r).mono'
      (Selection.aestronglyMeasurable_affineSubSkewCutoffEnergyDefect hq t P g hg p r)
  filter_upwards with a
  have hbound := cutoffWeightedTerminalEnergy_nonneg_le_two_responseJ
    hq t (a.subSkew g hg) p r
  rw [Real.norm_eq_abs]
  exact abs_le.mpr
    ⟨by linarith only [hbound.1], by linarith only [hbound.2]⟩

/-- The same terminal moment gives the literal independently transposed
cutoff-defect integrability. -/
theorem integrable_cutoffWeightedTerminalAdjointEnergyDefect_subSkew [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (hint : HasFiniteAdaptedMean P q t)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) :
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
  apply (integrable_adjointResponseJ_subSkew_of_finiteAdaptedMean
    hq t hint g hg p r).mono'
      (Selection.aestronglyMeasurable_affineAdjointSubSkewCutoffEnergyDefect hq t P g hg p r)
  filter_upwards with a
  have hbound := cutoffWeightedTerminalAdjointEnergy_nonneg_le_two_responseJ
    hq t (a.subSkew g hg) p r
  rw [Real.norm_eq_abs]
  exact abs_le.mpr
    ⟨by linarith only [hbound.1], by linarith only [hbound.2]⟩

end

end HCPolySupport.HighContrast.Response
