/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ScalarMaximizerExistence
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.SubcellDeficitIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.DiagonalDefectCarriers
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ReferenceCubeAveragePullback
public import LeanPool.HighContrastHomogenization.Entry.Response.Pairing.CoarseBlockFenchelPairing
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.TerminalEnergyMeasurability

/-!
# High-contrast homogenization: Entry.Response.Direct.SubcellEnergyIntegrability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Sample Integrability of the Subcell Deficits and Energies

The subcell deficit of the first error row — the amount by which the terminal optimizer fails
to maximize the response on an aligned subcell of the coarse scale — is nonnegative, and its
flat sum over a generation equals the flat sum of the subcell responses minus the terminal
response, both `P`-integrable; decomposing the subcell average of the response integrand into the
subcell energy and the subcell cell average of the doubled optimizer field, each measurable,
makes the subcell deficit itself `P`-integrable. The weighted energy readout of the terminal
optimizer is measurable in the sample for every weight bounded by two; taking the weight to be
the indicator of an aligned subcell turns the terminal-cell average into the subcell average up
to the constant ratio of volumes, so the subcell average of the terminal optimizer's energy
density is itself measurable.  These results serve the terminal-optimizer replacement row of
`p.response.transfer`.
-/

section
/-!
## Sample integrability of the subcell deficits

The subcell deficit of the terminal-optimizer replacement row of `p.response.transfer` is the
amount by which the terminal optimizer fails to maximize the response on an aligned subcell of the
coarse scale.  It is nonnegative, and its flat sum over the generation is the flat sum of the
subcell responses minus the terminal response, both `P`-integrable; its own measurability comes
from the decomposition of the subcell average of the response integrand into the subcell energy
and the subcell cell average of the doubled optimizer field, each measurable in the sample.  Hence
each deficit is `P`-integrable.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The bilinear pairing of a fixed doubled vector with `A X` expands over the flattened basis. -/
private theorem blockVecDot_blockMatVecMul_eq_sum_bilinear {d : ℕ} (A : BlockMat d) (u X : BlockVec d) :
    blockVecDot u (blockMatVecMul A X) =
      ∑ α : BlockCoord d, ∑ β : BlockCoord d,
        toFullBlockVec u α * (toFullBlockMat A α β * toFullBlockVec X β) := by
  rw [← dotProduct_toFullBlockVec u (blockMatVecMul A X), toFullBlockVec_blockMatVecMul]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]

/-- **Integrability of the subcell deficits, minus sign.**  On each aligned subcell of the coarse
scale, the amount by which the terminal optimizer for `a_- = a - g` fails to maximize the subcell
response is `P`-integrable.  The deficit is nonnegative, its flat sum over the triadic index box
is the flat sum of the subcell responses minus the terminal response `J_t^-`, each `P`-integrable,
and it is measurable in the sample through the subcell energy and the subcell average of the
doubled optimizer field; domination by the flat sum then gives integrability of each term. -/
theorem integrable_subcellDeficit_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (hjs : (jStar : ℤ) ≤ s) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hmeasE : ∀ w ∈ triadicIndexBox d H, MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P) :
    ∀ w ∈ triadicIndexBox d H, MeasureTheory.Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P := by
  classical
  have _hjs := hjs
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  let v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffMinus F a) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    fun w a => (Classical.choice
      (nonempty_scalarCanonicalMaximizer_respCoeffMinus_adaptedCellAtCenter (respGrid jStar F) hq s w F a
        (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e))).toAHarmonicFunctionMeanZero.toAHarmonicFunction
  have hv : ∀ (w : Fin d → ℤ) (a : CoeffSpace d),
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        (respCoeffMinus F a) (v w a) :=
    fun w a => (Classical.choice
      (nonempty_scalarCanonicalMaximizer_respCoeffMinus_adaptedCellAtCenter (respGrid jStar F) hq s w F a
        (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e))).isResponseMaximizer
  have hDnn := zero_le_subcellDeficit_respCoeffMinus P jStar hjStar F hm H s t ht e uM v hv
  let g : CoeffSpace d → ℝ := fun a =>
    ((triadicIndexBox d H).card : ℝ) *
      ((((triadicIndexBox d H).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d H,
            ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
              (respqMinus P jStar F t e) (respCoeffMinus F a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a))
  have hg : MeasureTheory.Integrable g P := by
    have h1 := integrable_avsum_responseJ_adaptedCellAtCenter_respCoeffMinus P jStar hjStar F hm H s
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) hblk
    exact (h1.sub hJt).const_mul _
  have hcard : ((triadicIndexBox d H).card : ℝ) ≠ 0 := by
    have hpos : 0 < ((triadicIndexBox d H).card : ℝ) := by
      rw [card_triadicIndexBox]
      positivity
    exact ne_of_gt hpos
  have hsum : ∀ a : CoeffSpace d,
      ∑ w ∈ triadicIndexBox d H,
        (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))
      = g a := by
    intro a
    have hid := avsum_subcellDeficit_respCoeffMinus_eq P jStar hjStar F hm H s t ht e uM hmax a
    calc ∑ w ∈ triadicIndexBox d H,
          (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
              (respqMinus P jStar F t e) (respCoeffMinus F a)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                  (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))
        = ((triadicIndexBox d H).card : ℝ) *
            ((((triadicIndexBox d H).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d H,
                (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
                    (respqMinus P jStar F t e) (respCoeffMinus F a)
                  - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                      (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))) := by
          rw [mul_inv_cancel_left₀ hcard]
      _ = g a := by
          rw [hid]
  have hmeas : ∀ w ∈ triadicIndexBox d H,
      MeasureTheory.AEStronglyMeasurable (fun a : CoeffSpace d =>
        ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P := by
    intro w hw
    have hts : t - (H : ℤ) = s := by omega
    have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F t := by
      have h := adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
      rwa [hts] at h
    have hV : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) s w) :=
      (isOpen_adaptedCellAtCenter_of_isUnit hq s w).measurableSet
    have hDefEq : (fun a : CoeffSpace d =>
        ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))
        = fun a : CoeffSpace d =>
            ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
                (respqMinus P jStar F t e) (respCoeffMinus F a)
              - (- (1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                    (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
                  + blockVecDot (-(respP (respMean P jStar F t) e), respqMinus P jStar F t e)
                      (blockMatVecMul (blockSwap d)
                        (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                          (optimizerField (respCoeffMinus F a) (uM a))))) := by
      funext a
      rw [volumeAverage_scalarResponseIntegrand_adaptedCellAtCenter_respCoeffMinus_eq P jStar hjStar F hm
        H s t ht e uM a w hw]
    rw [hDefEq]
    have hResp : MeasureTheory.AEStronglyMeasurable (fun a : CoeffSpace d =>
        ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)) P :=
      (integrable_responseJ_respCoeffMinus_adaptedCellAtCenter P hq F s w
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (hblk w)).aestronglyMeasurable
    have hEnergy : MeasureTheory.AEStronglyMeasurable (fun a : CoeffSpace d =>
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P := hmeasE w hw
    have hZ : ∀ α : BlockCoord d, Measurable (fun a : CoeffSpace d =>
        toFullBlockVec (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffMinus F a) (uM a))) α) :=
      fun α => measurable_cellAverage_optimizerField_respCoeffMinus P jStar hjStar F hm t e α
        uM hmax hV hVU
    have hB : MeasureTheory.AEStronglyMeasurable (fun a : CoeffSpace d =>
        blockVecDot (-(respP (respMean P jStar F t) e), respqMinus P jStar F t e)
          (blockMatVecMul (blockSwap d)
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffMinus F a) (uM a))))) P := by
      have hmeasB : Measurable (fun a : CoeffSpace d =>
          blockVecDot (-(respP (respMean P jStar F t) e), respqMinus P jStar F t e)
            (blockMatVecMul (blockSwap d)
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffMinus F a) (uM a))))) := by
        rw [show (fun a : CoeffSpace d =>
              blockVecDot (-(respP (respMean P jStar F t) e), respqMinus P jStar F t e)
                (blockMatVecMul (blockSwap d)
                  (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                    (optimizerField (respCoeffMinus F a) (uM a)))))
            = fun a : CoeffSpace d => ∑ α : BlockCoord d, ∑ β : BlockCoord d,
                toFullBlockVec (-(respP (respMean P jStar F t) e), respqMinus P jStar F t e) α *
                  (toFullBlockMat (blockSwap d) α β *
                    toFullBlockVec (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                      (optimizerField (respCoeffMinus F a) (uM a))) β) by
          funext a
          exact blockVecDot_blockMatVecMul_eq_sum_bilinear (blockSwap d)
            (-(respP (respMean P jStar F t) e), respqMinus P jStar F t e)
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffMinus F a) (uM a)))]
        exact Finset.measurable_sum _ (fun α _ =>
          Finset.measurable_sum _ (fun β _ =>
            ((hZ β).const_mul (toFullBlockMat (blockSwap d) α β)).const_mul
              (toFullBlockVec (-(respP (respMean P jStar F t) e), respqMinus P jStar F t e) α)))
      exact hmeasB.aestronglyMeasurable
    have hEnergy' : MeasureTheory.AEStronglyMeasurable (fun a : CoeffSpace d =>
        - (1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P := by
      simpa only [neg_mul] using hEnergy.const_mul (-(1 / 2 : ℝ))
    exact hResp.sub (hEnergy'.add hB)
  exact integrable_of_nonneg_of_sum_eq hDnn hmeas hg hsum

/-- **Integrability of the subcell deficits, plus sign.**  The transposed twin of
`integrable_subcellDeficit_respCoeffMinus`: the coefficient family `a_+ = aᵀ + g`, the dual load
`q^+` and the terminal optimizer family `uP` replace their minus-sign counterparts, and
nonnegativity, the flat-sum identity and sample measurability transport verbatim. -/
theorem integrable_subcellDeficit_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (hjs : (jStar : ℤ) ≤ s) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hmeasE : ∀ w ∈ triadicIndexBox d H, MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P) :
    ∀ w ∈ triadicIndexBox d H, MeasureTheory.Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P := by
  classical
  have _hjs := hjs
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  let v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffPlus F a) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    fun w a => (Classical.choice
      (nonempty_scalarCanonicalMaximizer_respCoeffPlus_adaptedCellAtCenter (respGrid jStar F) hq s w F a
        (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e))).toAHarmonicFunctionMeanZero.toAHarmonicFunction
  have hv : ∀ (w : Fin d → ℤ) (a : CoeffSpace d),
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
        (respCoeffPlus F a) (v w a) :=
    fun w a => (Classical.choice
      (nonempty_scalarCanonicalMaximizer_respCoeffPlus_adaptedCellAtCenter (respGrid jStar F) hq s w F a
        (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e))).isResponseMaximizer
  have hDnn := zero_le_subcellDeficit_respCoeffPlus P jStar hjStar F hm H s t ht e uP v hv
  let g : CoeffSpace d → ℝ := fun a =>
    ((triadicIndexBox d H).card : ℝ) *
      ((((triadicIndexBox d H).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d H,
            ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a))
  have hg : MeasureTheory.Integrable g P := by
    have h1 := integrable_avsum_responseJ_adaptedCellAtCenter_respCoeffPlus P jStar hjStar F hm H s
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) hblk
    exact (h1.sub hJt).const_mul _
  have hcard : ((triadicIndexBox d H).card : ℝ) ≠ 0 := by
    have hpos : 0 < ((triadicIndexBox d H).card : ℝ) := by
      rw [card_triadicIndexBox]
      positivity
    exact ne_of_gt hpos
  have hsum : ∀ a : CoeffSpace d,
      ∑ w ∈ triadicIndexBox d H,
        (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))
      = g a := by
    intro a
    have hid := avsum_subcellDeficit_respCoeffPlus_eq P jStar hjStar F hm H s t ht e uP hmax a
    calc ∑ w ∈ triadicIndexBox d H,
          (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                  (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))
        = ((triadicIndexBox d H).card : ℝ) *
            ((((triadicIndexBox d H).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d H,
                (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
                    (respqPlus P jStar F t e) (respCoeffPlus F a)
                  - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                      (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))) := by
          rw [mul_inv_cancel_left₀ hcard]
      _ = g a := by
          rw [hid]
  have hmeas : ∀ w ∈ triadicIndexBox d H,
      MeasureTheory.AEStronglyMeasurable (fun a : CoeffSpace d =>
        ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P := by
    intro w hw
    have hts : t - (H : ℤ) = s := by omega
    have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F t := by
      have h := adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
      rwa [hts] at h
    have hV : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) s w) :=
      (isOpen_adaptedCellAtCenter_of_isUnit hq s w).measurableSet
    have hDefEq : (fun a : CoeffSpace d =>
        ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))
        = fun a : CoeffSpace d =>
            ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
                (respqPlus P jStar F t e) (respCoeffPlus F a)
              - (- (1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                    (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
                  + blockVecDot (-(respP (respMean P jStar F t) e), respqPlus P jStar F t e)
                      (blockMatVecMul (blockSwap d)
                        (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                          (optimizerField (respCoeffPlus F a) (uP a))))) := by
      funext a
      rw [volumeAverage_scalarResponseIntegrand_adaptedCellAtCenter_respCoeffPlus_eq P jStar hjStar F hm
        H s t ht e uP a w hw]
    rw [hDefEq]
    have hResp : MeasureTheory.AEStronglyMeasurable (fun a : CoeffSpace d =>
        ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)) P :=
      (integrable_responseJ_respCoeffPlus_adaptedCellAtCenter P hq F s w
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (hblk w)).aestronglyMeasurable
    have hEnergy : MeasureTheory.AEStronglyMeasurable (fun a : CoeffSpace d =>
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P := hmeasE w hw
    have hZ : ∀ α : BlockCoord d, Measurable (fun a : CoeffSpace d =>
        toFullBlockVec (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffPlus F a) (uP a))) α) :=
      fun α => measurable_cellAverage_optimizerField_respCoeffPlus P jStar hjStar F hm t e α
        uP hmax hV hVU
    have hB : MeasureTheory.AEStronglyMeasurable (fun a : CoeffSpace d =>
        blockVecDot (-(respP (respMean P jStar F t) e), respqPlus P jStar F t e)
          (blockMatVecMul (blockSwap d)
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffPlus F a) (uP a))))) P := by
      have hmeasB : Measurable (fun a : CoeffSpace d =>
          blockVecDot (-(respP (respMean P jStar F t) e), respqPlus P jStar F t e)
            (blockMatVecMul (blockSwap d)
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffPlus F a) (uP a))))) := by
        rw [show (fun a : CoeffSpace d =>
              blockVecDot (-(respP (respMean P jStar F t) e), respqPlus P jStar F t e)
                (blockMatVecMul (blockSwap d)
                  (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                    (optimizerField (respCoeffPlus F a) (uP a)))))
            = fun a : CoeffSpace d => ∑ α : BlockCoord d, ∑ β : BlockCoord d,
                toFullBlockVec (-(respP (respMean P jStar F t) e), respqPlus P jStar F t e) α *
                  (toFullBlockMat (blockSwap d) α β *
                    toFullBlockVec (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                      (optimizerField (respCoeffPlus F a) (uP a))) β) by
          funext a
          exact blockVecDot_blockMatVecMul_eq_sum_bilinear (blockSwap d)
            (-(respP (respMean P jStar F t) e), respqPlus P jStar F t e)
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffPlus F a) (uP a)))]
        exact Finset.measurable_sum _ (fun α _ =>
          Finset.measurable_sum _ (fun β _ =>
            ((hZ β).const_mul (toFullBlockMat (blockSwap d) α β)).const_mul
              (toFullBlockVec (-(respP (respMean P jStar F t) e), respqPlus P jStar F t e) α)))
      exact hmeasB.aestronglyMeasurable
    have hEnergy' : MeasureTheory.AEStronglyMeasurable (fun a : CoeffSpace d =>
        - (1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P := by
      simpa only [neg_mul] using hEnergy.const_mul (-(1 / 2 : ℝ))
    exact hResp.sub (hEnergy'.add hB)
  exact integrable_of_nonneg_of_sum_eq hDnn hmeas hg hsum

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The subcell energy of the terminal optimizer is measurable in the sample

The weighted energy readout of the terminal optimizer of `p.response.transfer` is measurable in the
coefficient sample for every weight bounded by two.  Taking the weight to be the indicator of an
aligned subcell turns the terminal-cell average into the subcell average, up to the constant ratio
of the two volumes; hence the subcell average of the energy density of the terminal optimizer is
measurable in the sample, for an arbitrary family of terminal maximizers.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The terminal-cell average of a function weighted by the indicator of a measurable subcell is
the ratio of the two volumes times the subcell average of that function. -/
private theorem volumeAverage_indicator_mul {d : ℕ} {U V : Set (Vec d)} (hV : MeasurableSet V)
    (hVU : V ⊆ U) (hVvol : (volume V).toReal ≠ 0) (f : Vec d → ℝ) :
    volumeAverage U (fun x => V.indicator (fun _ : Vec d => (1 : ℝ)) x * f x)
      = ((volume V).toReal / (volume U).toReal) * volumeAverage V f := by
  have hfun : (fun x => V.indicator (fun _ : Vec d => (1 : ℝ)) x * f x) = V.indicator f := by
    funext x
    by_cases hx : x ∈ V
    · simp only [Set.indicator_of_mem hx, one_mul]
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  have hint : ∫ x in U, V.indicator f x = ∫ x in V, f x := by
    rw [MeasureTheory.setIntegral_indicator hV, Set.inter_eq_self_of_subset_right hVU]
  rw [volumeAverage, hfun, hint, volumeAverage]
  field_simp

/-- **The subcell energy of the terminal optimizer is measurable in the sample, minus sign.**  For
every aligned subcell of the coarse scale, the subcell average of the energy density of the
terminal optimizer of the recentred coefficient `a_- = a - g` is a measurable function of the
coefficient sample, for an arbitrary family of terminal maximizers. -/
theorem measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d H) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hts : t - (H : ℤ) = s := by omega
  have hVmeas : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) s w) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq s w).measurableSet
  have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F t := by
    have h := adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
    rwa [hts] at h
  set eta : Vec d → ℝ := (adaptedCellAtCenter (respGrid jStar F) s w).indicator
    (fun _ : Vec d => (1 : ℝ)) with heta
  have hetam : AEStronglyMeasurable eta (volumeMeasureOn (respCell jStar F t)) :=
    (measurable_const.indicator hVmeas).aestronglyMeasurable
  have hetab : ∀ᵐ x ∂volumeMeasureOn (respCell jStar F t), ‖eta x‖ ≤ 2 := by
    filter_upwards with x
    by_cases hx : x ∈ adaptedCellAtCenter (respGrid jStar F) s w
    · simp only [heta, Set.indicator_of_mem hx, norm_one]
      norm_num
    · simp only [heta, Set.indicator_of_notMem hx, norm_zero]
      norm_num
  have hmeas := measurable_volumeAverage_weighted_energy_respCoeffMinus P jStar hjStar F hm t e
    uM hmax (eta := eta) hetam hetab
  have hVpos : 0 < (volume (adaptedCellAtCenter (respGrid jStar F) s w)).toReal :=
    volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq s w
  set c : ℝ := (volume (respCell jStar F t)).toReal /
    (volume (adaptedCellAtCenter (respGrid jStar F) s w)).toReal with hc
  have hkey : (fun a : CoeffSpace d =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))
      = fun a : CoeffSpace d => c * volumeAverage (respCell jStar F t)
          (fun x => eta x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x) := by
    funext a
    rw [volumeAverage_indicator_mul hVmeas hVU (ne_of_gt hVpos)
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))]
    have hUpos : 0 < (volume (respCell jStar F t)).toReal := by
      simpa only [respCell] using adaptedCell_volume_toReal_pos (respGrid jStar F) hq t
    rw [hc]
    field_simp
  rw [hkey]
  exact hmeas.const_mul c

/-- **The subcell energy of the terminal optimizer is measurable in the sample, plus sign.**  The
adjoint twin of `measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus`. -/
theorem measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d H) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hts : t - (H : ℤ) = s := by omega
  have hVmeas : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) s w) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq s w).measurableSet
  have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F t := by
    have h := adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
    rwa [hts] at h
  set eta : Vec d → ℝ := (adaptedCellAtCenter (respGrid jStar F) s w).indicator
    (fun _ : Vec d => (1 : ℝ)) with heta
  have hetam : AEStronglyMeasurable eta (volumeMeasureOn (respCell jStar F t)) :=
    (measurable_const.indicator hVmeas).aestronglyMeasurable
  have hetab : ∀ᵐ x ∂volumeMeasureOn (respCell jStar F t), ‖eta x‖ ≤ 2 := by
    filter_upwards with x
    by_cases hx : x ∈ adaptedCellAtCenter (respGrid jStar F) s w
    · simp only [heta, Set.indicator_of_mem hx, norm_one]
      norm_num
    · simp only [heta, Set.indicator_of_notMem hx, norm_zero]
      norm_num
  have hmeas := measurable_volumeAverage_weighted_energy_respCoeffPlus P jStar hjStar F hm t e
    uP hmax (eta := eta) hetam hetab
  have hVpos : 0 < (volume (adaptedCellAtCenter (respGrid jStar F) s w)).toReal :=
    volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq s w
  set c : ℝ := (volume (respCell jStar F t)).toReal /
    (volume (adaptedCellAtCenter (respGrid jStar F) s w)).toReal with hc
  have hkey : (fun a : CoeffSpace d =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))
      = fun a : CoeffSpace d => c * volumeAverage (respCell jStar F t)
          (fun x => eta x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) := by
    funext a
    rw [volumeAverage_indicator_mul hVmeas hVU (ne_of_gt hVpos)
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))]
    have hUpos : 0 < (volume (respCell jStar F t)).toReal := by
      simpa only [respCell] using adaptedCell_volume_toReal_pos (respGrid jStar F) hq t
    rw [hc]
    field_simp
  rw [hkey]
  exact hmeas.const_mul c

end

end HCPolySupport.HighContrast.Multiscale
end
