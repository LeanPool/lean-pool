/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.ResponseTransferFromCutoffBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantEnergyAndFenchelSlots
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantFenchelProbe
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantHeadBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantIndexStationarity
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TriadicRefinementIncrement
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Limit.DescendantLimitDomination
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CarrierIntegrabilityConditions
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CellHalfFinalBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CutoffOscillationHalfClosure

/-!
# High-contrast homogenization: Entry.Response.Rows.CutoffOscillationAdjointCarrier

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The oscillation half of the cutoff-mean row for the adjoint sign

This file proves, for the adjoint recentred coefficient `a_+ = a^T + g`, the same closing
statement proved elsewhere for the negative sign: the oscillation half of the cutoff-mean row is
bounded by the source load once the terminal optimizer family supplies the refinement identity at
every depth, the cutoff-weight increment, and the pathwise crossed-pairing bound on each
descendant cell. Only the sign of the recentred coefficient changes; the increment envelope, the
vanishing remainder, and the general closure statement are shared with the negative-sign case and
are not reproved here. The per-descendant-cell crossed-pairing bound is again left as a hypothesis,
to be discharged where the terminal optimizer field for this sign is actually constructed. The
bound is the adjoint-sign half of the cutoff-mean row used by the cutoff estimate
`p.response.transfer`, and so contributes to the polynomial entry result `t.polynomial.entry`.
-/

section
/-!
## The oscillation half of the cutoff-mean row at the carriers, adjoint sign

The adjoint twin of `CutoffOscillationHalfClosure`: the same carrier data for the recentred adjoint
coefficient `a_+ = aᵀ + g`, with the same per-descendant-cell crossed pairing left as a
hypothesis.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

private theorem hasIntegrableCoarseBlock_respGridAdaptedCell {d : ℕ}
    (hd : 2 ≤ d) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d)
    (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) :
    ∀ (k : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) k w) := fun k w =>
  hasIntegrableCoarseBlock_adaptedCellAtCenter_respGrid hd P γ E Ψ Kg Src hstat hdag jStar hjStar
    F hm k w

private theorem respCoeffPlusCarrierIntegrabilityFacts {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hstat : IsStationaryLaw P) (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
    (Src : CoeffSpace d → ℝ) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (hq : IsUnit (respGrid jStar F))
    (t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (hφ : IsResponseCutoff (respGrid jStar F) t φ) (Y : BlockVec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P) :
    AEStronglyMeasurable (fun a => volumeAverage (respCell jStar F t)
      (fun x => (φ x - 1) * (vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1 +
        vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2))) P ∧
    (∀ a : CoeffSpace d, IntegrableOn
      (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1 +
        vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2)
      (HighContrast.adaptedCell (respGrid jStar F) t)) ∧
    (∀ (k : ℤ) (W : Fin d → ℤ), Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) k W) (respCoeffPlus F a)).upperLeft Y.1)) +
       Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) k W) (respCoeffPlus F a)).lowerRight Y.2)) ^ 2)
          P) := by
  have hq0 : IsUnit (respGrid jStar F) := hq
  have hUmeas : MeasurableSet (respCell jStar F t) :=
    (isOpen_adaptedCell_of_isUnit hq0 t).measurableSet
  have hPhiM : AEStronglyMeasurable (fun a => volumeAverage (respCell jStar F t)
      (fun x => (φ x - 1) * (vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1 +
        vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2))) P := by
    have hcont : Continuous (fun x : Vec d => φ x - 1) :=
      hφ.2.2.2.2.2.1.continuous.sub continuous_const
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq0
        t).isFiniteMeasure_restrict_volume
    have hL2 : MemScalarL2 (respCell jStar F t)
        ((respCell jStar F t).indicator (fun x => φ x - 1)) := by
      refine MemLp.of_bound ((hcont.measurable.indicator hUmeas).aestronglyMeasurable) 2
        (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ respCell jStar F t
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_le]
        have h1 := hφ.1 x
        have h2 := hφ.2.1 x
        constructor <;> linarith only [h1, h2]
      · rw [Set.indicator_of_notMem hx, norm_zero]
        norm_num
    exact (measurable_volumeAverage_weighted_cross_optimizerField_respCoeffPlus P jStar hjStar F
      hm t e uP hmax hUmeas (fun x hx => hx) hcont hL2 Y).aestronglyMeasurable
  have hUcell : adaptedCellAtCenter (respGrid jStar F) (t - ((0 : ℕ) : ℤ)) 0 =
      respCell jStar F t := by
    rw [Nat.cast_zero, sub_zero]
    exact adaptedCellAtCenter_zero (respGrid jStar F) t
  have hfat : ∀ (a : CoeffSpace d) (m : ℕ), ∀ W ∈ triadicIndexBox d m, IntegrableOn
      (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1 +
        vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2)
      (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W) := fun a m W hW =>
    (integrableOn_cross_optimizerField_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm t m a
      (uP a) Y hW).1
  have hfint : ∀ a : CoeffSpace d, IntegrableOn
      (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1 +
        vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2)
      (HighContrast.adaptedCell (respGrid jStar F) t) := by
    intro a
    have h := hfat a 0 0 (zero_mem_triadicIndexBox 0)
    rwa [hUcell] at h
  have hUL0 : ∀ (k : ℤ) (W : Fin d → ℤ) (a : CoeffSpace d), 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k W)
        (respCoeffPlus F a)).upperLeft Y.1) := fun k W a =>
    (zero_le_vecDot_coarseBlockMatrix_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm k a Y W).1
  have hLR0 : ∀ (k : ℤ) (W : Fin d → ℤ) (a : CoeffSpace d), 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k W)
        (respCoeffPlus F a)).lowerRight Y.2) := fun k W a =>
    (zero_le_vecDot_coarseBlockMatrix_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm k a Y W).2
  have hheadsq : ∀ (k : ℤ) (W : Fin d → ℤ), Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) k W) (respCoeffPlus F a)).upperLeft Y.1)) +
        Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) k W) (respCoeffPlus F a)).lowerRight Y.2)) ^ 2)
      P := by
    intro k W
    have hblk : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) k W) :=
      hasIntegrableCoarseBlock_adaptedCellAtCenter_respGrid hd P γ E Ψ Kg Src hstat hdag jStar
        hjStar
        F hm k W
    exact integrable_sq_sqrt_add_sqrt_coarseBlockMatrix Y
      (integrable_vecDot_coarseBlockMatrix_upperLeft Y
        (integrable_coarseBlockMatrix_upperLeft_respCoeffPlus P jStar hjStar F hm k W hblk))
      (integrable_vecDot_coarseBlockMatrix_lowerRight Y
        (integrable_coarseBlockMatrix_lowerRight_respCoeffPlus P jStar hjStar F hm k W hblk))
      (fun a => hUL0 k W a) (fun a => hLR0 k W a)
  exact ⟨hPhiM, hfint, hheadsq⟩

/-- **The oscillation half of the cutoff-mean row at the carriers, plus sign.**  The
`(φ-1)`-weighted cell average of the crossed pairing of the deterministic dual variable with the
terminal optimizer state is `P`-integrable, and its annealed mean differs from that of its
depth-`H` cell part by at most `32 d² Θ 3^{-H} (3^{3/2} 𝓛_s^-)^{1/2} (8 E[J_t^-])^{1/2}` times the
geometric factor. -/
theorem integrable_and_abs_integral_cross_sub_cellPart_le_respCoeffPlus_car {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hstat : IsStationaryLaw P) (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
    (Src : CoeffSpace d → ℝ) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (hq : IsUnit (respGrid jStar F))
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (hjs : (jStar : ℤ) ≤ s)
    (e : Vec d) (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (Y : BlockVec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hEint : ∀ a, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hsumm : Summable (fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
      ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffPlus F)).upperLeft Y.1)) +
            Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffPlus F)).lowerRight Y.2))) ^ 2))) :
    Integrable (fun a => volumeAverage (respCell jStar F t)
        (fun x => (φ x - 1) * (vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2))) P
      ∧ |(∫ a, volumeAverage (respCell jStar F t)
              (fun x => (φ x - 1) * (vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
                + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2)) ∂P)
            - ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
                    (fun x => φ x - 1) *
                  volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
                    (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
                      + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2) ∂P|
          ≤ (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
              * (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
                  * Real.sqrt ((3 : ℝ) ^ ((3 : ℝ) / 2) *
                      respSourceLoad P jStar F s (respCoeffPlus F) Y))
              * Real.sqrt (2 * (4 * respEJPlus P jStar F t e)) := by
  classical
  have hblkAll := hasIntegrableCoarseBlock_respGridAdaptedCell hd P γ E Ψ Kg Src hstat hdag
    jStar hjStar F hm
  have hcross : ∀ (m : ℕ), ∀ W ∈ triadicIndexBox d m, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2)) P :=
    fun m W hW => integrable_volumeAverage_cross_optimizerField_respCoeffPlus P jStar hjStar F hm
      t e uP hmax hJ hblkAll Y m W hW
  have hcellP : ∀ (n : ℕ), ∀ W ∈ triadicIndexBox d (H + n + 1), Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
        (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2)) P :=
    fun n W hW => hcross (H + n + 1) W hW
  have hT : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) (fun x => φ x - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
            (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
              + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2)) P :=
    integrable_avsum_weighted_pairing (fun _ => triadicIndexBox d H)
      (fun _ w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
        (fun x => φ x - 1))
      (fun _ w a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
        (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2))
      (fun _ W hW => hcross H W hW) 0
  obtain ⟨hPhiM, hfint, hheadsq⟩ := respCoeffPlusCarrierIntegrabilityFacts hd P hstat γ E Ψ Kg Src
    hdag jStar hjStar F hm hq t e φ hφ Y uP hmax hJ
  have hcellE : ∀ (n : ℕ), ∀ W ∈ triadicIndexBox d (H + n + 1), Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P :=
    fun n W hW => integrable_volumeAverage_energy_descendant_respCoeffPlus P jStar hjStar F hm
      H s t ht e uP hmax hJ n W hW
  refine integrable_and_abs_integral_sub_cellPart_le_descendant_load_of_carriers
    P jStar F s (respCoeffPlus F) Y
    (fun a => volumeAverage (respCell jStar F t)
      (fun x => (φ x - 1) * (vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
        + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2)))
    (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) (fun x => φ x - 1) *
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
            + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2))
    (fun n a => ((triadicIndexBox d (H + n + 1)).card : ℝ)⁻¹ *
      ∑ W ∈ triadicIndexBox d (H + n + 1),
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
              (fun x => φ x - 1)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n : ℕ) : ℤ))
                (Transport.gridParent W)) (fun x => φ x - 1)) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
            (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
              + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2))
    (fun N a => volumeAverage (respCell jStar F t)
        (fun x => (φ x - 1) * (vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2))
      - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
              (fun x => φ x - 1) *
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
              (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
                + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2))
    (fun n => triadicIndexBox d (H + n + 1))
    (fun n W => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
          (fun x => φ x - 1)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n : ℕ) : ℤ))
            (Transport.gridParent W)) (fun x => φ x - 1))
    (fun n W a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) :
      ℤ)) W)
      (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
        + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2))
    (fun n W a => Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
          (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
          (respCoeffPlus F a)).upperLeft Y.1))
      + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
          (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
          (respCoeffPlus F a)).lowerRight Y.2)))
    (fun n W a => 2 * volumeAverage
      (adaptedCellAtCenter (respGrid jStar F) (t - ((H + n + 1 : ℕ) : ℤ)) W)
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))
    (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
    (4 * respEJPlus P jStar F t e) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hPhiM hT ?_ ?_ ?_ ?_ ?_ hsumm
  · exact mul_nonneg (mul_nonneg (by positivity)
      (by linarith only [one_le_responseCutoffProfileConst])) (by positivity)
  · have := zero_le_respEJPlus P jStar F t e hq
    linarith only [this]
  · intro N a
    exact volumeAverage_sub_one_eq_cellPart_add_sum_range_add_rem hq t H N φ (hfint a)
  · intro n a
    rfl
  · intro a
    exact tendsto_zero_descendantRemainder_respCoeffPlus jStar hjStar F hm t H hφ uP Y a
  · intro n W _
    exact abs_cutoff_weight_increment_le hq hφ H n W
  · intro n W _ a
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · intro n W hW a
    have := zero_le_volumeAverage_scalarVariationEnergyIntegrand_respCoeffPlus_adaptedCellAtCenter
      jStar hjStar F hm t (H + n + 1) a (uP a) hW
    linarith only [this]
  · intro n W hW a
    exact abs_volumeAverage_cross_optimizerField_respCoeffPlus_adaptedCellAtCenter_le jStar hjStar F
      hm t (H + n + 1) a (uP a) Y hW
      (fun i => (integrableOn_optimizerField_respCoeffPlus_box (respGrid jStar F) hq t F a
        (uP a) (H + n + 1) W hW i).1)
      (fun i => (integrableOn_optimizerField_respCoeffPlus_box (respGrid jStar F) hq t F a
        (uP a) (H + n + 1) W hW i).2)
      ((integrableOn_vecDot_optimizerField_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm t
        (H + n + 1) a (uP a) hW).1 Y.2)
      ((integrableOn_vecDot_optimizerField_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm t
        (H + n + 1) a (uP a) hW).2 Y.1)
  · intro n
    have hshift : t - ((H + n + 1 : ℕ) : ℤ) = s - ((n + 1 : ℕ) : ℤ) := by
      rw [ht]; push_cast; ring
    simp only [hshift]
    exact integral_avsum_sq_head_descendant_le_respCoeffPlus_car hd P hstat γ E Ψ Kg Src hdag
      jStar hjStar F hm H (n + 1) s hjs Y
  · intro n
    exact (integral_avsum_two_mul_doubledEnergy_eq_respEJPlus P jStar F t (H + n + 1) e hq uP
      hmax hEint hJ).le
  · intro n
    exact integrable_avsum_weighted_pairing (fun m => triadicIndexBox d (H + m + 1))
      (fun m W => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) :
        ℤ)) W)
            (fun x => φ x - 1)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m : ℕ) : ℤ))
              (Transport.gridParent W)) (fun x => φ x - 1))
      (fun m W a => volumeAverage
        (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
        (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2))
      hcellP n
  · intro n
    exact integrable_avsum_sq_head (fun m => triadicIndexBox d (H + m + 1))
      (fun m W a => Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
            (respCoeffPlus F a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
            (respCoeffPlus F a)).lowerRight Y.2)))
      (fun m W _ => hheadsq (t - ((H + m + 1 : ℕ) : ℤ)) W) n
  · intro n
    exact integrable_avsum_two_mul_energy (fun m => triadicIndexBox d (H + m + 1))
      (fun m W a => 2 * volumeAverage
        (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))
      (fun m W hW => (hcellE m W hW).const_mul 2) n
  · intro n
    exact integrable_sqrt_avsum_mul_sqrt_avsum (fun m => triadicIndexBox d (H + m + 1))
      (fun m W a => Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
            (respCoeffPlus F a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
            (respCoeffPlus F a)).lowerRight Y.2)))
      (fun m W a => 2 * volumeAverage
        (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))
      (fun m W _ => hheadsq (t - ((H + m + 1 : ℕ) : ℤ)) W)
      (fun m W hW => (hcellE m W hW).const_mul 2) n
  · intro n
    exact integrable_avsum_weighted_sqrt_mul_sqrt (fun m => triadicIndexBox d (H + m + 1))
      (fun m W => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) :
        ℤ)) W)
            (fun x => φ x - 1)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m : ℕ) : ℤ))
              (Transport.gridParent W)) (fun x => φ x - 1))
      (fun m W a => Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
            (respCoeffPlus F a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
            (respCoeffPlus F a)).lowerRight Y.2)))
      (fun m W a => 2 * volumeAverage
        (adaptedCellAtCenter (respGrid jStar F) (t - ((H + m + 1 : ℕ) : ℤ)) W)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))
      (fun m W _ => hheadsq (t - ((H + m + 1 : ℕ) : ℤ)) W)
      (fun m W hW => (hcellE m W hW).const_mul 2) n

end

end HCPolySupport.HighContrast.Multiscale
end
