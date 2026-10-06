/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.ResponseTransferFromCutoffBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.OptimizerEnergyDefectRow
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.OptimizerRowSideConditions
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.SubcellDeficitIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.SubcellEnergyIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TerminalDeficitCarrierBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.AbstractCellPairingBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CutoffEstimateRowClosure
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.ScaleDefectIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.StationaryAnnealedErrorScalars
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.TerminalEnergyMeasurability
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.TerminalHalfEnergyIntegrability

/-!
# High-contrast homogenization: Entry.Response.Rows.CutoffEnergyDefectRowObligations

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The first error row as a named, monotone obligation

The first error row of `p.response.transfer`, proved in the adjoint configuration from a list of
pathwise and sample-side hypotheses, is discharged here on the response's own data for that sign:
every pathwise ingredient — the energy-defect identity, the oscillation split, the subcell
comparison, the two cutoff-weight facts, and the relevant signs — is supplied directly. The cutoff
estimate consumes this replacement bound in the predicate form of two named obligations, one per
sign, and on the response's own data that obligation is exactly the replacement bound already
proved, once its three remaining sample-side integrability hypotheses — the subcell deficits, the
subcell energies, and the cutoff-weighted terminal energy — are shown to follow from the data the
row already carries. Because the energy-defect row and the cutoff-mean row are produced with
different constants, a final pair of monotonicity lemmas records that raising either constant
preserves the corresponding bound, so both rows can be read at one common constant.
-/

section
/-!
## The first error row on the carriers, side conditions discharged (adjoint sign)

The first error row of `p.response.transfer` is proved in the adjoint configuration by
`abs_integral_cutoffHalfEnergy_sub_respJ_le_rowPlus` from fifteen hypotheses.  Every one of them
that is a pathwise statement — the energy-defect identity, the oscillation split, the subcell
comparison, the two cutoff-weight facts, the three signs, the stationarity of the annealed subcell
response and the scale-defect identity — is available on the carriers of the cutoff estimate
without any pointwise ellipticity hypothesis, because a coefficient of the carrier is elliptic only
almost everywhere and the transport along an a.e.-elliptic representative has been built.  This
module assembles those statements and leaves only the sample integrabilities as hypotheses:

* the terminal and coarse pathwise responses are `P`-integrable;
* the subcell response deficits and the averaged optimizer energies are `P`-integrable;
* the cutoff-weighted optimizer energy is `P`-integrable.

The conclusion is the printed bound
`C (τ^+ + (τ^+ E[J_t^+])^{1/2} + 3^{-H} E[J_t^+])` with the explicit dimensional constant
`C = max 3 (32 d^2 responseCutoffProfileConst)`.

Paper: `p.response.transfer`.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The terminal-optimizer replacement row on the cutoff carriers, adjoint sign, side
conditions discharged.**  Under a stationary probability law on the coefficient carrier, let `uP`
be a terminal optimizer for the adjoint recentred coefficient `a_+ = aᵗ + g`, `φ` a cutoff of the
response class, and suppose the annealed pathwise responses at the terminal and coarse scales are
`P`-integrable, the subcell response deficits, the averaged subcell optimizer energies and the
cutoff-weighted optimizer energy are `P`-integrable.  Then the law-integral of the cutoff
half-energy of `uP` minus the terminal response is at most
`max 3 (32 d^2 responseCutoffProfileConst)` times
`τ^+ + (τ^+ E[J_t^+])^{1/2} + 3^{-H} E[J_t^+]`.  All pathwise side conditions are supplied by the
a.e.-elliptic representative transport, so no pointwise ellipticity is assumed.  This is the first
error row of `p.response.transfer` on the carriers of the cutoff estimate. -/
theorem abs_integral_cutoffHalfEnergy_sub_respJ_le_rowPlus_of_carriers {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (hjs : (jStar : ℤ) ≤ s) (e : Vec d) (φ : Vec d → ℝ)
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hblk : ∀ (j : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hDint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P)
    (hEint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P)
    (hWint : Integrable (fun a => volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
      scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)) P) :
    |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)) ∂P|
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
          (respTauPlus P jStar F s t e +
            Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) +
            (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hts : t - (H : ℤ) = s := by omega
  have hvol : (volume (HighContrast.adaptedCell (respGrid jStar F) t)).toReal ≠ 0 := by
    have hpos : 0 < (volume (HighContrast.adaptedCell (respGrid jStar F) t)).toReal := by
      rw [Geometry.volume_adaptedCell_toReal]
      have hdet : 0 < |(respGrid jStar F).det| := abs_pos.mpr (by
        have hunit := (Matrix.isUnit_iff_isUnit_det (respGrid jStar F)).mp hq
        exact IsUnit.ne_zero hunit)
      positivity
    exact ne_of_gt hpos
  have hid : ∀ a, cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
      = (1 / 2 : ℝ) * volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) :=
    fun a => cutoffHalfEnergyAux_sub_respJ_eq_respCoeffPlus hjStar hm t φ hφ
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) a (uP a) (hmax a)
  have hosc : ∀ a, |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
            scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)
          - (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))|
        ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)) *
            (2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a)) := by
    intro a
    have h := abs_volumeAverage_sub_one_energy_sub_avsum_le_respCoeffPlus hjStar hm t H hφ
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) a (uP a) (hmax a)
    simpa only [hts] using h
  have hcmp : ∀ w ∈ triadicIndexBox d H, ∀ a,
      |(1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
          - ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a)|
        ≤ (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                  (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))
          + 2 * Real.sqrt (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a) *
            (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
                (respqPlus P jStar F t e) (respCoeffPlus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))) := by
    intro w hw a
    have h := abs_half_energy_adaptedCellAtCenter_sub_responseJ_le_respCoeffPlus hjStar hm t H
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) a (uP a) hw
    simpa only [hts] using h
  have hc0 : (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1) = 0 := by
    have h := avsum_volumeAverage_sub_one_eq_zero (qq := respGrid jStar F) hq t H hφ
      (by
        simpa only [adaptedCellAtCenter_zero] using
          integrableOn_sub_one_isResponseCutoff hq hφ t 0)
      hvol
      (by
        simpa only [adaptedCellAtCenter_zero] using
          integrableOn_isResponseCutoff hq hφ t 0)
    simpa only [hts] using h
  have hc1 : ∀ w ∈ triadicIndexBox d H,
      |volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)| ≤ 1 :=
    fun w _ => abs_volumeAverage_sub_one_isResponseCutoff_le_one hq hφ s w
  have hJ0 : ∀ w ∈ triadicIndexBox d H, ∀ a,
      0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) := by
    intro w hw a
    have h := (responseJ_nonneg_and_deficit_nonneg_respCoeffPlus hjStar hm t H
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) a (uP a) hw).1
    simpa only [hts] using h
  have hD0 : ∀ w ∈ triadicIndexBox d H, ∀ a,
      0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)) := by
    intro w hw a
    have h := (responseJ_nonneg_and_deficit_nonneg_respCoeffPlus hjStar hm t H
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) a (uP a) hw).2
    simpa only [hts] using h
  have hJt0 : ∀ a, 0 ≤ respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) := by
    intro a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
    let v : AHarmonicFunction f (respCell jStar F t) := Response.aHarmonicOfAEEq hae (uP a)
    have hmaxf : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) f v :=
      isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff hae
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (hmax a)
    have hconv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
      adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      hconv.isFiniteMeasure_restrict_volume
    have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    have hJf : 0 ≤ ResponseJ (respCell jStar F t) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) f :=
      responseJ_nonneg_of_isResponseMaximizer hEll
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) v hmaxf
        (hdata.weakFlux v)
        (hdata.response (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) v)
        (hdata.firstVariation (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) v v)
        (hdata.energy v)
    have hJplus : 0 ≤ ResponseJ (respCell jStar F t) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) := by
      rw [responseJ_congr_of_ae_eq hae (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e)]
      exact hJf
    simpa only [respJ] using! hJplus
  have hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P :=
    fun w _ => integrable_responseJ_respCoeffPlus_adaptedCellAtCenter P hq F s w
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (hblk s w)
  have hRint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P := by
    intro w hw
    have heq : (fun a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))
        = fun a => ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a)
            - (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) := by
      funext a
      ring
    rw [heq]
    exact (hJint w hw).sub (hDint w hw)
  have hrespint : ∀ a, MeasureTheory.IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))
      (respCell jStar F t) := by
    intro a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
    have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    have hv : MeasureTheory.IntegrableOn
        (scalarResponseIntegrand (respCell jStar F t) f
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
          (Response.aHarmonicOfAEEq hae (uP a))) (respCell jStar F t) :=
      hdata.response (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
        (Response.aHarmonicOfAEEq hae (uP a))
    exact integrableOn_scalarResponseIntegrand_aHarmonicFunctionOfAEEqCoeff (subset_refl _)
      hae.symm (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
      (Response.aHarmonicOfAEEq hae (uP a)) hv
  have hJval : ∀ w ∈ triadicIndexBox d H,
      (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P)
        = ∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P := by
    intro w _
    have hw' := integral_responseJ_respCoeffPlus_adaptedCellAtCenter_eq_direct P hstat jStar hjStar F hm s hjs w
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (hblk s w)
    have h0 := integral_responseJ_respCoeffPlus_adaptedCellAtCenter_eq_direct P hstat jStar hjStar F hm s hjs 0
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (hblk s 0)
    rw [adaptedCellAtCenter_zero (respGrid jStar F) s] at h0
    have hcJs : (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P)
        = blockResponseEnergy (blockCongr (respGPlus F) (respMean P jStar F s))
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) := by
      simpa only [respJ] using h0
    rw [hcJs]
    exact hw'
  have hDval : (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
        (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) ∂P)
      = respTauPlus P jStar F s t e :=
    integral_avsum_subcellDeficit_eq_respTauPlus P hstat jStar hjStar F hm H s t ht hjs e uP hmax
      (fun w => hblk s w) hrespint hJint hRint hJt hJs
  exact abs_integral_cutoffHalfEnergy_sub_respJ_le_rowPlus (d := d) P jStar F H s t e φ uP
    hid hosc hcmp hc0 hc1 hJ0 hD0 hJt0 hJint hDint hEint hWint hJt hJval hDval

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The first error row of `p.response.transfer` as the named obligation

The cutoff estimate of `e.response.cutoff.estimate` consumes the first error row of
`p.response.transfer` — the cost of replacing the terminal optimizer by the coarse-cell
optimizers — in the predicate form `CutoffEnergyDefectRowMinus`, and its adjoint twin
`CutoffEnergyDefectRowPlus`.  On the response carriers that row is the replacement bound with the
explicit dimensional constant `max 3 (32 d^2 responseCutoffProfileConst)`.

The two declarations here restate the carrier bounds of `OptimizerRowSideConditions` and
`CutoffEnergyDefectRowObligations` directly as those predicates, so that the row assembly of the
cutoff
estimate can consume them without unfolding the predicate at each use site.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The first error row of `p.response.transfer` on the response carriers, as
`CutoffEnergyDefectRowMinus`.**  Under the hypotheses of the carrier bound, the law-integral of the
cutoff half-energy of the terminal optimizer minus the terminal response is at most
`max 3 (32 d^2 responseCutoffProfileConst)` times
`τ^- + (τ^- E[J_t^-])^{1/2} + 3^{-H} E[J_t^-]`, which is exactly the named obligation
`CutoffEnergyDefectRowMinus` used by `e.response.cutoff.estimate`. -/
theorem cutoffEnergyDefectRowMinus_of_carriers {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (hjs : (jStar : ℤ) ≤ s) (e : Vec d) (φ : Vec d → ℝ)
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hblk : ∀ (j : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hDint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P)
    (hEint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P)
    (hWint : Integrable (fun a => volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
      scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)) P) :
    CutoffEnergyDefectRowMinus (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
      P jStar F H s t e φ uM := by
  unfold CutoffEnergyDefectRowMinus
  exact abs_integral_cutoffHalfEnergy_sub_respJ_le_rowMinus_of_carriers P hstat jStar hjStar F hm
    H s t ht hjs e φ hφ uM hmax hblk hJt hJs hDint hEint hWint

/-- **The first error row of `p.response.transfer` on the response carriers, as
`CutoffEnergyDefectRowPlus`.**  This is the adjoint-sign twin of
`cutoffEnergyDefectRowMinus_of_carriers`: under the hypotheses of the carrier bound for the
terminal optimizer `uP` of the adjoint recentred coefficient, the law-integral of the cutoff
half-energy of `uP` minus the terminal response is at most
`max 3 (32 d^2 responseCutoffProfileConst)` times
`τ^+ + (τ^+ E[J_t^+])^{1/2} + 3^{-H} E[J_t^+]`, which is exactly the named obligation
`CutoffEnergyDefectRowPlus` used by `e.response.cutoff.estimate`. -/
theorem cutoffEnergyDefectRowPlus_of_carriers {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (hjs : (jStar : ℤ) ≤ s) (e : Vec d) (φ : Vec d → ℝ)
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hblk : ∀ (j : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hDint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P)
    (hEint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P)
    (hWint : Integrable (fun a => volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
      scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)) P) :
    CutoffEnergyDefectRowPlus (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
      P jStar F H s t e φ uP := by
  unfold CutoffEnergyDefectRowPlus
  exact abs_integral_cutoffHalfEnergy_sub_respJ_le_rowPlus_of_carriers P hstat jStar hjStar F hm
    H s t ht hjs e φ hφ uP hmax hblk hJt hJs hDint hEint hWint

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The terminal-optimizer replacement row with no sample-side residue

The terminal-optimizer replacement row of `p.response.transfer` — the first error row of
`e.response.cutoff.estimate` — was stated on the response carriers with three sample-side
integrability hypotheses left open: the subcell deficits, the subcell energies, and the
cutoff-weighted terminal energy.  All three follow from the data the row already carries, so the
row holds with no sample-side residue beyond the measurability of the subcell energies.

The two declarations below restate `cutoffEnergyDefectRowMinus_of_carriers` and its adjoint twin
with those three integrability hypotheses removed, discharging them from the subcell-energy
measurability as an almost-everywhere strong measurability.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The first error row of `p.response.transfer` on the response carriers with no sample-side
residue, minus sign.**  Under the hypotheses of the carrier bound for the terminal optimizer `uM`
of the recentred coefficient `a_- = a - g`, only the subcell-energy measurability
(`hmeasE`) is assumed: the integrability of the subcell deficits, of the subcell energies and of
the cutoff-weighted terminal energy follows from it, together with the annealed data already
carried.  The conclusion is the named obligation
`CutoffEnergyDefectRowMinus` at the explicit constant
`max 3 (32 d^2 responseCutoffProfileConst)`. -/
theorem cutoffEnergyDefectRowMinus_of_carriers_of_measurable {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (hjs : (jStar : ℤ) ≤ s) (e : Vec d) (φ : Vec d → ℝ)
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hblk : ∀ (j : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hJs : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hmeasE : ∀ w ∈ triadicIndexBox d H, Measurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))) :
    CutoffEnergyDefectRowMinus (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
      P jStar F H s t e φ uM := by
  have hmeasEae : ∀ w ∈ triadicIndexBox d H, MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P :=
    fun w hw => (hmeasE w hw).aestronglyMeasurable
  have hmeasW : MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)) P := by
    have hφm : Measurable φ := hφ.2.2.2.2.2.1.continuous.measurable
    refine (measurable_volumeAverage_weighted_energy_respCoeffMinus P jStar hjStar F hm t e uM
      hmax (eta := fun x => φ x - 1) ?_ ?_).aestronglyMeasurable
    · exact (hφm.sub measurable_const).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        linarith only [abs_isResponseCutoff_sub_one hφ x])
  have hD : ∀ w ∈ triadicIndexBox d H, MeasureTheory.Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P :=
    integrable_subcellDeficit_respCoeffMinus P jStar hjStar F hm H s t ht hjs e uM hmax
      (hblk s) hJt hmeasEae
  have hE : ∀ w ∈ triadicIndexBox d H, MeasureTheory.Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P :=
    integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus P jStar hjStar F hm H s t ht e
      uM hmax hJt hmeasEae
  have hW : MeasureTheory.Integrable (fun a =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)) P :=
    integrable_volumeAverage_weighted_energy_respCoeffMinus P jStar hjStar F hm t e φ hφ uM
      hmax hJt hmeasW
  exact cutoffEnergyDefectRowMinus_of_carriers P hstat jStar hjStar F hm H s t ht hjs e φ hφ uM
    hmax hblk hJt hJs hD hE hW

/-- **The first error row of `p.response.transfer` on the response carriers with no sample-side
residue, plus sign.**  This is the adjoint twin of
`cutoffEnergyDefectRowMinus_of_carriers_of_measurable`: the coefficient family `a_+ = aᵀ + g`, the
dual load `q^+` and the terminal optimizer family `uP` replace their minus-sign counterparts, and
the subcell-energy measurability discharges the same three sample-side integrabilities.  The
conclusion is the named obligation `CutoffEnergyDefectRowPlus` at the explicit constant
`max 3 (32 d^2 responseCutoffProfileConst)`. -/
theorem cutoffEnergyDefectRowPlus_of_carriers_of_measurable {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (hjs : (jStar : ℤ) ≤ s) (e : Vec d) (φ : Vec d → ℝ)
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hblk : ∀ (j : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hJs : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hmeasE : ∀ w ∈ triadicIndexBox d H, Measurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))) :
    CutoffEnergyDefectRowPlus (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
      P jStar F H s t e φ uP := by
  have hmeasEae : ∀ w ∈ triadicIndexBox d H, MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P :=
    fun w hw => (hmeasE w hw).aestronglyMeasurable
  have hmeasW : MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)) P := by
    have hφm : Measurable φ := hφ.2.2.2.2.2.1.continuous.measurable
    refine (measurable_volumeAverage_weighted_energy_respCoeffPlus P jStar hjStar F hm t e uP
      hmax (eta := fun x => φ x - 1) ?_ ?_).aestronglyMeasurable
    · exact (hφm.sub measurable_const).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        linarith only [abs_isResponseCutoff_sub_one hφ x])
  have hD : ∀ w ∈ triadicIndexBox d H, MeasureTheory.Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P :=
    integrable_subcellDeficit_respCoeffPlus P jStar hjStar F hm H s t ht hjs e uP hmax
      (hblk s) hJt hmeasEae
  have hE : ∀ w ∈ triadicIndexBox d H, MeasureTheory.Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P :=
    integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus P jStar hjStar F hm H s t ht e
      uP hmax hJt hmeasEae
  have hW : MeasureTheory.Integrable (fun a =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)) P :=
    integrable_volumeAverage_weighted_energy_respCoeffPlus P jStar hjStar F hm t e φ hφ uP
      hmax hJt hmeasW
  exact cutoffEnergyDefectRowPlus_of_carriers P hstat jStar hjStar F hm H s t ht hjs e φ hφ uP
    hmax hblk hJt hJs hD hE hW

/-- **The terminal-optimizer replacement row of `p.response.transfer` on the carriers, minus
sign.**  The row holds with no sample-side hypothesis beyond the annealed data it already carries:
the measurability of the subcell energies is supplied by the canonical selection, and the three
integrabilities of the subcell deficits, of the subcell energies and of the cutoff-weighted
terminal energy follow by domination. -/
theorem cutoffEnergyDefectRowMinus_of_carriers_clean {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (hjs : (jStar : ℤ) ≤ s) (e : Vec d) (φ : Vec d → ℝ)
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hblk : ∀ (j : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hJs : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P) :
    CutoffEnergyDefectRowMinus (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
      P jStar F H s t e φ uM :=
  cutoffEnergyDefectRowMinus_of_carriers_of_measurable P hstat jStar hjStar F hm H s t ht hjs e φ
    hφ uM hmax hblk hJt hJs
    (fun w hw => measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus P jStar hjStar F hm
      H s t ht e uM hmax w hw)

/-- **The terminal-optimizer replacement row of `p.response.transfer` on the carriers, plus
sign.**  The adjoint twin of `cutoffEnergyDefectRowMinus_of_carriers_clean`. -/
theorem cutoffEnergyDefectRowPlus_of_carriers_clean {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (hjs : (jStar : ℤ) ≤ s) (e : Vec d) (φ : Vec d → ℝ)
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hblk : ∀ (j : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hJs : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P) :
    CutoffEnergyDefectRowPlus (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
      P jStar F H s t e φ uP :=
  cutoffEnergyDefectRowPlus_of_carriers_of_measurable P hstat jStar hjStar F hm H s t ht hjs e φ
    hφ uP hmax hblk hJt hJs
    (fun w hw => measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus P jStar hjStar F hm
      H s t ht e uP hmax w hw)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The two named error rows are monotone in their constant

The energy-defect row and the cutoff-mean row of `p.response.transfer` are produced with different
constants — `max 3 (32 d² Θ)` and `max 1 (respCutoffOscConst d)` — while the row assembly consumes
both at one common constant.  Both right-hand sides are the constant times a nonnegative quantity,
so raising the constant preserves the bound.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The energy-defect row weakens as the constant grows. -/
theorem cutoffEnergyDefectRowMinus_mono {C C' : ℝ} (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hτ : 0 ≤ respTauMinus P jStar F s t e) (hEJ : 0 ≤ respEJMinus P jStar F t e)
    (hCC : C ≤ C') (h : CutoffEnergyDefectRowMinus C P jStar F H s t e φ uM) :
    CutoffEnergyDefectRowMinus C' P jStar F H s t e φ uM := by
  unfold CutoffEnergyDefectRowMinus at h ⊢
  refine h.trans (mul_le_mul_of_nonneg_right hCC ?_)
  have h1 : (0 : ℝ) ≤ Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) :=
    Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e :=
    mul_nonneg (by positivity) hEJ
  linarith only [hτ, h1, h2]

/-- The adjoint energy-defect row weakens as the constant grows. -/
theorem cutoffEnergyDefectRowPlus_mono {C C' : ℝ} (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hτ : 0 ≤ respTauPlus P jStar F s t e) (hEJ : 0 ≤ respEJPlus P jStar F t e)
    (hCC : C ≤ C') (h : CutoffEnergyDefectRowPlus C P jStar F H s t e φ uP) :
    CutoffEnergyDefectRowPlus C' P jStar F H s t e φ uP := by
  unfold CutoffEnergyDefectRowPlus at h ⊢
  refine h.trans (mul_le_mul_of_nonneg_right hCC ?_)
  have h1 : (0 : ℝ) ≤ Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) :=
    Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e :=
    mul_nonneg (by positivity) hEJ
  linarith only [hτ, h1, h2]

/-- The cutoff-mean row weakens as the constant grows. -/
theorem cutoffMeanRowMinus_mono {C C' : ℝ} (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hCC : C ≤ C') (h : CutoffMeanRowMinus C P jStar F H s t e φ uM) :
    CutoffMeanRowMinus C' P jStar F H s t e φ uM := by
  unfold CutoffMeanRowMinus at h ⊢
  refine h.trans (add_le_add (mul_le_mul_of_nonneg_right hCC (Real.sqrt_nonneg _))
    (mul_le_mul_of_nonneg_right hCC ?_))
  exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)

/-- The adjoint cutoff-mean row weakens as the constant grows. -/
theorem cutoffMeanRowPlus_mono {C C' : ℝ} (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hCC : C ≤ C') (h : CutoffMeanRowPlus C P jStar F H s t e φ uP) :
    CutoffMeanRowPlus C' P jStar F H s t e φ uP := by
  unfold CutoffMeanRowPlus at h ⊢
  refine h.trans (add_le_add (mul_le_mul_of_nonneg_right hCC (Real.sqrt_nonneg _))
    (mul_le_mul_of_nonneg_right hCC ?_))
  exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)

end

end HCPolySupport.HighContrast.Multiscale
end
