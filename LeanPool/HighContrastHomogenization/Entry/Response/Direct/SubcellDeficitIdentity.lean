/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TerminalDeficitCarrierBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.BesovScaleSummationToolkit
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Pairing.SubcellDualPairingIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.StationaryAnnealedErrorScalars

/-!
# High-contrast homogenization: Entry.Response.Direct.SubcellDeficitIdentity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Subcell Deficit of the First Error Row

On each coarse subcell of the terminal cell, the terminal optimizer restricted there is an
admissible competitor for the subcell's own response problem, so the subcell deficit — response
minus the average of the terminal optimizer's response integrand — is nonnegative, pathwise, at
a pointwise elliptic representative of `respCoeff∓ F a`. Exact partition averaging collapses
the flat average of the subcell averages of that integrand to its average over the terminal cell,
so the flat average of the deficits equals the flat average of the subcell responses minus the
terminal response, an identity between `P`-integrable quantities. The response integrand of a
`b`-harmonic field expands pointwise as `-(1/2) ∇v·b∇v - p·(b∇v) + q·∇v`, so its
average over a subset is minus half the symmetric energy plus the pairing of `(-p, q)` with the
slot-swapped cell average; the pathwise response on every subcell is likewise `P`-integrable.
These are the pathwise and averaged subcell-deficit facts that the cell half of
`p.response.transfer` consumes.
-/

section
/-!
## Entrywise integrability of the coarse block response on every aligned subcell

The stationarity input of the terminal-optimizer replacement of `p.response.transfer` needs the
annealed response on each aligned cell of a fixed scale, so the pathwise response must be
`P`-integrable there for every aligned cell and not only for the centred one.  On an aligned cell
the pathwise response is a quadratic form in the entries of the recentred coarse block, and the
entries of that block are fixed real linear combinations of the entries of the coarse block of
the sample; `HasIntegrableCoarseBlock` therefore transfers to the recentred block and the
response is integrable.  This module records that consequence for the two recentred families
`a_-` and `a_+`.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  blockVecDot_blockMatVecMul_eq_sum coarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Entrywise integrability of the response on an aligned subcell, minus sign.**  If every
entry of the coarse block of the sample is `P`-integrable on the aligned cell
`adaptedCellAtCenter q j w` of the scale `3^j q ℤ^d`, then the pathwise response
`ResponseJ (adaptedCellAtCenter q j w) p r a_-` of the recentred coefficient `a_- = a - g` is
`P`-integrable. -/
theorem integrable_responseJ_respCoeffMinus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] {q : Mat d} (hq : IsUnit q)
    (F : BlockMat d) (j : ℤ) (w : Fin d → ℤ) (p r : Vec d)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter q j w)) :
    Integrable (fun a => ResponseJ (adaptedCellAtCenter q j w) p r (respCoeffMinus F a)) P := by
  have hquad : ∀ a : CoeffSpace d,
      HasQuadraticMu (adaptedCellAtCenter q j w) (⇑a.1 : CoeffField d) :=
    fun a => by
      simpa only [adaptedCellAtCenter] using
        hasQuadraticMu_adaptedCellTranslate q hq j (adaptedCellCenter q j w) a
  have hb : ∀ a : CoeffSpace d,
      coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a)
        = blockCongr (respG F) (coarseBlock (adaptedCellAtCenter q j w) a) :=
    fun a => coarseBlockMatrix_sub_skew_eq_blockCongr (U := adaptedCellAtCenter q j w)
      (a := (⇑a.1 : CoeffField d)) (g := respg F) (respg_isSkew F) (hquad a)
  have hint' : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a)) α β) P :=
    integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (G := respG F)
      (V := adaptedCellAtCenter q j w) (b := respCoeffMinus F) hint hb
  have hterm : ∀ α β : BlockCoord d, Integrable (fun a =>
      toFullBlockVec (-p, r) α *
        (blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter q j w)
          (respCoeffMinus F a)) α β * toFullBlockVec (-p, r) β)) P :=
    fun α β =>
      ((hint' α β).mul_const (toFullBlockVec (-p, r) β)).const_mul (toFullBlockVec (-p, r) α)
  have hQint : Integrable (fun a => blockVecDot (-p, r)
      (blockMatVecMul (coarseBlockMatrix (adaptedCellAtCenter q j w)
        (respCoeffMinus F a)) (-p, r))) P := by
    simp only [blockVecDot_blockMatVecMul_eq_sum]
    exact integrable_finsetSum _ fun α _ =>
      integrable_finsetSum _ fun β _ => hterm α β
  have hpath : ∀ a : CoeffSpace d,
      ResponseJ (adaptedCellAtCenter q j w) p r (respCoeffMinus F a)
        = (1 / 2 : ℝ) * blockVecDot (-p, r)
            (blockMatVecMul
              (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a))
              (-p, r))
          - vecDot p r :=
    fun a => responseJ_adaptedCellAtCenter_respCoeffMinus q hq j w F a p r
  have hfun : (fun a => ResponseJ (adaptedCellAtCenter q j w) p r (respCoeffMinus F a))
      = fun a => (1 / 2 : ℝ) * blockVecDot (-p, r)
            (blockMatVecMul
              (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a))
              (-p, r))
          - vecDot p r :=
    funext hpath
  rw [hfun]
  exact (hQint.const_mul (1 / 2 : ℝ)).sub (integrable_const (vecDot p r))

/-- **Entrywise integrability of the response on an aligned subcell, plus sign.**  If every
entry of the coarse block of the sample is `P`-integrable on the aligned cell
`adaptedCellAtCenter q j w` of the scale `3^j q ℤ^d`, then the pathwise response
`ResponseJ (adaptedCellAtCenter q j w) p r a_+` of the transposed recentred coefficient
`a_+ = aᵀ + g` is `P`-integrable. -/
theorem integrable_responseJ_respCoeffPlus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] {q : Mat d} (hq : IsUnit q)
    (F : BlockMat d) (j : ℤ) (w : Fin d → ℤ) (p r : Vec d)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter q j w)) :
    Integrable (fun a => ResponseJ (adaptedCellAtCenter q j w) p r (respCoeffPlus F a)) P := by
  have hb : ∀ a : CoeffSpace d,
      coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a)
        = blockCongr (respGPlus F) (coarseBlock (adaptedCellAtCenter q j w) a) :=
    fun a => coarseBlockMatrix_respCoeffPlus_at hq j w F a
  have hint' : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a)) α β) P :=
    integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (G := respGPlus F)
      (V := adaptedCellAtCenter q j w) (b := respCoeffPlus F) hint hb
  have hterm : ∀ α β : BlockCoord d, Integrable (fun a =>
      toFullBlockVec (-p, r) α *
        (blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter q j w)
          (respCoeffPlus F a)) α β * toFullBlockVec (-p, r) β)) P :=
    fun α β =>
      ((hint' α β).mul_const (toFullBlockVec (-p, r) β)).const_mul (toFullBlockVec (-p, r) α)
  have hQint : Integrable (fun a => blockVecDot (-p, r)
      (blockMatVecMul (coarseBlockMatrix (adaptedCellAtCenter q j w)
        (respCoeffPlus F a)) (-p, r))) P := by
    simp only [blockVecDot_blockMatVecMul_eq_sum]
    exact integrable_finsetSum _ fun α _ =>
      integrable_finsetSum _ fun β _ => hterm α β
  have hpath : ∀ a : CoeffSpace d,
      ResponseJ (adaptedCellAtCenter q j w) p r (respCoeffPlus F a)
        = (1 / 2 : ℝ) * blockVecDot (-p, r)
            (blockMatVecMul
              (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a))
              (-p, r))
          - vecDot p r :=
    fun a => responseJ_adaptedCellAtCenter_respCoeffPlus q hq j w F a p r
  have hfun : (fun a => ResponseJ (adaptedCellAtCenter q j w) p r (respCoeffPlus F a))
      = fun a => (1 / 2 : ℝ) * blockVecDot (-p, r)
            (blockMatVecMul
              (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a))
              (-p, r))
          - vecDot p r :=
    funext hpath
  rw [hfun]
  exact (hQint.const_mul (1 / 2 : ℝ)).sub (integrable_const (vecDot p r))

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The flat sum of the subcell deficits of the first error row

The subcell deficit of the first error row of `p.response.transfer` is the amount by which the
terminal optimizer fails to maximize the response on an aligned subcell of the coarse scale.
Exact partition averaging collapses the flat average of the subcell averages of the response
integrand of the terminal optimizer to its average over the terminal cell, which at a maximizer
is the terminal response.  Hence the flat average of the subcell deficits is the flat average of
the subcell responses minus the terminal response, an identity between quantities each of which
is a fixed linear functional of the coarse blocks of the sample and is therefore `P`-integrable.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The flat sum of the subcell deficits is the flat sum of the subcell responses minus the
terminal response, minus sign.**  On each aligned subcell of the coarse scale the first error row
of `p.response.transfer` measures the response of the sample against the subcell average of the
response integrand of the terminal optimizer.  The subcells partition the terminal cell and all
have the same volume, so the normalized sum of those averages is the terminal cell average, which
at a maximizer is the terminal response `J_t^-`.  Therefore the normalized sum of the subcell
deficits equals the normalized sum of the subcell responses minus `J_t^-`. -/
theorem avsum_subcellDeficit_respCoeffMinus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a)) (a : CoeffSpace d) :
    (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
        (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))
      = (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
          ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hts : t - (H : ℤ) = s := by
    rw [ht]
    ring
  have hf : IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))
      (HighContrast.adaptedCell (respGrid jStar F) t) := by
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
    have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    have hv : IntegrableOn
        (scalarResponseIntegrand (respCell jStar F t) f
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
          (Response.aHarmonicOfAEEq hae (uM a))) (respCell jStar F t) :=
      hdata.response (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        (Response.aHarmonicOfAEEq hae (uM a))
    exact integrableOn_scalarResponseIntegrand_aHarmonicFunctionOfAEEqCoeff (subset_refl _)
      hae.symm (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
      (Response.aHarmonicOfAEEq hae (uM a)) hv
  have hpart := avsum_volumeAverage_eq (respGrid jStar F) hq t H
    (f := scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)) hf
  have hpart' : (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))
      = respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a) := by
    rw [show (∑ w ∈ triadicIndexBox d H,
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))
        = ∑ w ∈ triadicIndexBox d H,
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)) by
      exact Finset.sum_congr rfl (fun w _ => by rw [hts])] at hpart
    rw [hpart]
    simpa only [respJ, respCell] using
      (responseJ_eq_of_isResponseMaximizer (respCell jStar F t)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        (respCoeffMinus F a) (hmax a)).symm
  rw [Finset.sum_sub_distrib, mul_sub, hpart']

/-- **The flat sum of the subcell deficits is the flat sum of the subcell responses minus the
terminal response, plus sign.**  The transposed twin of `avsum_subcellDeficit_respCoeffMinus_eq`:
the coefficient family `a_+ = aᵀ + g`, the dual load `q^+` and the terminal optimizer family `uP`
replace their minus-sign counterparts, and the terminal response is `J_t^+`. -/
theorem avsum_subcellDeficit_respCoeffPlus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a)) (a : CoeffSpace d) :
    (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
        (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))
      = (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
          ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hts : t - (H : ℤ) = s := by
    rw [ht]
    ring
  have hf : IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))
      (HighContrast.adaptedCell (respGrid jStar F) t) := by
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
    have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    have hv : IntegrableOn
        (scalarResponseIntegrand (respCell jStar F t) f
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
          (Response.aHarmonicOfAEEq hae (uP a))) (respCell jStar F t) :=
      hdata.response (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
        (Response.aHarmonicOfAEEq hae (uP a))
    exact integrableOn_scalarResponseIntegrand_aHarmonicFunctionOfAEEqCoeff (subset_refl _)
      hae.symm (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
      (Response.aHarmonicOfAEEq hae (uP a)) hv
  have hpart := avsum_volumeAverage_eq (respGrid jStar F) hq t H
    (f := scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)) hf
  have hpart' : (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))
      = respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a) := by
    rw [show (∑ w ∈ triadicIndexBox d H,
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))
        = ∑ w ∈ triadicIndexBox d H,
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)) by
      exact Finset.sum_congr rfl (fun w _ => by rw [hts])] at hpart
    rw [hpart]
    simpa only [respJ, respCell] using
      (responseJ_eq_of_isResponseMaximizer (respCell jStar F t)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
        (respCoeffPlus F a) (hmax a)).symm
  rw [Finset.sum_sub_distrib, mul_sub, hpart']

/-- **Integrability of the flat sum of the subcell responses, minus sign.**  Each aligned subcell
response of the recentred coefficient `a_-` is `P`-integrable when the coarse blocks of the sample
are, so the normalized sum over the triadic index box is `P`-integrable as well. -/
theorem integrable_avsum_responseJ_adaptedCellAtCenter_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s : ℤ) (p r : Vec d)
    (hblk : ∀ w : Fin d → ℤ, HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w)) :
    MeasureTheory.Integrable (fun a => (((triadicIndexBox d H).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d H, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) p r
        (respCoeffMinus F a)) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  exact (integrable_finsetSum (triadicIndexBox d H) fun w _ =>
    integrable_responseJ_respCoeffMinus_adaptedCellAtCenter P hq F s w p r (hblk w)).const_mul _

/-- **Integrability of the flat sum of the subcell responses, plus sign.**  The transposed twin of
`integrable_avsum_responseJ_adaptedCellAtCenter_respCoeffMinus`, with the coefficient family `a_+`
instead of `a_-`. -/
theorem integrable_avsum_responseJ_adaptedCellAtCenter_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s : ℤ) (p r : Vec d)
    (hblk : ∀ w : Fin d → ℤ, HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w)) :
    MeasureTheory.Integrable (fun a => (((triadicIndexBox d H).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d H, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) p r
        (respCoeffPlus F a)) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  exact (integrable_finsetSum (triadicIndexBox d H) fun w _ =>
    integrable_responseJ_respCoeffPlus_adaptedCellAtCenter P hq F s w p r (hblk w)).const_mul _

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Nonnegativity of the subcell deficit at the response coefficients

On each coarse subcell of the terminal cell, the terminal optimiser restricted there is an
admissible competitor for the subcell's own response problem, so the subcell deficit of
`p.response.transfer` — the subcell response minus the average over the subcell of the terminal
optimiser's response integrand — is nonnegative, pathwise in the coefficient sample.  The response
coefficients `respCoeff∓ F a` are elliptic only almost everywhere, so the argument runs at the
pointwise elliptic representative supplied by `EllipticRepresentativeInputs` and transports both
the response
and the averaged integrand back across the almost-everywhere replacement, which leaves each of them
invariant.  This is the hypothesis `hD` of the cell half of the cutoff-mean row of
`p.response.transfer`, for the minus sign and for its plus twin.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The subcell deficit is nonnegative, minus family.**  Let `a_- = respCoeffMinus F a` be the
response coefficient of the terminal cell `U_t = respCell jStar F t`, let `uM a` be a `a_-`-harmonic
field on `U_t`, and suppose that on every aligned subcell `U_s(w)` the field `v w a` maximises that
subcell's response for the loads `(p, q^-)`.  Then, for every subcell `w` of the depth-`H` partition
of `U_t` (`t = s + H`) and every sample `a`, the subcell deficit

  `J(U_s(w), p, q^-; a_-) − ⨍_{U_s(w)} g_{U_t}(uM a)`

is nonnegative: `uM a` restricted to the subcell is an admissible competitor there, and the
restriction does not change the scalar response integrand.  The coefficient is elliptic only almost
everywhere, so the competitor argument is run at the pointwise elliptic representative of `a_-` and
both terms are carried back, which leaves them unchanged. -/
theorem zero_le_subcellDeficit_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffMinus F a) (adaptedCellAtCenter (respGrid jStar F) s w))
    (hv : ∀ (w : Fin d → ℤ) (a : CoeffSpace d),
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a) (v w a)) :
    ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)) := by
  subst t
  intro w hw a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm (s + (H : ℤ)) a
  have hk : (s + (H : ℤ)) - (H : ℤ) = s := by ring
  have hU : IsOpen (respCell jStar F (s + (H : ℤ))) :=
    isOpen_adaptedCell_of_isUnit hq (s + (H : ℤ))
  have hV : IsOpen (adaptedCellAtCenter (respGrid jStar F) s w) :=
    isOpen_adaptedCellAtCenter_of_isUnit hq s w
  have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F (s + (H : ℤ)) := by
    simpa only [hk] using!
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) (s + (H : ℤ)) H hw
  have hdom : IsOpenBoundedConvexDomain (adaptedCellAtCenter (respGrid jStar F) s w) :=
    isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq s w
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter (respGrid jStar F) s w)) := by
    simpa [volumeMeasureOn] using hdom.isFiniteMeasure_restrict_volume
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter (respGrid jStar F) s w) f :=
    hEll.mono hV.measurableSet hVU
  have haeV : respCoeffMinus F a =ᵐ[volumeMeasureOn (adaptedCellAtCenter (respGrid jStar F) s w)] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
  have hmaxV' : IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
      (respP (respMean P jStar F (s + (H : ℤ))) e)
      (respqMinus P jStar F (s + (H : ℤ)) e) f
      (Response.aHarmonicOfAEEq haeV (v w a)) :=
    isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff haeV
      (respP (respMean P jStar F (s + (H : ℤ))) e)
      (respqMinus P jStar F (s + (H : ℤ)) e) (hv w a)
  have hlef := volumeAverage_scalarResponseIntegrand_le_responseJ hU hV hVU hEllV
    (respP (respMean P jStar F (s + (H : ℤ))) e)
    (respqMinus P jStar F (s + (H : ℤ)) e)
    (Response.aHarmonicOfAEEq hae (uM a))
    (Response.aHarmonicOfAEEq haeV (v w a)) hmaxV'
  rw [responseJ_congr_of_ae_eq_subset hVU hae
        (respP (respMean P jStar F (s + (H : ℤ))) e)
        (respqMinus P jStar F (s + (H : ℤ)) e),
      ← volumeAverage_scalarResponseIntegrand_subset_aHarmonicFunctionOfAEEqCoeff hVU hae
        (respP (respMean P jStar F (s + (H : ℤ))) e)
        (respqMinus P jStar F (s + (H : ℤ)) e) (uM a)]
  linarith only [hlef]

/-- **The subcell deficit is nonnegative, plus family.**  The transposed twin of
`zero_le_subcellDeficit_respCoeffMinus`: with the response coefficient `a_+ = respCoeffPlus F a`,
the loads `(p, q^+)` and subcell maximisers `v w a` for `a_+`, the subcell deficit

  `J(U_s(w), p, q^+; a_+) − ⨍_{U_s(w)} g_{U_t}(uM a)`

is nonnegative on every subcell of the depth-`H` partition of the terminal cell, pathwise in the
sample `a`.  The a.e.-elliptic representative of `a_+` again makes the competitor argument valid. -/
theorem zero_le_subcellDeficit_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffPlus F a) (adaptedCellAtCenter (respGrid jStar F) s w))
    (hv : ∀ (w : Fin d → ℤ) (a : CoeffSpace d),
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a) (v w a)) :
    ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uM a)) := by
  subst t
  intro w hw a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm (s + (H : ℤ)) a
  have hk : (s + (H : ℤ)) - (H : ℤ) = s := by ring
  have hU : IsOpen (respCell jStar F (s + (H : ℤ))) :=
    isOpen_adaptedCell_of_isUnit hq (s + (H : ℤ))
  have hV : IsOpen (adaptedCellAtCenter (respGrid jStar F) s w) :=
    isOpen_adaptedCellAtCenter_of_isUnit hq s w
  have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F (s + (H : ℤ)) := by
    simpa only [hk] using!
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) (s + (H : ℤ)) H hw
  have hdom : IsOpenBoundedConvexDomain (adaptedCellAtCenter (respGrid jStar F) s w) :=
    isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq s w
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter (respGrid jStar F) s w)) := by
    simpa [volumeMeasureOn] using hdom.isFiniteMeasure_restrict_volume
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter (respGrid jStar F) s w) f :=
    hEll.mono hV.measurableSet hVU
  have haeV : respCoeffPlus F a =ᵐ[volumeMeasureOn (adaptedCellAtCenter (respGrid jStar F) s w)] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
  have hmaxV' : IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
      (respP (respMean P jStar F (s + (H : ℤ))) e)
      (respqPlus P jStar F (s + (H : ℤ)) e) f
      (Response.aHarmonicOfAEEq haeV (v w a)) :=
    isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff haeV
      (respP (respMean P jStar F (s + (H : ℤ))) e)
      (respqPlus P jStar F (s + (H : ℤ)) e) (hv w a)
  have hlef := volumeAverage_scalarResponseIntegrand_le_responseJ hU hV hVU hEllV
    (respP (respMean P jStar F (s + (H : ℤ))) e)
    (respqPlus P jStar F (s + (H : ℤ)) e)
    (Response.aHarmonicOfAEEq hae (uM a))
    (Response.aHarmonicOfAEEq haeV (v w a)) hmaxV'
  rw [responseJ_congr_of_ae_eq_subset hVU hae
        (respP (respMean P jStar F (s + (H : ℤ))) e)
        (respqPlus P jStar F (s + (H : ℤ)) e),
      ← volumeAverage_scalarResponseIntegrand_subset_aHarmonicFunctionOfAEEqCoeff hVU hae
        (respP (respMean P jStar F (s + (H : ℤ))) e)
        (respqPlus P jStar F (s + (H : ℤ)) e) (uM a)]
  linarith only [hlef]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The subcell average of the response integrand

The response integrand of a `b`-harmonic field expands pointwise as
`-(1/2) ∇v·b∇v - p·(b∇v) + q·∇v`.  Averaging this identity over an arbitrary measurable
subset `V` of the cell expresses the average of the response integrand as minus one half of
the average pathwise symmetric energy on `V`, plus the pairing of `(-p, q)` with the
slot-swapped cell average of the doubled optimizer field on `V`.  This is the algebraic
expansion behind the cell-average half of the response identity, stated on a subcell rather
than on the cell itself, which is what turns the subcell deficit of the first error row of
`p.response.transfer` into quantities that are measurable in the sample.

The general identity is stated for an arbitrary subcell `V ⊆ U` and the three integrability
facts it consumes; the two carrier specialisations run it on an aligned adapted subcell and
transport the result across the almost-everywhere elliptic representative of a response
coefficient.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The subcell average of the response integrand of a `b`-harmonic field on `U`: the average
over any subset `V ⊆ U` is minus one half of the average pathwise symmetric energy on `V`, plus
the pairing of `(-p, r)` with the slot-swapped average of the doubled optimizer field on `V`. -/
theorem volumeAverage_scalarResponseIntegrand_subset_eq_blockVecDot {d : ℕ} [NeZero d]
    {U V : Set (Vec d)} (hVU : V ⊆ U) {b : CoeffField d}
    (v : AHarmonicFunction b U) (p r : Vec d)
    (hEnergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand b v) V)
    (hFlux : ∀ i : Fin d, MeasureTheory.IntegrableOn
      (fun x => matVecMul (b x) (v.toH1.grad x) i) V)
    (hGrad : ∀ i : Fin d, MeasureTheory.IntegrableOn (fun x => v.toH1.grad x i) V) :
    volumeAverage V (scalarResponseIntegrand U b p r v) =
      - (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand b v)
        + blockVecDot (-p, r)
            (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v))) := by
  have _hVUsub : V ⊆ U := hVU
  have hA : MeasureTheory.IntegrableOn
      (((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand b v)) V :=
    hEnergy.integrable.smul (-(1 / 2 : ℝ))
  have hF : MeasureTheory.IntegrableOn
      (fun x => vecDot p (matVecMul (b x) (v.toH1.grad x))) V := by
    have hsum : MeasureTheory.IntegrableOn
        (fun x => ∑ i, p i * matVecMul (b x) (v.toH1.grad x) i) V :=
      integrable_finsetSum Finset.univ (fun i _ => (hFlux i).const_mul (p i))
    simpa [vecDot] using hsum
  have hG : MeasureTheory.IntegrableOn (fun x => vecDot r (v.toH1.grad x)) V := by
    have hsum : MeasureTheory.IntegrableOn
        (fun x => ∑ i, r i * v.toH1.grad x i) V :=
      integrable_finsetSum Finset.univ (fun i _ => (hGrad i).const_mul (r i))
    simpa [vecDot] using hsum
  have hAB : MeasureTheory.IntegrableOn
      (((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand b v) -
        fun x => vecDot p (matVecMul (b x) (v.toH1.grad x))) V :=
    hA.integrable.sub hF.integrable
  have hdecomp : scalarResponseIntegrand U b p r v =
      (((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand b v) -
        (fun x => vecDot p (matVecMul (b x) (v.toH1.grad x)))) +
        (fun x => vecDot r (v.toH1.grad x)) := by
    funext x
    simp only [scalarResponseIntegrand, scalarVariationEnergyIntegrand, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [hdecomp, volumeAverage_add hAB hG, volumeAverage_sub hA hF, volumeAverage_smul]
  rw [volumeAverage_vecDot_left p (fun x => matVecMul (b x) (v.toH1.grad x)) hFlux,
    volumeAverage_vecDot_left r (fun x => v.toH1.grad x) hGrad]
  have hZ1 : (cellAverage V (optimizerField b v)).1
      = fun i => volumeAverage V (fun x => v.toH1.grad x i) := rfl
  have hZ2 : (cellAverage V (optimizerField b v)).2
      = fun i => volumeAverage V (fun x => matVecMul (b x) (v.toH1.grad x) i) := rfl
  have hs1 : (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v))).1
      = (cellAverage V (optimizerField b v)).2 := blockMatVecMul_blockSwap_fst _
  have hs2 : (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v))).2
      = (cellAverage V (optimizerField b v)).1 := blockMatVecMul_blockSwap_snd _
  rw [blockVecDot, hs1, hs2, hZ1, hZ2, vecDot_neg_left]
  ring

/-- The subcell average of the response integrand for the minus response coefficient, on an
aligned adapted subcell of the terminal cell: minus one half of the subcell energy plus the
pairing of `(-p, q^-)` with the slot-swapped subcell average of the doubled optimizer field.
The coefficient is transported from its almost-everywhere elliptic representative. -/
theorem volumeAverage_scalarResponseIntegrand_adaptedCellAtCenter_respCoeffMinus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (a : CoeffSpace d) (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d H) :
    volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)) =
      - (1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
        + blockVecDot (-(respP (respMean P jStar F t) e), respqMinus P jStar F t e)
            (blockMatVecMul (blockSwap d)
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffMinus F a) (uM a)))) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hs : s = t - (H : ℤ) := by omega
  have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F t := by
    rw [respCell, hs]
    exact adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) := by
    have hconv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
      adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t
    simpa [volumeMeasureOn] using hconv.isFiniteMeasure_restrict_volume
  set v : AHarmonicFunction f (respCell jStar F t) := Response.aHarmonicOfAEEq hae (uM a)
    with hv
  have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hEnergy : MeasureTheory.IntegrableOn
      (scalarVariationEnergyIntegrand f v) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    (hdata.energy v).mono_set hVU
  have hFlux : ∀ i : Fin d, MeasureTheory.IntegrableOn
      (fun x => matVecMul (f x) (v.toH1.grad x) i) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    fun i => by
      have h := (hdata.flux (Pi.single i 1) v).mono_set hVU
      simpa [vecDot_single_left] using h
  have hGrad : ∀ i : Fin d, MeasureTheory.IntegrableOn
      (fun x => v.toH1.grad x i) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    fun i => by
      have h := (hdata.grad (Pi.single i 1) v).mono_set hVU
      simpa [vecDot_single_left] using h
  have hmain := volumeAverage_scalarResponseIntegrand_subset_eq_blockVecDot hVU v
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) hEnergy hFlux hGrad
  have hresp : volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) f
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) v) =
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)) := by
    rw [hv]
    exact volumeAverage_scalarResponseIntegrand_subset_aHarmonicFunctionOfAEEqCoeff hVU hae
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)
  have henergy : volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand f v) =
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := by
    rw [hv]
    exact volumeAverage_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff hVU hae (uM a)
  have hcell : cellAverage (adaptedCellAtCenter (respGrid jStar F) s w) (optimizerField f v)
      = cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffMinus F a) (uM a)) := by
    rw [hv]
    refine cellAverage_congr_ae hVU ?_
    filter_upwards [hae] with x hx
    simp only [optimizerField, Response.aHarmonicOfAEEq_grad, hx]
  rw [hresp, henergy, hcell] at hmain
  exact hmain

/-- The plus twin of the subcell average identity, for the plus response coefficient and the
load `q^+`. -/
theorem volumeAverage_scalarResponseIntegrand_adaptedCellAtCenter_respCoeffPlus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (a : CoeffSpace d) (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d H) :
    volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)) =
      - (1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
        + blockVecDot (-(respP (respMean P jStar F t) e), respqPlus P jStar F t e)
            (blockMatVecMul (blockSwap d)
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (optimizerField (respCoeffPlus F a) (uP a)))) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hs : s = t - (H : ℤ) := by omega
  have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F t := by
    rw [respCell, hs]
    exact adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) := by
    have hconv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
      adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t
    simpa [volumeMeasureOn] using hconv.isFiniteMeasure_restrict_volume
  set v : AHarmonicFunction f (respCell jStar F t) := Response.aHarmonicOfAEEq hae (uP a)
    with hv
  have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hEnergy : MeasureTheory.IntegrableOn
      (scalarVariationEnergyIntegrand f v) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    (hdata.energy v).mono_set hVU
  have hFlux : ∀ i : Fin d, MeasureTheory.IntegrableOn
      (fun x => matVecMul (f x) (v.toH1.grad x) i) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    fun i => by
      have h := (hdata.flux (Pi.single i 1) v).mono_set hVU
      simpa [vecDot_single_left] using h
  have hGrad : ∀ i : Fin d, MeasureTheory.IntegrableOn
      (fun x => v.toH1.grad x i) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    fun i => by
      have h := (hdata.grad (Pi.single i 1) v).mono_set hVU
      simpa [vecDot_single_left] using h
  have hmain := volumeAverage_scalarResponseIntegrand_subset_eq_blockVecDot hVU v
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) hEnergy hFlux hGrad
  have hresp : volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) f
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) v) =
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)) := by
    rw [hv]
    exact volumeAverage_scalarResponseIntegrand_subset_aHarmonicFunctionOfAEEqCoeff hVU hae
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)
  have henergy : volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand f v) =
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := by
    rw [hv]
    exact volumeAverage_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff hVU hae (uP a)
  have hcell : cellAverage (adaptedCellAtCenter (respGrid jStar F) s w) (optimizerField f v)
      = cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffPlus F a) (uP a)) := by
    rw [hv]
    refine cellAverage_congr_ae hVU ?_
    filter_upwards [hae] with x hx
    simp only [optimizerField, Response.aHarmonicOfAEEq_grad, hx]
  rw [hresp, henergy, hcell] at hmain
  exact hmain

end

end HCPolySupport.HighContrast.Multiscale
end
