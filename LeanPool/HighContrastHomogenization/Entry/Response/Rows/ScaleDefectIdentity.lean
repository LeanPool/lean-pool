/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TerminalEnergyDeficitBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.StationaryAnnealedErrorScalars

/-!
# High-contrast homogenization: Entry.Response.Rows.ScaleDefectIdentity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Scale Defect as an Annealed Mean Deficit

Subdividing the terminal cell `U_t` into the aligned cells of the coarse scale `s`, the
restriction of the terminal optimizer to each subcell is an admissible competitor there, so its
response value falls short of that subcell's own response by a nonnegative deficit. Exact
partition averaging identifies the flat average of the restricted response values with the
terminal response itself, and stationarity identifies the annealed subcell response with the
annealed response at the coarse scale on every subcell; taking expectations, the flat average of
the deficits equals exactly the scale defect `tau^± = E[J(U_s)] - E[J(U_t)]`. Because the
quadratic-response identity measures the energy of a difference field by twice the deficit, the
row assembly consumes this defect with a factor two: the flat average, over the depth-`H` aligned
subcells, of twice each subcell's deficit integrates to `2 tau^∓`. The identity is the mean-deficit
row of `p.response.transfer`.
-/

section
/-!
## The mean deficit of the subdivision is the scale defect

The terminal-optimizer replacement of `p.response.transfer` subdivides the terminal cell `U_t`
into the `3 ^ (H * d)` aligned cells of the coarse scale `s`.  On each of them the restriction of
the terminal optimizer is an admissible competitor, so its response value falls short of that
subcell's own response by a nonnegative deficit.  Exact partition averaging says that the flat
average of the restricted response values is the terminal response value itself, and stationarity
says that the annealed subcell response is the same on every subcell, hence equal to the annealed
response at the coarse scale.  Therefore the expectation of the flat average of the deficits is
exactly the scale defect

  `tau^± = E[J(U_s, p, q^±; a_±)] - E[J(U_t, p, q^±; a_±)]`.

No subcell optimizer is selected: the deficit is defined directly from the restricted terminal
optimizer, so no measurability of a subcell optimizer family is needed.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The mean subcell deficit of the subdivision is the minus scale defect**
(`p.response.transfer`).  For a stationary law `P`, the flat average over the depth-`H` aligned
subcells of the coarse scale `s` of the gap between each subcell's own response and the restricted
terminal response integrates to the defect `respTauMinus` between the coarse and terminal scales.
The restricted-response half identifies the averaged pathwise response with the terminal response
by exact partition averaging, and the subcell-response half replaces the averaged subcell responses
by the common annealed coarse-scale response by stationarity. -/
theorem integral_avsum_subcellDeficit_eq_respTauMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (hjs : (jStar : ℤ) ≤ s) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hrespint : ∀ a, MeasureTheory.IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))
      (respCell jStar F t))
    (hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hRint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P)
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P) :
    (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
        (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) ∂P)
      = respTauMinus P jStar F s t e := by
  classical
  have hq : IsUnit (respGrid jStar F) := by
    simpa [respGrid] using Geometry.isUnit_roundedGrid hjStar hm
  have _ := hJt
  have _ := hJs
  have hcard : (triadicIndexBox d H).card ≠ 0 :=
    Finset.card_ne_zero_of_mem (zero_mem_triadicIndexBox H)
  have hN0 : (((triadicIndexBox d H).card : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hcard
  have hcJs : (∫ a, respJ (respGrid jStar F) s
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        (respCoeffMinus F a) ∂P)
      = blockResponseEnergy (blockCongr (respG F) (respMean P jStar F s))
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) := by
    have h0 := integral_responseJ_respCoeffMinus_adaptedCellAtCenter_eq_direct P hstat jStar hjStar F hm s hjs 0
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (hblk 0)
    rw [adaptedCellAtCenter_zero (respGrid jStar F) s] at h0
    simpa only [respJ] using h0
  have hpath : ∀ a : CoeffSpace d,
      (((triadicIndexBox d H).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d H,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))
        = respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a) := by
    intro a
    have h := avsum_volumeAverage_scalarResponseIntegrand_eq_responseJ (respGrid jStar F) hq t H
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a) (hmax a) (hrespint a)
    have ht' : t - (H : ℤ) = s := by rw [ht]; ring
    rw [ht'] at h
    simpa only [respJ, respCell] using h
  have hJsum : (((triadicIndexBox d H).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
          (respCoeffMinus F a) ∂P)
      = (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P) := by
    have hc : ∀ w ∈ triadicIndexBox d H,
        (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
          (respCoeffMinus F a) ∂P)
        = (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P) := by
      intro w _
      have hw' := integral_responseJ_respCoeffMinus_adaptedCellAtCenter_eq_direct P hstat jStar hjStar F hm s hjs w
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (hblk w)
      rw [hcJs]
      exact hw'
    have hsum : ∑ w ∈ triadicIndexBox d H,
        (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
          (respCoeffMinus F a) ∂P)
        = (triadicIndexBox d H).card •
          (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P) := by
      rw [Finset.sum_congr rfl hc, Finset.sum_const]
    rw [hsum, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  have hRsum : (((triadicIndexBox d H).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (∫ a, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
            (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)) ∂P)
      = respEJMinus P jStar F t e := by
    have hInt1 : (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)) ∂P)
        = (((triadicIndexBox d H).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d H,
            (∫ a, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)) ∂P) := by
      rw [integral_const_mul,
        integral_finsetSum (triadicIndexBox d H) (fun w hw => hRint w hw)]
    have hInt2 : (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)) ∂P)
        = (∫ a, respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P) := by
      refine integral_congr_ae ?_
      filter_upwards with a
      exact hpath a
    rw [← hInt1, hInt2]
    rfl
  have hsubint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)
      - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
            (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P :=
    fun w hw => (hJint w hw).sub (hRint w hw)
  calc (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
              (respCoeffMinus F a)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                  (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) ∂P)
      = (((triadicIndexBox d H).card : ℝ))⁻¹ *
          (∫ a, ∑ w ∈ triadicIndexBox d H,
            (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
                (respCoeffMinus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) ∂P) := by
        rw [integral_const_mul]
      _ = (((triadicIndexBox d H).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d H,
            (∫ a, (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
                (respCoeffMinus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) ∂P) := by
        rw [integral_finsetSum (triadicIndexBox d H) hsubint]
      _ = (((triadicIndexBox d H).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d H,
            ((∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
                (respCoeffMinus F a) ∂P)
              - (∫ a, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)) ∂P)) := by
        exact congrArg (fun t : ℝ => (((triadicIndexBox d H).card : ℝ))⁻¹ * t)
          (Finset.sum_congr rfl (fun w hw => integral_sub (hJint w hw) (hRint w hw)))
      _ = (((triadicIndexBox d H).card : ℝ))⁻¹ *
          (∑ w ∈ triadicIndexBox d H,
            (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
                (respCoeffMinus F a) ∂P)
          - ∑ w ∈ triadicIndexBox d H,
            (∫ a, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                  (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)) ∂P)) := by
        rw [Finset.sum_sub_distrib]
      _ = (((triadicIndexBox d H).card : ℝ))⁻¹ *
            (∑ w ∈ triadicIndexBox d H,
              (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
                  (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
                  (respCoeffMinus F a) ∂P))
          - (((triadicIndexBox d H).card : ℝ))⁻¹ *
            (∑ w ∈ triadicIndexBox d H,
              (∫ a, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)) ∂P)) := by
        rw [mul_sub]
      _ = respTauMinus P jStar F s t e := by
        rw [hJsum, hRsum]
        rfl

/-- **The mean subcell deficit of the subdivision is the plus scale defect**
(`p.response.transfer`).  The adjoint twin of `integral_avsum_subcellDeficit_eq_respTauMinus`:
for a stationary law `P`, the flat average over the depth-`H` aligned subcells of the coarse scale
`s` of the gap between each subcell's own response and the restricted terminal response integrates
to the adjoint defect `respTauPlus`.  The restricted-response half is exact partition averaging and
the subcell-response half is the stationarity of the adjoint annealed response. -/
theorem integral_avsum_subcellDeficit_eq_respTauPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (hjs : (jStar : ℤ) ≤ s) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hrespint : ∀ a, MeasureTheory.IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))
      (respCell jStar F t))
    (hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hRint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P)
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P) :
    (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
        (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) ∂P)
      = respTauPlus P jStar F s t e := by
  classical
  have hq : IsUnit (respGrid jStar F) := by
    simpa [respGrid] using Geometry.isUnit_roundedGrid hjStar hm
  have _ := hJt
  have _ := hJs
  have hcard : (triadicIndexBox d H).card ≠ 0 :=
    Finset.card_ne_zero_of_mem (zero_mem_triadicIndexBox H)
  have hN0 : (((triadicIndexBox d H).card : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hcard
  have hcJs : (∫ a, respJ (respGrid jStar F) s
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
        (respCoeffPlus F a) ∂P)
      = blockResponseEnergy (blockCongr (respGPlus F) (respMean P jStar F s))
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) := by
    have h0 := integral_responseJ_respCoeffPlus_adaptedCellAtCenter_eq_direct P hstat jStar hjStar F hm s hjs 0
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (hblk 0)
    rw [adaptedCellAtCenter_zero (respGrid jStar F) s] at h0
    simpa only [respJ] using h0
  have hpath : ∀ a : CoeffSpace d,
      (((triadicIndexBox d H).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d H,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))
        = respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a) := by
    intro a
    have h := avsum_volumeAverage_scalarResponseIntegrand_eq_responseJ (respGrid jStar F) hq t H
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a) (hmax a) (hrespint a)
    have ht' : t - (H : ℤ) = s := by rw [ht]; ring
    rw [ht'] at h
    simpa only [respJ, respCell] using h
  have hJsum : (((triadicIndexBox d H).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
          (respCoeffPlus F a) ∂P)
      = (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P) := by
    have hc : ∀ w ∈ triadicIndexBox d H,
        (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
          (respCoeffPlus F a) ∂P)
        = (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P) := by
      intro w _
      have hw' := integral_responseJ_respCoeffPlus_adaptedCellAtCenter_eq_direct P hstat jStar hjStar F hm s hjs w
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (hblk w)
      rw [hcJs]
      exact hw'
    have hsum : ∑ w ∈ triadicIndexBox d H,
        (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
          (respCoeffPlus F a) ∂P)
        = (triadicIndexBox d H).card •
          (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P) := by
      rw [Finset.sum_congr rfl hc, Finset.sum_const]
    rw [hsum, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  have hRsum : (((triadicIndexBox d H).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (∫ a, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)) ∂P)
      = respEJPlus P jStar F t e := by
    have hInt1 : (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)) ∂P)
        = (((triadicIndexBox d H).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d H,
            (∫ a, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)) ∂P) := by
      rw [integral_const_mul,
        integral_finsetSum (triadicIndexBox d H) (fun w hw => hRint w hw)]
    have hInt2 : (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)) ∂P)
        = (∫ a, respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P) := by
      refine integral_congr_ae ?_
      filter_upwards with a
      exact hpath a
    rw [← hInt1, hInt2]
    rfl
  have hsubint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)
      - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P :=
    fun w hw => (hJint w hw).sub (hRint w hw)
  calc (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
              (respCoeffPlus F a)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                  (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) ∂P)
      = (((triadicIndexBox d H).card : ℝ))⁻¹ *
          (∫ a, ∑ w ∈ triadicIndexBox d H,
            (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
                (respCoeffPlus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) ∂P) := by
        rw [integral_const_mul]
      _ = (((triadicIndexBox d H).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d H,
            (∫ a, (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
                (respCoeffPlus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) ∂P) := by
        rw [integral_finsetSum (triadicIndexBox d H) hsubint]
      _ = (((triadicIndexBox d H).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d H,
            ((∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
                (respCoeffPlus F a) ∂P)
              - (∫ a, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)) ∂P)) := by
        exact congrArg (fun t : ℝ => (((triadicIndexBox d H).card : ℝ))⁻¹ * t)
          (Finset.sum_congr rfl (fun w hw => integral_sub (hJint w hw) (hRint w hw)))
      _ = (((triadicIndexBox d H).card : ℝ))⁻¹ *
          (∑ w ∈ triadicIndexBox d H,
            (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
                (respCoeffPlus F a) ∂P)
          - ∑ w ∈ triadicIndexBox d H,
            (∫ a, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                  (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)) ∂P)) := by
        rw [Finset.sum_sub_distrib]
      _ = (((triadicIndexBox d H).card : ℝ))⁻¹ *
            (∑ w ∈ triadicIndexBox d H,
              (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
                  (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
                  (respCoeffPlus F a) ∂P))
          - (((triadicIndexBox d H).card : ℝ))⁻¹ *
            (∑ w ∈ triadicIndexBox d H,
              (∫ a, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)) ∂P)) := by
        rw [mul_sub]
      _ = respTauPlus P jStar F s t e := by
        rw [hJsum, hRsum]
        rfl

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Twice the annealed mean subcell deficit is twice the scale defect

The row assembly of `p.response.transfer` consumes the scale defect with a factor two, because the
quadratic-response identity measures the energy of the difference field by twice the deficit.  This
module records that rescaling of the mean subcell deficit: the flat average, over the depth-`H`
aligned subcells of the coarse scale `s`, of twice each subcell's deficit integrates to twice the
scale defect `tau^∓`.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Twice the mean subcell deficit is twice the minus scale defect** (`p.response.transfer`).
The rescaling by the constant `2` of `integral_avsum_subcellDeficit_eq_respTauMinus`: for a
stationary law `P`, the flat average over the depth-`H` aligned subcells of the coarse scale `s` of
twice the gap between each subcell's own response and the restricted terminal response integrates
to twice the defect `respTauMinus` between the coarse and terminal scales. -/
theorem integral_avsum_two_subcellDeficit_eq_two_respTauMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (hjs : (jStar : ℤ) ≤ s) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hrespint : ∀ a, MeasureTheory.IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))
      (respCell jStar F t))
    (hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hRint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P)
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P) :
    (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
        2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) ∂P)
      = 2 * respTauMinus P jStar F s t e := by
  have h := integral_avsum_subcellDeficit_eq_respTauMinus P hstat jStar hjStar F hm H s t ht hjs e
    uM hmax hblk hrespint hJint hRint hJt hJs
  rw [← h, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with a
  rw [← Finset.mul_sum]
  ring

/-- **Twice the mean subcell deficit is twice the plus scale defect** (`p.response.transfer`).
The rescaling by the constant `2` of `integral_avsum_subcellDeficit_eq_respTauPlus`: for a
stationary law `P`, the flat average over the depth-`H` aligned subcells of the coarse scale `s` of
twice the gap between each subcell's own response and the restricted terminal response integrates
to twice the adjoint defect `respTauPlus` between the coarse and terminal scales. -/
theorem integral_avsum_two_subcellDeficit_eq_two_respTauPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (hjs : (jStar : ℤ) ≤ s) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hrespint : ∀ a, MeasureTheory.IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))
      (respCell jStar F t))
    (hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hRint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P)
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P) :
    (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
        2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) ∂P)
      = 2 * respTauPlus P jStar F s t e := by
  have h := integral_avsum_subcellDeficit_eq_respTauPlus P hstat jStar hjStar F hm H s t ht hjs e
    uP hmax hblk hrespint hJint hRint hJt hJs
  rw [← h, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with a
  rw [← Finset.mul_sum]
  ring

end

end HCPolySupport.HighContrast.Multiscale
end
