/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.ResponseTransferFromCutoffBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantHeadBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.FirstErrorRowArithmetic
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.OptimizerEnergyDefectRow
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.SubcellDeficitIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TerminalDeficitCarrierBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TerminalEnergyDeficitBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.WeakEstimateAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.AbstractCellPairingBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.ScaleDefectIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.StationaryAnnealedErrorScalars

/-!
# High-contrast homogenization: Entry.Response.Direct.OptimizerRowSideConditions

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Discharging the side conditions of the first error row

The split of the cutoff's oscillation against the terminal-optimizer energy on each aligned coarse
subcell, proved for a general coefficient of the response class, is specialized here to the two
concrete response coefficients `respCoeffMinus` and `respCoeffPlus`. The first error row of the
cutoff estimate — comparing the cutoff half-energy of the terminal optimizer with the terminal
response, integrated over the law of coefficients — states that comparison with every pathwise
ingredient left as a hypothesis; this file discharges every one of those hypotheses on the
response's own data for the negative sign, leaving no side condition open. The same first error row
is then stated, and proved on the response's own data, for the adjoint sign. Together these are the
terminal-optimizer replacement row and the first error row of `p.response.transfer`, on the
response's own coefficient carriers.
-/

section
/-!
## The cutoff oscillation split at a coefficient of the carrier

The terminal-optimizer replacement row of `p.response.transfer` splits the cutoff fluctuation
`φ - 1` against the optimizer energy on each aligned subcell of the coarse scale.  The variational
identities that produce the split are stated for a coefficient that is elliptic pointwise, while a
sample of the coefficient carrier is elliptic only almost everywhere.  These two statements run the
split at a pointwise elliptic representative of `a_- = a - g` (respectively `a_+ = aᵗ + g`) on the
terminal cell and transport the result back: the carried-along harmonic function has the same
gradient, every quantity of the split is invariant under the almost-everywhere replacement, and the
pathwise response is unchanged as well.

Paper: `p.response.transfer`.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The oscillation split of the cutoff fluctuation against the optimizer energy, for the minus
family, with no pointwise ellipticity hypothesis.  On the terminal cell `respCell jStar F t`, for a
cutoff `φ` of the response class and a response maximizer `u` of the loads `(p, r)` for the
recentred coefficient `respCoeffMinus F a`, the `(φ − 1)`-weighted optimizer energy differs from the
normalized sum, over the depth-`n` triadic subdivision, of the products of the subcell means of
`φ − 1` and of the energy by at most `32 d² responseCutoffProfileConst 3^{-n}` times twice the
pathwise response `respJ (respGrid jStar F) t p r (respCoeffMinus F a)`.  The coefficient is
elliptic only almost everywhere, so the estimate is run at a pointwise elliptic representative and
transported back; the response of the representative agrees with the response of the carrier
coefficient, and the carried-along optimizer has the same gradient.  This is the scale-gain step of
the cutoff estimate of `p.response.transfer`, in the form the row assembly consumes. -/
theorem abs_volumeAverage_sub_one_energy_sub_avsum_le_respCoeffMinus {d : ℕ} [NeZero d]
    {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (n : ℕ)
    {φ : Vec d → ℝ} (hφ : IsResponseCutoff (respGrid jStar F) t φ) (p r : Vec d)
    (a : CoeffSpace d) (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : IsResponseMaximizer (respCell jStar F t) p r (respCoeffMinus F a) u) :
    |volumeAverage (respCell jStar F t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand (respCoeffMinus F a) u x)
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (fun x => φ x - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (scalarVariationEnergyIntegrand (respCoeffMinus F a) u)|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) *
          (2 * respJ (respGrid jStar F) t p r (respCoeffMinus F a)) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  obtain ⟨lam, Lam, f, _, _, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  let v : AHarmonicFunction f (respCell jStar F t) := Response.aHarmonicOfAEEq hae u
  have hmaxf : IsResponseMaximizer (respCell jStar F t) p r f v :=
    isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff hae p r hmax
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
  have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have henergy : IntegrableOn (scalarVariationEnergyIntegrand f v) (respCell jStar F t) :=
    hdata.energy v
  have hUmeas : MeasurableSet (respCell jStar F t) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isOpen.measurableSet
  have hUfin : volume (respCell jStar F t) ≠ ⊤ :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).volume_lt_top.ne
  have hφE : IntegrableOn (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
      (respCell jStar F t) :=
    integrableOn_cutoff_mul_coord hUmeas hUfin
      (hφ.contDiff.continuous.measurable.sub measurable_const)
      (fun x => by
        show |φ x - 1| ≤ (1 : ℝ)
        rw [abs_le]
        exact ⟨by linarith only [hφ.nonneg x], by linarith only [hφ.le_two x]⟩)
      henergy
  have hEat : ∀ w ∈ triadicIndexBox d n, IntegrableOn (scalarVariationEnergyIntegrand f v)
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) :=
    fun w hw => henergy.mono_set (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw)
  have hφat : ∀ w ∈ triadicIndexBox d n, IntegrableOn φ
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) :=
    fun w _ => integrableOn_isResponseCutoff hq hφ (t - (n : ℤ)) w
  have hφEat : ∀ w ∈ triadicIndexBox d n,
      IntegrableOn (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) :=
    fun w hw => hφE.mono_set (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw)
  have hmain := abs_volumeAverage_sub_one_energy_sub_avsum_le hq t n hφ hEll p r v hmaxf
    (hdata.weakFlux v) (hdata.response p r v) (hdata.firstVariation p r v v) henergy
    hφE hEat hφat hφEat
  have hUw : volumeAverage (respCell jStar F t)
        (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
      = volumeAverage (respCell jStar F t)
        (fun x => (φ x - 1) * scalarVariationEnergyIntegrand (respCoeffMinus F a) u x) :=
    volumeAverage_weighted_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff
      (subset_refl (respCell jStar F t)) hae (fun x => φ x - 1) u
  have hVw : ∀ w ∈ triadicIndexBox d n,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand f v)
        = volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) u) :=
    fun w hw => volumeAverage_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff
      (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw) hae u
  have hsum : (∑ w ∈ triadicIndexBox d n,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (fun x => φ x - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (scalarVariationEnergyIntegrand f v))
      = ∑ w ∈ triadicIndexBox d n,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (fun x => φ x - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) u) := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    rw [hVw w hw]
  have htrans : |volumeAverage (respCell jStar F t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (fun x => φ x - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (scalarVariationEnergyIntegrand f v)|
      = |volumeAverage (respCell jStar F t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand (respCoeffMinus F a) u x)
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (fun x => φ x - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (scalarVariationEnergyIntegrand (respCoeffMinus F a) u)| := by
    rw [hUw, hsum]
  have hJw : respJ (respGrid jStar F) t p r f
      = respJ (respGrid jStar F) t p r (respCoeffMinus F a) := by
    unfold respJ
    exact (responseJ_congr_of_ae_eq hae p r).symm
  have hRHS : 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) *
        (2 * respJ (respGrid jStar F) t p r f)
      = 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) *
        (2 * respJ (respGrid jStar F) t p r (respCoeffMinus F a)) := by
    rw [hJw]
  have htransA := htrans
  simp only [respCell] at htransA
  rw [htransA, hRHS] at hmain
  exact hmain

/-- The adjoint twin of `abs_volumeAverage_sub_one_energy_sub_avsum_le_respCoeffMinus`: the same
oscillation split of the cutoff fluctuation against the optimizer energy, for the transposed
recentred coefficient `respCoeffPlus F a = aᵗ + g` and a response maximizer `u` of the loads
`(p, r)` for it.  The coefficient is elliptic only almost everywhere, so the estimate runs at a
pointwise elliptic representative and is transported back exactly as in the minus case.  This is
the scale-gain step of the adjoint cutoff estimate of `p.response.transfer`. -/
theorem abs_volumeAverage_sub_one_energy_sub_avsum_le_respCoeffPlus {d : ℕ} [NeZero d]
    {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (n : ℕ)
    {φ : Vec d → ℝ} (hφ : IsResponseCutoff (respGrid jStar F) t φ) (p r : Vec d)
    (a : CoeffSpace d) (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : IsResponseMaximizer (respCell jStar F t) p r (respCoeffPlus F a) u) :
    |volumeAverage (respCell jStar F t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand (respCoeffPlus F a) u x)
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (fun x => φ x - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (scalarVariationEnergyIntegrand (respCoeffPlus F a) u)|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) *
          (2 * respJ (respGrid jStar F) t p r (respCoeffPlus F a)) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  obtain ⟨lam, Lam, f, _, _, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  let v : AHarmonicFunction f (respCell jStar F t) := Response.aHarmonicOfAEEq hae u
  have hmaxf : IsResponseMaximizer (respCell jStar F t) p r f v :=
    isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff hae p r hmax
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
  have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have henergy : IntegrableOn (scalarVariationEnergyIntegrand f v) (respCell jStar F t) :=
    hdata.energy v
  have hUmeas : MeasurableSet (respCell jStar F t) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isOpen.measurableSet
  have hUfin : volume (respCell jStar F t) ≠ ⊤ :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).volume_lt_top.ne
  have hφE : IntegrableOn (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
      (respCell jStar F t) :=
    integrableOn_cutoff_mul_coord hUmeas hUfin
      (hφ.contDiff.continuous.measurable.sub measurable_const)
      (fun x => by
        show |φ x - 1| ≤ (1 : ℝ)
        rw [abs_le]
        exact ⟨by linarith only [hφ.nonneg x], by linarith only [hφ.le_two x]⟩)
      henergy
  have hEat : ∀ w ∈ triadicIndexBox d n, IntegrableOn (scalarVariationEnergyIntegrand f v)
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) :=
    fun w hw => henergy.mono_set (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw)
  have hφat : ∀ w ∈ triadicIndexBox d n, IntegrableOn φ
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) :=
    fun w _ => integrableOn_isResponseCutoff hq hφ (t - (n : ℤ)) w
  have hφEat : ∀ w ∈ triadicIndexBox d n,
      IntegrableOn (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) :=
    fun w hw => hφE.mono_set (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw)
  have hmain := abs_volumeAverage_sub_one_energy_sub_avsum_le hq t n hφ hEll p r v hmaxf
    (hdata.weakFlux v) (hdata.response p r v) (hdata.firstVariation p r v v) henergy
    hφE hEat hφat hφEat
  have hUw : volumeAverage (respCell jStar F t)
        (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
      = volumeAverage (respCell jStar F t)
        (fun x => (φ x - 1) * scalarVariationEnergyIntegrand (respCoeffPlus F a) u x) :=
    volumeAverage_weighted_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff
      (subset_refl (respCell jStar F t)) hae (fun x => φ x - 1) u
  have hVw : ∀ w ∈ triadicIndexBox d n,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand f v)
        = volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) u) :=
    fun w hw => volumeAverage_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff
      (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw) hae u
  have hsum : (∑ w ∈ triadicIndexBox d n,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (fun x => φ x - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (scalarVariationEnergyIntegrand f v))
      = ∑ w ∈ triadicIndexBox d n,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (fun x => φ x - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) u) := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    rw [hVw w hw]
  have htrans : |volumeAverage (respCell jStar F t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (fun x => φ x - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (scalarVariationEnergyIntegrand f v)|
      = |volumeAverage (respCell jStar F t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand (respCoeffPlus F a) u x)
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (fun x => φ x - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (scalarVariationEnergyIntegrand (respCoeffPlus F a) u)| := by
    rw [hUw, hsum]
  have hJw : respJ (respGrid jStar F) t p r f
      = respJ (respGrid jStar F) t p r (respCoeffPlus F a) := by
    unfold respJ
    exact (responseJ_congr_of_ae_eq hae p r).symm
  have hRHS : 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) *
        (2 * respJ (respGrid jStar F) t p r f)
      = 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) *
        (2 * respJ (respGrid jStar F) t p r (respCoeffPlus F a)) := by
    rw [hJw]
  have htransA := htrans
  simp only [respCell] at htransA
  rw [htransA, hRHS] at hmain
  exact hmain

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The first error row of `p.response.transfer` on the carriers, side conditions discharged

The terminal-optimizer replacement row of `p.response.transfer` compares the cutoff half-energy of
the terminal optimizer with the terminal response, integrated over the law of coefficients.  The
assembly `abs_integral_cutoffHalfEnergy_sub_respJ_le_rowMinus` states that comparison with every
pathwise ingredient as a hypothesis.  This module supplies those ingredients on the coefficient
carriers: the energy-defect identity, the oscillation split over the coarse subdivision, the subcell
comparison, the two cutoff-weight facts, the three signs, the subcell-response integrabilities, the
common annealed subcell value and the identification of the flat mean deficit with the scale defect.
Only the sample integrabilities and the positivity of the canonical metric remain as hypotheses; no
pointwise ellipticity is assumed, because the a.e.-elliptic representative transport produces every
pathwise statement on the carriers.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The first error row of `p.response.transfer` on the response carriers.**  Let `P` be a
stationary probability law on the coefficient space, `F` a block matrix with positive definite
canonical metric, `jStar` a scale with `2 d ≤ 3 ^ jStar`, and `s ≤ t = s + H` two scales with
`jStar ≤ s`.  For a cutoff `φ` of the response class at the terminal scale and a family `uM` of
terminal maximizers for the recentred coefficients, assume that every coarse block of the sample is
integrable on every aligned cell, that the terminal and coarse pathwise responses are
`P`-integrable,
and that the subcell deficit, the subcell energy and the `(φ - 1)`-weighted terminal energy have
`P`-integrable flat means.  Then the law-integral of the cutoff half-energy of the terminal
optimizer
minus the terminal response is at most
`max 3 (32 d^2 responseCutoffProfileConst)` times
`τ^- + (τ^- E[J_t^-])^{1/2} + 3^{-H} E[J_t^-]`, the printed first error row of
`p.response.transfer`.  The pathwise side conditions of the row are discharged here; the
integrability of the sample data is the only remaining input. -/
theorem abs_integral_cutoffHalfEnergy_sub_respJ_le_rowMinus_of_carriers {d : ℕ} [NeZero d]
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
    |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)) ∂P|
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
          (respTauMinus P jStar F s t e +
            Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) +
            (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hts : t - (H : ℤ) = s := by
    rw [ht]
    ring
  have hint : IntegrableOn (fun x => φ x - 1) (HighContrast.adaptedCell (respGrid jStar F) t) := by
    have h := integrableOn_sub_one_isResponseCutoff hq hφ t 0
    rwa [adaptedCellAtCenter_zero (respGrid jStar F) t] at h
  have hφint : IntegrableOn φ (HighContrast.adaptedCell (respGrid jStar F) t) := by
    have h := integrableOn_isResponseCutoff hq hφ t 0
    rwa [adaptedCellAtCenter_zero (respGrid jStar F) t] at h
  have hvol : (volume (HighContrast.adaptedCell (respGrid jStar F) t)).toReal ≠ 0 := by
    rw [Geometry.volume_adaptedCell_toReal]
    exact mul_ne_zero
      (ne_of_gt (abs_pos.mpr
        (IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det (respGrid jStar F)).mp hq))))
      (ne_of_gt (by positivity : (0 : ℝ) < ((3 : ℝ) ^ t) ^ d))
  have hrespint : ∀ a, IntegrableOn (scalarResponseIntegrand (respCell jStar F t)
      (respCoeffMinus F a) (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
      (uM a)) (respCell jStar F t) := by
    intro a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
    have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    have hv := hdata.response (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
      (Response.aHarmonicOfAEEq hae (uM a))
    exact integrableOn_scalarResponseIntegrand_aHarmonicFunctionOfAEEqCoeff (subset_refl _) hae.symm
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
      (Response.aHarmonicOfAEEq hae (uM a)) hv
  have hJt0 : ∀ a, 0 ≤ respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) := by
    intro a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
    have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    let v : AHarmonicFunction f (respCell jStar F t) := Response.aHarmonicOfAEEq hae (uM a)
    have hmaxf : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) f v :=
      isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff hae _ _ (hmax a)
    have hnonneg : 0 ≤ ResponseJ (respCell jStar F t) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) f :=
      responseJ_nonneg_of_isResponseMaximizer hEll _ _ v hmaxf
        (hdata.weakFlux v) (hdata.response _ _ v) (hdata.firstVariation _ _ v v) (hdata.energy v)
    have hcongr : respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)
        = respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) f := by
      unfold respJ
      exact responseJ_congr_of_ae_eq hae _ _
    rw [hcongr]
    simpa only [respJ, respCell] using hnonneg
  have hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P :=
    fun w _ => integrable_responseJ_respCoeffMinus_adaptedCellAtCenter P hq F s w _ _ (hblk s w)
  have hRint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P := by
    intro w hw
    refine ((hJint w hw).sub (hDint w hw)).congr ?_
    filter_upwards with a
    simp only [Pi.sub_apply]
    ring
  have hJs_eq : (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P)
      = blockResponseEnergy (blockCongr (respG F) (respMean P jStar F s))
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) := by
    have h0 := integral_responseJ_respCoeffMinus_adaptedCellAtCenter_eq_direct P hstat jStar hjStar F hm s hjs 0
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (hblk s 0)
    rw [adaptedCellAtCenter_zero (respGrid jStar F) s] at h0
    simpa only [respJ] using h0
  exact abs_integral_cutoffHalfEnergy_sub_respJ_le_rowMinus (P := P) jStar F H s t e φ uM
    (fun a => cutoffHalfEnergyAux_sub_respJ_eq_respCoeffMinus hjStar hm t φ hφ
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) a (uM a) (hmax a))
    (fun a => by
      have h := abs_volumeAverage_sub_one_energy_sub_avsum_le_respCoeffMinus (jStar := jStar)
        (F := F) hjStar hm t H hφ (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        a (uM a) (hmax a)
      simpa only [hts] using h)
    (fun w hw a => by
      have h := abs_half_energy_adaptedCellAtCenter_sub_responseJ_le_respCoeffMinus (jStar := jStar)
        (F := F) hjStar hm t H (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        a (uM a) hw
      simpa only [hts] using h)
    (by
      have h := avsum_volumeAverage_sub_one_eq_zero (qq := respGrid jStar F) hq t H hφ hint hvol hφint
      simpa only [hts] using h)
    (fun w hw => abs_volumeAverage_sub_one_isResponseCutoff_le_one hq hφ s w)
    (fun w hw a => by
      have h := (responseJ_nonneg_and_deficit_nonneg_respCoeffMinus (jStar := jStar) (F := F)
        hjStar hm t H (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) a (uM a) hw).1
      simpa only [hts] using h)
    (fun w hw a => by
      have h := (responseJ_nonneg_and_deficit_nonneg_respCoeffMinus (jStar := jStar) (F := F)
        hjStar hm t H (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) a (uM a) hw).2
      simpa only [hts] using h)
    hJt0 hJint hDint hEint hWint hJt
    (fun w hw => (integral_responseJ_respCoeffMinus_adaptedCellAtCenter_eq_direct P hstat jStar hjStar F hm s hjs w
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (hblk s w)).trans hJs_eq.symm)
    (integral_avsum_subcellDeficit_eq_respTauMinus P hstat jStar hjStar F hm H s t ht hjs e uM hmax
      (fun w => hblk s w) hrespint hJint hRint hJt hJs)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The terminal-optimizer replacement row on the carriers of the cutoff estimate

The first error row of `p.response.transfer` is stated on the concrete objects that the cutoff
estimate produces: the cutoff half-energy of a terminal optimizer minus the terminal response,
integrated against the law.  The pathwise identification of the defect with the `(φ - 1)`-weighted
optimizer energy, the oscillation split of that energy over the aligned cells of the coarse scale,
and the subcell comparison of half-energy with subcell response are the three inputs, taken in the
shape in which the modules that prove them state them.  Given those, the expectation of the defect
is bounded by `C (τ^- + √(τ^- E[J_t^-]) + 3^{-H} E[J_t^-])` with the explicit constant
`C = max 3 (32 d² responseCutoffProfileConst)`.

Paper: `p.response.transfer`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The cutoff half-energy row on the carriers of the estimate.**  Let `uP` be a terminal
optimizer, `φ` a cutoff, and suppose the defect `cutoffHalfEnergyAux - respJ` is identified
pathwise with the `(φ - 1)`-weighted optimizer energy; suppose the weighted energy splits over the
aligned cells of the coarse scale into its cell means plus the osculation cost
`32 d² responseCutoffProfileConst 3^{-H}` times twice the terminal response; and suppose on each
subcell the half-energy and the subcell response satisfy the one-parameter comparison
`|(1/2) E - J| ≤ D + 2 √(J D)`.  With the cutoff weights averaging to `0` and bounded by `1`, with
nonnegative subcell response and deficit, and with the annealed flat deficit equal to the scale
defect `τ^-`, the expectation of the defect is at most
`max 3 (32 d² responseCutoffProfileConst) (τ^- + √(τ^- E[J_t^-]) + 3^{-H} E[J_t^-])`.  This is the
terminal-optimizer replacement row of `p.response.transfer` assembled on the carriers the cutoff
estimate uses. -/
theorem abs_integral_cutoffHalfEnergy_sub_respJ_le_rowPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hid : ∀ a, cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
      = (1 / 2 : ℝ) * volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x))
    (hosc : ∀ a, |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
            scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)
          - (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))|
        ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)) *
            (2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a)))
    (hcmp : ∀ w ∈ triadicIndexBox d H, ∀ a,
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
                    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))))
    (hc0 : (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1) = 0)
    (hc1 : ∀ w ∈ triadicIndexBox d H,
      |volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)| ≤ 1)
    (hJ0 : ∀ w ∈ triadicIndexBox d H, ∀ a,
      0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a))
    (hD0 : ∀ w ∈ triadicIndexBox d H, ∀ a,
      0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))
    (hJt0 : ∀ a, 0 ≤ respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a))
    (hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
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
      scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)) P)
    (hJtint : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hJval : ∀ w ∈ triadicIndexBox d H,
      (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P)
        = ∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P)
    (hDval : (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
      (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) ∂P)
      = respTauPlus P jStar F s t e) :
    |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)) ∂P|
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
          (respTauPlus P jStar F s t e +
            Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) +
            (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) := by
  have hK : (0 : ℝ) ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)) := by
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(H : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hΘ : (0 : ℝ) ≤ responseCutoffProfileConst := le_of_lt responseCutoffProfileConst_pos
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg (d : ℝ))) hΘ) h3
  have hEJdef : (∫ a, respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P) = respEJPlus P jStar F t e := by
    unfold respEJPlus
    rfl
  have hcJdef : (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P)
      = respEJPlus P jStar F t e + respTauPlus P jStar F s t e := by
    unfold respTauPlus respEJPlus
    ring
  have hglue := abs_integral_le_row1_of_parts (P := P) (n := H)
    (c := fun w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
    (Ecell := fun w a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))
    (J := fun w a => ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a))
    (D := fun w a => ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a)
      - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a)))
    (Wtot := fun a => volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
      scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x))
    (Jt := fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a))
    (K := 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
    (cJ := ∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P)
    (τ := respTauPlus P jStar F s t e) (EJ := respEJPlus P jStar F t e)
    hK hosc hcmp hc0 hc1 hJ0 hD0 hJt0 hJint hDint hEint hWint hJtint hJval hDval hEJdef hcJdef
  have hτ0 : 0 ≤ respTauPlus P jStar F s t e := by
    rw [← hDval]
    exact integral_nonneg (fun a => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun w hw => hD0 w hw a)))
  have hEJ0 : 0 ≤ respEJPlus P jStar F t e := by
    unfold respEJPlus
    exact integral_nonneg hJt0
  have h3H0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(H : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) :=
    Real.sqrt_nonneg _
  set C : ℝ := max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) with hCdef
  have hC3 : (3 : ℝ) ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hCΘ : 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst ≤ C := by
    rw [hCdef]; exact le_max_right _ _
  have hKbound : (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
        * respEJPlus P jStar F t e
      ≤ C * ((3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) := by
    have hEq : (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * respEJPlus P jStar F t e
        = (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
          * ((3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) := by ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_right hCΘ (mul_nonneg h3H0 hEJ0)
  have hstep : (1 / 2 : ℝ) * |∫ a, volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) ∂P|
      ≤ 3 * respTauPlus P jStar F s t e
        + 2 * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
        + (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
            * respEJPlus P jStar F t e := by
    have h := mul_le_mul_of_nonneg_left hglue (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
    calc (1 / 2 : ℝ) * |∫ a, volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) ∂P|
        ≤ (1 / 2 : ℝ) * (6 * respTauPlus P jStar F s t e
            + 4 * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
            + 2 * (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
                * respEJPlus P jStar F t e) := h
      _ = 3 * respTauPlus P jStar F s t e
            + 2 * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
            + (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
                * respEJPlus P jStar F t e := by ring
  have hfinal : 3 * respTauPlus P jStar F s t e
        + 2 * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
        + (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
            * respEJPlus P jStar F t e
      ≤ C * (respTauPlus P jStar F s t e
          + Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
          + (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) := by
    have h1 : 3 * respTauPlus P jStar F s t e ≤ C * respTauPlus P jStar F s t e :=
      mul_le_mul_of_nonneg_right hC3 hτ0
    have h2 : 2 * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
        ≤ C * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) :=
      mul_le_mul_of_nonneg_right (by linarith only [hC3] : (2 : ℝ) ≤ C) hsqrt0
    calc 3 * respTauPlus P jStar F s t e
          + 2 * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
          + (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
              * respEJPlus P jStar F t e
        ≤ C * respTauPlus P jStar F s t e
          + C * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
          + C * ((3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) :=
          add_le_add (add_le_add h1 h2) hKbound
      _ = C * (respTauPlus P jStar F s t e
          + Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
          + (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) := by ring
  calc |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)) ∂P|
      = (1 / 2 : ℝ) * |∫ a, volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) ∂P| := by
        rw [show (∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
              - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
                  (respqPlus P jStar F t e) (respCoeffPlus F a)) ∂P)
            = ∫ a, (1 / 2 : ℝ) * volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
                scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) ∂P from
          integral_congr_ae (Filter.Eventually.of_forall hid)]
        rw [integral_const_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (1 : ℝ) / 2 by norm_num)]
    _ ≤ 3 * respTauPlus P jStar F s t e
          + 2 * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
          + (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
              * respEJPlus P jStar F t e := hstep
    _ ≤ C * (respTauPlus P jStar F s t e
          + Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
          + (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) := hfinal

end

end HCPolySupport.HighContrast.Multiscale
end
