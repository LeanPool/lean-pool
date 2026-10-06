/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantHeadBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.FirstErrorRowArithmetic
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TerminalEnergyDeficitBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.WeakEstimateAssembly

/-!
# High-contrast homogenization: Entry.Response.Direct.OptimizerEnergyDefectRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The terminal-optimizer replacement row, assembled on the response's own data

The `(φ-1)`-weighted optimizer energy on the terminal cell splits, over the subdivision into the
aligned cells of the coarse scale, into an oscillation part — costing the cutoff class's Lipschitz
gain times the terminal response — and a subcell-mean part, the mean-zero weighting of the subcell
half-energies; combining the two gives the first error row of `p.response.transfer`. This file
instantiates that row on the same carriers the cutoff estimate uses: the difference between the
cutoff half-energy of the terminal optimizer and the terminal response, integrated over the law of
coefficients. The pathwise identity behind that difference, `cutoffHalfEnergyAux - respJ` equal to
half the `(φ-1)`-weighted optimizer energy, holds only for a coefficient that is pointwise elliptic
on the cell, so it is transported here across an almost-everywhere equality to the two response
coefficients `respCoeffMinus` and `respCoeffPlus`, each elliptic only almost everywhere.
-/

section
/-!
## The terminal-optimizer replacement row of `p.response.transfer`

The `(φ - 1)`-weighted optimizer energy on the terminal cell splits, over the subdivision into
the aligned cells of the coarse scale, into its oscillation part and its subcell-mean part.  The
oscillation part costs the Lipschitz gain of the cutoff class times the terminal response.  The
subcell-mean part is the mean-zero weighting of the subcell half-energies, and the abstract row
bounds its expectation by `τ + 2 √(τ cJ)`, where `τ` is the scale defect and `cJ` the common
annealed subcell response.  Since `cJ = EJ + τ` and `√(τ (EJ + τ)) ≤ √(τ EJ) + τ`, the two halves
combine into the printed shape `6 τ + 4 √(τ EJ) + 2 K EJ`.

Paper: `p.response.transfer`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The terminal-optimizer replacement row.**  Suppose the terminal response `Wtot` differs from
the normalized mean-zero weighting `N ∑ c w Ecell w` of the subcell half-energies, where
`N = |triadicIndexBox d n|⁻¹`, by at most `K` times twice the terminal response `Jt`.  Suppose
further that on each subcell the half-energy `(1/2) Ecell` and the subcell response `J` satisfy the
one-parameter comparison `|(1/2) Ecell - J| ≤ D + 2 √(J D)` with nonnegative `J` and deficit `D`,
that the weights `c` are bounded by `1` and average to `0`, that `∫ J w = cJ` is the same on every
subcell, and that the annealed flat average of the deficits `D` is the scale defect `τ`.  When
`cJ = EJ + τ` with `EJ = ∫ Jt`, the expectation of the terminal response is at most
`6 τ + 4 √(τ EJ) + 2 K EJ`.  This is the first error row of `p.response.transfer` assembled from
its oscillation and subcell-mean halves. -/
theorem abs_integral_le_row1_of_parts {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] {d : ℕ} (n : ℕ)
    (c : (Fin d → ℤ) → ℝ) (Ecell J D : (Fin d → ℤ) → α → ℝ) (Wtot Jt : α → ℝ)
    (K cJ τ EJ : ℝ) (hK : 0 ≤ K)
    (hosc : ∀ a, |Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * Ecell w a| ≤ K * (2 * Jt a))
    (hcmp : ∀ w ∈ triadicIndexBox d n, ∀ a,
      |(1 / 2 : ℝ) * Ecell w a - J w a| ≤ D w a + 2 * Real.sqrt (J w a * D w a))
    (hc0 : (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n, c w = 0)
    (hc1 : ∀ w ∈ triadicIndexBox d n, |c w| ≤ 1)
    (hJ0 : ∀ w ∈ triadicIndexBox d n, ∀ a, 0 ≤ J w a)
    (hD0 : ∀ w ∈ triadicIndexBox d n, ∀ a, 0 ≤ D w a)
    (hJt0 : ∀ a, 0 ≤ Jt a)
    (hJint : ∀ w ∈ triadicIndexBox d n, Integrable (J w) P)
    (hDint : ∀ w ∈ triadicIndexBox d n, Integrable (D w) P)
    (hEint : ∀ w ∈ triadicIndexBox d n, Integrable (Ecell w) P)
    (hWint : Integrable Wtot P) (hJtint : Integrable Jt P)
    (hJval : ∀ w ∈ triadicIndexBox d n, (∫ a, J w a ∂P) = cJ)
    (hDval : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, D w a ∂P) = τ)
    (hEJ : (∫ a, Jt a ∂P) = EJ) (hcJ : cJ = EJ + τ) :
    |∫ a, Wtot a ∂P| ≤ 6 * τ + 4 * Real.sqrt (τ * EJ) + 2 * K * EJ := by
  have hSint : Integrable (fun a => (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * Ecell w a) P :=
    (integrable_finsetSum _ (fun w hw => (hEint w hw).const_mul (c w))).const_mul _
  have hdiff_int : Integrable (fun a => Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * Ecell w a) P := hWint.sub hSint
  have hdiff_abs_int : Integrable (fun a => |Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * Ecell w a|) P := by
    simpa only [Real.norm_eq_abs] using hdiff_int.abs
  have hSplit : (∫ a, Wtot a ∂P)
      = (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * Ecell w a ∂P)
        + (∫ a, (Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * Ecell w a) ∂P) := by
    rw [← integral_add hSint hdiff_int]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun a => by ring))
  have hAbsSplit : |∫ a, Wtot a ∂P|
      ≤ |∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * Ecell w a ∂P|
        + |∫ a, (Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * Ecell w a) ∂P| := by
    rw [hSplit]
    exact abs_add_le _ _
  have hKabs : |K| = K := abs_of_nonneg hK
  have hoscK : ∀ a, |Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * Ecell w a| ≤ |K| * (2 * Jt a) := by
    intro a
    rw [hKabs]
    exact hosc a
  have hdiff_bound : |∫ a, (Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * Ecell w a) ∂P| ≤ 2 * K * EJ := by
    have hKJt_int : Integrable (fun a => |K| * (2 * Jt a)) P :=
      (hJtint.const_mul (2 : ℝ)).const_mul |K|
    have hmono : (∫ a, |Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * Ecell w a| ∂P)
        ≤ ∫ a, |K| * (2 * Jt a) ∂P :=
      integral_mono hdiff_abs_int hKJt_int hoscK
    have hKint : (∫ a, |K| * (2 * Jt a) ∂P) = 2 * K * EJ := by
      rw [integral_const_mul, integral_const_mul, hEJ, hKabs]
      ring
    calc |∫ a, (Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * Ecell w a) ∂P|
        ≤ ∫ a, |Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * Ecell w a| ∂P :=
          abs_integral_le_integral_abs
      _ ≤ ∫ a, |K| * (2 * Jt a) ∂P := hmono
      _ = 2 * K * EJ := hKint
  have hEint' : ∀ w ∈ triadicIndexBox d n,
      Integrable (fun a => (1 / 2 : ℝ) * Ecell w a) P :=
    fun w hw => (hEint w hw).const_mul (1 / 2 : ℝ)
  have habs : |∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * ((1 / 2 : ℝ) * Ecell w a) ∂P|
      ≤ τ + 2 * Real.sqrt (τ * cJ) :=
    abs_integral_avsum_weighted_energy_le P n c (fun w a => (1 / 2 : ℝ) * Ecell w a)
      J D cJ τ hc0 hc1 hJ0 hD0 hcmp hJint hDint hEint' hJval hDval
  have hS_eq : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * Ecell w a ∂P)
      = 2 * (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * ((1 / 2 : ℝ) * Ecell w a) ∂P) := by
    have hpt : ∀ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * Ecell w a
        = 2 * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * ((1 / 2 : ℝ) * Ecell w a)) := by
      intro a
      have hinner : (∑ w ∈ triadicIndexBox d n, c w * ((1 / 2 : ℝ) * Ecell w a))
          = (1 / 2 : ℝ) * ∑ w ∈ triadicIndexBox d n, c w * Ecell w a := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun w _ => by ring)
      rw [hinner]
      ring
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hAbsS : |∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * Ecell w a ∂P|
      ≤ 2 * (τ + 2 * Real.sqrt (τ * cJ)) := by
    rw [hS_eq, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    exact mul_le_mul_of_nonneg_left habs (show (0 : ℝ) ≤ 2 by norm_num)
  have hNnonneg : 0 ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ := by
    have hcard : ((triadicIndexBox d n).card : ℝ) = ((3 : ℝ) ^ n) ^ d :=
      card_triadicIndexBox n
    rw [hcard]
    positivity
  have hτ0 : 0 ≤ τ := by
    rw [← hDval]
    exact integral_nonneg (fun a => mul_nonneg hNnonneg
      (Finset.sum_nonneg (fun w hw => hD0 w hw a)))
  have hEJ0 : 0 ≤ EJ := by
    rw [← hEJ]
    exact integral_nonneg hJt0
  have hsqrt : Real.sqrt (τ * cJ) ≤ Real.sqrt (τ * EJ) + τ := by
    rw [hcJ]
    exact sqrt_mul_add_le_sqrt_mul_add EJ τ hEJ0 hτ0
  have hAbsS' : |∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * Ecell w a ∂P|
      ≤ 2 * (τ + 2 * (Real.sqrt (τ * EJ) + τ)) := by
    have h2 : 2 * Real.sqrt (τ * cJ) ≤ 2 * (Real.sqrt (τ * EJ) + τ) :=
      mul_le_mul_of_nonneg_left hsqrt (show (0 : ℝ) ≤ 2 by norm_num)
    linarith only [hAbsS, h2]
  calc |∫ a, Wtot a ∂P|
      ≤ |∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, c w * Ecell w a ∂P|
          + |∫ a, (Wtot a - (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, c w * Ecell w a) ∂P| := hAbsSplit
    _ ≤ 2 * (τ + 2 * (Real.sqrt (τ * EJ) + τ)) + 2 * K * EJ :=
        add_le_add hAbsS' hdiff_bound
    _ = 6 * τ + 4 * Real.sqrt (τ * EJ) + 2 * K * EJ := by ring

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The terminal-optimizer replacement row on the carriers of the cutoff estimate

This assembles the first error row of `p.response.transfer` on the same carriers the cutoff
estimate uses.  The left-hand side is the difference between the cutoff half-energy of the
terminal optimizer and the terminal response, integrated over the law of coefficients.  The three
geometric inputs — the pathwise identification of that difference with the `(φ - 1)`-weighted
optimizer energy, the oscillation split of that energy over the subdivision into the aligned
coarse cells, and the subcell comparison of the half-energy with the subcell response — enter as
hypotheses in the shape in which the modules that prove them produce them.  The conclusion is the
printed bound

`C (τ^- + (τ^- E[J_t^-])^{1/2} + 3^{-H} E[J_t^-])`

with the explicit dimensional constant `C = max 3 (32 d^2 * responseCutoffProfileConst)`.

Paper: `p.response.transfer`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The terminal-optimizer replacement row on the cutoff carriers.**  Assume the pathwise
identification `hid` of the cutoff half-energy minus the terminal response with the
`(φ - 1)`-weighted optimizer energy; the oscillation split `hosc` of that weighted energy over the
aligned cells of the coarse scale, costing `32 d^2 responseCutoffProfileConst 3^{-H}` times twice
the terminal response; and the subcell comparison `hcmp` of half the subcell energy with the
subcell response through its nonnegative deficit.  Assume the cutoff fluctuation has mean-zero
normalized subcell means `hc0` and is bounded by `1` on each subcell `hc1`, the subcell responses
and deficits are nonnegative and integrable, the subcell responses have a common annealed value
`hJval`, and the annealed flat mean of the deficits is the scale defect `hDval`.  Then the
law-integral of the cutoff half-energy minus the terminal response is at most
`max 3 (32 d^2 responseCutoffProfileConst)` times
`τ^- + (τ^- E[J_t^-])^{1/2} + 3^{-H} E[J_t^-]`.  This is the first error row of
`p.response.transfer` on the carriers of the cutoff estimate. -/
theorem abs_integral_cutoffHalfEnergy_sub_respJ_le_rowMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hid : ∀ a, cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)
      = (1 / 2 : ℝ) * volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x))
    (hosc : ∀ a, |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
            scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)
          - (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))|
        ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)) *
            (2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqMinus P jStar F t e) (respCoeffMinus F a)))
    (hcmp : ∀ w ∈ triadicIndexBox d H, ∀ a,
      |(1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
          - ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
              (respqMinus P jStar F t e) (respCoeffMinus F a)|
        ≤ (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
              (respqMinus P jStar F t e) (respCoeffMinus F a)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                  (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))
          + 2 * Real.sqrt (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a) *
            (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
                (respqMinus P jStar F t e) (respCoeffMinus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))))
    (hc0 : (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1) = 0)
    (hc1 : ∀ w ∈ triadicIndexBox d H,
      |volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)| ≤ 1)
    (hJ0 : ∀ w ∈ triadicIndexBox d H, ∀ a,
      0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a))
    (hD0 : ∀ w ∈ triadicIndexBox d H, ∀ a,
      0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))
    (hJt0 : ∀ a, 0 ≤ respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a))
    (hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
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
      scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)) P)
    (hJtint : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hJval : ∀ w ∈ triadicIndexBox d H,
      (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P)
        = ∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P)
    (hDval : (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
      (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) ∂P)
      = respTauMinus P jStar F s t e) :
    |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)) ∂P|
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
          (respTauMinus P jStar F s t e +
            Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) +
            (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) := by
  have hK : 0 ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)) := by
    have hθ : 0 ≤ responseCutoffProfileConst := le_of_lt responseCutoffProfileConst_pos
    have h3 : 0 ≤ (3 : ℝ) ^ (-(H : ℝ)) := Real.rpow_nonneg (by norm_num) _
    positivity
  have hcJ : (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P)
      = respEJMinus P jStar F t e + respTauMinus P jStar F s t e := by
    unfold respTauMinus
    ring
  have hglue : |∫ a, volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x) ∂P|
      ≤ 6 * respTauMinus P jStar F s t e
        + 4 * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
        + 2 * (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
            * respEJMinus P jStar F t e :=
    abs_integral_le_row1_of_parts (d := d) P H
      (fun w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
      (fun w a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))
      (fun w a => ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a))
      (fun w a => ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)))
      (fun a => volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x))
      (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a))
      (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
      (∫ a, respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P)
      (respTauMinus P jStar F s t e) (respEJMinus P jStar F t e)
      hK hosc hcmp hc0 hc1 hJ0 hD0 hJt0 hJint hDint hEint hWint hJtint hJval hDval rfl hcJ
  have hLHS : |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)) ∂P|
      = (1 / 2 : ℝ) * |∫ a, volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x) ∂P| := by
    have h1 : (∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
          - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqMinus P jStar F t e) (respCoeffMinus F a)) ∂P)
        = ∫ a, (1 / 2 : ℝ) * volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
            scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall hid)
    rw [h1, integral_const_mul, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)]
  have hNnonneg : 0 ≤ (((triadicIndexBox d H).card : ℝ))⁻¹ := by
    have hcard : ((triadicIndexBox d H).card : ℝ) = ((3 : ℝ) ^ H) ^ d :=
      card_triadicIndexBox H
    rw [hcard]
    positivity
  have hτ0 : 0 ≤ respTauMinus P jStar F s t e := by
    rw [← hDval]
    exact integral_nonneg (fun a => mul_nonneg hNnonneg
      (Finset.sum_nonneg (fun w hw => hD0 w hw a)))
  have hEJ0 : 0 ≤ respEJMinus P jStar F t e := by
    show 0 ≤ ∫ a, respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P
    exact integral_nonneg hJt0
  have h3H : 0 ≤ (3 : ℝ) ^ (-(H : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hC3 : (3 : ℝ) ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) :=
    le_max_left _ _
  have hCθ : 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) := le_max_right _ _
  have hC2 : (2 : ℝ) ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) :=
    le_trans (by norm_num) hC3
  have h1 : 3 * respTauMinus P jStar F s t e
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) * respTauMinus P jStar F s t e :=
    mul_le_mul_of_nonneg_right hC3 hτ0
  have h2 : 2 * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
          * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) :=
    mul_le_mul_of_nonneg_right hC2 (Real.sqrt_nonneg _)
  have h3 : (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
        * respEJMinus P jStar F t e
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
          * ((3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) := by
    calc (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * respEJMinus P jStar F t e
        = (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
            * ((3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) := by ring
      _ ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
            * ((3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) :=
          mul_le_mul_of_nonneg_right hCθ (mul_nonneg h3H hEJ0)
  have hfinal : 3 * respTauMinus P jStar F s t e
        + 2 * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
        + (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
            * respEJMinus P jStar F t e
      ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
          * (respTauMinus P jStar F s t e
            + Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
            + (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) := by
    calc 3 * respTauMinus P jStar F s t e
          + 2 * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
          + (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
              * respEJMinus P jStar F t e
        ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) * respTauMinus P jStar F s t e
          + max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
              * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
          + max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
              * ((3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) :=
          add_le_add (add_le_add h1 h2) h3
      _ = max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst)
          * (respTauMinus P jStar F s t e
            + Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
            + (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) := by ring
  calc |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)) ∂P|
      = (1 / 2 : ℝ) * |∫ a, volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x) ∂P| := hLHS
    _ ≤ (1 / 2 : ℝ) * (6 * respTauMinus P jStar F s t e
          + 4 * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
          + 2 * (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
              * respEJMinus P jStar F t e) :=
        mul_le_mul_of_nonneg_left hglue (by norm_num)
    _ = 3 * respTauMinus P jStar F s t e
          + 2 * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
          + (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
              * respEJMinus P jStar F t e := by ring
    _ ≤ max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
          (respTauMinus P jStar F s t e
            + Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
            + (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) := hfinal

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cutoff energy defect at an almost-everywhere elliptic coefficient

The response identity `cutoffHalfEnergy_sub_respJ_eq` identifies the cutoff energy defect
`cutoffHalfEnergyAux - respJ` with half the `(φ - 1)`-weighted optimizer energy, but only for a
coefficient that is pointwise elliptic on the cell.  The two coefficient fields of the response
problem, `respCoeffMinus F a` and `respCoeffPlus F a`, are elliptic only almost everywhere: a point
of `CoeffSpace d` is an a.e. class, and no representative is elliptic pointwise.

The identity is nevertheless invariant under an a.e. replacement of the coefficient, because
carrying a harmonic function along the replacement leaves its gradient — and hence both the
cutoff half-energy and the pathwise response — unchanged.  Running the pointwise identity at the
elliptic representative supplied by `exists_elliptic_representative_respCell_respCoeffMinus` and
transporting back gives the defect identity verbatim for the carrier coefficient and the given
maximizer:

* `cutoffHalfEnergyAux_sub_respJ_eq_respCoeffMinus` — the minus family `a_- = a - g`;
* `cutoffHalfEnergyAux_sub_respJ_eq_respCoeffPlus` — the adjoint twin `a_+ = a^t + g`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The doubled optimizer energy `⟨Z₁, Z₂⟩ = ∇v · b ∇v` agrees pointwise with the variation energy
`∇v · (symmPart b) ∇v`, since the antisymmetric part of `b` contributes nothing to the quadratic
form. -/
private theorem vecDot_optimizerField_eq_scalarVariationEnergyIntegrand {d : ℕ}
    (b : CoeffField d) {U : Set (Vec d)} (v : AHarmonicFunction b U) :
    (fun x => vecDot (optimizerField b v x).1 (optimizerField b v x).2)
      = scalarVariationEnergyIntegrand b v := by
  funext x
  simp only [optimizerField, scalarVariationEnergyIntegrand]
  exact (vecDot_matVecMul_symmPart (b x) (v.toH1.grad x)).symm

/-- The cutoff energy defect identity at a pointwise elliptic coefficient that agrees almost
everywhere with the carrier coefficient.  The maximizer `u` for the carrier coefficient `c` is
carried along the a.e. equality to a maximizer for the elliptic representative `f`; the identity
`cutoffHalfEnergy_sub_respJ_eq` is applied there and every quantity is transported back across the
a.e. equality.  Both sides are unchanged by the replacement, so the conclusion names `c` and `u`. -/
private theorem cutoffHalfEnergyAux_sub_respJ_eq_of_ae_eq {d : ℕ} [NeZero d] {q : Mat d}
    (hq : IsUnit q) (t : ℤ) {c f : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f)
    (hae : c =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff q t φ) (p r : Vec d)
    (u : AHarmonicFunction c (HighContrast.adaptedCell q t))
    (hmax : IsResponseMaximizer (HighContrast.adaptedCell q t) p r c u) :
    cutoffHalfEnergyAux (HighContrast.adaptedCell q t) φ c u - respJ q t p r c
      = (1 / 2 : ℝ) * volumeAverage (HighContrast.adaptedCell q t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand c u x) := by
  have hconv : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t) :=
    adaptedCell_isOpenBoundedConvexDomain q hq t
  let v : AHarmonicFunction f (HighContrast.adaptedCell q t) :=
    Response.aHarmonicOfAEEq hae u
  have hmaxf : IsResponseMaximizer (HighContrast.adaptedCell q t) p r f v :=
    isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff hae p r hmax
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    hconv.isFiniteMeasure_restrict_volume
  have hdata : ResponseLinearIntegrabilityData (HighContrast.adaptedCell q t) f :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hu_int : weakFluxIntegrable (HighContrast.adaptedCell q t) f v := hdata.weakFlux v
  have hresp_u :
      IntegrableOn (scalarResponseIntegrand (HighContrast.adaptedCell q t) f p r v)
        (HighContrast.adaptedCell q t) :=
    hdata.response p r v
  have hlin_self :
      IntegrableOn (scalarFirstVariationIntegrand (HighContrast.adaptedCell q t) f p r v v)
        (HighContrast.adaptedCell q t) :=
    hdata.firstVariation p r v v
  have henergy : IntegrableOn (scalarVariationEnergyIntegrand f v) (HighContrast.adaptedCell q t) :=
    hdata.energy v
  have hφm : Measurable φ := hφ.2.2.2.2.2.1.continuous.measurable
  have hφb : ∀ x, |φ x| ≤ 2 := fun x => by
    rw [abs_of_nonneg (hφ.1 x)]
    exact hφ.2.1 x
  have hvecD : (fun x => vecDot (optimizerField f v x).1 (optimizerField f v x).2)
      = scalarVariationEnergyIntegrand f v :=
    vecDot_optimizerField_eq_scalarVariationEnergyIntegrand f v
  have hD_int :
      IntegrableOn (fun x => vecDot (optimizerField f v x).1 (optimizerField f v x).2)
        (HighContrast.adaptedCell q t) := by
    rw [hvecD]
    exact henergy
  have hφD :
      IntegrableOn (fun x => φ x * vecDot (optimizerField f v x).1 (optimizerField f v x).2)
        (HighContrast.adaptedCell q t) :=
    integrableOn_cutoff_mul_coord hconv.isOpen.measurableSet hconv.volume_lt_top.ne hφm
      hφb hD_int
  have hkey := cutoffHalfEnergy_sub_respJ_eq (q := q) hq t hEll φ p r v hmaxf
    hu_int hresp_u hlin_self henergy hφD
  have hvecφ : (fun x => φ x * vecDot (optimizerField f v x).1 (optimizerField f v x).2)
      = fun x => φ x * scalarVariationEnergyIntegrand f v x := by
    funext x
    rw [congrFun hvecD x]
  have hvecψ :
      (fun x => (φ x - 1) * vecDot (optimizerField f v x).1 (optimizerField f v x).2)
        = fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x := by
    funext x
    rw [congrFun hvecD x]
  rw [hvecφ, hvecψ] at hkey
  have hkeyE : cutoffHalfEnergyAux (HighContrast.adaptedCell q t) φ f v - respJ q t p r f
      = (1 / 2 : ℝ) * volumeAverage (HighContrast.adaptedCell q t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x) := by
    unfold cutoffHalfEnergyAux
    rw [hvecφ]
    exact hkey
  have hcut : cutoffHalfEnergyAux (HighContrast.adaptedCell q t) φ f v
      = cutoffHalfEnergyAux (HighContrast.adaptedCell q t) φ c u :=
    cutoffHalfEnergyAux_aHarmonicFunctionOfAEEqCoeff (U := HighContrast.adaptedCell q t) hae φ u
  have hrespJ : respJ q t p r c = respJ q t p r f := by
    unfold respJ
    exact responseJ_congr_of_ae_eq_subset (U := HighContrast.adaptedCell q t)
      (V := HighContrast.adaptedCell q t) subset_rfl hae p r
  have hLHS : cutoffHalfEnergyAux (HighContrast.adaptedCell q t) φ c u - respJ q t p r c
      = cutoffHalfEnergyAux (HighContrast.adaptedCell q t) φ f v - respJ q t p r f := by
    rw [← hcut, hrespJ]
  have hRHS : volumeAverage (HighContrast.adaptedCell q t)
        (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
      = volumeAverage (HighContrast.adaptedCell q t)
        (fun x => (φ x - 1) * scalarVariationEnergyIntegrand c u x) :=
    volumeAverage_weighted_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff
      (U := HighContrast.adaptedCell q t) (V := HighContrast.adaptedCell q t) subset_rfl hae
      (fun x => φ x - 1) u
  rw [hLHS, hkeyE, hRHS]

/-- The cutoff energy defect of the minus family, with no pointwise ellipticity hypothesis. -/
theorem cutoffHalfEnergyAux_sub_respJ_eq_respCoeffMinus {d : ℕ} [NeZero d] {jStar : ℕ}
    (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ) (p r : Vec d)
    (a : CoeffSpace d) (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : IsResponseMaximizer (respCell jStar F t) p r (respCoeffMinus F a) u) :
    cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) u
        - respJ (respGrid jStar F) t p r (respCoeffMinus F a)
      = (1 / 2 : ℝ) * volumeAverage (respCell jStar F t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand (respCoeffMinus F a) u x) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  obtain ⟨lam, Lam, f, _, _, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  exact cutoffHalfEnergyAux_sub_respJ_eq_of_ae_eq (q := respGrid jStar F) hq t hEll hae
    φ hφ p r u hmax

/-- The adjoint twin. -/
theorem cutoffHalfEnergyAux_sub_respJ_eq_respCoeffPlus {d : ℕ} [NeZero d] {jStar : ℕ}
    (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ) (p r : Vec d)
    (a : CoeffSpace d) (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : IsResponseMaximizer (respCell jStar F t) p r (respCoeffPlus F a) u) :
    cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) u
        - respJ (respGrid jStar F) t p r (respCoeffPlus F a)
      = (1 / 2 : ℝ) * volumeAverage (respCell jStar F t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand (respCoeffPlus F a) u x) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  obtain ⟨lam, Lam, f, _, _, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  exact cutoffHalfEnergyAux_sub_respJ_eq_of_ae_eq (q := respGrid jStar F) hq t hEll hae
    φ hφ p r u hmax

end

end HCPolySupport.HighContrast.Multiscale
end
