/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RecentCellDefectBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.WeakEstimateAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.TerminalEnergyMeasurability

/-!
# High-contrast homogenization: Entry.Response.Rows.TerminalHalfEnergyIntegrability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Sample Integrability of the Terminal and Half-Energy Readouts

For each aligned subcell of the coarse scale, this file shows the subcell average of the terminal
optimizer's energy density and the `(φ - 1)`-weighted terminal energy are both `P`-integrable,
by domination: the subcell energies are nonnegative with flat average the nonnegative terminal
energy, while a response cutoff's weight lies in `[0, 2]` so the cutoff-weighted half-energy is
dominated by the terminal energy itself. It also records, on an aligned cell, the
almost-everywhere strong measurability and the `P`-integrability of the individual entries of the
pathwise coarse block of the recentred coefficients `a_- = a - g` and `a_+ = a^T + g`, read
through the block response mean of the subcell maximizer and the two diagonal quadratic forms
against the dual variable.

Paper: `p.response.transfer`.
-/

section
/-!
## Sample integrability of the subcell and weighted optimizer energies

The terminal-optimizer replacement row of `p.response.transfer` needs, for each aligned subcell of
the coarse scale, the sample integrability of the subcell average of the terminal optimizer's
energy density, and the sample integrability of the `(φ - 1)`-weighted terminal energy.  Both are
obtained by domination.  The subcell energies are nonnegative and their flat average is the
terminal cell energy, which at a maximizer is twice the terminal response; and the cutoff satisfies
`|φ - 1| ≤ 1`, so the weighted terminal energy is dominated by the terminal energy, itself twice the
response.  The four statements below are the two signs of each fact, for the recentred coefficient
`a_- = a - g` and its adjoint twin `a_+ = aᵗ + g`.

Paper: `p.response.transfer`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Sample integrability of the subcell energy, minus sign.**  On every aligned subcell of the
coarse scale the average of the terminal optimizer energy density is `P`-integrable, because that
average is nonnegative and the flat sum of the subcell averages equals the terminal cell average,
which at a maximizer is twice the terminal response `J_t^-`; the response is `P`-integrable and each
subcell average is `P`-a.e.-strongly measurable. -/
theorem integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hmeasE : ∀ w ∈ triadicIndexBox d H, MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P) :
    ∀ w ∈ triadicIndexBox d H, MeasureTheory.Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P := by
  have hcard : (((triadicIndexBox d H).card : ℝ)) ≠ 0 := by
    rw [card_triadicIndexBox]
    exact ne_of_gt (by positivity)
  refine fun w hw => integrable_of_nonneg_of_sum_eq
    (Z := triadicIndexBox d H)
    (f := fun w a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))
    (g := fun a => ((triadicIndexBox d H).card : ℝ) *
      (2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)))
    ?_ ?_ ?_ ?_ w hw
  · intro i hi a
    exact zero_le_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus
      jStar hjStar F hm H s t ht uM a i hi
  · exact hmeasE
  · simpa only [mul_assoc] using hJt.const_mul (((triadicIndexBox d H).card : ℝ) * 2)
  · intro a
    have h1 := avsum_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus_eq
      jStar hjStar F hm H s t ht uM a
    have h2 := volumeAverage_energy_respCell_respCoeffMinus_eq P jStar hjStar F hm t e uM hmax a
    rw [h2] at h1
    calc ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
        = 1 * (∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) := (one_mul _).symm
      _ = (((triadicIndexBox d H).card : ℝ) * (((triadicIndexBox d H).card : ℝ))⁻¹) *
            (∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) := by
            rw [mul_inv_cancel₀ hcard]
      _ = ((triadicIndexBox d H).card : ℝ) *
            ((((triadicIndexBox d H).card : ℝ))⁻¹ *
              (∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))) := by
            rw [mul_assoc]
      _ = ((triadicIndexBox d H).card : ℝ) *
            (2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqMinus P jStar F t e) (respCoeffMinus F a)) := by
            rw [h1]

/-- **Sample integrability of the weighted terminal energy, minus sign.**  For a response cutoff
`φ` with `0 ≤ φ ≤ 2`, the `(φ - 1)`-weighted terminal optimizer energy is `P`-integrable: its
absolute value is at most the terminal energy average, which at a maximizer is twice the terminal
response `J_t^-`, and the response is `P`-integrable. -/
theorem integrable_volumeAverage_weighted_energy_respCoeffMinus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (t : ℤ) (e : Vec d) (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hmeasW : MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)) P) :
    MeasureTheory.Integrable (fun a =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hU : MeasurableSet (respCell jStar F t) :=
    (isOpen_adaptedCell_of_isUnit hq t).measurableSet
  refine (hJt.const_mul 2).mono' hmeasW ?_
  filter_upwards with a
  rw [Real.norm_eq_abs]
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  let v : AHarmonicFunction f (respCell jStar F t) := Response.aHarmonicOfAEEq hae (uM a)
  have hE : IntegrableOn (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
      (respCell jStar F t) :=
    integrableOn_energy_respCell_respCoeffMinus jStar hjStar F hm t uM a
  have hφm : Measurable φ := hφ.2.2.2.2.2.1.continuous.measurable
  have hEae : scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)
      =ᵐ[volumeMeasureOn (respCell jStar F t)] scalarVariationEnergyIntegrand f v := by
    filter_upwards [hae] with x hx
    dsimp only [v]
    simp only [scalarVariationEnergyIntegrand, Response.aHarmonicOfAEEq_grad]
    rw [hx]
  have hEf_nonneg_ae : 0 ≤ᵐ[volumeMeasureOn (respCell jStar F t)]
      scalarVariationEnergyIntegrand f v :=
    (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall fun x hx =>
      scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
        (respCell jStar F t) f hEll v x hx)
  have hE_nonneg : 0 ≤ᵐ[volumeMeasureOn (respCell jStar F t)]
      scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) := by
    filter_upwards [hEae, hEf_nonneg_ae] with x hx hx0
    rw [hx]
    exact hx0
  have hF : IntegrableOn (fun x => (φ x - 1) *
      scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x) (respCell jStar F t) := by
    refine (hE.abs).mono' ?_ ?_
    · exact ((hφm.sub measurable_const).aestronglyMeasurable).mul hE.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul]
      calc |φ x - 1| * |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|
          ≤ 1 * |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x| :=
            mul_le_mul_of_nonneg_right (abs_isResponseCutoff_sub_one hφ x) (abs_nonneg _)
        _ = |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x| := one_mul _
  have hle : ∀ x ∈ respCell jStar F t,
      |(φ x - 1) * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|
        ≤ |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x| := by
    intro x _hx
    rw [abs_mul]
    calc |φ x - 1| * |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|
        ≤ 1 * |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x| :=
          mul_le_mul_of_nonneg_right (abs_isResponseCutoff_sub_one hφ x) (abs_nonneg _)
      _ = |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x| := one_mul _
  have hmain : |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
      scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)|
      ≤ volumeAverage (respCell jStar F t)
        (fun x => |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|) :=
    volumeAverage_abs_le_of_le hU hle hF hE.abs
  have habs_eq : volumeAverage (respCell jStar F t)
        (fun x => |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|)
      = volumeAverage (respCell jStar F t)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := by
    unfold volumeAverage
    rw [integral_congr_ae (hE_nonneg.mono fun x hx => abs_of_nonneg hx)]
  have hE_eq : volumeAverage (respCell jStar F t)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
      = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a) :=
    volumeAverage_energy_respCell_respCoeffMinus_eq P jStar hjStar F hm t e uM hmax a
  calc |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)|
      ≤ volumeAverage (respCell jStar F t)
        (fun x => |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|) := hmain
    _ = volumeAverage (respCell jStar F t)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := habs_eq
    _ = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a) := hE_eq

/-- **Sample integrability of the subcell energy, plus sign.**  The twin of
`integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus` for the adjoint recentred
coefficient `a_+ = aᵗ + g` and its terminal optimizer. -/
theorem integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hmeasE : ∀ w ∈ triadicIndexBox d H, MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P) :
    ∀ w ∈ triadicIndexBox d H, MeasureTheory.Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P := by
  have hcard : (((triadicIndexBox d H).card : ℝ)) ≠ 0 := by
    rw [card_triadicIndexBox]
    exact ne_of_gt (by positivity)
  refine fun w hw => integrable_of_nonneg_of_sum_eq
    (Z := triadicIndexBox d H)
    (f := fun w a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))
    (g := fun a => ((triadicIndexBox d H).card : ℝ) *
      (2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)))
    ?_ ?_ ?_ ?_ w hw
  · intro i hi a
    exact zero_le_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus
      jStar hjStar F hm H s t ht uP a i hi
  · exact hmeasE
  · simpa only [mul_assoc] using hJt.const_mul (((triadicIndexBox d H).card : ℝ) * 2)
  · intro a
    have h1 := avsum_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus_eq
      jStar hjStar F hm H s t ht uP a
    have h2 := volumeAverage_energy_respCell_respCoeffPlus_eq P jStar hjStar F hm t e uP hmax a
    rw [h2] at h1
    calc ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
        = 1 * (∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) := (one_mul _).symm
      _ = (((triadicIndexBox d H).card : ℝ) * (((triadicIndexBox d H).card : ℝ))⁻¹) *
            (∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) := by
            rw [mul_inv_cancel₀ hcard]
      _ = ((triadicIndexBox d H).card : ℝ) *
            ((((triadicIndexBox d H).card : ℝ))⁻¹ *
              (∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))) := by
            rw [mul_assoc]
      _ = ((triadicIndexBox d H).card : ℝ) *
            (2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a)) := by
            rw [h1]

/-- **Sample integrability of the weighted terminal energy, plus sign.**  The twin of
`integrable_volumeAverage_weighted_energy_respCoeffMinus` for the adjoint recentred coefficient
`a_+ = aᵗ + g`. -/
theorem integrable_volumeAverage_weighted_energy_respCoeffPlus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (t : ℤ) (e : Vec d) (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hmeasW : MeasureTheory.AEStronglyMeasurable (fun a =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)) P) :
    MeasureTheory.Integrable (fun a =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hU : MeasurableSet (respCell jStar F t) :=
    (isOpen_adaptedCell_of_isUnit hq t).measurableSet
  refine (hJt.const_mul 2).mono' hmeasW ?_
  filter_upwards with a
  rw [Real.norm_eq_abs]
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  let v : AHarmonicFunction f (respCell jStar F t) := Response.aHarmonicOfAEEq hae (uP a)
  have hE : IntegrableOn (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
      (respCell jStar F t) :=
    integrableOn_energy_respCell_respCoeffPlus jStar hjStar F hm t uP a
  have hφm : Measurable φ := hφ.2.2.2.2.2.1.continuous.measurable
  have hEae : scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)
      =ᵐ[volumeMeasureOn (respCell jStar F t)] scalarVariationEnergyIntegrand f v := by
    filter_upwards [hae] with x hx
    dsimp only [v]
    simp only [scalarVariationEnergyIntegrand, Response.aHarmonicOfAEEq_grad]
    rw [hx]
  have hEf_nonneg_ae : 0 ≤ᵐ[volumeMeasureOn (respCell jStar F t)]
      scalarVariationEnergyIntegrand f v :=
    (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall fun x hx =>
      scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
        (respCell jStar F t) f hEll v x hx)
  have hE_nonneg : 0 ≤ᵐ[volumeMeasureOn (respCell jStar F t)]
      scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) := by
    filter_upwards [hEae, hEf_nonneg_ae] with x hx hx0
    rw [hx]
    exact hx0
  have hF : IntegrableOn (fun x => (φ x - 1) *
      scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) (respCell jStar F t) := by
    refine (hE.abs).mono' ?_ ?_
    · exact ((hφm.sub measurable_const).aestronglyMeasurable).mul hE.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul]
      calc |φ x - 1| * |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|
          ≤ 1 * |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x| :=
            mul_le_mul_of_nonneg_right (abs_isResponseCutoff_sub_one hφ x) (abs_nonneg _)
        _ = |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x| := one_mul _
  have hle : ∀ x ∈ respCell jStar F t,
      |(φ x - 1) * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|
        ≤ |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x| := by
    intro x _hx
    rw [abs_mul]
    calc |φ x - 1| * |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|
        ≤ 1 * |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x| :=
          mul_le_mul_of_nonneg_right (abs_isResponseCutoff_sub_one hφ x) (abs_nonneg _)
      _ = |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x| := one_mul _
  have hmain : |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
      scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)|
      ≤ volumeAverage (respCell jStar F t)
        (fun x => |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|) :=
    volumeAverage_abs_le_of_le hU hle hF hE.abs
  have habs_eq : volumeAverage (respCell jStar F t)
        (fun x => |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|)
      = volumeAverage (respCell jStar F t)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := by
    unfold volumeAverage
    rw [integral_congr_ae (hE_nonneg.mono fun x hx => abs_of_nonneg hx)]
  have hE_eq : volumeAverage (respCell jStar F t)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
      = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a) :=
    volumeAverage_energy_respCell_respCoeffPlus_eq P jStar hjStar F hm t e uP hmax a
  calc |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
        scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)|
      ≤ volumeAverage (respCell jStar F t)
        (fun x => |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|) := hmain
    _ = volumeAverage (respCell jStar F t)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := habs_eq
    _ = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a) := hE_eq

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Sample integrability of the cutoff half-energy defect

The centred cutoff decomposition of `p.response.transfer` integrates, against the law `P` of
coefficients, the difference between the cutoff-weighted half-energy of the terminal optimizer and
the terminal response.  A response cutoff keeps its weight between zero and two, so the
cutoff-weighted half-energy is dominated by the terminal energy, which at a maximizer is twice the
terminal response; the response is `P`-integrable and the weighted energy readout is measurable in
the sample, so that difference is `P`-integrable.

Both signs of the recentred coefficient, `a_- = a - g` and its adjoint twin `a_+ = aᵗ + g`, are
covered.

Paper: `p.response.transfer`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Sample integrability of the cutoff half-energy defect, minus sign.**  For a response cutoff
`φ` with `0 ≤ φ ≤ 2` and a terminal optimizer family for the recentred coefficient `a_-`, the
difference between the cutoff-weighted half-energy of the optimizer and the terminal response
`J_t^-` is `P`-integrable.  The half-energy is one half of the `φ`-weighted average of the terminal
energy density; its absolute value is at most twice the terminal response, since the terminal energy
average is twice the response and `|φ| ≤ 2`, so integrability follows by domination from the
`P`-integrability of the response. -/
theorem integrable_cutoffHalfEnergyAux_sub_respJ_respCoeffMinus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (t : ℤ) (e : Vec d) (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P) :
    MeasureTheory.Integrable (fun a =>
      cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)) P := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hU : MeasurableSet (respCell jStar F t) :=
    (isOpen_adaptedCell_of_isUnit hq t).measurableSet
  have hφm : Measurable φ := hφ.2.2.2.2.2.1.continuous.measurable
  have hφabs : ∀ x : Vec d, ‖φ x‖ ≤ 2 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.1 x)]
    exact hφ.2.1 x
  have hpt : ∀ (a : CoeffSpace d) (x : Vec d),
      vecDot (optimizerField (respCoeffMinus F a) (uM a) x).1
        (optimizerField (respCoeffMinus F a) (uM a) x).2
      = scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x := by
    intro a x
    simp only [scalarVariationEnergyIntegrand, optimizerField]
    exact (vecDot_matVecMul_symmPart (respCoeffMinus F a x) ((uM a).toH1.grad x)).symm
  have hptfun : ∀ a : CoeffSpace d,
      (fun x : Vec d => φ x * vecDot (optimizerField (respCoeffMinus F a) (uM a) x).1
          (optimizerField (respCoeffMinus F a) (uM a) x).2)
        = fun x : Vec d => φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x := by
    intro a
    funext x
    rw [hpt a x]
  have hEqFun : (fun a => cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a))
      = fun a => (1 / 2 : ℝ) * volumeAverage (respCell jStar F t)
          (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x) := by
    funext a
    simp only [cutoffHalfEnergyAux]
    rw [hptfun a]
  have hMeas : Measurable (fun a : CoeffSpace d => volumeAverage (respCell jStar F t)
      (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)) :=
    measurable_volumeAverage_weighted_energy_respCoeffMinus P jStar hjStar F hm t e uM hmax
      hφm.aestronglyMeasurable (Filter.Eventually.of_forall hφabs)
  have hHalfInt : MeasureTheory.Integrable
      (fun a => cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)) P := by
    rw [hEqFun]
    refine (hJt.const_mul 2).mono' ?_ ?_
    · exact (hMeas.const_mul (1 / 2)).aestronglyMeasurable
    · filter_upwards with a
      rw [Real.norm_eq_abs]
      obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
        exists_elliptic_representative_respCell_respCoeffMinus (F := F) hjStar hm t a
      let v : AHarmonicFunction f (respCell jStar F t) := Response.aHarmonicOfAEEq hae (uM a)
      have hE : IntegrableOn (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
          (respCell jStar F t) :=
        integrableOn_energy_respCell_respCoeffMinus jStar hjStar F hm t uM a
      have hEae : scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)
          =ᵐ[volumeMeasureOn (respCell jStar F t)] scalarVariationEnergyIntegrand f v := by
        filter_upwards [hae] with x hx
        dsimp only [v]
        simp only [scalarVariationEnergyIntegrand, Response.aHarmonicOfAEEq_grad]
        rw [hx]
      have hEf_nonneg_ae : 0 ≤ᵐ[volumeMeasureOn (respCell jStar F t)]
          scalarVariationEnergyIntegrand f v :=
        (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall fun x hx =>
          scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
            (respCell jStar F t) f hEll v x hx)
      have hE_nonneg : 0 ≤ᵐ[volumeMeasureOn (respCell jStar F t)]
          scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) := by
        filter_upwards [hEae, hEf_nonneg_ae] with x hx hx0
        rw [hx]
        exact hx0
      have hF : IntegrableOn
          (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)
          (respCell jStar F t) := by
        refine ((hE.abs).const_mul 2).mono' ?_ ?_
        · exact (hφm.aestronglyMeasurable).mul hE.aestronglyMeasurable
        · filter_upwards with x
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (hφabs x) (abs_nonneg _)
      have hle : ∀ x ∈ respCell jStar F t,
          |φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|
            ≤ 2 * |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x| := by
        intro x _hx
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hφabs x) (abs_nonneg _)
      have hmain : |volumeAverage (respCell jStar F t)
            (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)|
          ≤ volumeAverage (respCell jStar F t)
            (fun x => 2 * |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|) :=
        volumeAverage_abs_le_of_le hU hle hF ((hE.abs).const_mul 2)
      have habs_eq : volumeAverage (respCell jStar F t)
            (fun x => |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|)
          = volumeAverage (respCell jStar F t)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := by
        unfold volumeAverage
        rw [integral_congr_ae (hE_nonneg.mono fun x hx => abs_of_nonneg hx)]
      have h2 : volumeAverage (respCell jStar F t)
            (fun x => 2 * |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|)
          = 2 * volumeAverage (respCell jStar F t)
            (fun x => |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|) := by
        simpa only [smul_eq_mul] using!
          volumeAverage_smul (respCell jStar F t) (2 : ℝ)
            (fun x => |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|)
      have hE_eq : volumeAverage (respCell jStar F t)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
          = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqMinus P jStar F t e) (respCoeffMinus F a) :=
        volumeAverage_energy_respCell_respCoeffMinus_eq P jStar hjStar F hm t e uM hmax a
      calc |(1 / 2 : ℝ) * volumeAverage (respCell jStar F t)
              (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)|
          = (1 / 2 : ℝ) * |volumeAverage (respCell jStar F t)
              (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)| := by
              rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
        _ ≤ (1 / 2 : ℝ) * volumeAverage (respCell jStar F t)
              (fun x => 2 * |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|) :=
              mul_le_mul_of_nonneg_left hmain (by norm_num)
        _ = (1 / 2 : ℝ) * (2 * volumeAverage (respCell jStar F t)
              (fun x => |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|)) := by
              rw [h2]
        _ = volumeAverage (respCell jStar F t)
              (fun x => |scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x|) := by ring
        _ = volumeAverage (respCell jStar F t)
              (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := habs_eq
        _ = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqMinus P jStar F t e) (respCoeffMinus F a) := hE_eq
  exact hHalfInt.sub hJt

/-- **Sample integrability of the cutoff half-energy defect, plus sign.**  The twin of
`integrable_cutoffHalfEnergyAux_sub_respJ_respCoeffMinus` for the adjoint recentred coefficient
`a_+ = aᵗ + g` and its terminal optimizer. -/
theorem integrable_cutoffHalfEnergyAux_sub_respJ_respCoeffPlus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (t : ℤ) (e : Vec d) (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hJt : MeasureTheory.Integrable (fun a =>
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P) :
    MeasureTheory.Integrable (fun a =>
      cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)) P := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hU : MeasurableSet (respCell jStar F t) :=
    (isOpen_adaptedCell_of_isUnit hq t).measurableSet
  have hφm : Measurable φ := hφ.2.2.2.2.2.1.continuous.measurable
  have hφabs : ∀ x : Vec d, ‖φ x‖ ≤ 2 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.1 x)]
    exact hφ.2.1 x
  have hpt : ∀ (a : CoeffSpace d) (x : Vec d),
      vecDot (optimizerField (respCoeffPlus F a) (uP a) x).1
        (optimizerField (respCoeffPlus F a) (uP a) x).2
      = scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x := by
    intro a x
    simp only [scalarVariationEnergyIntegrand, optimizerField]
    exact (vecDot_matVecMul_symmPart (respCoeffPlus F a x) ((uP a).toH1.grad x)).symm
  have hptfun : ∀ a : CoeffSpace d,
      (fun x : Vec d => φ x * vecDot (optimizerField (respCoeffPlus F a) (uP a) x).1
          (optimizerField (respCoeffPlus F a) (uP a) x).2)
        = fun x : Vec d => φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x := by
    intro a
    funext x
    rw [hpt a x]
  have hEqFun : (fun a => cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a))
      = fun a => (1 / 2 : ℝ) * volumeAverage (respCell jStar F t)
          (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) := by
    funext a
    simp only [cutoffHalfEnergyAux]
    rw [hptfun a]
  have hMeas : Measurable (fun a : CoeffSpace d => volumeAverage (respCell jStar F t)
      (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)) :=
    measurable_volumeAverage_weighted_energy_respCoeffPlus P jStar hjStar F hm t e uP hmax
      hφm.aestronglyMeasurable (Filter.Eventually.of_forall hφabs)
  have hHalfInt : MeasureTheory.Integrable
      (fun a => cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)) P := by
    rw [hEqFun]
    refine (hJt.const_mul 2).mono' ?_ ?_
    · exact (hMeas.const_mul (1 / 2)).aestronglyMeasurable
    · filter_upwards with a
      rw [Real.norm_eq_abs]
      obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
        exists_elliptic_representative_respCell_respCoeffPlus (F := F) hjStar hm t a
      let v : AHarmonicFunction f (respCell jStar F t) := Response.aHarmonicOfAEEq hae (uP a)
      have hE : IntegrableOn (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
          (respCell jStar F t) :=
        integrableOn_energy_respCell_respCoeffPlus jStar hjStar F hm t uP a
      have hEae : scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)
          =ᵐ[volumeMeasureOn (respCell jStar F t)] scalarVariationEnergyIntegrand f v := by
        filter_upwards [hae] with x hx
        dsimp only [v]
        simp only [scalarVariationEnergyIntegrand, Response.aHarmonicOfAEEq_grad]
        rw [hx]
      have hEf_nonneg_ae : 0 ≤ᵐ[volumeMeasureOn (respCell jStar F t)]
          scalarVariationEnergyIntegrand f v :=
        (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall fun x hx =>
          scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
            (respCell jStar F t) f hEll v x hx)
      have hE_nonneg : 0 ≤ᵐ[volumeMeasureOn (respCell jStar F t)]
          scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) := by
        filter_upwards [hEae, hEf_nonneg_ae] with x hx hx0
        rw [hx]
        exact hx0
      have hF : IntegrableOn
          (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)
          (respCell jStar F t) := by
        refine ((hE.abs).const_mul 2).mono' ?_ ?_
        · exact (hφm.aestronglyMeasurable).mul hE.aestronglyMeasurable
        · filter_upwards with x
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (hφabs x) (abs_nonneg _)
      have hle : ∀ x ∈ respCell jStar F t,
          |φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|
            ≤ 2 * |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x| := by
        intro x _hx
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hφabs x) (abs_nonneg _)
      have hmain : |volumeAverage (respCell jStar F t)
            (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)|
          ≤ volumeAverage (respCell jStar F t)
            (fun x => 2 * |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|) :=
        volumeAverage_abs_le_of_le hU hle hF ((hE.abs).const_mul 2)
      have habs_eq : volumeAverage (respCell jStar F t)
            (fun x => |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|)
          = volumeAverage (respCell jStar F t)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := by
        unfold volumeAverage
        rw [integral_congr_ae (hE_nonneg.mono fun x hx => abs_of_nonneg hx)]
      have h2 : volumeAverage (respCell jStar F t)
            (fun x => 2 * |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|)
          = 2 * volumeAverage (respCell jStar F t)
            (fun x => |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|) := by
        simpa only [smul_eq_mul] using!
          volumeAverage_smul (respCell jStar F t) (2 : ℝ)
            (fun x => |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|)
      have hE_eq : volumeAverage (respCell jStar F t)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
          = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a) :=
        volumeAverage_energy_respCell_respCoeffPlus_eq P jStar hjStar F hm t e uP hmax a
      calc |(1 / 2 : ℝ) * volumeAverage (respCell jStar F t)
              (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)|
          = (1 / 2 : ℝ) * |volumeAverage (respCell jStar F t)
              (fun x => φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)| := by
              rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
        _ ≤ (1 / 2 : ℝ) * volumeAverage (respCell jStar F t)
              (fun x => 2 * |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|) :=
              mul_le_mul_of_nonneg_left hmain (by norm_num)
        _ = (1 / 2 : ℝ) * (2 * volumeAverage (respCell jStar F t)
              (fun x => |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|)) := by
              rw [h2]
        _ = volumeAverage (respCell jStar F t)
              (fun x => |scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x|) := by ring
        _ = volumeAverage (respCell jStar F t)
              (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := habs_eq
        _ = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
              (respqPlus P jStar F t e) (respCoeffPlus F a) := hE_eq
  exact hHalfInt.sub hJt

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The full entry family of the recentred coarse block on an aligned cell

The cell half of the cutoff-mean row of `p.response.transfer` reads the pathwise coarse block of
the recentred coefficients `a_- = a - g` and `a_+ = aᵀ + g` through three different functionals:
the two diagonal quadratic forms against the dual variable, the block response mean of the subcell
maximizer, which uses ALL four sub-blocks, and the stationarity collapse at the centred cell,
which asks only for measurability.  `CarrierIntegrabilityConditions` records the two diagonal
sub-blocks; this
module records the whole entry family, in both the integrable and the measurable form, from the
same congruence bridge.

Recentring by a constant skew matrix field is a block congruence on an aligned adapted cell, so
every entry of the recentred block is a fixed real linear combination of the entries of the coarse
block of the sample; integrability is then `HasIntegrableCoarseBlock` and measurability is
unconditional.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Every entry of the recentred coarse block is integrable on an aligned cell, minus sign.**
The pathwise coarse block of `a_- = a - g` on an aligned adapted cell is the constant congruence
`Gᵀ 𝐀(V; a) G` of the coarse block of the sample, so each of its entries is a fixed real linear
combination of integrable functions. -/
theorem integrable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter q j w)) :
    ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a)) α β) P :=
  integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (respG F) hint
    (fun a => coarseBlockMatrix_respCoeffMinus_at hq j w F a)

/-- **Every entry of the recentred coarse block is integrable on an aligned cell, plus sign.**
The adjoint twin of `integrable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter`, with the
congruence
`G_+ = G D` of the adjoint recentring. -/
theorem integrable_blockMatEntry_respCoeffPlus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter q j w)) :
    ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a)) α β) P :=
  integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (respGPlus F) hint
    (fun a => coarseBlockMatrix_respCoeffPlus_at hq j w F a)

/-- **Every entry of the recentred coarse block is measurable on an aligned cell, minus sign.**
No integrability is needed: the congruence bridge writes the entry as a fixed linear combination of
the entries of the coarse block of the sample, which are measurable outright. -/
theorem aestronglyMeasurable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) :
    ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a)) α β) P := by
  intro α β
  simpa only [blockMatEntry_eq_toFullBlockMat] using
    (measurable_coarseBlockMatrix_minus hq j w F α β).aestronglyMeasurable

/-- **Every entry of the recentred coarse block is measurable on an aligned cell, plus sign.**
The adjoint twin of `aestronglyMeasurable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter`. -/
theorem aestronglyMeasurable_blockMatEntry_respCoeffPlus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) :
    ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a)) α β) P := by
  intro α β
  simpa only [blockMatEntry_eq_toFullBlockMat] using
    (measurable_coarseBlockMatrix_plus hq j w F α β).aestronglyMeasurable

/-- **Measurability of the recentred coarse block at the centred cell, minus sign.**  The centred
cell is the aligned cell at index `0`, so the aligned statement applies verbatim.  This is the
`hmeasBlk` premise of the cell half of the cutoff-mean row. -/
theorem aestronglyMeasurable_blockMatEntry_respCoeffMinus_adaptedCell {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : IsUnit q) (j : ℤ) (F : BlockMat d) :
    ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => blockMatEntry
      (coarseBlockMatrix (HighContrast.adaptedCell q j) (respCoeffMinus F a)) α β) P := by
  intro α β
  simpa only [adaptedCellAtCenter_zero q j] using
    aestronglyMeasurable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter P hq j 0 F α β

/-- **Measurability of the recentred coarse block at the centred cell, plus sign.**  The adjoint
twin of `aestronglyMeasurable_blockMatEntry_respCoeffMinus_adaptedCell`. -/
theorem aestronglyMeasurable_blockMatEntry_respCoeffPlus_adaptedCell {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : IsUnit q) (j : ℤ) (F : BlockMat d) :
    ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => blockMatEntry
      (coarseBlockMatrix (HighContrast.adaptedCell q j) (respCoeffPlus F a)) α β) P := by
  intro α β
  simpa only [adaptedCellAtCenter_zero q j] using
    aestronglyMeasurable_blockMatEntry_respCoeffPlus_adaptedCellAtCenter P hq j 0 F α β

end

end HCPolySupport.HighContrast.Multiscale
end
