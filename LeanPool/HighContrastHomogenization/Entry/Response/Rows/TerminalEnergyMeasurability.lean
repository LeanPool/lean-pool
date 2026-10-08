/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.CanonicalReadoutMeasurability
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.CutoffQuadraticReadout
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.DualityBoundHypotheses
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TerminalDeficitCarrierBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.BesovScaleSummationToolkit
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.IntegratedWeakEnergyBound
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.ConjExponents
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# High-contrast homogenization: Entry.Response.Rows.TerminalEnergyMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Terminal-Cell Energy Identity and Its Measurability

At a response maximizer, this file shows the variation energy of the optimizer is exactly twice
the pathwise response, so the volume average of the energy density over the terminal cell equals
twice the recentred response, for both signs. Exact partition averaging spreads this over the
aligned subcells of the coarse scale, and the energy density is a.e. nonnegative on every
subcell, giving the same identity and nonnegativity for an a.e. elliptic representative. Since
two response maximizers for the same loads and coefficient share the same doubled optimizer field
a.e., every weighted average of the terminal optimizer's energy density is measurable in the
sample. It also records the Cauchy-Schwarz bound for a cutoff-weighted pairing of two
square-integrable fields, the bound `|φ - 1| ≤ 1` for a cutoff of mean one, and that a
nonnegative summand of an integrable sum is itself integrable.  The terminal-cell energy identity
and the sample measurability of the weighted optimizer energy are the first error row of
`p.response.transfer` at the level of the response carriers.
-/

section
/-!
## The terminal cell energy of the optimizer on the response carriers

At a response maximizer the variation energy of the optimizer is exactly twice the response, so the
volume average of its energy density over the terminal cell is `2 J_t^∓`.  Exact partition averaging
then spreads that identity over the aligned subcells of the coarse scale, and the energy density is
nonnegative almost everywhere on every such subcell because the coefficient has an elliptic
representative on the terminal cell.  These are the pathwise facts from which the sample-side
integrability of the subcell energies is obtained by domination, and they are the first error row of
`p.response.transfer` at the level of the carriers.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Integrability of the variation energy of a harmonic field for a coefficient that agrees almost
everywhere with a pointwise elliptic representative. -/
private theorem integrableOn_energy_of_aeRep {d : ℕ} {U : Set (Vec d)}
    {a b : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U b)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (hae : a =ᵐ[volumeMeasureOn U] b)
    (u : AHarmonicFunction a U) :
    MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a u) U := by
  have hdata : ResponseLinearIntegrabilityData U b :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hE : MeasureTheory.IntegrableOn
      (scalarVariationEnergyIntegrand b (Response.aHarmonicOfAEEq hae u)) U :=
    hdata.energy (Response.aHarmonicOfAEEq hae u)
  refine hE.congr ?_
  filter_upwards [hae] with x hx
  simp only [scalarVariationEnergyIntegrand, Response.aHarmonicOfAEEq_grad]
  rw [hx]

/-- Nonnegativity of the variation energy average on a subset, for a coefficient that agrees almost
everywhere with a pointwise elliptic representative on the enclosing set. -/
private theorem volumeAverage_energy_nonneg_of_aeRep {d : ℕ} {U V : Set (Vec d)}
    {a b : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U b)
    (hVU : V ⊆ U) (hV : MeasurableSet V) (hae : a =ᵐ[volumeMeasureOn U] b)
    (u : AHarmonicFunction a U) :
    0 ≤ volumeAverage V (scalarVariationEnergyIntegrand a u) := by
  have hnn : 0 ≤ volumeAverage V
      (scalarVariationEnergyIntegrand b (Response.aHarmonicOfAEEq hae u)) := by
    refine volumeAverage_nonneg_of_nonneg_on hV ?_
    intro x hx
    exact scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn U b hEll
      (Response.aHarmonicOfAEEq hae u) x (hVU hx)
  rwa [volumeAverage_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff hVU hae u] at hnn

/-- The energy identity at a response maximizer, for a coefficient that agrees almost everywhere
with a pointwise elliptic representative: the terminal energy average is twice the response. -/
private theorem volumeAverage_energy_eq_two_respJ_of_aeRep {d : ℕ} {U : Set (Vec d)}
    {a b : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U b)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (hae : a =ᵐ[volumeMeasureOn U] b)
    (p r : Vec d) (u : AHarmonicFunction a U) (hmax : IsResponseMaximizer U p r a u) :
    volumeAverage U (scalarVariationEnergyIntegrand a u) = 2 * ResponseJ U p r a := by
  have hdata : ResponseLinearIntegrabilityData U b :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hmaxb : IsResponseMaximizer U p r b (Response.aHarmonicOfAEEq hae u) :=
    isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff hae p r hmax
  have henergy : MeasureTheory.IntegrableOn
      (scalarVariationEnergyIntegrand b (Response.aHarmonicOfAEEq hae u)) U :=
    hdata.energy (Response.aHarmonicOfAEEq hae u)
  have hresp : MeasureTheory.IntegrableOn
      (scalarResponseIntegrand U b p r (Response.aHarmonicOfAEEq hae u)) U :=
    hdata.response p r (Response.aHarmonicOfAEEq hae u)
  have hlin : MeasureTheory.IntegrableOn
      (scalarFirstVariationIntegrand U b p r (Response.aHarmonicOfAEEq hae u)
        (Response.aHarmonicOfAEEq hae u)) U :=
    hdata.firstVariation p r (Response.aHarmonicOfAEEq hae u)
      (Response.aHarmonicOfAEEq hae u)
  have hident : ResponseJ U p r b
      = (1 / 2 : ℝ) * volumeAverage U
          (scalarVariationEnergyIntegrand b (Response.aHarmonicOfAEEq hae u)) :=
    responseJ_energy_of_isResponseMaximizer U b p r (Response.aHarmonicOfAEEq hae u) hmaxb
      (hdata.weakFlux (Response.aHarmonicOfAEEq hae u)) hresp hlin henergy
  have hJ : ResponseJ U p r a = ResponseJ U p r b := responseJ_congr_of_ae_eq hae p r
  have hE : volumeAverage U
        (scalarVariationEnergyIntegrand b (Response.aHarmonicOfAEEq hae u))
      = volumeAverage U (scalarVariationEnergyIntegrand a u) :=
    volumeAverage_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff (fun _ hx => hx)
      hae u
  rw [hJ, hident, hE]
  ring

/-- **Integrability of the terminal optimizer energy, minus sign.**  On the terminal cell the
variation energy density of a terminal maximizer for `a_- = a - g` is integrable; the coefficient is
elliptic only almost everywhere, so the fact is transported from an elliptic representative. -/
theorem integrableOn_energy_respCell_respCoeffMinus {d : ℕ}
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (a : CoeffSpace d) :
    MeasureTheory.IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) (respCell jStar F t) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
  exact integrableOn_energy_of_aeRep hEll hae (uM a)

/-- **The terminal energy identity, minus sign.**  At a terminal maximizer for `a_- = a - g` the
volume average of the optimizer energy density over the terminal cell is twice the terminal
response, the exact energy identity behind the first error row of `p.response.transfer`. -/
theorem volumeAverage_energy_respCell_respCoeffMinus_eq {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a)) (a : CoeffSpace d) :
    volumeAverage (respCell jStar F t)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
      = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
  have hcore := volumeAverage_energy_eq_two_respJ_of_aeRep (U := respCell jStar F t) hEll hae
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a) (hmax a)
  simpa only [respJ, respCell] using hcore

/-- **Nonnegativity of the subcell energy, minus sign.**  On every aligned subcell of the coarse
scale the average of the terminal optimizer energy density is nonnegative, because the terminal
coefficient is elliptic almost everywhere there. -/
theorem zero_le_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus {d : ℕ}
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (a : CoeffSpace d) (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d H) :
    0 ≤ volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hts : t - (H : ℤ) = s := by omega
  have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F t := by
    have h := adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
    rwa [hts] at h
  have hV : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) s w) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq s w).measurableSet
  exact volumeAverage_energy_nonneg_of_aeRep (U := respCell jStar F t) hEll hVU hV hae (uM a)

/-- **Exact partition averaging of the terminal energy, minus sign.**  The normalized sum over the
aligned subcells of the coarse scale of the optimizer energy averages equals the terminal energy
average, since those subcells partition the terminal cell up to a null set. -/
theorem avsum_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus_eq {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (a : CoeffSpace d) :
    (((triadicIndexBox d H).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
      = volumeAverage (respCell jStar F t)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hf : IntegrableOn (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
      (HighContrast.adaptedCell (respGrid jStar F) t) := by
    simpa only [respCell] using
      integrableOn_energy_respCell_respCoeffMinus jStar hjStar F hm t uM a
  have h := avsum_volumeAverage_eq (respGrid jStar F) hq t H hf
  rw [show t - (H : ℤ) = s by omega] at h
  simpa only [respCell] using h

/-- **Integrability of the terminal optimizer energy, plus sign.**  The twin of the minus statement
for `a_+ = aᵗ + g`. -/
theorem integrableOn_energy_respCell_respCoeffPlus {d : ℕ}
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (a : CoeffSpace d) :
    MeasureTheory.IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) (respCell jStar F t) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
  exact integrableOn_energy_of_aeRep hEll hae (uP a)

/-- **The terminal energy identity, plus sign.**  The twin of the minus identity for
`a_+ = aᵗ + g`. -/
theorem volumeAverage_energy_respCell_respCoeffPlus_eq {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a)) (a : CoeffSpace d) :
    volumeAverage (respCell jStar F t)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
      = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
  have hcore := volumeAverage_energy_eq_two_respJ_of_aeRep (U := respCell jStar F t) hEll hae
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a) (hmax a)
  simpa only [respJ, respCell] using hcore

/-- **Nonnegativity of the subcell energy, plus sign.**  The twin of the minus statement for
`a_+ = aᵗ + g`. -/
theorem zero_le_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus {d : ℕ}
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (a : CoeffSpace d) (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d H) :
    0 ≤ volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hts : t - (H : ℤ) = s := by omega
  have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F t := by
    have h := adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
    rwa [hts] at h
  have hV : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) s w) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq s w).measurableSet
  exact volumeAverage_energy_nonneg_of_aeRep (U := respCell jStar F t) hEll hVU hV hae (uP a)

/-- **Exact partition averaging of the terminal energy, plus sign.**  The twin of the minus
statement for `a_+ = aᵗ + g`. -/
theorem avsum_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus_eq {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (a : CoeffSpace d) :
    (((triadicIndexBox d H).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
      = volumeAverage (respCell jStar F t)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hf : IntegrableOn (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
      (HighContrast.adaptedCell (respGrid jStar F) t) := by
    simpa only [respCell] using
      integrableOn_energy_respCell_respCoeffPlus jStar hjStar F hm t uP a
  have h := avsum_volumeAverage_eq (respGrid jStar F) hq t H hf
  rw [show t - (H : ℤ) = s by omega] at h
  simpa only [respCell] using h

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cutoff-weighted pairing bound on a cell

This file records the crude Cauchy--Schwarz bound for a cutoff-weighted pairing of two
square-integrable vector fields on a cell, used in the cutoff argument of
`e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)).  If `φ` is a cutoff with `0 ≤ φ ≤ 2`,
`A` and `B` are vector fields and `vol` denotes the normalized cell average, then

`|vol (φ · (A · B))| ≤ 2 · √(vol |A|²) · √(vol |B|²)`.

The three ingredients are the pointwise Cauchy--Schwarz inequality for the Euclidean dot
product, the monotonicity of the normalized cell average under pointwise domination, and an
averaged Cauchy--Schwarz (Hölder with conjugate exponents `2` and `2`) for nonnegative
functions.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Monotonicity of the normalized cell average: if `|f| ≤ g` pointwise on the measurable set
`U` and both are integrable on `U`, then `|vol f| ≤ vol g`.  The prefactor `(vol U)⁻¹` is
nonnegative and the set integral is monotone.  This is the averaging step of the
cutoff-weighted pairing bound `e.response.cutoff.estimate`. -/
theorem volumeAverage_abs_le_of_le {d : ℕ} {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hU : MeasurableSet U) (hle : ∀ x ∈ U, |f x| ≤ g x)
    (hf : MeasureTheory.IntegrableOn f U) (hg : MeasureTheory.IntegrableOn g U) :
    |volumeAverage U f| ≤ volumeAverage U g := by
  unfold volumeAverage
  have hc : 0 ≤ (volume U).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  rw [abs_mul, abs_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  calc |∫ x in U, f x| ≤ ∫ x in U, |f x| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ x in U, g x := MeasureTheory.setIntegral_mono_on hf.abs hg hU hle

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The weighted optimizer energy is measurable in the sample

Two response maximizers for the same loads and the same coefficient have the same doubled optimizer
field almost everywhere on the response cell, by Chapter-2 almost-everywhere gradient uniqueness
(AK.HC (2.9)).  Hence every weighted average of the energy density of the terminal optimizer of
`p.response.transfer` is computed by the canonical Chapter-2 selection, which depends measurably on
the sample.  In particular the `(φ - 1)`-weighted terminal energy and the energy on each aligned
subcell are measurable functions of the sample, for an arbitrary family of maximizers.

The pointwise pairing of the doubled optimizer field with itself is the variation energy
`∇v · (symmPart b) ∇v`: the antisymmetric part of the coefficient contributes nothing to the
quadratic form, so the pairing may be read with either the full coefficient or its symmetric part.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The canonical doubled optimizer state depends on the coefficient only through its
almost-everywhere class on the domain. -/
private theorem energyCanonicalState_congr_ae {d : ℕ} {U : Book.Ch02.Domain d}
    {A B : Book.Ch02.CoeffOn U} (hAB : Book.Ch02.CoeffOn.AEEq A B) (p r : Vec d) :
    canonicalOptimizerBlockState U A p r
      =ᵐ[volumeMeasureOn (U : Set (Vec d))] canonicalOptimizerBlockState U B p r := by
  have hgrad : (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory U A) p r).toSolution.toH1.grad
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory U B) p r).toSolution.toH1.grad := by
    simpa only [Book.Ch02.Solution.SameGradientAE, Book.Ch02.Solution.toH1_ofAEEq] using
      (Book.Ch02.canonicalMaximizer_sameGradientAE_ofAEEq hAB p r)
  filter_upwards [hgrad, hAB] with x hgradx hcoeffx
  simp only [canonicalOptimizerBlockState]
  rw [hgradx, hcoeffx]

/-- An arbitrary response maximizer for the recentred coefficient `a_-` on an invertible adapted
cell has the same doubled optimizer field almost everywhere as the canonical Chapter-2 selection. -/
private theorem optimizerField_aeeq_canonicalRespCoeffMinus {d : ℕ}
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffMinus F a) u) :
    optimizerField (respCoeffMinus F a) u
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F a) p r := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) := by
    simpa [volumeMeasureOn] using
      (adaptedCell_isOpenBoundedConvexDomain q hq t).isFiniteMeasure_restrict_volume
  let A : Book.Ch02.CoeffOn (adaptedDomain q hq t) :=
    coeffOnOfIsEllipticFieldOn (U := adaptedDomain q hq t) hlam hle hEll
  let v : ScalarCanonicalMaximizer (HighContrast.adaptedCell q t) p r (respCoeffMinus F a) :=
    ScalarCanonicalMaximizer.ofIsResponseMaximizer u hu
  have hgrad : optimizerField (respCoeffMinus F a) u
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      optimizerField (respCoeffMinus F a)
        v.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
    apply Filter.Eventually.of_forall
    intro x
    have hg : v.toAHarmonicFunctionMeanZero.toAHarmonicFunction.toH1.grad x
        = u.toH1.grad x := AHarmonicFunction.grad_normalizeMeanZero u x
    simp only [optimizerField, hg]
  have hcanon : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      optimizerField (respCoeffMinus F a)
        v.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
    have hstate : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
        = optimizerField f (canonicalAHarmonicFunctionOfCoeffOn A p r) := by
      funext x
      rfl
    have hstateEq : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
        =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
        optimizerField f (canonicalAHarmonicFunctionOfCoeffOn A p r) :=
      Filter.Eventually.of_forall (fun x => congrFun hstate x)
    exact hstateEq.trans (optimizerField_scalarCanonicalMaximizer_ae_eq_canonicalOfAEEq
      (U := adaptedDomain q hq t) hlam hle hEll hbf p r v)
  have hAB : Book.Ch02.CoeffOn.AEEq A (canonicalRespCoeffMinusOn q hq t F a) := by
    filter_upwards [hbf.symm] with x hx
    simpa only [canonicalRespCoeffMinusOn_toFun] using! hx
  have hstate : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F a) p r :=
    energyCanonicalState_congr_ae hAB p r
  exact hgrad.trans (hcanon.symm.trans hstate)

/-- An arbitrary response maximizer for the recentred coefficient `a_+` on an invertible adapted
cell has the same doubled optimizer field almost everywhere as the canonical Chapter-2 selection. -/
private theorem optimizerField_aeeq_canonicalRespCoeffPlus {d : ℕ}
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffPlus F a) u) :
    optimizerField (respCoeffPlus F a) u
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F a) p r := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) := by
    simpa [volumeMeasureOn] using
      (adaptedCell_isOpenBoundedConvexDomain q hq t).isFiniteMeasure_restrict_volume
  let A : Book.Ch02.CoeffOn (adaptedDomain q hq t) :=
    coeffOnOfIsEllipticFieldOn (U := adaptedDomain q hq t) hlam hle hEll
  let v : ScalarCanonicalMaximizer (HighContrast.adaptedCell q t) p r (respCoeffPlus F a) :=
    ScalarCanonicalMaximizer.ofIsResponseMaximizer u hu
  have hgrad : optimizerField (respCoeffPlus F a) u
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      optimizerField (respCoeffPlus F a)
        v.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
    apply Filter.Eventually.of_forall
    intro x
    have hg : v.toAHarmonicFunctionMeanZero.toAHarmonicFunction.toH1.grad x
        = u.toH1.grad x := AHarmonicFunction.grad_normalizeMeanZero u x
    simp only [optimizerField, hg]
  have hcanon : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      optimizerField (respCoeffPlus F a)
        v.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
    have hstate : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
        = optimizerField f (canonicalAHarmonicFunctionOfCoeffOn A p r) := by
      funext x
      rfl
    have hstateEq : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
        =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
        optimizerField f (canonicalAHarmonicFunctionOfCoeffOn A p r) :=
      Filter.Eventually.of_forall (fun x => congrFun hstate x)
    exact hstateEq.trans (optimizerField_scalarCanonicalMaximizer_ae_eq_canonicalOfAEEq
      (U := adaptedDomain q hq t) hlam hle hEll hbf p r v)
  have hAB : Book.Ch02.CoeffOn.AEEq A (canonicalRespCoeffPlusOn q hq t F a) := by
    filter_upwards [hbf.symm] with x hx
    simpa only [canonicalRespCoeffPlusOn_toFun] using! hx
  have hstate : canonicalOptimizerBlockState (adaptedDomain q hq t) A p r
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F a) p r :=
    energyCanonicalState_congr_ae hAB p r
  exact hgrad.trans (hcanon.symm.trans hstate)

/-- The `η`-weighted terminal optimizer energy of the response functional for the recentred
coefficient `a_-`, for an arbitrary family of response maximizers, is measurable in the coefficient
sample.  The energy is the pairing `⟨X.1, X.2⟩ = ∇v · a_- ∇v` of the doubled optimizer field of the
maximizer; that field is determined almost everywhere by the measurable canonical Chapter-2
selection, so the weighted energy is a measurable function of the sample. -/
theorem measurable_volumeAverage_weighted_energy_respCoeffMinus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    {eta : Vec d → ℝ}
    (hetam : MeasureTheory.AEStronglyMeasurable eta (volumeMeasureOn (respCell jStar F t)))
    (hetab : ∀ᵐ x ∂volumeMeasureOn (respCell jStar F t), ‖eta x‖ ≤ 2) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (respCell jStar F t)
        (fun x => eta x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x) := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hEq : (fun a : CoeffSpace d => volumeAverage (respCell jStar F t)
        (fun x => eta x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x))
      = fun a : CoeffSpace d => volumeAverage (respCell jStar F t)
        (fun x => eta x * vecDot
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x).1
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x).2) := by
    funext a
    have hfield := optimizerField_aeeq_canonicalRespCoeffMinus
      (respGrid jStar F) hq t F a (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (uM a) (hmax a)
    have hInt : (fun x => eta x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x)
        =ᵐ[volumeMeasureOn (respCell jStar F t)]
        (fun x => eta x * vecDot
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x).1
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x).2) := by
      filter_upwards [hfield] with x hfieldx
      show eta x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x
          = eta x * vecDot
              (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
                (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x).1
              (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
                (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) x).2
      have hpt : scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x
          = vecDot
              (optimizerField (U := HighContrast.adaptedCell (respGrid jStar F) t)
                (respCoeffMinus F a) (uM a) x).1
              (optimizerField (U := HighContrast.adaptedCell (respGrid jStar F) t)
                (respCoeffMinus F a) (uM a) x).2 := by
        simp only [scalarVariationEnergyIntegrand, optimizerField]
        exact vecDot_matVecMul_symmPart (respCoeffMinus F a x) ((uM a).toH1.grad x)
      rw [hpt, hfieldx]
    exact volumeAverage_congr_ae subset_rfl hInt
  rw [hEq]
  exact measurable_volumeAverage_weighted_quadratic_canonicalRespCoeffMinus
    (respGrid jStar F) hq t F (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
    hetam hetab

/-- The `η`-weighted terminal optimizer energy of the response functional for the adjoint
coefficient `a_+`, for an arbitrary family of response maximizers, is measurable in the coefficient
sample.  This is the adjoint twin of `measurable_volumeAverage_weighted_energy_respCoeffMinus`. -/
theorem measurable_volumeAverage_weighted_energy_respCoeffPlus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    {eta : Vec d → ℝ}
    (hetam : MeasureTheory.AEStronglyMeasurable eta (volumeMeasureOn (respCell jStar F t)))
    (hetab : ∀ᵐ x ∂volumeMeasureOn (respCell jStar F t), ‖eta x‖ ≤ 2) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (respCell jStar F t)
        (fun x => eta x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x) := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hEq : (fun a : CoeffSpace d => volumeAverage (respCell jStar F t)
        (fun x => eta x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x))
      = fun a : CoeffSpace d => volumeAverage (respCell jStar F t)
        (fun x => eta x * vecDot
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x).1
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x).2) := by
    funext a
    have hfield := optimizerField_aeeq_canonicalRespCoeffPlus
      (respGrid jStar F) hq t F a (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (uP a) (hmax a)
    have hInt : (fun x => eta x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x)
        =ᵐ[volumeMeasureOn (respCell jStar F t)]
        (fun x => eta x * vecDot
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x).1
          (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
            (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
            (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x).2) := by
      filter_upwards [hfield] with x hfieldx
      show eta x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x
          = eta x * vecDot
              (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
                (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x).1
              (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
                (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) x).2
      have hpt : scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x
          = vecDot
              (optimizerField (U := HighContrast.adaptedCell (respGrid jStar F) t)
                (respCoeffPlus F a) (uP a) x).1
              (optimizerField (U := HighContrast.adaptedCell (respGrid jStar F) t)
                (respCoeffPlus F a) (uP a) x).2 := by
        simp only [scalarVariationEnergyIntegrand, optimizerField]
        exact vecDot_matVecMul_symmPart (respCoeffPlus F a x) ((uP a).toH1.grad x)
      rw [hpt, hfieldx]
    exact volumeAverage_congr_ae subset_rfl hInt
  rw [hEq]
  exact measurable_volumeAverage_weighted_quadratic_canonicalRespCoeffPlus
    (respGrid jStar F) hq t F (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
    hetam hetab

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The fluctuation of a response cutoff

A response cutoff `φ` of `e.response.cutoff.estimate` lies in `[0, 2]` and has volume average
one on its terminal cell, so its fluctuation `φ - 1` is bounded by one pointwise and has mean
zero on that cell.  Mean zero is what allows any constant to be subtracted from the factor paired
with the fluctuation without changing the weighted average: the centring step of the cutoff-mean
rows of the response-transfer estimate.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A response cutoff `φ` takes values in `[0, 2]`, so its fluctuation `φ - 1` is bounded by one
in absolute value at every point: `|φ x - 1| ≤ 1`. -/
theorem abs_isResponseCutoff_sub_one {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff qq t φ) (x : Vec d) : |φ x - 1| ≤ 1 := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith only [hφ.1 x]
  · linarith only [hφ.2.1 x]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Integrability of one nonnegative term of an integrable sum

The first error row of `p.response.transfer` needs the `P`-integrability of each subcell deficit
and of each subcell energy separately, while the exact partition identity supplies only the
integrability of their flat average.  Both families are nonnegative, so each member is dominated
by the whole sum; with almost-everywhere strong measurability of the member, integrability
follows.  This file records that elementary principle in the two forms the row consumes: a sum
bounded above by an integrable function, and a sum equal to one.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

/-- **A single nonnegative term of a sum bounded by an integrable function is integrable.**  Let
`f i` be nonnegative for every `i ∈ Z`, let each `f i` be `P`-a.e.-strongly measurable, let `g`
be `P`-integrable, and suppose `∑ i ∈ Z, f i a ≤ g a` for every `a`.  Then each `f i` with
`i ∈ Z` is `P`-integrable.  At every point the fixed term is bounded by the full sum through the
nonnegativity of the other terms and the sum is bounded by `g`; the norm in the domination
criterion is the term itself because the term is nonnegative. -/
theorem integrable_of_nonneg_of_sum_le {α ι : Type*} [MeasurableSpace α] {P : Measure α}
    {Z : Finset ι} {f : ι → α → ℝ} {g : α → ℝ}
    (hf0 : ∀ i ∈ Z, ∀ a, 0 ≤ f i a)
    (hmeas : ∀ i ∈ Z, MeasureTheory.AEStronglyMeasurable (f i) P)
    (hg : MeasureTheory.Integrable g P)
    (hsum : ∀ a, ∑ i ∈ Z, f i a ≤ g a) :
    ∀ i ∈ Z, MeasureTheory.Integrable (f i) P := by
  intro i hi
  refine hg.mono' (hmeas i hi) ?_
  filter_upwards with a
  rw [Real.norm_eq_abs, abs_of_nonneg (hf0 i hi a)]
  exact (Finset.single_le_sum (fun j hj => hf0 j hj a) hi).trans (hsum a)

/-- **A single nonnegative term of a sum equal to an integrable function is integrable.**  This
is the previous statement with the upper bound `∑ i ∈ Z, f i a ≤ g a` strengthened to the
identity `∑ i ∈ Z, f i a = g a` supplied by the exact partition identity of
`p.response.transfer`; the identity gives the bound by `le_of_eq`. -/
theorem integrable_of_nonneg_of_sum_eq {α ι : Type*} [MeasurableSpace α] {P : Measure α}
    {Z : Finset ι} {f : ι → α → ℝ} {g : α → ℝ}
    (hf0 : ∀ i ∈ Z, ∀ a, 0 ≤ f i a)
    (hmeas : ∀ i ∈ Z, MeasureTheory.AEStronglyMeasurable (f i) P)
    (hg : MeasureTheory.Integrable g P)
    (hsum : ∀ a, ∑ i ∈ Z, f i a = g a) :
    ∀ i ∈ Z, MeasureTheory.Integrable (f i) P :=
  integrable_of_nonneg_of_sum_le hf0 hmeas hg fun a => le_of_eq (hsum a)

end HCPolySupport.HighContrast.Multiscale
end
