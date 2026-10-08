/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.CanonicalReadoutMeasurability
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantFenchelProbe
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TerminalEnergyDeficitBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TriadicRefinementIncrement
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.WeakEstimateAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.AbstractCellPairingBound
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# High-contrast homogenization: Entry.Response.Direct.FirstErrorRowArithmetic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The scalar arithmetic and abstract bookkeeping behind the first error row

Bounding the pointwise defect `|E - J| ≤ D + 2√(J D)` between the terminal response and half the
restricted terminal-optimizer energy needs the square root replaced by the family
`2√(JD) ≤ εJ + D/ε`, integrated for each `ε > 0` and optimized afterward; this file proves the
scalar inequalities making that work, then bounds, in abstract bookkeeping terms, the aligned-cell
average of the weighted energy defect once each subcell carries a response, a half-energy, and a
deficit obeying the pointwise bound. Separately, the cutoff's within-cell oscillation against the
terminal-optimizer energy on each aligned subcell is bounded by the cutoff class's Lipschitz gain
`3^{-H}` times that energy, twice the pathwise response at a maximizer. Finally, the modulus of the
cutoff pairing of the cutoff estimate is shown almost-everywhere strongly measurable in the
coefficient sample for an arbitrary maximizer family, as the signed cutoff-pairing row needs for
integrability.  Altogether this is the scalar and abstract bookkeeping core of the first error row
of `p.response.transfer`.
-/

section
/-!
## The cutoff pairing is measurable in the sample without its absolute value

`CutoffQuadraticReadout` records that the MODULUS of the cutoff pairing of
`e.response.cutoff.estimate` is almost-everywhere strongly measurable in the coefficient sample for
an arbitrary family of response maximizers.  The row assembly
`abs_respCenteredJ{Minus,Plus}_le_cutoffRows_of_obligations` needs the `P`-integrability of the
SIGNED pairing, which the modulus alone does not give: an integrable modulus supplies the finite
integral but not the measurability of the signed function.

The signed measurability follows by the same route, and with no further input.  The doubled
optimizer state of an arbitrary response maximizer agrees almost everywhere on the terminal cell
with the measurable canonical Chapter-2 selection, so the signed pairing agrees with the canonical
signed pairing; and the canonical signed pairing is measurable by
`aestronglyMeasurable_pairing_canonical_of_quadratic`, whose quadratic input is discharged with no
hypothesis beyond the cutoff class by
`measurable_volumeAverage_cutoff_quadratic_canonicalRespCoeff{Minus,Plus}_full`.  Together with the
integrability of the modulus, which `p.response.transfer` already carries, this closes
the `hA` side condition of the row assembly.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The canonical signed cutoff pairing is measurable, minus recentring.**  With no hypothesis
beyond the cutoff class: the three linear readouts of the canonical optimizer state are measurable,
and so is the quadratic one. -/
theorem aestronglyMeasurable_canonical_cutoff_pairing_respCoeffMinus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (p q' : Vec d) (Y : BlockVec d) :
    AEStronglyMeasurable (fun a : CoeffSpace d => volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot
          ((canonicalOptimizerBlockState
              (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
              (canonicalRespCoeffMinusOn (respGrid jStar F)
                (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState
              (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
              (canonicalRespCoeffMinusOn (respGrid jStar F)
                (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).2 - Y.2))) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  refine aestronglyMeasurable_pairing_canonical_of_quadratic P (respGrid jStar F) hq t
    p q' Y hφ ?_ ?_ ?_ ?_
  · intro W
    simpa only [respCell] using
      measurable_volumeAverage_cutoff_vecDot_canonicalRespCoeffMinus_potential
        (respGrid jStar F) hq t F p q' hφ W
  · intro W
    simpa only [respCell] using
      measurable_volumeAverage_cutoff_vecDot_canonicalRespCoeffMinus_flux
        (respGrid jStar F) hq t F p q' hφ W
  · intro a
    simpa only [respCell] using
      memVectorL2_canonicalRespCoeffMinus_flux (respGrid jStar F) hq t F p q' a
  · exact (measurable_volumeAverage_cutoff_quadratic_canonicalRespCoeffMinus_full
      (respGrid jStar F) hq t F p q' hφ).aestronglyMeasurable

/-- **The canonical signed cutoff pairing is measurable, plus recentring.**  The adjoint twin of
`aestronglyMeasurable_canonical_cutoff_pairing_respCoeffMinus`. -/
theorem aestronglyMeasurable_canonical_cutoff_pairing_respCoeffPlus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (p q' : Vec d) (Y : BlockVec d) :
    AEStronglyMeasurable (fun a : CoeffSpace d => volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot
          ((canonicalOptimizerBlockState
              (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
              (canonicalRespCoeffPlusOn (respGrid jStar F)
                (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState
              (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
              (canonicalRespCoeffPlusOn (respGrid jStar F)
                (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).2 - Y.2))) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  refine aestronglyMeasurable_pairing_canonical_of_quadratic P (respGrid jStar F) hq t
    p q' Y hφ ?_ ?_ ?_ ?_
  · intro W
    simpa only [respCell] using
      measurable_volumeAverage_cutoff_vecDot_canonicalRespCoeffPlus_potential
        (respGrid jStar F) hq t F p q' hφ W
  · intro W
    simpa only [respCell] using
      measurable_volumeAverage_cutoff_vecDot_canonicalRespCoeffPlus_flux
        (respGrid jStar F) hq t F p q' hφ W
  · intro a
    simpa only [respCell] using
      memVectorL2_canonicalRespCoeffPlus_flux (respGrid jStar F) hq t F p q' a
  · exact (measurable_volumeAverage_cutoff_quadratic_canonicalRespCoeffPlus_full
      (respGrid jStar F) hq t F p q' hφ).aestronglyMeasurable

/-- **The signed cutoff pairing of an arbitrary maximizer family is measurable, minus
recentring.**  The doubled optimizer state of the maximizer agrees almost everywhere on the
terminal cell with the canonical Chapter-2 selection, so the two pairings agree sample by sample. -/
theorem aestronglyMeasurable_cutoffPairingOnCell_respCoeffMinus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (p q' : Vec d) (Y : BlockVec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (respCoeffMinus F a) (uM a)) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      cutoffPairingOnCellAux (respCell jStar F t) φ Y (respCoeffMinus F a) (uM a)) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hEq : (fun a : CoeffSpace d =>
        cutoffPairingOnCellAux (respCell jStar F t) φ Y (respCoeffMinus F a) (uM a))
      = fun a : CoeffSpace d => volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q' x).2 - Y.2)) := by
    funext a
    have hfield := optimizerField_ae_eq_canonicalState_respCoeffMinus
      (respGrid jStar F) hq t F a p q' (uM a) (hmax a)
    have hInt : (fun x => φ x * vecDot ((optimizerField (respCoeffMinus F a) (uM a) x).1 - Y.1)
          ((optimizerField (respCoeffMinus F a) (uM a) x).2 - Y.2))
        =ᵐ[volumeMeasureOn (respCell jStar F t)]
        (fun x => φ x * vecDot
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q' x).2 - Y.2)) := by
      filter_upwards [hfield] with x hx
      rw [show optimizerField (respCoeffMinus F a) (uM a) x = _ from hx]
    exact volumeAverage_congr_ae (subset_refl (respCell jStar F t)) hInt
  rw [hEq]
  exact aestronglyMeasurable_canonical_cutoff_pairing_respCoeffMinus P jStar F t hjStar hm φ hφ
    p q' Y

/-- **The signed cutoff pairing of an arbitrary maximizer family is measurable, plus
recentring.**  The adjoint twin of
`aestronglyMeasurable_cutoffPairingOnCell_respCoeffMinus`. -/
theorem aestronglyMeasurable_cutoffPairingOnCell_respCoeffPlus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (p q' : Vec d) (Y : BlockVec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (respCoeffPlus F a) (uP a)) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      cutoffPairingOnCellAux (respCell jStar F t) φ Y (respCoeffPlus F a) (uP a)) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hEq : (fun a : CoeffSpace d =>
        cutoffPairingOnCellAux (respCell jStar F t) φ Y (respCoeffPlus F a) (uP a))
      = fun a : CoeffSpace d => volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q' x).2 - Y.2)) := by
    funext a
    have hfield := optimizerField_ae_eq_canonicalState_respCoeffPlus
      (respGrid jStar F) hq t F a p q' (uP a) (hmax a)
    have hInt : (fun x => φ x * vecDot ((optimizerField (respCoeffPlus F a) (uP a) x).1 - Y.1)
          ((optimizerField (respCoeffPlus F a) (uP a) x).2 - Y.2))
        =ᵐ[volumeMeasureOn (respCell jStar F t)]
        (fun x => φ x * vecDot
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q' x).2 - Y.2)) := by
      filter_upwards [hfield] with x hx
      rw [show optimizerField (respCoeffPlus F a) (uP a) x = _ from hx]
    exact volumeAverage_congr_ae (subset_refl (respCell jStar F t)) hInt
  rw [hEq]
  exact aestronglyMeasurable_canonical_cutoff_pairing_respCoeffPlus P jStar F t hjStar hm φ hφ
    p q' Y

/-- **The `hA` side condition of the row assembly, minus recentring.**  The half-weighted signed
cutoff pairing is `P`-integrable: its modulus is integrable by the premise that
`p.response.transfer` already carries, and the signed function is measurable.  The modulus is
stated through `cutoffPairingOnCellAux`, which is the same function as the kernel's
`hc3CutoffPairingOnCell` -- the two definitions have identical bodies, so the premise
discharges `habs` directly. -/
theorem integrable_half_cutoffPairingOnCell_respCoeffMinus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (p q' : Vec d) (Y : BlockVec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (respCoeffMinus F a) (uM a))
    (habs : Integrable (fun a : CoeffSpace d =>
      |cutoffPairingOnCellAux (respCell jStar F t) φ Y (respCoeffMinus F a) (uM a)|) P) :
    Integrable (fun a : CoeffSpace d => (1 / 2 : ℝ) *
      cutoffPairingOnCellAux (respCell jStar F t) φ Y (respCoeffMinus F a) (uM a)) P := by
  have hmeas := aestronglyMeasurable_cutoffPairingOnCell_respCoeffMinus
    P jStar F t hjStar hm φ hφ p q' Y uM hmax
  refine Integrable.const_mul ?_ (1 / 2 : ℝ)
  refine habs.mono' hmeas (Filter.Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs]

/-- **The `hA` side condition of the row assembly, plus recentring.**  The adjoint twin of
`integrable_half_cutoffPairingOnCell_respCoeffMinus`. -/
theorem integrable_half_cutoffPairingOnCell_respCoeffPlus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (p q' : Vec d) (Y : BlockVec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (respCoeffPlus F a) (uP a))
    (habs : Integrable (fun a : CoeffSpace d =>
      |cutoffPairingOnCellAux (respCell jStar F t) φ Y (respCoeffPlus F a) (uP a)|) P) :
    Integrable (fun a : CoeffSpace d => (1 / 2 : ℝ) *
      cutoffPairingOnCellAux (respCell jStar F t) φ Y (respCoeffPlus F a) (uP a)) P := by
  have hmeas := aestronglyMeasurable_cutoffPairingOnCell_respCoeffPlus
    P jStar F t hjStar hm φ hφ p q' Y uP hmax
  refine Integrable.const_mul ?_ (1 / 2 : ℝ)
  refine habs.mono' hmeas (Filter.Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cutoff oscillation against the terminal-optimizer energy

In the terminal-optimizer replacement of `p.response.transfer`, the cutoff fluctuation `φ - 1` is
split on each aligned subcell of the coarse scale into its subcell mean and its oscillation there.
The oscillation part costs the Lipschitz gain `3^{-H}` of the cutoff class times the energy of the
terminal optimizer, which at a maximizer is twice the pathwise response.  This module records that
step for the optimizer's energy density, replacing the general nonnegative density of the
oscillation split by the concrete one the estimate uses.

Paper: `p.response.transfer`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The cutoff oscillation of the terminal-optimizer energy.**  On the adapted cell `⋄_t^q`, for
a cutoff `φ` of the response class and a response maximizer `u` of the loads `(p, r)`, the
`(φ − 1)`-weighted optimizer energy differs from the normalized sum of the products of the subcell
means of `φ − 1` and of the energy by at most the oscillation cost
`32 d² responseCutoffProfileConst 3^{-n}` times twice the pathwise response `J(⋄_t^q; p, r; b)`.
The variation energy of the terminal optimizer is nonnegative only on the cell, so the oscillation
split is applied to its positive part, which agrees with it there, and at a maximizer the
cell-average energy is exactly `2 J`.  This is the scale-gain step of the cutoff estimate of
`p.response.transfer`. -/
theorem abs_volumeAverage_sub_one_energy_sub_avsum_le {d : ℕ} [NeZero d] {q : Mat d}
    (hq : IsUnit q) (t : ℤ) (n : ℕ) {φ : Vec d → ℝ} (hφ : IsResponseCutoff q t φ)
    {lam Lam : ℝ} {b : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) b)
    (p r : Vec d) (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (hmax : IsResponseMaximizer (HighContrast.adaptedCell q t) p r b u)
    (hu_int : weakFluxIntegrable (HighContrast.adaptedCell q t) b u)
    (hresp_u : MeasureTheory.IntegrableOn
      (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u) (HighContrast.adaptedCell
        q t))
    (hlin_self : MeasureTheory.IntegrableOn
      (scalarFirstVariationIntegrand (HighContrast.adaptedCell q t) b p r u u)
      (HighContrast.adaptedCell q t))
    (henergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand b u)
      (HighContrast.adaptedCell q t))
    (hφE : MeasureTheory.IntegrableOn
      (fun x => (φ x - 1) * scalarVariationEnergyIntegrand b u x) (HighContrast.adaptedCell q t))
    (hEat : ∀ w ∈ triadicIndexBox d n, MeasureTheory.IntegrableOn
      (scalarVariationEnergyIntegrand b u) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (hφat : ∀ w ∈ triadicIndexBox d n, MeasureTheory.IntegrableOn φ
      (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (hφEat : ∀ w ∈ triadicIndexBox d n, MeasureTheory.IntegrableOn
      (fun x => (φ x - 1) * scalarVariationEnergyIntegrand b u x)
      (adaptedCellAtCenter q (t - (n : ℤ)) w)) :
    |volumeAverage (HighContrast.adaptedCell q t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand b u x)
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (fun x => φ x - 1) *
              volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (scalarVariationEnergyIntegrand b u)|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) *
          (2 * respJ q t p r b) := by
  set Dpos : Vec d → ℝ := fun x => max (scalarVariationEnergyIntegrand b u x) 0 with hDposdef
  have hUmeas : MeasurableSet (HighContrast.adaptedCell q t) :=
    (adaptedCell_isOpenBoundedConvexDomain q hq t).isOpen.measurableSet
  have hVmeas : ∀ w : Fin d → ℤ,
      MeasurableSet (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    fun w => (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet
  have hsub : ∀ w ∈ triadicIndexBox d n,
      adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    fun w hw => adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hDpos_nonneg : ∀ x, 0 ≤ Dpos x := by
    intro x
    rw [hDposdef]
    exact le_max_right _ _
  have hDpos_eq_on : ∀ x ∈ HighContrast.adaptedCell q t,
      Dpos x = scalarVariationEnergyIntegrand b u x := by
    intro x hx
    rw [hDposdef]
    exact max_eq_left
      (scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
        (HighContrast.adaptedCell q t) b hEll u x hx)
  have hDpos_U : IntegrableOn Dpos (HighContrast.adaptedCell q t) :=
    henergy.congr_fun (fun x hx => (hDpos_eq_on x hx).symm) hUmeas
  have hφDpos_U : IntegrableOn (fun x => (φ x - 1) * Dpos x) (HighContrast.adaptedCell q t) :=
    hφE.congr_fun (fun x hx => by rw [hDpos_eq_on x hx]) hUmeas
  have hDpos_at : ∀ w ∈ triadicIndexBox d n,
      IntegrableOn Dpos (adaptedCellAtCenter q (t - (n : ℤ)) w) := by
    intro w hw
    exact (hEat w hw).congr_fun
      (fun x hx => (hDpos_eq_on x (hsub w hw hx)).symm) (hVmeas w)
  have hφDpos_at : ∀ w ∈ triadicIndexBox d n,
      IntegrableOn (fun x => (φ x - 1) * Dpos x) (adaptedCellAtCenter q (t - (n : ℤ)) w) := by
    intro w hw
    exact (hφEat w hw).congr_fun
      (fun x hx => by rw [hDpos_eq_on x (hsub w hw hx)]) (hVmeas w)
  have hvolAt : ∀ w : Fin d → ℤ,
      0 < (volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal := by
    intro w
    rw [Geometry.volume_adaptedCellAtCenter, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (t - (n : ℤ)))]
    exact mul_pos
      (abs_pos.mpr (IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det q).mp hq)))
      (pow_pos (by positivity : (0 : ℝ) < (3 : ℝ) ^ (t - (n : ℤ))) d)
  have hsplit := abs_volumeAverage_sub_one_mul_sub_avsum_le (d := d) (qq := q) hq t n hφ
    (D := Dpos) hDpos_nonneg hDpos_U hφDpos_U hDpos_at hφat hφDpos_at
    (fun w _ => ne_of_gt (hvolAt w))
    (fun w _ => Geometry.volume_adaptedCellAtCenter_ne_top q (t - (n : ℤ)) w)
  have havgU_f : volumeAverage (HighContrast.adaptedCell q t) (fun x => (φ x - 1) * Dpos x)
      = volumeAverage (HighContrast.adaptedCell q t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand b u x) := by
    unfold volumeAverage
    rw [MeasureTheory.setIntegral_congr_fun hUmeas (fun x hx => by rw [hDpos_eq_on x hx])]
  have havgU_D : volumeAverage (HighContrast.adaptedCell q t) Dpos
      = volumeAverage (HighContrast.adaptedCell q t)
          (scalarVariationEnergyIntegrand b u) := by
    unfold volumeAverage
    rw [MeasureTheory.setIntegral_congr_fun hUmeas (fun x hx => hDpos_eq_on x hx)]
  have havgV_D : ∀ w ∈ triadicIndexBox d n,
      volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Dpos
        = volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (scalarVariationEnergyIntegrand b u) := by
    intro w hw
    unfold volumeAverage
    rw [MeasureTheory.setIntegral_congr_fun (hVmeas w)
      (fun x hx => hDpos_eq_on x (hsub w hw hx))]
  have hterms : (∑ w ∈ triadicIndexBox d n,
        volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (fun x => φ x - 1)
          * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Dpos)
      = ∑ w ∈ triadicIndexBox d n,
        volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (fun x => φ x - 1)
          * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (scalarVariationEnergyIntegrand b u) := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    rw [havgV_D w hw]
  have henergy_avg : volumeAverage (HighContrast.adaptedCell q t)
        (scalarVariationEnergyIntegrand b u) = 2 * respJ q t p r b := by
    have h := responseJ_energy_of_isResponseMaximizer (HighContrast.adaptedCell q t) b p r u
      hmax hu_int hresp_u hlin_self henergy
    unfold respJ
    linarith only [h]
  rw [havgU_f, hterms, havgU_D] at hsplit
  rw [henergy_avg] at hsplit
  exact hsplit

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Scalar arithmetic for the first error row

The first error row of `p.response.transfer` is assembled by integrating a pointwise bound
`|E - J| ≤ D + 2 √(J D)`.  Because the square root carries no measurability hypothesis, the
integrand is replaced by the one-parameter family `2 √(J D) ≤ ε J + D / ε`, integrated for each
`ε > 0`, and optimized only at the end.  This module supplies the scalar inequalities behind that
replacement together with the subadditivity that turns `√(τ (E + τ))` into `√(τ E) + τ`.

* `two_mul_sqrt_mul_le_eps_add_div` — the one-parameter Young bound on the cross term.
* `le_add_two_mul_sqrt_of_forall_pos` — optimization of the parameter at the end.
* `sqrt_mul_add_le_sqrt_mul_add` — splitting the terminal-scale annealed response.

Paper: the first error row of `p.response.transfer`.
-/

namespace HCPolySupport.HighContrast.Multiscale

noncomputable section

/-- Young's inequality in the product form used for the cross term: for `J, D ≥ 0` and `ε > 0`,
`2 √(J D) ≤ ε J + D / ε`. -/
theorem two_mul_sqrt_mul_le_eps_add_div (J D ε : ℝ) (hJ : 0 ≤ J) (hD : 0 ≤ D) (hε : 0 < ε) :
    2 * Real.sqrt (J * D) ≤ ε * J + D / ε := by
  have hε0 : 0 ≤ ε := hε.le
  have hεJ : 0 ≤ ε * J := mul_nonneg hε0 hJ
  have hDε : 0 ≤ D / ε := div_nonneg hD hε0
  have harg : (ε * J) * (D / ε) = J * D := by
    field_simp [hε.ne']
  have hsqrt : Real.sqrt (J * D) = Real.sqrt (ε * J) * Real.sqrt (D / ε) := by
    rw [← Real.sqrt_mul hεJ (D / ε), harg]
  calc 2 * Real.sqrt (J * D)
      = 2 * Real.sqrt (ε * J) * Real.sqrt (D / ε) := by rw [hsqrt]; ring
    _ ≤ Real.sqrt (ε * J) ^ 2 + Real.sqrt (D / ε) ^ 2 := two_mul_le_add_sq _ _
    _ = ε * J + D / ε := by rw [Real.sq_sqrt hεJ, Real.sq_sqrt hDε]

/-- Optimizing the one-parameter family: if `X ≤ B + ε A + T / ε` for every `ε > 0` and
`A, T ≥ 0`, then `X ≤ B + 2 √(T A)`. -/
theorem le_add_two_mul_sqrt_of_forall_pos (X B A T : ℝ) (hA : 0 ≤ A) (hT : 0 ≤ T)
    (h : ∀ ε : ℝ, 0 < ε → X ≤ B + (ε * A + T / ε)) :
    X ≤ B + 2 * Real.sqrt (T * A) := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · subst hA0
    simp only [mul_zero, Real.sqrt_zero, add_zero]
    rcases eq_or_lt_of_le hT with hT0 | hTpos
    · subst hT0
      simpa using h 1 one_pos
    · apply le_of_forall_pos_le_add
      intro δ hδ
      have hε : 0 < T / δ := div_pos hTpos hδ
      calc X ≤ B + ((T / δ) * 0 + T / (T / δ)) := h (T / δ) hε
        _ = B + δ := by field_simp [hTpos.ne', hδ.ne']; ring
  · rcases eq_or_lt_of_le hT with hT0 | hTpos
    · subst hT0
      simp only [zero_mul, Real.sqrt_zero, mul_zero, add_zero]
      apply le_of_forall_pos_le_add
      intro δ hδ
      have hε : 0 < δ / A := div_pos hδ hApos
      calc X ≤ B + ((δ / A) * A + 0 / (δ / A)) := h (δ / A) hε
        _ = B + δ := by field_simp [hApos.ne', hδ.ne']; ring
    · have hTA : 0 ≤ T * A := mul_nonneg hTpos.le hApos.le
      have hTA' : 0 ≤ T / A := div_nonneg hTpos.le hApos.le
      have hε : 0 < Real.sqrt (T / A) := Real.sqrt_pos.2 (div_pos hTpos hApos)
      have hA1 : Real.sqrt (T / A) * A = Real.sqrt (T * A) := by
        calc Real.sqrt (T / A) * A
            = Real.sqrt (T / A) * Real.sqrt (A ^ 2) := by rw [Real.sqrt_sq hApos.le]
          _ = Real.sqrt ((T / A) * A ^ 2) := (Real.sqrt_mul hTA' (A ^ 2)).symm
          _ = Real.sqrt (T * A) := by
                congr 1
                field_simp [hApos.ne']
      have hA2 : T / Real.sqrt (T / A) = Real.sqrt (T * A) := by
        rw [div_eq_iff hε.ne']
        calc T = Real.sqrt (T ^ 2) := (Real.sqrt_sq hTpos.le).symm
          _ = Real.sqrt ((T * A) * (T / A)) := by
                congr 1
                field_simp [hApos.ne']
          _ = Real.sqrt (T * A) * Real.sqrt (T / A) := Real.sqrt_mul hTA (T / A)
      calc X ≤ B + (Real.sqrt (T / A) * A + T / Real.sqrt (T / A)) := h _ hε
        _ = B + 2 * Real.sqrt (T * A) := by rw [hA1, hA2]; ring

/-- The terminal-scale splitting of the annealed response: for `A, T ≥ 0`,
`√(T (A + T)) ≤ √(T A) + T`. -/
theorem sqrt_mul_add_le_sqrt_mul_add (A T : ℝ) (hA : 0 ≤ A) (hT : 0 ≤ T) :
    Real.sqrt (T * (A + T)) ≤ Real.sqrt (T * A) + T := by
  rw [Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) hT)]
  have hTA : 0 ≤ T * A := mul_nonneg hT hA
  have hsq : (Real.sqrt (T * A) + T) ^ 2
      = T * (A + T) + 2 * (T * Real.sqrt (T * A)) := by
    rw [add_sq, Real.sq_sqrt hTA]
    ring
  rw [hsq]
  have hnonneg : 0 ≤ 2 * (T * Real.sqrt (T * A)) :=
    mul_nonneg (by norm_num) (mul_nonneg hT (Real.sqrt_nonneg _))
  exact le_add_of_nonneg_right hnonneg

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The first error row in abstract bookkeeping form

The terminal-optimizer replacement of `p.response.transfer`, after the terminal cell is subdivided
into the aligned coarse cells, reduces to the following bookkeeping.  Each subcell carries three
sample functions: the response `J`, half the restricted terminal optimizer energy `E`, and the
nonnegative deficit `D` between them, compared pointwise by `|E - J| ≤ D + 2 √(J D)`.  The weights
`c` are the subcell means of the cutoff fluctuation and average to zero, stationarity makes the
annealed response `∫ J` the same `cJ` on every subcell, and the annealed flat average of the
deficits is the scale defect `τ`.

The weighted average of the half-energies then has expectation at most `τ + 2 √(τ cJ)`: the
`J`-part is annihilated by the mean-zero weights, and the remainder is controlled by the deficits
through the one-parameter Cauchy--Schwarz bound `2 √(J D) ≤ ε J + D / ε`.

Paper: `p.response.transfer`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The abstract first error row.**  Under the pointwise comparison `|E - J| ≤ D + 2 √(J D)`, a
common annealed response `∫ J w = cJ`, a mean-zero normalized weighting `c`, and an annealed
flat deficit `τ`, the expectation of the weighted average of the half-energies is at most
`τ + 2 √(τ cJ)`.  This is the bookkeeping content of the terminal-optimizer replacement of the
first error row of `p.response.transfer`. -/
theorem abs_integral_avsum_weighted_energy_le {α : Type*} [MeasurableSpace α]
    (P : Measure α) {d : ℕ} (n : ℕ)
    (c : (Fin d → ℤ) → ℝ) (E J D : (Fin d → ℤ) → α → ℝ) (cJ τ : ℝ)
    (hc0 : (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n, c w = 0)
    (hc1 : ∀ w ∈ triadicIndexBox d n, |c w| ≤ 1)
    (hJ0 : ∀ w ∈ triadicIndexBox d n, ∀ a, 0 ≤ J w a)
    (hD0 : ∀ w ∈ triadicIndexBox d n, ∀ a, 0 ≤ D w a)
    (hcmp : ∀ w ∈ triadicIndexBox d n, ∀ a,
      |E w a - J w a| ≤ D w a + 2 * Real.sqrt (J w a * D w a))
    (hJint : ∀ w ∈ triadicIndexBox d n, Integrable (J w) P)
    (hDint : ∀ w ∈ triadicIndexBox d n, Integrable (D w) P)
    (hEint : ∀ w ∈ triadicIndexBox d n, Integrable (E w) P)
    (hJval : ∀ w ∈ triadicIndexBox d n, (∫ a, J w a ∂P) = cJ)
    (hDval : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, D w a ∂P) = τ) :
    |∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * E w a ∂P|
      ≤ τ + 2 * Real.sqrt (τ * cJ) := by
  have hcard : ((triadicIndexBox d n).card : ℝ) = ((3 : ℝ) ^ n) ^ d :=
    card_triadicIndexBox n
  have hZcard_pos : (0 : ℝ) < ((triadicIndexBox d n).card : ℝ) := by
    rw [hcard]
    positivity
  have hNnonneg : 0 ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ :=
    inv_nonneg.mpr hZcard_pos.le
  have hNcard : (((triadicIndexBox d n).card : ℝ))⁻¹ * ((triadicIndexBox d n).card : ℝ) = 1 :=
    inv_mul_cancel₀ (ne_of_gt hZcard_pos)
  have hFJint : Integrable (fun a => (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * J w a) P :=
    (integrable_finsetSum _ (fun w hw => (hJint w hw).const_mul (c w))).const_mul _
  have hFEJint : Integrable (fun a => (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a)) P :=
    (integrable_finsetSum _
      (fun w hw => ((hEint w hw).sub (hJint w hw)).const_mul (c w))).const_mul _
  have hFEJabs : Integrable (fun a => |(((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a)|) P := by
    simpa only [Real.norm_eq_abs] using hFEJint.abs
  have hFE_split : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * E w a ∂P)
      = (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * J w a ∂P)
        + (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a) ∂P) := by
    have hpt : ∀ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * E w a
        = (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, c w * J w a
          + (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a) := by
      intro a
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun w _ => by ring)
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hFJint hFEJint]
  have hFJcancel : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * J w a ∂P) = 0 :=
    integral_avsum_mul_eq_zero P n c J cJ hc0 hJval hJint
  have hFE_eq : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * E w a ∂P)
      = (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a) ∂P) := by
    rw [hFE_split, hFJcancel, zero_add]
  have hDsum : (∫ a, ∑ w ∈ triadicIndexBox d n, D w a ∂P)
      = ∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P) :=
    integral_finsetSum _ (fun w hw => hDint w hw)
  have hNStau : (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P) = τ := by
    have key := hDval
    rw [integral_const_mul, hDsum] at key
    exact key
  have hmain : ∀ ε : ℝ, 0 < ε →
      |(∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * E w a ∂P)|
        ≤ τ + (ε * cJ + τ / ε) := by
    intro ε hε
    have hinner : ∀ w ∈ triadicIndexBox d n,
        (∫ a, (D w a + ε * J w a + D w a / ε) ∂P)
          = (∫ a, D w a ∂P) + ε * cJ + (∫ a, D w a ∂P) / ε := by
      intro w hw
      have hsplit : (∫ a, (D w a + ε * J w a + D w a / ε) ∂P)
          = (∫ a, (D w a + ε * J w a) ∂P) + (∫ a, D w a / ε ∂P) :=
        integral_add
          (show Integrable (fun a => D w a + ε * J w a) P from
            (hDint w hw).add ((hJint w hw).const_mul ε))
          ((hDint w hw).div_const ε)
      have hDJ : (∫ a, (D w a + ε * J w a) ∂P)
          = (∫ a, D w a ∂P) + (∫ a, ε * J w a ∂P) :=
        integral_add (hDint w hw) ((hJint w hw).const_mul ε)
      rw [hsplit, hDJ, integral_const_mul, hJval w hw,
        integral_div ε (fun a => D w a)]
    have hsum_eval : (∑ w ∈ triadicIndexBox d n,
          ((∫ a, D w a ∂P) + ε * cJ + (∫ a, D w a ∂P) / ε))
        = (∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P))
          + (((triadicIndexBox d n).card : ℝ) * (ε * cJ))
          + (∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P)) / ε := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.sum_div]
    have hsum_congr : (∑ w ∈ triadicIndexBox d n,
          (∫ a, (D w a + ε * J w a + D w a / ε) ∂P))
        = ∑ w ∈ triadicIndexBox d n,
            ((∫ a, D w a ∂P) + ε * cJ + (∫ a, D w a ∂P) / ε) :=
      Finset.sum_congr rfl (fun w hw => hinner w hw)
    have hGε_int : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, (D w a + ε * J w a + D w a / ε) ∂P)
        = τ + ε * cJ + τ / ε := by
      have hconst : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, (D w a + ε * J w a + D w a / ε) ∂P)
          = (((triadicIndexBox d n).card : ℝ))⁻¹ *
            (∫ a, ∑ w ∈ triadicIndexBox d n,
              (D w a + ε * J w a + D w a / ε) ∂P) :=
        integral_const_mul _ (fun a => ∑ w ∈ triadicIndexBox d n,
          (D w a + ε * J w a + D w a / ε))
      have hsum : (∫ a, ∑ w ∈ triadicIndexBox d n,
            (D w a + ε * J w a + D w a / ε) ∂P)
          = ∑ w ∈ triadicIndexBox d n,
            (∫ a, (D w a + ε * J w a + D w a / ε) ∂P) :=
        integral_finsetSum _ (fun w hw =>
          show Integrable (fun a => D w a + ε * J w a + D w a / ε) P from
            ((hDint w hw).add ((hJint w hw).const_mul ε)).add
              ((hDint w hw).div_const ε))
      rw [hconst, hsum, hsum_congr, hsum_eval]
      calc (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ((∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P))
              + (((triadicIndexBox d n).card : ℝ) * (ε * cJ))
              + (∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P)) / ε)
          = (((triadicIndexBox d n).card : ℝ))⁻¹ *
              (∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P))
            + (((triadicIndexBox d n).card : ℝ))⁻¹ *
              (((triadicIndexBox d n).card : ℝ) * (ε * cJ))
            + (((triadicIndexBox d n).card : ℝ))⁻¹ *
              ((∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P)) / ε) := by ring
        _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
              (∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P))
            + ((((triadicIndexBox d n).card : ℝ))⁻¹ *
              ((triadicIndexBox d n).card : ℝ)) * (ε * cJ)
            + ((((triadicIndexBox d n).card : ℝ))⁻¹ *
              (∑ w ∈ triadicIndexBox d n, (∫ a, D w a ∂P))) / ε := by ring
        _ = τ + ε * cJ + τ / ε := by rw [hNStau, hNcard]; ring
    have hpt : ∀ a, |(((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a)|
        ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, (D w a + ε * J w a + D w a / ε) := by
      intro a
      calc |(((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a)|
          = (((triadicIndexBox d n).card : ℝ))⁻¹ *
              |∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a)| := by
            rw [abs_mul, abs_of_nonneg hNnonneg]
        _ ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, |c w * (E w a - J w a)| :=
            mul_le_mul_of_nonneg_left
              (Finset.abs_sum_le_sum_abs
                (fun w => c w * (E w a - J w a)) (triadicIndexBox d n))
              hNnonneg
        _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, |c w| * |E w a - J w a| := by
            congr 1
            exact Finset.sum_congr rfl (fun w _ => by rw [abs_mul])
        _ ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, 1 * |E w a - J w a| := by
            apply mul_le_mul_of_nonneg_left _ hNnonneg
            apply Finset.sum_le_sum
            intro w hw
            exact mul_le_mul_of_nonneg_right (hc1 w hw) (abs_nonneg _)
        _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, |E w a - J w a| := by
            congr 1
            exact Finset.sum_congr rfl (fun w _ => by rw [one_mul])
        _ ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, (D w a + ε * J w a + D w a / ε) := by
            apply mul_le_mul_of_nonneg_left _ hNnonneg
            apply Finset.sum_le_sum
            intro w hw
            calc |E w a - J w a|
                ≤ D w a + 2 * Real.sqrt (J w a * D w a) := hcmp w hw a
              _ ≤ D w a + (ε * J w a + D w a / ε) := by
                  have hY := two_mul_sqrt_mul_le_eps_add_div (J w a) (D w a) ε
                    (hJ0 w hw a) (hD0 w hw a) hε
                  linarith only [hY]
              _ = D w a + ε * J w a + D w a / ε := by ring
    have hGεint : Integrable (fun a => (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, (D w a + ε * J w a + D w a / ε)) P :=
      (integrable_finsetSum _ (fun w hw =>
        show Integrable (fun a => D w a + ε * J w a + D w a / ε) P from
          ((hDint w hw).add ((hJint w hw).const_mul ε)).add
            ((hDint w hw).div_const ε))).const_mul _
    calc |(∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, c w * E w a ∂P)|
        = |(∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a) ∂P)| := by rw [hFE_eq]
      _ ≤ ∫ a, |(((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, c w * (E w a - J w a)| ∂P :=
          abs_integral_le_integral_abs
      _ ≤ ∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, (D w a + ε * J w a + D w a / ε) ∂P :=
          integral_mono hFEJabs hGεint (fun a => hpt a)
      _ = τ + ε * cJ + τ / ε := hGε_int
      _ = τ + (ε * cJ + τ / ε) := by ring
  have hcJ_nonneg : 0 ≤ cJ := by
    have hZnonempty : (triadicIndexBox d n).Nonempty :=
      Finset.card_pos.mp (Nat.cast_pos'.mp hZcard_pos)
    obtain ⟨w0, hw0⟩ := hZnonempty
    rw [← hJval w0 hw0]
    exact integral_nonneg (fun a => hJ0 w0 hw0 a)
  have hτ_nonneg : 0 ≤ τ := by
    rw [← hDval]
    exact integral_nonneg (fun a => mul_nonneg hNnonneg
      (Finset.sum_nonneg (fun w hw => hD0 w hw a)))
  exact le_add_two_mul_sqrt_of_forall_pos _ τ cJ τ hcJ_nonneg hτ_nonneg hmain

end

end HCPolySupport.HighContrast.Multiscale
end
