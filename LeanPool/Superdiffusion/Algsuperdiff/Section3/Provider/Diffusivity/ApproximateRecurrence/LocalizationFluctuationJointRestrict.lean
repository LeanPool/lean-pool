/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationJointBackground

/-!
# LocalizationFluctuationJointRestrict

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Restricting a doubled `L^2` class from the localization cube to a cell

ABK26, `l.approximate.recurrence.formula`, Step 2.

## The missing plumbing this module supplies

`Corrector.CorrectorMeasurableGradient` records explicitly that "the
restriction map to a subwindow. is not built here".  This module builds it.

The map is the identity on representatives; the only content is that it is
**well defined** on classes (a null set of the larger restricted measure is a
null set of the smaller one) and **`1`-Lipschitz** (`eLpNorm` is monotone in the
measure).  Neither linearity nor any Hilbert structure is used, and none is
needed: measurability of a composition only asks for continuity.

## Main results

* `restrictHilbertBlockL2` --- the map, with `coeFn_restrictHilbertBlockL2` and
  the compatibility `restrictHilbertBlockL2_toHilbertBlockL2OfBlockField`.
* `lipschitzWith_restrictHilbertBlockL2`, `measurable_restrictHilbertBlockL2`.
* `measurable_toHilbertBlockL2OfBlockField_of_subset` --- the transfer a
  consumer uses: a measurable class on the larger set gives a measurable class
  on the smaller one.

## Binders

Only the inclusion of sets and the `L^2` membership on the larger set.  No
estimate, no integrability, no ellipticity and no proposition about the sample
law occurs.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula`, Step 2.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open HCPolySupport.Internal.Ch02.BookCh02
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The restriction of a doubled `L^2` class -/

/-- The restricted volume measure is monotone in the domain. -/
theorem volumeMeasureOn_mono {S T : Set (Vec d)} (hTS : T ⊆ S) :
    volumeMeasureOn T ≤ volumeMeasureOn S :=
  Measure.restrict_mono hTS le_rfl

/-- **Restriction of a doubled `L^2` class to a smaller domain.**  The identity
on representatives; well defined because a null set of the larger restricted
measure is a null set of the smaller one. -/
def restrictHilbertBlockL2 {S T : Set (Vec d)} (hTS : T ⊆ S) (f : HilbertBlockL2 S) :
    HilbertBlockL2 T :=
  (MemLp.mono_measure (volumeMeasureOn_mono hTS) (Lp.memLp f)).toLp
    (fun x => (f : Vec d → HilbertBlockVec d) x)

theorem coeFn_restrictHilbertBlockL2 {S T : Set (Vec d)} (hTS : T ⊆ S)
    (f : HilbertBlockL2 S) :
    restrictHilbertBlockL2 hTS f =ᵐ[volumeMeasureOn T]
      fun x => (f : Vec d → HilbertBlockVec d) x :=
  MemLp.coeFn_toLp _

/-- The restriction map is `1`-Lipschitz: `eLpNorm` is monotone in the
measure. -/
theorem lipschitzWith_restrictHilbertBlockL2 {S T : Set (Vec d)} (hTS : T ⊆ S) :
    LipschitzWith 1 (restrictHilbertBlockL2 (d := d) hTS) := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  have hae : (fun x => (restrictHilbertBlockL2 hTS f - restrictHilbertBlockL2 hTS g :
        HilbertBlockL2 T) x)
      =ᵐ[volumeMeasureOn T]
        fun x => (f : Vec d → HilbertBlockVec d) x - (g : Vec d → HilbertBlockVec d) x := by
    filter_upwards [Lp.coeFn_sub (restrictHilbertBlockL2 hTS f) (restrictHilbertBlockL2 hTS g),
      coeFn_restrictHilbertBlockL2 hTS f, coeFn_restrictHilbertBlockL2 hTS g] with x h1 h2 h3
    rw [h1]
    simp only [Pi.sub_apply]
    rw [h2, h3]
  have hae2 : (fun x => (f - g : HilbertBlockL2 S) x)
      =ᵐ[volumeMeasureOn S]
        fun x => (f : Vec d → HilbertBlockVec d) x - (g : Vec d → HilbertBlockVec d) x := by
    filter_upwards [Lp.coeFn_sub f g] with x h1
    rw [h1]
    simp
  have hfin : eLpNorm (fun x => (f - g : HilbertBlockL2 S) x) 2 (volumeMeasureOn S) ≠ ⊤ :=
    (Lp.eLpNorm_lt_top (f - g)).ne
  rw [dist_eq_norm, dist_eq_norm]
  simp only [NNReal.coe_one, one_mul]
  rw [Lp.norm_def, Lp.norm_def]
  refine ENNReal.toReal_mono hfin ?_
  calc eLpNorm (fun x => (restrictHilbertBlockL2 hTS f - restrictHilbertBlockL2 hTS g :
          HilbertBlockL2 T) x) 2 (volumeMeasureOn T)
      = eLpNorm (fun x => (f : Vec d → HilbertBlockVec d) x
          - (g : Vec d → HilbertBlockVec d) x) 2 (volumeMeasureOn T) := eLpNorm_congr_ae hae
    _ ≤ eLpNorm (fun x => (f : Vec d → HilbertBlockVec d) x
          - (g : Vec d → HilbertBlockVec d) x) 2 (volumeMeasureOn S) :=
        eLpNorm_mono_measure _ (volumeMeasureOn_mono hTS)
    _ = eLpNorm (fun x => (f - g : HilbertBlockL2 S) x) 2 (volumeMeasureOn S) :=
        (eLpNorm_congr_ae hae2).symm

theorem continuous_restrictHilbertBlockL2 {S T : Set (Vec d)} (hTS : T ⊆ S) :
    Continuous (restrictHilbertBlockL2 (d := d) hTS) :=
  (lipschitzWith_restrictHilbertBlockL2 hTS).continuous

theorem measurable_restrictHilbertBlockL2 {S T : Set (Vec d)} (hTS : T ⊆ S)
    [MeasurableSpace (HilbertBlockL2 S)] [BorelSpace (HilbertBlockL2 S)]
    [MeasurableSpace (HilbertBlockL2 T)] [BorelSpace (HilbertBlockL2 T)] :
    Measurable (restrictHilbertBlockL2 (d := d) hTS) :=
  (continuous_restrictHilbertBlockL2 hTS).measurable

/-- **Compatibility with the class map.**  Restricting the class of a block
field is the class of the same block field on the smaller domain. -/
theorem restrictHilbertBlockL2_toHilbertBlockL2OfBlockField {S T : Set (Vec d)}
    (hTS : T ⊆ S) {F : Vec d → BlockVec d} (hS : MemBlockL2 S F) :
    restrictHilbertBlockL2 hTS (toHilbertBlockL2OfBlockField hS)
      = toHilbertBlockL2OfBlockField (hS.mono_measure (volumeMeasureOn_mono hTS)) := by
  apply MeasureTheory.Lp.ext
  have hsub : ∀ᵐ x ∂(volumeMeasureOn T),
      (toHilbertBlockL2OfBlockField hS : Vec d → HilbertBlockVec d) x
        = hilbertifyBlockField F x :=
    Filter.Eventually.filter_mono (ae_mono (volumeMeasureOn_mono hTS))
      (coeFn_toHilbertBlockL2OfBlockField hS)
  filter_upwards [coeFn_restrictHilbertBlockL2 hTS (toHilbertBlockL2OfBlockField hS),
    coeFn_toHilbertBlockL2OfBlockField (hS.mono_measure (volumeMeasureOn_mono hTS)),
    hsub] with x h1 h2 h3
  rw [h1, h2, h3]

/-! ## The transfer -/

/-- **A measurable class on a larger domain restricts to a measurable class on a
smaller one.** -/
theorem measurable_toHilbertBlockL2OfBlockField_of_subset {Omega : Type*}
    [MeasurableSpace Omega] {S T : Set (Vec d)} (hTS : T ⊆ S)
    [MeasurableSpace (HilbertBlockL2 S)] [BorelSpace (HilbertBlockL2 S)]
    [MeasurableSpace (HilbertBlockL2 T)] [BorelSpace (HilbertBlockL2 T)]
    {F : Omega → Vec d → BlockVec d} (hS : ∀ omega, MemBlockL2 S (F omega))
    (hmeas : Measurable fun omega => toHilbertBlockL2OfBlockField (hS omega)) :
    Measurable fun omega =>
      toHilbertBlockL2OfBlockField ((hS omega).mono_measure (volumeMeasureOn_mono hTS)) := by
  have hrw : (fun omega =>
      toHilbertBlockL2OfBlockField ((hS omega).mono_measure (volumeMeasureOn_mono hTS)))
      = fun omega => restrictHilbertBlockL2 hTS (toHilbertBlockL2OfBlockField (hS omega)) := by
    funext omega
    exact (restrictHilbertBlockL2_toHilbertBlockL2OfBlockField hTS (hS omega)).symm
  rw [hrw]
  exact (measurable_restrictHilbertBlockL2 hTS).comp hmeas

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
