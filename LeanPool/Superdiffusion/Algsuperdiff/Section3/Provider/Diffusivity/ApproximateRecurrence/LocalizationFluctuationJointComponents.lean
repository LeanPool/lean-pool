/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationJointRestrict

/-!
# LocalizationFluctuationJointComponents

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Assembling a doubled `L^2` class from its two vector legs

ABK26, `l.approximate.recurrence.formula`, Step 2.

## Why this module exists

The measurability hypothesis of `LocalizationFluctuationJointField` is stated
at the **doubled** carrier `HilbertBlockL2`.  This module is the bridge.

## Method

The pairing map is not treated as a bilinear object at all.  Writing

```
  (F, G)  =  iota_1 F  +  iota_2 G ,
```

with `iota_1 v = (v, 0)` and `iota_2 v = (0, v)`, each summand is post-composition
of an `L^2` class with a **fixed continuous linear map of the fibres**, i.e.
`ContinuousLinearMap.compLpL`, which is itself a continuous linear map of `L^2`
spaces.  Continuity of the assembly is therefore free, and no `eLpNorm`
computation occurs anywhere below.

## Main results

* `measurable_toHilbertBlockL2OfComponents` --- a measurable class for each leg
  gives a measurable doubled class.
* `toHilbertBlockL2OfBlockField_const` --- the constant leg (the load `P_z` of
  `e.Pz.def`) is the image of its block vector under the continuous linear
  `blockVecToHilbertBlockL2Const`.

## Binders

Beyond the typing binders: the vector-`L^2` memberships of the two legs and
measurability of their classes.  No estimate, no integrability and no
proposition about the sample law occurs.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula`, Step 2, `e.Pz.def`, `e.Fz.def`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open HCPolySupport.Internal.Ch02.BookCh02
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The two fibre embeddings -/

/-- The potential-leg embedding of a Hilbert vector into a Hilbert block
vector. -/
def hilbertBlockInl (d : ℕ) : HilbertVec d →L[ℝ] HilbertBlockVec d :=
  ((HilbertBlockVec.continuousLinearEquivBlockVec d).symm).toContinuousLinearMap.comp
    ((ContinuousLinearMap.inl ℝ (Vec d) (Vec d)).comp
      ((HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap))

/-- The flux-leg embedding of a Hilbert vector into a Hilbert block vector. -/
def hilbertBlockInr (d : ℕ) : HilbertVec d →L[ℝ] HilbertBlockVec d :=
  ((HilbertBlockVec.continuousLinearEquivBlockVec d).symm).toContinuousLinearMap.comp
    ((ContinuousLinearMap.inr ℝ (Vec d) (Vec d)).comp
      ((HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap))

/-! ## Assembling the doubled class -/

/-- **The doubled class of a pair of vector fields is the sum of the two
post-composed vector classes.** -/
theorem toHilbertBlockL2OfComponents_eq_compLp_add {U : Set (Vec d)}
    {f g : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    toHilbertBlockL2OfComponents hf hg =
      (hilbertBlockInl d).compLp (toHilbertVectorL2OfVecField hf) +
        (hilbertBlockInr d).compLp (toHilbertVectorL2OfVecField hg) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_toHilbertBlockL2OfComponents hf hg,
    MeasureTheory.Lp.coeFn_add ((hilbertBlockInl d).compLp (toHilbertVectorL2OfVecField hf))
      ((hilbertBlockInr d).compLp (toHilbertVectorL2OfVecField hg)),
    (hilbertBlockInl d).coeFn_compLp' (toHilbertVectorL2OfVecField hf),
    (hilbertBlockInr d).coeFn_compLp' (toHilbertVectorL2OfVecField hg),
    coeFn_toHilbertVectorL2OfVecField hf, coeFn_toHilbertVectorL2OfVecField hg] with
    x hx hadd hl hr hfx hgx
  rw [hx, hadd]
  simp only [Pi.add_apply]
  rw [hl, hr, hfx, hgx]
  apply HilbertBlockVec.ext
  · ext i
    simp [hilbertBlockField, hilbertifyBlockField, blockField, hilbertBlockInl,
      hilbertBlockInr, hilbertifyVecField]
  · ext i
    simp [hilbertBlockField, hilbertifyBlockField, blockField, hilbertBlockInl,
      hilbertBlockInr, hilbertifyVecField]

/-- **A measurable class for each leg gives a measurable doubled class.** -/
theorem measurable_toHilbertBlockL2OfComponents {Omega : Type*} [MeasurableSpace Omega]
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    [MeasurableSpace (HilbertVectorL2 U)] [BorelSpace (HilbertVectorL2 U)]
    [MeasurableSpace (HilbertBlockL2 U)] [BorelSpace (HilbertBlockL2 U)]
    [SecondCountableTopology (HilbertBlockL2 U)]
    {f g : Omega → Vec d → Vec d}
    (hf : ∀ omega, MemVectorL2 U (f omega)) (hg : ∀ omega, MemVectorL2 U (g omega))
    (hfm : Measurable fun omega => toHilbertVectorL2OfVecField (hf omega))
    (hgm : Measurable fun omega => toHilbertVectorL2OfVecField (hg omega)) :
    Measurable fun omega => toHilbertBlockL2OfComponents (hf omega) (hg omega) := by
  let : Fact ((1 : ENNReal) ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  have hrw : (fun omega => toHilbertBlockL2OfComponents (hf omega) (hg omega))
      = fun omega =>
        ((hilbertBlockInl d).compLpL (μ := volumeMeasureOn U) (p := 2)
            (toHilbertVectorL2OfVecField (hf omega)),
          (hilbertBlockInr d).compLpL (μ := volumeMeasureOn U) (p := 2)
            (toHilbertVectorL2OfVecField (hg omega))).1 +
        ((hilbertBlockInl d).compLpL (μ := volumeMeasureOn U) (p := 2)
            (toHilbertVectorL2OfVecField (hf omega)),
          (hilbertBlockInr d).compLpL (μ := volumeMeasureOn U) (p := 2)
            (toHilbertVectorL2OfVecField (hg omega))).2 := by
    funext omega
    exact toHilbertBlockL2OfComponents_eq_compLp_add (hf omega) (hg omega)
  rw [hrw]
  exact Measurable.add
    (((hilbertBlockInl d).compLpL (μ := volumeMeasureOn U) (p := 2)).continuous.measurable.comp hfm)
    (((hilbertBlockInr d).compLpL (μ := volumeMeasureOn U) (p := 2)).continuous.measurable.comp hgm)

/-! ## The constant leg -/

/-- **The doubled class of a constant block field is its image under the proved
continuous linear constant embedding.** -/
theorem toHilbertBlockL2OfBlockField_const {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] (P : BlockVec d)
    (hP : MemBlockL2 U (fun _ => P)) :
    toHilbertBlockL2OfBlockField hP = blockVecToHilbertBlockL2Const (U := U) P := by
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_toHilbertBlockL2OfBlockField hP,
    coeFn_blockVecToHilbertBlockL2Const (U := U) P] with x hx hy
  rw [hx, hy]
  rfl

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
