/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.FourierMultiplierSub
public import LeanPool.FastDynamo.Analysis.ComplexForm
public import LeanPool.FastDynamo.Operator.AssociatedForm
public import LeanPool.FastDynamo.Operator.WholePlaneLocal
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compactness assembly for whole-plane local perturbations

This file isolates the finite-component part of the local Rellich argument.
The analytic input is stated directly, using Mathlib's
`IsCompactOperator`, for the concrete scalar maps

`u ↦ a u : H¹(ℝ²; ℂ) → L²(ℝ²; ℂ)`.

A continuous linear map into a finite product is compact when every coordinate
is (`isCompactOperator_pi_of_fintype`), and multiplication by a bounded scalar
coefficient supported in a finite-volume set `s` factors through restriction to
`s`, so that it is compact as soon as that restriction is
(`isCompactOperator_wholePlaneScalarLocalizationH1_of_restriction`).  The
restriction itself is proved compact in `WholePlaneBandLimitedRellichUnconditional`,
and `WholePlaneLocalCompactnessUnconditional` combines the two.

The Mathlib version used here supplies the abstract compact-operator calculus used below,
but no Rellich--Kondrachov theorem for Euclidean weak Sobolev spaces.  In
particular, this file does not infer the scalar hypothesis from compact support.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## Finite-component compactness -/

/-- A continuous linear map into a finite product is compact when every
coordinate map is compact. -/
theorem isCompactOperator_pi_of_fintype
    {E ι : Type*} [Finite ι]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {F : ι → Type*} [∀ i, SeminormedAddCommGroup (F i)]
    [∀ i, NormedSpace ℂ (F i)]
    (T : E →L[ℂ] (∀ i, F i))
    (hT : ∀ i, IsCompactOperator
      ((ContinuousLinearMap.proj i).comp T)) :
    IsCompactOperator T := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hEq : T = ∑ i : ι,
      (ContinuousLinearMap.single ℂ F i).comp
        ((ContinuousLinearMap.proj i).comp T) := by
    ext x i
    simp
  rw [hEq]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simpa using (isCompactOperator_zero :
        IsCompactOperator (0 : E → (∀ i, F i)))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact ((hT i).clm_comp
        (ContinuousLinearMap.single ℂ F i)).add ih

/-! ## The exact scalar local Rellich input -/

/-- Multiplication by an `L∞` scalar coefficient, viewed as a concrete map
from the weak whole-plane `H¹` graph into scalar `L²`. -/
def wholePlaneScalarLocalizationH1 (a : WholePlaneScalarLInf) :
    WholePlaneScalarH1 →L[ℂ] WholePlaneScalarL2 :=
  (scalarVectorMulL2 (E := ℂ) volume a).comp
    (wholePlaneH1Embedding ℂ)

/-- Multiplication by an `L∞` scalar coefficient on the weak `H¹` graph acts through the
physical `L²` field: it is the `L∞`-`L²` product of `a` with the embedded value of `u`. -/
@[simp] theorem wholePlaneScalarLocalizationH1_apply
    (a : WholePlaneScalarLInf) (u : WholePlaneScalarH1) :
    wholePlaneScalarLocalizationH1 a u =
      scalarVectorMulL2 volume a (wholePlaneH1Embedding ℂ u) :=
  rfl

/-- The `L∞` indicator of a measurable finite-measure localization set. -/
def wholePlaneLocalizationIndicator
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) : WholePlaneScalarLInf :=
  indicatorConstLp ∞ hs hsm (1 : ℂ)

/-- Restriction to a measurable finite-measure set, represented on quotient
spaces by multiplication with its indicator. -/
def wholePlaneScalarRestrictionH1
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) :
    WholePlaneScalarH1 →L[ℂ] WholePlaneScalarL2 :=
  wholePlaneScalarLocalizationH1
    (wholePlaneLocalizationIndicator s hs hsm)

/-- A coefficient which vanishes almost everywhere off `s` factors through
the concrete restriction to `s`. -/
theorem wholePlaneScalarLocalizationH1_eq_comp_restriction
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) (a : WholePlaneScalarLInf)
    (ha : ∀ᵐ x ∂volume, x ∉ s → a x = 0) :
    wholePlaneScalarLocalizationH1 a =
      (scalarVectorMulL2 (E := ℂ) volume a).comp
        (wholePlaneScalarRestrictionH1 s hs hsm) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  have hleft := scalarVectorMulL2_coe_ae volume a
    (wholePlaneH1Embedding ℂ u)
  have hcut := scalarVectorMulL2_coe_ae volume
    (wholePlaneLocalizationIndicator s hs hsm)
    (wholePlaneH1Embedding ℂ u)
  have hright := scalarVectorMulL2_coe_ae volume a
    (wholePlaneScalarRestrictionH1 s hs hsm u)
  have hind := indicatorConstLp_coeFn
    (p := ∞) (hs := hs) (hμs := hsm) (c := (1 : ℂ))
  filter_upwards [hleft, hcut, hright, hind, ha]
    with x hleftx hcutx hrightx hindx hax
  change
    (scalarVectorMulL2 (E := ℂ) volume a
        (scalarVectorMulL2 (E := ℂ) volume
          (wholePlaneLocalizationIndicator s hs hsm)
          (wholePlaneH1Embedding ℂ u)) : WholePlane → ℂ) x =
      a x •
        (scalarVectorMulL2 (E := ℂ) volume
          (wholePlaneLocalizationIndicator s hs hsm)
          (wholePlaneH1Embedding ℂ u) : WholePlane → ℂ) x at hrightx
  change (wholePlaneLocalizationIndicator s hs hsm : WholePlane → ℂ) x =
    s.indicator (fun _ => (1 : ℂ)) x at hindx
  change
    (scalarVectorMulL2 (E := ℂ) volume a
        (wholePlaneH1Embedding ℂ u) : WholePlane → ℂ) x =
      (scalarVectorMulL2 (E := ℂ) volume a
        (scalarVectorMulL2 (E := ℂ) volume
          (wholePlaneLocalizationIndicator s hs hsm)
          (wholePlaneH1Embedding ℂ u)) : WholePlane → ℂ) x
  rw [hleftx, hrightx, hcutx, hindx]
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, hax hx]
    simp

/-- A scalar local-Rellich certificate for the indicator of `s` proves
compactness of multiplication by every bounded coefficient supported in
`s`. -/
theorem isCompactOperator_wholePlaneScalarLocalizationH1_of_restriction
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞) (a : WholePlaneScalarLInf)
    (ha : ∀ᵐ x ∂volume, x ∉ s → a x = 0)
    (hRellich : IsCompactOperator
      (wholePlaneScalarRestrictionH1 s hs hsm)) :
    IsCompactOperator (wholePlaneScalarLocalizationH1 a) := by
  rw [wholePlaneScalarLocalizationH1_eq_comp_restriction
    s hs hsm a ha]
  exact hRellich.clm_comp (scalarVectorMulL2 volume a)

end

end FastDynamo
