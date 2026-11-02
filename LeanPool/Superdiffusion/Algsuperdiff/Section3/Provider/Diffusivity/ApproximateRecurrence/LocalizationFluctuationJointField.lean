/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationJointCoeff

/-!
# LocalizationFluctuationJointField

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The sample-dependent competitor: from a fixed field to a measurable `L^2` class

ABK26, `l.approximate.recurrence.formula`, Step 2.

## The obligation this module discharges

`LocalizationFluctuationJointCoeff.measurable_doubledMuValue_meshCellCoeff`
makes the doubled energy value measurable in the sample when the competitor
field is **fixed**.  The Step-2 integrand needs it when the competitor moves
with the sample as well: the background of the field-slope problem is
`P_z(omega) + bfF_z(omega)`, whose two legs are read along the corrector
family.  This module removes the fixed-field restriction, at the only cost that
is unavoidable: the competitor must be presented through a **measurable `L^2`
class**, not through a pointwise family.

## Method

For a fixed coefficient `a` the doubled energy value is a **continuous function
of the `L^2` class of the competitor**: this is CoarseGraining's own Hilbert
realization of the doubled problem
(`MuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_ of_blockState`
together with `quadraticEnergy_continuous`), packaged here as
`exists_continuous_doubledMuValue_of_class`.  Composing:

* in the class variable the energy is continuous, for every sample;
* in the sample variable it is measurable, for every fixed class --- because
  every class is the class of *some* honest block field
  (`exists_memBlockL2_toHilbertBlockL2OfBlockField_eq`, from the canonical
  strongly measurable `Lp` representative), and at a fixed field the
  measurability is the previous module's.

`MeasureTheory.measurable_uncurry_of_continuous_of_measurable` (Caratheodory)
then makes the two-variable energy jointly measurable, and composing with the
measurable class of the competitor finishes.  `HilbertBlockL2` is a separable
metrizable space, which is what the Caratheodory lemma asks of the index.

**No measurable selection occurs.**  The competitor is not chosen: it is given,
and only its `L^2` class is used.  The block-field representative extracted from
a class is used solely as a witness inside a measurability proof; no statement
below mentions it.

## Main results

* `exists_memBlockL2_toHilbertBlockL2OfBlockField_eq` --- surjectivity of the
  class map onto the doubled `L^2` carrier.
* `exists_continuous_doubledMuValue_of_class` --- the doubled energy value is a
  continuous function of the competitor's `L^2` class.
* `measurable_doubledMuValue_of_measurable_class` --- the generic transfer.
* `measurable_doubledMuValue_meshCellCoeff_of_measurable_class` --- its
  instantiation at the Step-2 cell coefficient, which is the statement the
  `hcomp` binder of
  `LocalizationFluctuationMuMeasCell.integrable_meshFluctuationCellIntegrand'`
  and the measurability half of its `hbg` binder both reduce to.

## Binders

Beyond the typing binders: `[NeZero d]`; the `L^2` membership of the competitor
at every sample (a typing property of the corrector data, not an estimate); and
measurability of its class.  No integrability, no ellipticity constant, no
smallness and no estimate occurs.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula`, Step 2, the two `argmin` displays,
  `e.variational.mu.U.P`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open HCPolySupport.Internal.Ch02.BookCh02
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Every doubled `L^2` class is the class of an honest block field -/

/-- **Surjectivity of the class map.**  The canonical `Lp` representative of a
doubled `L^2` class is a strongly measurable block field whose class is the
given one.  No choice beyond `Lp`'s own representative occurs. -/
theorem exists_memBlockL2_toHilbertBlockL2OfBlockField_eq {U : Set (Vec d)}
    (xi : HilbertBlockL2 U) :
    ∃ (F : Vec d → BlockVec d) (hF : MemBlockL2 U F),
      Measurable (fun x => (F x).1) ∧ Measurable (fun x => (F x).2) ∧
        toHilbertBlockL2OfBlockField hF = xi := by
  classical
  set F : Vec d → BlockVec d := fun x => HilbertBlockVec.toBlockVec (xi x) with hFdef
  have hmeas : Measurable (fun x => xi x) := (Lp.stronglyMeasurable xi).measurable
  have hF : MemBlockL2 U F := by
    have := ((HilbertBlockVec.continuousLinearEquivBlockVec d).toContinuousLinearMap).comp_memLp'
      (Lp.memLp xi)
    simpa [hFdef] using! this
  refine ⟨F, hF, ?_, ?_, ?_⟩
  · exact (measurable_fst.comp
      (((HilbertBlockVec.continuousLinearEquivBlockVec d).continuous).measurable.comp hmeas))
  · exact (measurable_snd.comp
      (((HilbertBlockVec.continuousLinearEquivBlockVec d).continuous).measurable.comp hmeas))
  · have hfun : hilbertifyBlockField F = fun x => xi x := by
      funext x
      simp [hFdef, hilbertifyBlockField]
    have hxi : MemHilbertBlockL2 U (fun x => (xi : Vec d → HilbertBlockVec d) x) := Lp.memLp xi
    have h1 : toHilbertBlockL2 hxi = xi := Lp.toLp_coeFn xi hxi
    have h2 : toHilbertBlockL2 (memHilbertBlockL2_hilbertifyBlockField hF)
        = toHilbertBlockL2 hxi :=
      (toHilbertBlockL2_eq_toHilbertBlockL2_iff _ hxi).2 (Filter.EventuallyEq.of_eq hfun)
    change toHilbertBlockL2 (memHilbertBlockL2_hilbertifyBlockField hF) = xi
    rw [h2, h1]

/-! ## The energy as a continuous function of the competitor's class -/

/-- **The doubled energy value is a continuous function of the competitor's
`L^2` class.**

For every Chapter 2 domain and every coefficient there is a continuous real
function on the doubled `L^2` carrier which returns `doubledMuValue` at the
class of any block-`L^2` doubled field.  This is CoarseGraining's Hilbert
realization of the doubled problem, read at a fixed coefficient; it is the
exact ingredient `LocalizationFluctuationMuMeasCore` already uses to transfer
an infimum, exported here on its own. -/
theorem exists_continuous_doubledMuValue_of_class [NeZero d] (U : Domain d) (a : CoeffOn U) :
    ∃ g : HilbertBlockL2 (U : Set (Vec d)) → ℝ, Continuous g ∧
      ∀ (W : DoubledField d) (hW : MemBlockL2 (U : Set (Vec d)) (blockStateOfDoubled W).eval),
        g (toHilbertBlockL2OfBlockField hW) = doubledMuValue U a W := by
  classical
  let : Fact ((1 : ENNReal) ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  set b : CoeffOn U := pointwiseCoeffOn U a with hbdef
  have hba : CoeffOn.AEEq b a := by
    simpa [hbdef] using pointwiseCoeffOn_ae_eq U a
  have hval : ∀ X : DoubledField d, doubledMuValue U b X = doubledMuValue U a X :=
    fun X => doubledMuValue_eq_ofAEEq hba X
  have hEll : IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField := by
    simpa [hbdef] using pointwiseCoeffOn_isEllipticFieldOn U a
  let Rdat : PotentialSolenoidalL2RecoveryData (U : Set (Vec d)) :=
    potentialSolenoidalL2RecoveryDataOfClosureRealization
      (PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_convexDomain
        U.isDomain)
  let Mr : MuOperatorRealization (U : Set (Vec d)) b.toCoeffField :=
    (Rdat.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
      (domain_volume_pos U)).toMuOperatorRealization
  set B := energyBilinOfOperator Mr.operator with hBdef
  refine ⟨quadraticEnergy B, quadraticEnergy_continuous B, ?_⟩
  intro W hW
  rw [hBdef, Mr.quadraticEnergy_eq_blockEnergyAverage_of_blockState hW,
    ← doubledMuValue_eq_blockEnergyAverage U b W]
  exact hval W

/-! ## The transfer -/

/-- **The doubled energy value at a sample-dependent coefficient *and* a
sample-dependent competitor is measurable, as soon as the competitor's `L^2`
class is.**

The competitor family `X` is arbitrary: no measurability of `omega |-> X omega`
as a family of functions is assumed, and no minimizer or representative is
selected.  Only the class map `omega |-> [X omega]` is asked to be measurable,
which is the shape the proved corrector-gradient measurability delivers.

on `hX` (block-`L^2` membership at every sample, a typing property), `hclass`,
and `hfixed` --- measurability in the sample at every **fixed** competitor with
measurable components, which
`LocalizationFluctuationJointCoeff.measurable_doubledMuValue_meshCellCoeff`
supplies at the Step-2 carriers. -/
theorem measurable_doubledMuValue_of_measurable_class [NeZero d] {Omega : Type*}
    [MeasurableSpace Omega] (U : Domain d)
    [MeasurableSpace (HilbertBlockL2 (U : Set (Vec d)))]
    [BorelSpace (HilbertBlockL2 (U : Set (Vec d)))]
    (a : Omega → CoeffOn U) (X : Omega → DoubledField d)
    (hX : ∀ omega, MemBlockL2 (U : Set (Vec d)) (blockStateOfDoubled (X omega)).eval)
    (hclass : Measurable fun omega => toHilbertBlockL2OfBlockField (hX omega))
    (hfixed : ∀ W : DoubledField d, Measurable W.potential → Measurable W.flux →
      Measurable fun omega => doubledMuValue U (a omega) W) :
    Measurable fun omega => doubledMuValue U (a omega) (X omega) := by
  classical
  let : Fact ((1 : ENNReal) ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have : SecondCountableTopology (HilbertBlockL2 (U : Set (Vec d))) := inferInstance
  choose g hgcont hgval using fun omega : Omega =>
    exists_continuous_doubledMuValue_of_class U (a omega)
  have hmeasAt : ∀ xi : HilbertBlockL2 (U : Set (Vec d)),
      Measurable fun omega : Omega => g omega xi := by
    intro xi
    obtain ⟨F, hF, hF1, hF2, hFeq⟩ := exists_memBlockL2_toHilbertBlockL2OfBlockField_eq xi
    set W : DoubledField d :=
      { potential := fun x => (F x).1, flux := fun x => (F x).2 } with hWdef
    have hWeval : (blockStateOfDoubled W).eval = F := by
      funext x
      exact Prod.ext rfl rfl
    have hWmem : MemBlockL2 (U : Set (Vec d)) (blockStateOfDoubled W).eval := by
      rw [hWeval]; exact hF
    have hclassW : toHilbertBlockL2OfBlockField hWmem = xi := by
      rw [← hFeq]
      rfl
    have hrw : (fun omega : Omega => g omega xi)
        = fun omega : Omega => doubledMuValue U (a omega) W := by
      funext omega
      rw [← hclassW, hgval omega W hWmem]
    rw [hrw]
    exact hfixed W hF1 hF2
  have hjoint : Measurable (Function.uncurry
      (fun (xi : HilbertBlockL2 (U : Set (Vec d))) (omega : Omega) => g omega xi)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun omega => hgcont omega) hmeasAt
  have hcomp : Measurable fun omega : Omega =>
      g omega (toHilbertBlockL2OfBlockField (hX omega)) :=
    hjoint.comp (hclass.prodMk measurable_id)
  have hfin : (fun omega : Omega => doubledMuValue U (a omega) (X omega))
      = fun omega : Omega => g omega (toHilbertBlockL2OfBlockField (hX omega)) := by
    funext omega
    exact (hgval omega (X omega) (hX omega)).symm
  rw [hfin]
  exact hcomp

/-- **The Step-2 instantiation.**  At the cell coefficient `meshCellCoeff M m R`
the fixed-competitor measurability is proved
(`LocalizationFluctuationJointCoeff.measurable_doubledMuValue_meshCellCoeff`),
so a measurable `L^2` class of the competitor is all that is needed.

This is the joint-measurability layer's payoff: it turns the `hcomp` binder of
`LocalizationFluctuationMuMeasCell.integrable_meshFluctuationCellIntegrand'`, and
the measurability half of that lemma's `hbg` binder, into the single statement
"the background field's `L^2` class is a measurable function of the sample". -/
theorem measurable_doubledMuValue_meshCellCoeff_of_measurable_class [NeZero d]
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    [MeasurableSpace (HilbertBlockL2 ((cubeDomain R : Domain d) : Set (Vec d)))]
    [BorelSpace (HilbertBlockL2 ((cubeDomain R : Domain d) : Set (Vec d)))]
    (X : CutoffSample d → DoubledField d)
    (hX : ∀ omega, MemBlockL2 ((cubeDomain R : Domain d) : Set (Vec d))
      (blockStateOfDoubled (X omega)).eval)
    (hclass : Measurable fun omega => toHilbertBlockL2OfBlockField (hX omega)) :
    Measurable fun omega : CutoffSample d =>
      doubledMuValue (cubeDomain R) (meshCellCoeff M m R omega) (X omega) :=
  measurable_doubledMuValue_of_measurable_class (cubeDomain R)
    (fun omega => meshCellCoeff M m R omega) X hX hclass
    (fun W hpot hflux => measurable_doubledMuValue_meshCellCoeff M m R W hpot hflux)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
