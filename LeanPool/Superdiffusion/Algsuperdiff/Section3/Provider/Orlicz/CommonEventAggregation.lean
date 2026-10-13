/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.CommonEventOrlicz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.CommonEnvelope
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.TailSqrt

/-!
# CommonEventAggregation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Countable aggregation of weak-Orlicz bounds onto one common event

That is the content of
`Algsuperdiff.Section3.Probability.IsCommonEventTwoTermBigOWith`, and this
module is the first A on that carrier:

* amplitude monotonicity, at fixed envelopes and fixed common event;
* absorption of a nonnegative deterministic shift into the first amplitude,
  with no side condition;
* transfer along an almost-sure pointwise domination by members of an already
  bounded family, the step by which an arbitrary --- possibly uncountable ---
  index type inherits a bound obtained for a countable one, the index
  quantifier staying *inside* the event;
* the countable aggregation itself, at the amplitudes
  `C_triangle(sigma) * sum a`.

The two Orlicz terms stay separate and one-sided
throughout: the two lanes are never merged.  Positivity of the individual
amplitudes is never a hypothesis; it is carried by each two-term datum.  The
passage from the one-sided `IsBigOWith` of the weak-Orlicz notation to the
two-sided `IsBigO` required by the envelope engine is done by replacing each
lane by its positive part, and its one-sided half is *consumed*, not
re-derived: it is the public `isBigOWith_max_zero` of
`Provider/Tail/TailSqrt.lean`.

Nothing in this module refers to Section 3.5.  Typing data: the abstract
carriers `Omega`, `mu`, `Psi1`, `Psi2`, the index types, the families and the
amplitudes.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport
open _root_.HCPolySupport.IndependentSums
open Algsuperdiff.Section3

noncomputable section

section Abstract

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The one-sided weak-Orlicz relation transfers to the positive part as a
two-sided relation, at the same amplitude.

The weak-Orlicz notation of the ABK26 Appendix controls only the upper tail,
while a countable envelope has to be built from absolute values.  Replacing a
lane by its positive part costs nothing: the two upper-tail events agree above
every positive threshold, and the positive part still dominates the lane. -/
theorem isBigO_posPart_of_isBigOWith {Psi : ℝ → ℝ} {Y : Omega → ℝ} {A : ℝ}
    (hA : 0 < A) (hY : IsBigOWith mu Psi Y A) :
    IsBigO mu Psi (fun omega => max (Y omega) 0) A := by
  have h := Algsuperdiff.Section3.Provider.Tail.isBigOWith_max_zero hA hY
  have heq : (fun omega => |max (Y omega) 0|) = fun omega => max 0 (Y omega) := by
    funext omega
    rw [abs_of_nonneg (le_max_right _ _), max_comm]
  show IsBigOWith mu Psi (fun omega => |max (Y omega) 0|) A
  rw [heq]
  exact h

/-- Amplitude monotonicity for the common-event two-term relation.  The two
envelopes and the common event are unchanged; only the two scales grow. -/
theorem isCommonEventTwoTermBigOWith_mono_scale {I : Type*} [IsFiniteMeasure mu]
    {Psi1 Psi2 : ℝ → ℝ} {X : I → Omega → ℝ} {A1 A2 B1 B2 : ℝ}
    (hX : Probability.IsCommonEventTwoTermBigOWith mu Psi1 Psi2 X A1 A2)
    (h1 : A1 ≤ B1) (h2 : A2 ≤ B2) :
    Probability.IsCommonEventTwoTermBigOWith mu Psi1 Psi2 X B1 B2 := by
  obtain ⟨Y, Z, hPsi1, hPsi2, hA1, hA2, hXm, hYm, hZm, hdom, hYt, hZt⟩ := hX
  exact ⟨Y, Z, hPsi1, hPsi2, lt_of_lt_of_le hA1 h1, lt_of_lt_of_le hA2 h2, hXm,
    hYm, hZm, hdom, hYt.mono_scale h1, hZt.mono_scale h2⟩

/-- A nonnegative deterministic shift is absorbed by the first lane at the cost
of the same shift in its amplitude.

This is the absorption performed at ABK26, where the deterministic mean bound
`(1/2) epsilon E^2 gamma` produced by the iteration is added to the fluctuation
estimate and the sum is rewritten as a single `Gamma_1` term. -/
theorem isCommonEventTwoTermBigOWith_add_const {I : Type*} [IsFiniteMeasure mu]
    {Psi1 Psi2 : ℝ → ℝ} {X : I → Omega → ℝ} {A1 A2 c : ℝ}
    (hX : Probability.IsCommonEventTwoTermBigOWith mu Psi1 Psi2 X A1 A2)
    (hc : 0 ≤ c) :
    Probability.IsCommonEventTwoTermBigOWith mu Psi1 Psi2
      (fun i omega => X i omega + c) (A1 + c) A2 := by
  obtain ⟨Y, Z, hPsi1, hPsi2, hA1, hA2, hXm, hYm, hZm, hdom, hYt, hZt⟩ := hX
  refine ⟨fun omega => Y omega + c, Z, hPsi1, hPsi2, by linarith, hA2,
    fun i => (hXm i).add_const c, hYm.add_const c, hZm, ?_, ?_, hZt⟩
  · filter_upwards [hdom] with omega homega
    intro i
    have := homega i
    linarith
  · intro t ht
    refine (measureReal_mono ?_).trans (hYt ht)
    intro omega homega
    have hlt : (A1 + c) * t < Y omega + c := homega
    have hct : c ≤ c * t := le_mul_of_one_le_right hc ht
    show A1 * t < Y omega
    nlinarith

/-- Transfer of a common-event two-term bound along an almost-sure pointwise
domination by members of the bounded family.

The new family may be indexed by an arbitrary type: the domination is one
almost-sure statement whose index quantifier sits *inside* the event, so no
intersection over the new index is taken.  This is the step that lets an
uncountable index inherit the bound obtained for a countable one. -/
theorem isCommonEventTwoTermBigOWith_of_ae_forall_exists_le {I J : Type*}
    {Psi1 Psi2 : ℝ → ℝ} {W : J → Omega → ℝ} {X : I → Omega → ℝ} {A1 A2 : ℝ}
    (hW : Probability.IsCommonEventTwoTermBigOWith mu Psi1 Psi2 W A1 A2)
    (hXm : ∀ i, Measurable (X i))
    (hle : ∀ᵐ omega ∂mu, ∀ i : I, ∃ j : J, X i omega ≤ W j omega) :
    Probability.IsCommonEventTwoTermBigOWith mu Psi1 Psi2 X A1 A2 := by
  obtain ⟨Y, Z, hPsi1, hPsi2, hA1, hA2, -, hYm, hZm, hdom, hYt, hZt⟩ := hW
  refine ⟨Y, Z, hPsi1, hPsi2, hA1, hA2, hXm, hYm, hZm, ?_, hYt, hZt⟩
  filter_upwards [hdom, hle] with omega hdomega hleomega
  intro i
  obtain ⟨j, hj⟩ := hleomega i
  exact hj.trans (hdomega j)

/-- **The countable aggregation.**  A sequence of one-sided two-term
weak-Orlicz bounds with summable amplitudes admits one pair of measurable
envelopes dominating every member on a single event of probability one, at the
two amplitudes `C_triangle(sigma) * sum a`.

Positivity of the individual amplitudes is not a hypothesis: it is carried by
each two-term datum.  No independence between the members is used. -/
theorem isCommonEventTwoTermBigOWith_of_summable_isTwoTermBigOWith
    [IsProbabilityMeasure mu] {sigmaOne sigmaTwo : ℝ}
    (hsigmaOne : 0 < sigmaOne) (hsigmaTwo : 0 < sigmaTwo)
    {aOne aTwo : ℕ → ℝ} (haOne : Summable aOne) (haTwo : Summable aTwo)
    {W : ℕ → Omega → ℝ}
    (hW : ∀ j, Probability.IsTwoTermBigOWith mu (gammaSigma sigmaOne)
      (gammaSigma sigmaTwo) (W j) (aOne j) (aTwo j)) :
    Probability.IsCommonEventTwoTermBigOWith mu (gammaSigma sigmaOne)
      (gammaSigma sigmaTwo) W
      (gammaTriangleConst sigmaOne * ∑' j, aOne j)
      (gammaTriangleConst sigmaTwo * ∑' j, aTwo j) := by
  classical
  choose Y Z hwit using hW
  have haOnePos : ∀ j, 0 < aOne j := fun j => (hwit j).2.2.1
  have haTwoPos : ∀ j, 0 < aTwo j := fun j => (hwit j).2.2.2.1
  have hWm : ∀ j, Measurable (W j) := fun j => (hwit j).2.2.2.2.1
  have hYm : ∀ j, Measurable (Y j) := fun j => (hwit j).2.2.2.2.2.1
  have hZm : ∀ j, Measurable (Z j) := fun j => (hwit j).2.2.2.2.2.2.1
  have hpt : ∀ j, ∀ omega, W j omega ≤ Y j omega + Z j omega :=
    fun j => (hwit j).2.2.2.2.2.2.2.1
  have hYt : ∀ j, IsBigOWith mu (gammaSigma sigmaOne) (Y j) (aOne j) :=
    fun j => (hwit j).2.2.2.2.2.2.2.2.1
  have hZt : ∀ j, IsBigOWith mu (gammaSigma sigmaTwo) (Z j) (aTwo j) :=
    fun j => (hwit j).2.2.2.2.2.2.2.2.2
  obtain ⟨SOne, STwo, hSOnem, hSTwom, hSOnedom, hSTwodom, hSOnet, hSTwot⟩ :=
    Provider.Orlicz.exists_twoChannel_commonEnvelope_of_summable
      (mu := mu) hsigmaOne hsigmaTwo (aOne := aOne) (aTwo := aTwo)
      haOnePos haTwoPos haOne haTwo
      (FOne := fun j omega => max (Y j omega) 0)
      (FTwo := fun j omega => max (Z j omega) 0)
      (fun j => ((hYm j).max measurable_const).aemeasurable)
      (fun j => ((hZm j).max measurable_const).aemeasurable)
      (fun j => isBigO_posPart_of_isBigOWith (haOnePos j) (hYt j))
      (fun j => isBigO_posPart_of_isBigOWith (haTwoPos j) (hZt j))
  refine ⟨SOne, STwo, Probability.isAdmissibleTail_gammaSigma hsigmaOne,
    Probability.isAdmissibleTail_gammaSigma hsigmaTwo,
    mul_pos gammaTriangleConst_pos
      (haOne.tsum_pos (fun j => (haOnePos j).le) 0 (haOnePos 0)),
    mul_pos gammaTriangleConst_pos
      (haTwo.tsum_pos (fun j => (haTwoPos j).le) 0 (haTwoPos 0)),
    hWm, hSOnem, hSTwom, ?_, hSOnet, hSTwot⟩
  have hall1 : ∀ᵐ omega ∂mu, ∀ j : ℕ, |max (Y j omega) 0| ≤ SOne omega :=
    (MeasureTheory.ae_all_iff).2 hSOnedom
  have hall2 : ∀ᵐ omega ∂mu, ∀ j : ℕ, |max (Z j omega) 0| ≤ STwo omega :=
    (MeasureTheory.ae_all_iff).2 hSTwodom
  filter_upwards [hall1, hall2] with omega h1 h2
  intro j
  calc W j omega ≤ Y j omega + Z j omega := hpt j omega
    _ ≤ max (Y j omega) 0 + max (Z j omega) 0 :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
    _ ≤ |max (Y j omega) 0| + |max (Z j omega) 0| :=
        add_le_add (le_abs_self _) (le_abs_self _)
    _ ≤ SOne omega + STwo omega := add_le_add (h1 j) (h2 j)

end Abstract

end

end Algsuperdiff.Section3.Provider.Homogenization
