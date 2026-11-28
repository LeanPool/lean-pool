/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Coherent risk measures: the four axioms of Artzner, Delbaen, Eber and Heath

A **coherent risk measure** on the integrable losses of a measure space `(Ω, P)` is a functional
`ρ : (Ω → ℝ) → ℝ` with the four axioms of Artzner, Delbaen, Eber and Heath, *Coherent measures of
risk*, Math. Finance **9** (1999), in the convention of McNeil, Frey and Embrechts (*Quantitative
Risk Management*, Definition 2.18): a **loss** is signed as a loss, so a larger `X` is worse and
`ρ` increases with it.

* `mono`: `X ≤ Y` almost surely gives `ρ X ≤ ρ Y`;
* `add_const`: `ρ (X + m) = ρ X + m`, so `ρ X` is the capital that makes the loss `X` acceptable;
* `const_mul`: `ρ (c X) = c ρ X` for `c ≥ 0`;
* `add_le`: `ρ (X + Y) ≤ ρ X + ρ Y`.

This is the one coherence structure of the library: value-at-risk's cousin expected shortfall, the
spectral risk measures, worst-case loss and the acceptance-set theory
(`Risk/AcceptanceSet.lean`) all land in it. The older *positions* convention of the ADEH
paper (a position `X` is a gain, its loss is `−X`; `ρ` decreases with `X` and
`ρ (X + m) = ρ X − m`) is the same object at `L ↦ ρ(−L)` on a finite state space with counting
measure; `Risk/PositionsConvention.lean` proves that.

The axioms only constrain `ρ` on integrable losses, and almost-sure monotonicity is the weakest
order that makes `ρ` a function of the loss's law. On a finite state space with a finite measure
every function is integrable and the order is still implied by the pointwise order, so the
finite-state theory (`IsCoherentRiskMeasure.mono_of_le`, `IsCoherentRiskMeasure.continuous`) needs
no support hypothesis.

## Main definitions

* `IsConvexRiskMeasure`: the base object of the theory (Föllmer and Schied 2002): almost-sure
  monotonicity, translation `ρ (X + m) = ρ X + m`, and convexity on the integrable losses.
* `IsCoherentRiskMeasure`: the four axioms of a coherent risk measure `ρ` of losses on a measure
  space `(Ω, P)`: almost-sure monotonicity, translation `ρ (X + m) = ρ X + m`, positive
  homogeneity `ρ (c X) = c ρ X` for `c ≥ 0`, and subadditivity.

## Main results

* `IsCoherentRiskMeasure.toIsConvexRiskMeasure`: a coherent risk measure is a convex one (a parent
  projection).
* `IsCoherentRiskMeasure.rho_zero`: `ρ 0 = 0`.
* `convexOn_of_const_mul_of_add_le`: positive homogeneity and subadditivity give convexity.
* `IsCoherentRiskMeasure.mono_of_le`, `IsCoherentRiskMeasure.continuous`: on a finite state space
  `ρ` is pointwise-monotone and continuous.

## Tags

coherent risk measure, Artzner-Delbaen-Eber-Heath, subadditivity, translation invariance,
positive homogeneity, monotonicity, capital requirement, MSC 91G70, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A measure that charges every point of a countable space sees all of it: a property holds
almost everywhere exactly when it holds everywhere. Counting measure is the case `P {ω} = 1`. -/
lemma ae_iff_forall_of_singleton_ne_zero {P : Measure Ω} {p : Ω → Prop} [Countable Ω]
    (hP : ∀ ω, P {ω} ≠ 0) : (∀ᵐ ω ∂P, p ω) ↔ ∀ ω, p ω :=
  ae_iff_of_countable.trans <| forall_congr' fun ω ↦ ⟨fun h ↦ h (hP ω), fun h _ ↦ h⟩

/-- The three axioms of a **convex risk measure** (Föllmer and Schied, *Convex measures of risk
and trading constraints*, Finance Stoch. 6 (2002)) for a functional `ρ` on the integrable losses of
`(Ω, P)`, in the loss convention of `IsCoherentRiskMeasure`: almost-sure monotonicity,
translation `ρ (X + m) = ρ X + m`, and convexity. This is the base object: the entropic risk
measure and shortfall risk are convex and not coherent, and `IsCoherentRiskMeasure` extends it
with positive homogeneity and subadditivity. -/
structure IsConvexRiskMeasure (P : Measure Ω) (ρ : (Ω → ℝ) → ℝ) : Prop where
  mono : ∀ ⦃X Y : Ω → ℝ⦄, Integrable X P → Integrable Y P → X ≤ᵐ[P] Y → ρ X ≤ ρ Y
  add_const : ∀ ⦃X : Ω → ℝ⦄, Integrable X P → ∀ m : ℝ, ρ (fun ω ↦ X ω + m) = ρ X + m
  convexOn : ConvexOn ℝ {X | Integrable X P} ρ

/-- Positive homogeneity and subadditivity give convexity on the integrable losses. -/
lemma convexOn_of_const_mul_of_add_le {P : Measure Ω} {ρ : (Ω → ℝ) → ℝ}
    (const_mul : ∀ ⦃X : Ω → ℝ⦄, Integrable X P → ∀ ⦃c : ℝ⦄, 0 ≤ c →
      ρ (fun ω ↦ c * X ω) = c * ρ X)
    (add_le : ∀ ⦃X Y : Ω → ℝ⦄, Integrable X P → Integrable Y P →
      ρ (fun ω ↦ X ω + Y ω) ≤ ρ X + ρ Y) :
    ConvexOn ℝ {X | Integrable X P} ρ := by
  refine ⟨fun x hx y hy a b _ _ _ ↦ ?_, fun x hx y hy a b ha hb _ ↦ ?_⟩
  · exact (hx.smul a).add (hy.smul b)
  · have h := add_le (hx.const_mul a) (hy.const_mul b)
    rw [const_mul hx ha, const_mul hy hb] at h
    exact h

/-- The four axioms of a **coherent risk measure** (Artzner, Delbaen, Eber and Heath 1999;
McNeil–Frey–Embrechts, Definition 2.18) for a functional `ρ` on the integrable losses of
`(Ω, P)`: monotonicity, translation invariance, positive homogeneity and subadditivity. A loss is
signed as a loss, so a larger `X` is worse and `ρ` increases with it. It is a convex risk measure
(`toIsConvexRiskMeasure`): convexity is the default of that field, derived from positive
homogeneity and subadditivity, so a constructor supplies the four axioms only. -/
structure IsCoherentRiskMeasure (P : Measure Ω) (ρ : (Ω → ℝ) → ℝ) : Prop
    extends IsConvexRiskMeasure P ρ where
  const_mul : ∀ ⦃X : Ω → ℝ⦄, Integrable X P → ∀ ⦃c : ℝ⦄, 0 ≤ c →
    ρ (fun ω ↦ c * X ω) = c * ρ X
  add_le : ∀ ⦃X Y : Ω → ℝ⦄, Integrable X P → Integrable Y P →
    ρ (fun ω ↦ X ω + Y ω) ≤ ρ X + ρ Y
  convexOn := convexOn_of_const_mul_of_add_le const_mul add_le

namespace IsCoherentRiskMeasure

variable {P : Measure Ω} {ρ : (Ω → ℝ) → ℝ}

/-- `ρ 0 = 0` (positive homogeneity at `c = 2`). -/
lemma rho_zero (hρ : IsCoherentRiskMeasure P ρ) : ρ 0 = 0 := by
  have h := hρ.const_mul (integrable_zero Ω ℝ P) (c := 2) (by norm_num)
  rw [show (fun ω ↦ 2 * (0 : Ω → ℝ) ω) = 0 by ext; simp] at h
  linarith

section Finite

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {P : Measure ι} [IsFiniteMeasure P] {ρ : (ι → ℝ) → ℝ}

omit [Fintype ι] in
/-- On a finite state space a pointwise smaller loss has the smaller risk: pointwise order implies
almost-sure order, and every function is integrable. -/
lemma mono_of_le [Finite ι] (hρ : IsCoherentRiskMeasure P ρ) {X Y : ι → ℝ} (h : X ≤ Y) :
    ρ X ≤ ρ Y :=
  hρ.mono .of_finite .of_finite (ae_of_all _ h)

omit [Fintype ι] in
/-- A finite-state coherent risk measure is convex on all of `ℝ^ι`. -/
lemma convexOn_univ [Finite ι] (hρ : IsCoherentRiskMeasure P ρ) : ConvexOn ℝ Set.univ ρ := by
  simpa [show {X : ι → ℝ | Integrable X P} = Set.univ from
    Set.eq_univ_of_forall fun _ ↦ .of_finite] using hρ.convexOn

omit [Fintype ι] in
/-- A finite-state coherent risk measure is continuous (a finite convex function on `ℝ^ι`). -/
lemma continuous [Finite ι] (hρ : IsCoherentRiskMeasure P ρ) : Continuous ρ := by
  have := Fintype.ofFinite ι
  rw [← continuousOn_univ]
  exact hρ.convexOn_univ.continuousOn isOpen_univ

end Finite

end IsCoherentRiskMeasure

end MathFin
