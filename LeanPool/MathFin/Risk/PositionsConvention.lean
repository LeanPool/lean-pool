/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.Coherent

/-!
# Coherent risk measures of positions are coherent risk measures of losses

Artzner, Delbaen, Eber and Heath state coherence for **positions**: a position `X` is a gain, so
a risk measure `ρ` *decreases* in `X` (`X ≤ Y → ρ Y ≤ ρ X`) and adding cash `m` lowers the capital
requirement (`ρ (X + m) = ρ X − m`). The library's single coherence structure is stated for
**losses** (`IsCoherentRiskMeasure`, McNeil–Frey–Embrechts' convention), where `ρ` increases and
`ρ (L + m) = ρ L + m`. The two are one object seen through the sign flip `L = −X`.

`isCoherentRiskMeasure_neg_iff` makes that precise on a finite state space `ι` with a finite
measure that charges every state (counting measure is the model case), where almost-sure order is
pointwise order and every function is integrable: `ρ` satisfies
the four ADEH axioms for positions exactly when `L ↦ ρ (−L)` is an `IsCoherentRiskMeasure`.
The axioms of positions are written out rather than bundled in a second structure: bundling them
would be the duplicate that this module exists to remove. `Solution.lean` uses the statement to
discharge the positions-convention declarations of `Challenge.lean`, which may not import the
library.

## Main results

* `isCoherentRiskMeasure_neg_iff`: the four ADEH axioms for positions, written out, are
  equivalent to `IsCoherentRiskMeasure P (fun L ↦ ρ (-L))`, for any finite measure `P` with
  `P {i} ≠ 0` for every state `i`.

## References

* [P. Artzner et al., *Coherent measures of risk*][ArtznerDelbaenEberHeath1999]
* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Definition 2.18

## Tags

coherent risk measure, positions convention, Artzner-Delbaen-Eber-Heath, sign convention,
gains and losses, MSC 91G70, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory

/-- **Positions from losses.** On a finite state space, for any finite measure `P`, if
`L ↦ ρ (−L)` is a coherent risk measure of losses then `ρ` satisfies the four
Artzner–Delbaen–Eber–Heath axioms for positions (monotone decreasing, `ρ (X + m) = ρ X − m`,
positively homogeneous, subadditive). No support assumption: the converse is where the order on
almost-sure classes must be pointwise (`isCoherentRiskMeasure_neg_iff`). -/
theorem IsCoherentRiskMeasure.positions_of_neg {ι : Type*} [Finite ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {P : Measure ι} [IsFiniteMeasure P] {ρ : (ι → ℝ) → ℝ}
    (hρ : IsCoherentRiskMeasure P (fun L ↦ ρ (-L))) :
    (∀ X Y : ι → ℝ, (∀ i, X i ≤ Y i) → ρ Y ≤ ρ X) ∧
      (∀ (X : ι → ℝ) (m : ℝ), ρ (fun i ↦ X i + m) = ρ X - m) ∧
      (∀ l : ℝ, 0 ≤ l → ∀ X : ι → ℝ, ρ (l • X) = l * ρ X) ∧
      ∀ X Y : ι → ℝ, ρ (X + Y) ≤ ρ X + ρ Y := by
  refine ⟨fun X Y h ↦ ?_, fun X m ↦ ?_, fun l hl X ↦ ?_, fun X Y ↦ ?_⟩
  · simpa only [neg_neg] using
      hρ.mono_of_le (X := -Y) (Y := -X) fun i ↦ neg_le_neg (h i)
  · have h := hρ.add_const (X := -fun i ↦ X i + m) .of_finite m
    have e : (-fun ω ↦ (-fun i ↦ X i + m) ω + m) = X := by
      ext i; simp only [Pi.neg_apply]; ring
    change ρ (-fun ω ↦ (-fun i ↦ X i + m) ω + m) = ρ (-(-fun i ↦ X i + m)) + m at h
    rw [e, neg_neg] at h
    linarith
  · have h := hρ.const_mul (X := -X) .of_finite hl
    have e : (-fun ω ↦ l * (-X) ω) = l • X := by
      ext i; simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]; ring
    change ρ (-fun ω ↦ l * (-X) ω) = l * ρ (-(-X)) at h
    rwa [e, neg_neg] at h
  · have h := hρ.add_le (X := -X) (Y := -Y) .of_finite .of_finite
    have e : (-fun ω ↦ (-X) ω + (-Y) ω) = X + Y := by
      ext i; simp only [Pi.neg_apply, Pi.add_apply]; ring
    change ρ (-fun ω ↦ (-X) ω + (-Y) ω) ≤ ρ (-(-X)) + ρ (-(-Y)) at h
    rwa [e, neg_neg, neg_neg] at h

/-- **Positions versus losses.** On a finite state space with a finite measure `P` charging every
state (`P {i} ≠ 0`, so almost-sure order is the pointwise order), a functional
`ρ : (ι → ℝ) → ℝ` satisfies the four Artzner–Delbaen–Eber–Heath axioms for positions
(monotone decreasing, `ρ (X + m) = ρ X − m`, positively homogeneous, subadditive) if and only if
`L ↦ ρ (−L)` is a coherent risk measure of losses. -/
theorem isCoherentRiskMeasure_neg_iff {ι : Type*} [Finite ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {P : Measure ι} [IsFiniteMeasure P] (hP : ∀ i, P {i} ≠ 0)
    {ρ : (ι → ℝ) → ℝ} :
    IsCoherentRiskMeasure P (fun L ↦ ρ (-L)) ↔
      (∀ X Y : ι → ℝ, (∀ i, X i ≤ Y i) → ρ Y ≤ ρ X) ∧
      (∀ (X : ι → ℝ) (m : ℝ), ρ (fun i ↦ X i + m) = ρ X - m) ∧
      (∀ l : ℝ, 0 ≤ l → ∀ X : ι → ℝ, ρ (l • X) = l * ρ X) ∧
      ∀ X Y : ι → ℝ, ρ (X + Y) ≤ ρ X + ρ Y := by
  refine ⟨IsCoherentRiskMeasure.positions_of_neg, ?_⟩
  rintro ⟨hm, hc, hh, hs⟩
  refine
    { mono := fun X Y _ _ h ↦ ?_
      add_const := fun X _ m ↦ ?_
      const_mul := fun X _ c hc' ↦ ?_
      add_le := fun X Y _ _ ↦ ?_ }
  · exact hm (-Y) (-X) fun i ↦ neg_le_neg ((ae_iff_forall_of_singleton_ne_zero hP).1 h i)
  · have e : (-fun ω ↦ X ω + m) = fun i ↦ (-X) i + -m := by
      ext i; simp only [Pi.neg_apply]; ring
    change ρ (-fun ω ↦ X ω + m) = ρ (-X) + m
    rw [e, hc (-X) (-m)]
    ring
  · have e : (-fun ω ↦ c * X ω) = c • -X := by
      ext i; simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]; ring
    change ρ (-fun ω ↦ c * X ω) = c * ρ (-X)
    rw [e, hh c hc' (-X)]
  · have e : (-fun ω ↦ X ω + Y ω) = -X + -Y := by
      ext i; simp only [Pi.neg_apply, Pi.add_apply]; ring
    change ρ (-fun ω ↦ X ω + Y ω) ≤ ρ (-X) + ρ (-Y)
    rw [e]
    exact hs (-X) (-Y)

end MathFin
