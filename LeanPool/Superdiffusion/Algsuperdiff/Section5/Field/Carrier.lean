/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.SharpTailGrowth
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.TailProbability

/-!
# Carrier

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The sample carrier of the full stream matrix

`Algsuperdiff.Section3.Cutoff.CutoffSample` carries exactly the descending
convergence needed by the lower-infinite cutoffs `k_m = Σ_{n ≤ m} j_n`.  The
full normalized field `k(x) = Σ_{n ∈ ℤ} (j_n(x) - j_n(0))` needs the ascending
half as well, and needs it quantitatively, since the size of `k` on a cube of
scale `ℓ` is governed by the two tails at that scale.

This module adds the two ascending conditions to that carrier and builds the
resulting sample space and its law.  The carrier is the event itself: no value
is assigned off it, and every statement about the field is a statement on the
carrier.

## Main definitions

* `FullTailGood γ ω` — lower-tail goodness, the sharp two-sided rates, and the
  ascending gradient condition on the countable family of cubes `y + □_n` with
  `y` rational.
* `FullSample d γ` — the subtype of `CutoffSample d` cut out by `FullTailGood γ`.
* `fullSampleLaw M` — the induced probability law.

## Main results

* `measurableSet_fullTailGood`, `ae_fullTailGood` — the event is measurable and
  has full probability.
* `map_fullSampleLaw_val` — pushing the law forward recovers the cutoff-sample
  law, so every cutoff statement transports to the new carrier.

## References

* ABK26, the stream matrix and its scale decomposition.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The points of `Vec d` with rational coordinates: the countable family of
cube centres on which the ascending gradient condition is imposed. -/
def ratPoint (y : Fin d → ℚ) : Vec d := fun i => (y i : ℝ)

@[simp]
theorem ratPoint_zero : ratPoint (0 : Fin d → ℚ) = (0 : Vec d) := by
  ext i
  exact Rat.cast_zero

/-- **The full-tail event.**  Lower-tail goodness is already carried by the
ambient `CutoffSample`; this adds the ascending half in two forms.

The sharp conjunct gives one sample constant for the two pointwise shell rates
at every shell/cube crossover.  For an admissible model exponent those rates
imply the former quantitative two-leg growth condition.

The final conjunct is the ascending gradient condition on the countable family
of cubes `y + □_n` with rational centres.  It supplies local summability for the
field at an arbitrary exponent and is also the bridge to the
Section 5.1 large-scale event: it is that event on the same cubes, written with
bounded partial sums instead of a threshold, and
`exists_mem_largeScaleEvent_of_upperGradBounded` turns it into membership of
`Algsuperdiff.Section5.Support.largeScaleEvent` at a finite threshold, the form
the large-scale estimates consume.  It is carried on the field's carrier so
that the field and those estimates speak about one and the same sample. -/
def FullTailGood (gamma : ℝ) (omega : CutoffSample d) : Prop :=
  LowerTailGood omega.1 ∧ SharpTailGood gamma omega ∧
    ∀ (n : ℤ) (y : Fin d → ℚ), UpperGradBounded n (ratPoint y) omega

theorem fullTailGood_sharp {gamma : ℝ} {omega : CutoffSample d}
    (h : FullTailGood gamma omega) : SharpTailGood gamma omega := h.2.1

theorem fullTailGood_upperGrad {gamma : ℝ} {omega : CutoffSample d}
    (h : FullTailGood gamma omega) (n : ℤ) (y : Fin d → ℚ) :
    UpperGradBounded n (ratPoint y) omega := h.2.2 n y

/-- The measurable set cut out by the full-tail event. -/
def fullTailGoodSet (d : ℕ) (gamma : ℝ) : Set (CutoffSample d) :=
  {omega | FullTailGood gamma omega}

theorem measurableSet_fullTailGood (d : ℕ) (gamma : ℝ) :
    MeasurableSet (fullTailGoodSet d gamma) := by
  have hrw : fullTailGoodSet d gamma =
      {omega : CutoffSample d | SharpTailGood gamma omega} ∩
        ⋂ n : ℤ, ⋂ y : Fin d → ℚ,
          {omega : CutoffSample d | UpperGradBounded n (ratPoint y) omega} := by
    ext omega
    simp only [fullTailGoodSet, FullTailGood, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_iInter]
    exact and_iff_right omega.2
  rw [hrw]
  exact (measurableSet_sharpTailGood gamma).inter
    (MeasurableSet.iInter fun n =>
      MeasurableSet.iInter fun y => measurableSet_upperGradBounded n (ratPoint y))

/-- **The full-tail event has probability one.** -/
theorem ae_fullTailGood (M : ABKModel d) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure, FullTailGood M.gamma omega := by
  have hsharp := ae_sharpTailGood M
  have hupper : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ (n : ℤ) (y : Fin d → ℚ), UpperGradBounded n (ratPoint y) omega :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun y => ae_upperGradBounded M n (ratPoint y)
  filter_upwards [hsharp, hupper] with omega h1 h2
  exact ⟨omega.2, h1, h2⟩

/-! ## The carrier and its law -/

/-- **The sample carrier of the full stream matrix**: the elements of the
cutoff-sample carrier on which both tails of the scale decomposition converge,
the ascending one quantitatively. -/
abbrev FullSample (d : ℕ) (gamma : ℝ) :=
  {omega : CutoffSample d // FullTailGood gamma omega}

/-- On the carrier at the exponent of an ABK model, the sharp rates recover
the original quantitative two-leg growth condition. -/
theorem fullTailGood_growth (M : ABKModel d) (omega : FullSample d M.gamma) :
    ∃ C : ℕ, StreamGrowthBounded C omega.1 :=
  exists_streamGrowthBounded_of_sharpTailGood M (fullTailGood_sharp omega.2)

theorem ae_mem_range_fullSample_val (M : ABKModel d) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      omega ∈ Set.range (Subtype.val : FullSample d M.gamma → CutoffSample d) := by
  filter_upwards [ae_fullTailGood M] with omega homega
  exact ⟨⟨omega, homega⟩, rfl⟩

/-- The canonical probability law restricted to the full-tail carrier. -/
noncomputable def fullSampleLaw (M : ABKModel d) : ProbabilityMeasure (FullSample d M.gamma) :=
  ⟨Measure.comap (Subtype.val : FullSample d M.gamma → CutoffSample d)
      (cutoffSampleLaw M).toMeasure,
    (MeasurableEmbedding.subtype_coe
      (measurableSet_fullTailGood d M.gamma)).isProbabilityMeasure_comap
      (ae_mem_range_fullSample_val M)⟩

/-- Pushing the induced full-sample law forward along `Subtype.val` recovers the
cutoff-sample law. -/
theorem map_fullSampleLaw_val (M : ABKModel d) :
    Measure.map (Subtype.val : FullSample d M.gamma → CutoffSample d)
        (fullSampleLaw M).toMeasure = (cutoffSampleLaw M).toMeasure := by
  calc
    Measure.map (Subtype.val : FullSample d M.gamma → CutoffSample d)
        (fullSampleLaw M).toMeasure =
        (cutoffSampleLaw M).toMeasure.restrict {omega | FullTailGood M.gamma omega} :=
      map_comap_subtype_coe (measurableSet_fullTailGood d M.gamma)
        (cutoffSampleLaw M).toMeasure
    _ = (cutoffSampleLaw M).toMeasure :=
      Measure.restrict_eq_self_of_ae_mem (ae_fullTailGood M)

end

end Algsuperdiff.Section5.Field
