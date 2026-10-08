/-
Copyright (c) 2026 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Bounds for essentially bounded functions

The norm bound and almost-everywhere evaluation bound apply to arbitrary measures
and normed additive groups. Both the half-line input API and periodic-mean examples
use this shared implementation.
-/

namespace AbstractLinearControl

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace ALCS

variable {α U : Type*} [MeasurableSpace α] [NormedAddCommGroup U] {μ : Measure α}

/-- The `L^∞` norm is bounded by any nonnegative a.e. bound. -/
lemma lp_norm_le {u : Lp U ∞ μ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ t ∂μ, ‖u t‖ ≤ C) : ‖u‖ ≤ C := by
  have htop : eLpNorm (⇑u) ∞ μ = eLpNormEssSup (⇑u) μ :=
    eLpNorm_exponent_top (Lp.aestronglyMeasurable u)
  rw [Lp.norm_def, htop]
  calc
    (eLpNormEssSup (⇑u) μ).toReal ≤ (ENNReal.ofReal C).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound hb)
    _ = C := ENNReal.toReal_ofReal hC

/-- The representative of an `L^∞` class obeys its norm bound a.e. -/
lemma ae_norm_le (u : Lp U ∞ μ) : ∀ᵐ t ∂μ, ‖u t‖ ≤ ‖u‖ := by
  have htop : eLpNorm (⇑u) ∞ μ = eLpNormEssSup (⇑u) μ :=
    eLpNorm_exponent_top (Lp.aestronglyMeasurable u)
  have hfinite : eLpNormEssSup (⇑u) μ ≠ ∞ := by
    rw [← htop]
    exact Lp.eLpNorm_ne_top u
  filter_upwards [enorm_ae_le_eLpNormEssSup (⇑u) μ] with t ht
  have ht' := ENNReal.toReal_mono hfinite ht
  simpa only [Lp.norm_def, htop, toReal_enorm] using ht'

end ALCS

end

end AbstractLinearControl
