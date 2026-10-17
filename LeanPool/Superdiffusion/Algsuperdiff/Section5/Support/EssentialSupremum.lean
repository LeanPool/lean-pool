/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.HolderGauge

/-!
# EssentialSupremum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# On an open set the essential supremum of a continuous function is its supremum

The `L^∞` norm of a Sobolev function on an open set is an essential supremum: it
does not see a null set, so it is attached to the almost-everywhere class and not
to any pointwise choice.  When the class has a representative continuous on the
open set, the essential supremum is the *pointwise* supremum of that
representative: the two inequalities are the almost-everywhere bound in one
direction and, in the other, the fact that a nonempty open subset of `ℝ^d` has
positive volume, so no continuous function can exceed its essential supremum on a
null set only.

This is what lets the localized error of Section 5.1 be stated as the honest
essential supremum of the Sobolev functions while still being computed, where a
continuous representative exists, from pointwise values.

## Main results

* `eLpNorm_top_restrict_le_supNormOn` — the elementary direction.
* `supNormOn_le_eLpNorm_top_restrict` — the direction that uses continuity.
* `eLpNorm_top_restrict_eq_supNormOn`, `eLpNorm_top_restrict_eq_supNormOn_of_ae`.

## References

* ABK26, the localized error of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The essential supremum never exceeds the pointwise supremum.** -/
theorem eLpNorm_top_restrict_le_supNormOn {U : Set (Vec d)} (hU : MeasurableSet U)
    (f : Vec d → ℝ) (hf : AEStronglyMeasurable f (volume.restrict U)) :
    eLpNorm f ⊤ (volume.restrict U) ≤ supNormOn U f := by
  rw [eLpNorm_exponent_top hf]
  refine essSup_le_of_ae_le _ ((ae_restrict_iff' hU).2 ?_)
  refine Filter.Eventually.of_forall fun x hx => ?_
  change ‖f x‖ₑ ≤ supNormOn U f
  rw [← ofReal_norm]
  exact le_supNormOn hx

/-- **On an open set a continuous function does not exceed its essential
supremum.**  Otherwise it would exceed it on a nonempty open set, which has
positive volume. -/
theorem supNormOn_le_eLpNorm_top_restrict {U : Set (Vec d)} (hU : IsOpen U)
    {f : Vec d → ℝ} (hf : ContinuousOn f U) :
    supNormOn U f ≤ eLpNorm f ⊤ (volume.restrict U) := by
  rw [eLpNorm_exponent_top (hf.aestronglyMeasurable hU.measurableSet)]
  refine supNormOn_le_iff.2 fun x hx => ?_
  by_contra hcon
  push Not at hcon
  have hctop : eLpNormEssSup f (volume.restrict U) ≠ ⊤ := hcon.ne_top
  have ht0 : (0 : ℝ) ≤ (eLpNormEssSup f (volume.restrict U)).toReal := ENNReal.toReal_nonneg
  have hlt : (eLpNormEssSup f (volume.restrict U)).toReal < ‖f x‖ := by
    have hcon' := hcon
    rw [← ENNReal.ofReal_toReal hctop] at hcon'
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht0).1 hcon'
  have hae : ∀ᵐ z ∂(volume.restrict U), ‖f z‖ₑ ≤ eLpNormEssSup f (volume.restrict U) :=
    ae_le_essSup
  have hzero :
      volume ({z | ¬ ‖f z‖ₑ ≤ eLpNormEssSup f (volume.restrict U)} ∩ U) = 0 := by
    have hres :
        (volume.restrict U) {z | ¬ ‖f z‖ₑ ≤ eLpNormEssSup f (volume.restrict U)} = 0 := by
      rw [ae_iff] at hae
      exact hae
    rwa [Measure.restrict_apply₀' hU.measurableSet.nullMeasurableSet] at hres
  obtain ⟨W, hWopen, hW⟩ :=
    continuousOn_iff'.1 hf.norm
      (Set.Ioi (((eLpNormEssSup f (volume.restrict U)).toReal + ‖f x‖) / 2)) isOpen_Ioi
  have hSopen : IsOpen ((fun z => ‖f z‖) ⁻¹'
      Set.Ioi (((eLpNormEssSup f (volume.restrict U)).toReal + ‖f x‖) / 2) ∩ U) := by
    rw [hW]
    exact hWopen.inter hU
  have hxS : x ∈ (fun z => ‖f z‖) ⁻¹'
      Set.Ioi (((eLpNormEssSup f (volume.restrict U)).toReal + ‖f x‖) / 2) ∩ U := by
    refine ⟨?_, hx⟩
    change ((eLpNormEssSup f (volume.restrict U)).toReal + ‖f x‖) / 2 < ‖f x‖
    linarith
  have hpos : 0 < volume ((fun z => ‖f z‖) ⁻¹'
      Set.Ioi (((eLpNormEssSup f (volume.restrict U)).toReal + ‖f x‖) / 2) ∩ U) :=
    hSopen.measure_pos volume ⟨x, hxS⟩
  have hsub : (fun z => ‖f z‖) ⁻¹'
      Set.Ioi (((eLpNormEssSup f (volume.restrict U)).toReal + ‖f x‖) / 2) ∩ U ⊆
      {z | ¬ ‖f z‖ₑ ≤ eLpNormEssSup f (volume.restrict U)} ∩ U := by
    rintro z ⟨hz1, hz2⟩
    refine ⟨?_, hz2⟩
    change ¬ ‖f z‖ₑ ≤ eLpNormEssSup f (volume.restrict U)
    rw [not_le, ← ofReal_norm, ← ENNReal.ofReal_toReal hctop]
    refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht0).2 ?_
    have hz1' : ((eLpNormEssSup f (volume.restrict U)).toReal + ‖f x‖) / 2 < ‖f z‖ := hz1
    linarith
  exact absurd (measure_mono_null hsub hzero) hpos.ne'

/-- **The `L^∞` norm on an open set is the supremum of a continuous
representative.** -/
theorem eLpNorm_top_restrict_eq_supNormOn {U : Set (Vec d)} (hU : IsOpen U)
    {f : Vec d → ℝ} (hf : ContinuousOn f U) :
    eLpNorm f ⊤ (volume.restrict U) = supNormOn U f :=
  le_antisymm (eLpNorm_top_restrict_le_supNormOn hU.measurableSet f
      (hf.aestronglyMeasurable hU.measurableSet))
    (supNormOn_le_eLpNorm_top_restrict hU hf)

/-- The same, reading the `L^∞` norm of a function through a continuous function
equal to it away from a null set. -/
theorem eLpNorm_top_restrict_eq_supNormOn_of_ae {U : Set (Vec d)} (hU : IsOpen U)
    {f g : Vec d → ℝ} (hae : g =ᵐ[volume.restrict U] f) (hg : ContinuousOn g U) :
    eLpNorm f ⊤ (volume.restrict U) = supNormOn U g := by
  rw [← eLpNorm_congr_ae hae]
  exact eLpNorm_top_restrict_eq_supNormOn hU hg

end

end Algsuperdiff.Section5.Support
