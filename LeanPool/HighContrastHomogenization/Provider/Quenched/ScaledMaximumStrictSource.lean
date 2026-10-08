/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.ScaledMaximumTail

/-!
# High-contrast homogenization: Provider.Quenched.ScaledMaximumStrictSource

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# A scaled-maximum tail with a strict source event

The source-tail assumption in `CoarseEllipticityDagger` is strict.  This
variant uses the strict slack `cSrc < C` from the half-threshold argument
instead of strengthening that input to a closed tail event.
-/

namespace HCPolySupport.HighContrast.Quenched

open MeasureTheory
open IndependentSums

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Union bound for a scaled normalized maximum, with a closed mixing tail and
a strict source tail.  No independence between the random scales is needed. -/
theorem measureReal_scaled_max_one_tail_le_of_source_lt
    {P : Measure Ω} [IsFiniteMeasure P]
    {Rmix Ssrc : Ω → ℝ} {L C cMix cSrc cd η t : ℝ} {Ψ : ℝ → ℝ}
    (hL : 0 < L) (ht : 1 ≤ t) (hC : 1 < C)
    (hcMix : cMix ≤ C) (hcSrc : cSrc < C)
    (hmix :
      P.real {ω | cMix * t ≤ Rmix ω} ≤ Real.exp (-cd * t ^ η))
    (hsrc :
      P.real (upperTailEvent Ssrc (cSrc * t)) ≤ (Ψ (cSrc * t))⁻¹) :
    P.real {ω | C * L * t ≤ L * max 1 (max (Rmix ω) (Ssrc ω))} ≤
      Real.exp (-cd * t ^ η) + (Ψ (cSrc * t))⁻¹ := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hCt : 1 < C * t := by
    calc
      1 < C := hC
      _ = C * 1 := by ring
      _ ≤ C * t :=
        mul_le_mul_of_nonneg_left ht (zero_le_one.trans hC.le)
  have hsubset :
      {ω | C * L * t ≤ L * max 1 (max (Rmix ω) (Ssrc ω))} ⊆
        {ω | cMix * t ≤ Rmix ω} ∪ upperTailEvent Ssrc (cSrc * t) := by
    intro ω hω
    have hmax : C * t ≤ max 1 (max (Rmix ω) (Ssrc ω)) := by
      apply le_of_mul_le_mul_left _ hL
      simpa only [mul_assoc, mul_left_comm, mul_comm, Set.mem_ofPred_eq] using hω
    have hrs : C * t ≤ max (Rmix ω) (Ssrc ω) := by
      rcases le_max_iff.mp hmax with hone | hrs
      · exact False.elim (hCt.not_ge hone)
      · exact hrs
    rcases le_max_iff.mp hrs with hRmix | hSsrc
    · exact Or.inl ((mul_le_mul_of_nonneg_right hcMix ht0.le).trans hRmix)
    · exact Or.inr <| (mul_lt_mul_of_pos_right hcSrc ht0).trans_le hSsrc
  calc
    P.real {ω | C * L * t ≤ L * max 1 (max (Rmix ω) (Ssrc ω))}
        ≤ P.real ({ω | cMix * t ≤ Rmix ω} ∪
            upperTailEvent Ssrc (cSrc * t)) :=
      measureReal_mono hsubset
    _ ≤ P.real {ω | cMix * t ≤ Rmix ω} +
          P.real (upperTailEvent Ssrc (cSrc * t)) :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-cd * t ^ η) + (Ψ (cSrc * t))⁻¹ :=
      add_le_add hmix hsrc

end HCPolySupport.HighContrast.Quenched
