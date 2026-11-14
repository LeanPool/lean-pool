/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.PercolationScale

/-!
# ExitTimeHomogenizationJointEvent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Monotonicity of the good cube event in its two parameters

The percolation estimate counts the sites at which the event

```text
  Q(z + □_n, ε) = 𝒢(z + □_n, ε) ∩ 𝒥(z + □_n, C⁻¹ ε γ^{-1/2})
```

occurs, and the exit-time comparison on a good cube is stated on the same
event with its own constant in place of `C`.  The two therefore speak the same
event as soon as the two constants agree, and where they do not agree the
inclusions of this file convert one into the other: the event grows with the
accuracy `ε` and shrinks as the constant `C` grows, because `C` enters only
through the threshold `C⁻¹ ε γ^{-1/2}` of the large-scale event.

The consequence used downstream is the rescaling of the accuracy: replacing
`ε` by `ε / max 1 C` turns the event formed with the constant `1` into the
event formed with the constant `C`, at every centre and every scale.

## References

* ABK26, the chains of good cubes of Section 5.2.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The two halves -/

/-- **The large-scale event grows with its threshold.** -/
theorem largeScaleEventBase_mono (M : ABKModel d) (n : ℤ) {theta theta' : ℝ}
    (h : theta ≤ theta') :
    largeScaleEventBase M n theta ⊆ largeScaleEventBase M n theta' := by
  intro omega homega
  exact le_trans homega (ENNReal.ofReal_le_ofReal h)

/-- **The large-scale event on a translated cube grows with its threshold.** -/
theorem largeScaleEvent_mono (M : ABKModel d) (n : ℤ) (y : Vec d) {theta theta' : ℝ}
    (h : theta ≤ theta') :
    largeScaleEvent M n y theta ⊆ largeScaleEvent M n y theta' :=
  Set.preimage_mono (largeScaleEventBase_mono M n h)

/-- **The good cube event grows with the accuracy and with the regularity
constant.** -/
theorem goodCubeEvent_mono (M : ABKModel d) (n : ℤ) (y : Vec d) {Creg Creg' ep ep' : ℝ}
    (hCreg : Creg ≤ Creg') (hep : ep ≤ ep') :
    goodCubeEvent M Creg n y ep ⊆ goodCubeEvent M Creg' n y ep' := by
  rintro omega ⟨h1, h2⟩
  exact ⟨le_trans h1 (ENNReal.ofReal_le_ofReal hep),
    le_trans h2 (ENNReal.ofReal_le_ofReal (by linarith only [hCreg]))⟩

/-! ## 2. The event `Q` -/

/-- **`Q` shrinks as the constant grows.**  The constant enters only through
the threshold `C⁻¹ ε γ^{-1/2}` of the large-scale event, which decreases. -/
theorem qEvent_antitone_const (M : ABKModel d) (Creg : ℝ) {Cinj Cinj' : ℝ}
    (hCinj : 0 < Cinj) (hle : Cinj ≤ Cinj') (n : ℤ) (z : Vec d) {ep : ℝ} (hep : 0 ≤ ep) :
    qEvent M Creg Cinj' n z ep ⊆ qEvent M Creg Cinj n z ep := by
  refine Set.inter_subset_inter_right _ (largeScaleEvent_mono M n z ?_)
  have hCinj' : (0 : ℝ) < Cinj' := lt_of_lt_of_le hCinj hle
  have hinv : Cinj'⁻¹ ≤ Cinj⁻¹ := by
    rw [inv_le_inv₀ hCinj' hCinj]
    exact hle
  have hsq : (0 : ℝ) ≤ (Real.sqrt M.gamma)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hinv hep) hsq

/-- **The accuracy rescaling.**  Dividing the accuracy by `max 1 C` turns the
event formed with the constant `1` into the event formed with the constant
`C`; both halves only improve, since `ε / max 1 C ≤ ε` and
`ε / max 1 C ≤ C⁻¹ ε`. -/
theorem qEvent_rescaled_accuracy_subset (M : ABKModel d) (Creg : ℝ) {Cinj : ℝ}
    (hCinj : 0 < Cinj) (n : ℤ) (z : Vec d) {ep : ℝ} (hep : 0 ≤ ep) :
    qEvent M Creg 1 n z (ep / max 1 Cinj) ⊆ qEvent M Creg Cinj n z ep := by
  have hmax : (0 : ℝ) < max 1 Cinj := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hsq : (0 : ℝ) ≤ (Real.sqrt M.gamma)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hquot : ep / max 1 Cinj ≤ ep := by
    rw [div_le_iff₀ hmax]
    nlinarith only [hep, le_max_left (1 : ℝ) Cinj]
  refine Set.inter_subset_inter (goodCubeEvent_mono M n z le_rfl hquot)
    (largeScaleEvent_mono M n z ?_)
  refine mul_le_mul_of_nonneg_right ?_ hsq
  rw [inv_one, one_mul]
  rw [div_le_iff₀ hmax]
  have hkey : ep ≤ Cinj⁻¹ * ep * max 1 Cinj := by
    have hCle : Cinj ≤ max 1 Cinj := le_max_right _ _
    have hstep : Cinj⁻¹ * ep * Cinj = ep := by field_simp
    calc ep = Cinj⁻¹ * ep * Cinj := hstep.symm
      _ ≤ Cinj⁻¹ * ep * max 1 Cinj :=
        mul_le_mul_of_nonneg_left hCle (by positivity)
  exact hkey

/-! ## 3. The site count -/

/-- **The site count is monotone under an inclusion of events.** -/
theorem qSiteCount_mono (M : ABKModel d) (Creg : ℝ) {Cinj Cinj' : ℝ} (n : ℤ) {ep ep' : ℝ}
    (S : Finset (Fin d → ℤ)) (omega : Cutoff.CutoffSample d)
    (hsub : ∀ z : Fin d → ℤ,
      qEvent M Creg Cinj n (rescaledLatticePoint n z) ep ⊆
        qEvent M Creg Cinj' n (rescaledLatticePoint n z) ep') :
    qSiteCount M Creg Cinj n ep S omega ≤ qSiteCount M Creg Cinj' n ep' S omega := by
  classical
  rw [qSiteCount_eq_card_filter, qSiteCount_eq_card_filter]
  refine Finset.card_le_card ?_
  intro z hz
  rw [Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, hsub z hz.2⟩

end

end Algsuperdiff.Section5.Support
