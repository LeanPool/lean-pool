/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.GoodEvents
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.Translate

/-!
# Api

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The consumption A of the frozen good event `𝒢(m, y; s, ε)`

`Algsuperdiff.Frozen.Section4.goodEventAt` (`d.good.event.for.lambda`) is a
*final frozen definition*: the translated good event is the
`Cutoff.translateCutoffSample y` preimage of the Section 4 support layer's
`goodEventBase`.  This module supplies the operations on it used below:

* **measure it** — `measurableSet_goodEventAt`;
* **compare two of them** — monotonicity in the coarse-ellipticity constant
  `Ccg` and in the threshold `ε` (and hence in the `𝒢₁` threshold
  `s ε c⋆^{1/2} γ^{-1/2}`, which is increasing in `ε`).

## What is *not* here

Monotonicity in the scale `m` is not stated, and none is claimed in either
direction.  `𝒢₀(m)` weights the `k`-supremum by `3^{-γ(m-k)/4}` and ranges `z`
over the annulus `□_m ∖ □_k`; `𝒢₁`'s second condition weights by
`3^{-s(m-n)/4}` and its first condition sums from `k = m`; `𝒢₂`'s double sum is
over `j ≤ m`.  Changing `m` moves the weights and the index sets at once, so
nothing here is a set inclusion in `m`; any `m`-comparison a lane needs is a
per-display estimate, to be produced where it is used.

## References

* ABK26, `d.good.event.for.lambda`; `e.lambda.good.events`.
-/

namespace Algsuperdiff.Section4.Provider.GoodEvents

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The `𝒢₁` threshold of `e.lambda.good.events`

`goodEventBase` instantiates `𝒢₁`'s threshold at `T = s ε √c⋆ (√γ)⁻¹`.  Its two
sign facts are used by every monotonicity statement below, so they are isolated
once. -/

/-- The `𝒢₁` threshold `s ε √c⋆ (√γ)⁻¹` of `e.lambda.good.events`. -/
def goodEventThreshold (M : ABKModel d) (s : {s : ℝ // 0 < s}) (ep : ℝ) : ℝ :=
  (s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹

/-- The threshold is nonnegative as soon as the printed `ε` is. -/
theorem goodEventThreshold_nonneg (M : ABKModel d) (s : {s : ℝ // 0 < s})
    {ep : ℝ} (hep : 0 ≤ ep) : 0 ≤ goodEventThreshold M s ep :=
  mul_nonneg
    (mul_nonneg (mul_nonneg s.2.le hep) (Real.sqrt_nonneg _))
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- The threshold is monotone in `ε`. -/
theorem goodEventThreshold_mono (M : ABKModel d) (s : {s : ℝ // 0 < s})
    {ep ep' : ℝ} (h : ep ≤ ep') :
    goodEventThreshold M s ep ≤ goodEventThreshold M s ep' :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h s.2.le)
      (Real.sqrt_nonneg _))
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-! ## 2. Membership and measurability -/

/-- The frozen event is a translate preimage, by definition. -/
theorem goodEventAt_eq_preimage (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y : Vec d)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep =
      Cutoff.translateCutoffSample y ⁻¹' Support.goodEventBase M Ccg m s ep :=
  rfl

/-- **The translated event is measurable.**  The support layer's measurability
transported through the proved measurability of `translateCutoffSample`. -/
theorem measurableSet_goodEventAt (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y : Vec d)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    MeasurableSet (Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep) :=
  (Support.measurableSet_goodEventBase M Ccg m s ep).preimage
    (Cutoff.measurable_translateCutoffSample y)

/-! ## 4. Monotonicity in the two displayed parameters -/

/-- **Monotonicity of the untranslated event.**  Raising the
coarse-ellipticity constant lowers `𝒢₀`'s positive parts, and raising `ε`
raises both `𝒢₁`'s threshold and `𝒢₂`'s. -/
theorem goodEventBase_subset_of_le (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) {Ccg Ccg' ep ep' : ℝ} (hC : Ccg ≤ Ccg')
    (hep : 0 ≤ ep) (heple : ep ≤ ep') :
    Support.goodEventBase M Ccg m s ep ⊆ Support.goodEventBase M Ccg' m s ep' := by
  rintro omega ⟨⟨h0, h1⟩, h2⟩
  exact ⟨⟨Support.eventG0_subset_of_le M m hC h0,
      Support.eventG1_subset_of_le M m (s : ℝ)
        (goodEventThreshold_nonneg M s hep)
        (goodEventThreshold_mono M s heple) h1⟩,
    Support.eventG2_subset_of_le M m s hep heple h2⟩

/-- **Monotonicity of the translated event.**  The preimage of an inclusion. -/
theorem goodEventAt_subset_of_le (M : ABKModel d) (m : ℤ) (y : Vec d)
    (s : {s : ℝ // 0 < s}) {Ccg Ccg' ep ep' : ℝ} (hC : Ccg ≤ Ccg')
    (hep : 0 ≤ ep) (heple : ep ≤ ep') :
    Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep ⊆
      Algsuperdiff.Frozen.Section4.goodEventAt M Ccg' m y s ep' :=
  Set.preimage_mono (goodEventBase_subset_of_le M m s hC hep heple)

/-- Monotonicity in the threshold `ε` alone. -/
theorem goodEventAt_mono_ep (M : ABKModel d) (Ccg : ℝ) (m : ℤ) (y : Vec d)
    (s : {s : ℝ // 0 < s}) {ep ep' : ℝ} (hep : 0 ≤ ep) (heple : ep ≤ ep') :
    Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep ⊆
      Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m y s ep' :=
  goodEventAt_subset_of_le M m y s le_rfl hep heple

/-! ## 5. The translate calculus of the event -/

/-- At `y = 0` the frozen event is the untranslated `goodEventBase`. -/
theorem goodEventAt_zero (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    Algsuperdiff.Frozen.Section4.goodEventAt M Ccg m (0 : Vec d) s ep =
      Support.goodEventBase M Ccg m s ep :=
  preimage_translateCutoffSample_zero _

end

end Algsuperdiff.Section4.Provider.GoodEvents
