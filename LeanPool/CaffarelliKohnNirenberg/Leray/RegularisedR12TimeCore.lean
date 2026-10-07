/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivOneDim

/-!
# Classical derivatives from weak time derivatives

On an open interval, a continuous function with a continuous weak derivative
has that derivative classically. This is the time-calculus step in the
regularized momentum equation of `thm:regularised` (R2).
-/

public section

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace CKN.Leray

/-- A continuous weak time derivative agrees with the classical derivative
at every interior point of a finite positive-time interval. -/
theorem regularisedR12TimeCore_hasDerivAt_of_weakDeriv
    (T : ℝ) (hT : 0 < T) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 T))
    (hg : ContinuousOn g (Set.Ioo 0 T))
    (hweak : CKN.HasWeakDerivOn (Set.Ioo 0 T) f g) :
    ∀ t ∈ Set.Ioo 0 T, HasDerivAt f (g t) t := by
  let t₀ : ℝ := T / 2
  have ht₀ : t₀ ∈ Ioo 0 T := by
    dsimp [t₀]
    constructor <;> linarith only [hT]
  have hfloc : LocallyIntegrableOn f (Ioo 0 T) volume :=
    hf.locallyIntegrableOn measurableSet_Ioo
  have hgloc : LocallyIntegrableOn g (Ioo 0 T) volume :=
    hg.locallyIntegrableOn measurableSet_Ioo
  obtain ⟨C, hrep⟩ := CKN.eq_const_add_intervalIntegral_of_continuous_weakDeriv
    hT ht₀ hfloc hgloc hweak hf
  intro t ht
  have hsub : uIcc t₀ t ⊆ Ioo 0 T := by
    intro s hs
    change s ∈ Icc (min t₀ t) (max t₀ t) at hs
    exact ⟨lt_of_lt_of_le (lt_min ht₀.1 ht.1) hs.1,
      lt_of_le_of_lt hs.2 (max_lt ht₀.2 ht.2)⟩
  have hint : IntervalIntegrable g volume t₀ t := by
    apply intervalIntegrable_iff.mpr
    exact (hgloc.integrableOn_compact_subset hsub isCompact_uIcc).mono_set
      uIoc_subset_uIcc
  have hgc : ContinuousAt g t := (hg t ht).continuousAt (isOpen_Ioo.mem_nhds ht)
  have hgm : StronglyMeasurableAtFilter g (𝓝 t) volume :=
    hg.stronglyMeasurableAtFilter isOpen_Ioo t ht
  have hprim := intervalIntegral.integral_hasDerivAt_right hint hgm hgc
  have hnear : (fun s => C + ∫ r in t₀..s, g r) =ᶠ[𝓝 t] f := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact (hrep s hs).symm
  exact (hprim.const_add C).congr_of_eventuallyEq hnear.symm

end CKN.Leray

end
