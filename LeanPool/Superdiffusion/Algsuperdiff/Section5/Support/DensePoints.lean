/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.HolderGauge

/-!
# DensePoints

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# A Hölder seminorm is a countable supremum on dense points

On an open set the Hölder seminorm of a continuous function is already
determined by pairs of distinct points in a dense subset.

## References

* ABK26, the localized error and regularity quantities of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

variable {d : ℕ}

/-! ## 1. A sequence in a dense subset of an open set -/

theorem exists_seq_mem_inter_tendsto {U D : Set (Vec d)} (hU : IsOpen U) (hD : Dense D)
    {x : Vec d} (hx : x ∈ U) :
    ∃ z : ℕ → Vec d, (∀ k, z k ∈ U ∩ D) ∧ Tendsto z atTop (𝓝 x) := by
  have hmem : x ∈ closure (U ∩ D) := hD.open_subset_closure_inter hU hx
  exact mem_closure_iff_seq_limit.1 hmem

/-! ## 2. The Hölder seminorm -/

/-- **The Hölder seminorm of a function continuous on an open set is already the
supremum over pairs of distinct points of a dense subset.** -/
theorem holderSeminormOn_eq_iSup_dense {E : Type*} [NormedAddCommGroup E]
    {U D : Set (Vec d)} (hU : IsOpen U) (hD : Dense D) {alpha : ℝ} {f : Vec d → E}
    (hf : ContinuousOn f U) :
    holderSeminormOn U alpha f =
      ⨆ x ∈ U ∩ D, ⨆ z ∈ U ∩ D, ⨆ _ : x ≠ z,
        ENNReal.ofReal (‖f x - f z‖ / ‖x - z‖ ^ alpha) := by
  refine le_antisymm ?_ ?_
  · simp only [holderSeminormOn, iSup_le_iff]
    intro x hx z hz hne
    obtain ⟨p, hp, hplim⟩ := exists_seq_mem_inter_tendsto hU hD hx
    obtain ⟨q, hq, hqlim⟩ := exists_seq_mem_inter_tendsto hU hD hz
    have hfp : Tendsto (fun k => f (p k)) atTop (𝓝 (f x)) :=
      (hf.continuousAt (hU.mem_nhds hx)).tendsto.comp hplim
    have hfq : Tendsto (fun k => f (q k)) atTop (𝓝 (f z)) :=
      (hf.continuousAt (hU.mem_nhds hz)).tendsto.comp hqlim
    have hnormpos : (0 : ℝ) < ‖x - z‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.2 hne
    have hnormlim : Tendsto (fun k => ‖p k - q k‖) atTop (𝓝 ‖x - z‖) :=
      (hplim.sub hqlim).norm
    have hden : Tendsto (fun k => ‖p k - q k‖ ^ alpha) atTop (𝓝 (‖x - z‖ ^ alpha)) :=
      (Real.continuousAt_rpow_const _ _ (Or.inl hnormpos.ne')).tendsto.comp hnormlim
    have hnum : Tendsto (fun k => ‖f (p k) - f (q k)‖) atTop (𝓝 ‖f x - f z‖) :=
      (hfp.sub hfq).norm
    have hquot : Tendsto (fun k =>
        ENNReal.ofReal (‖f (p k) - f (q k)‖ / ‖p k - q k‖ ^ alpha)) atTop
        (𝓝 (ENNReal.ofReal (‖f x - f z‖ / ‖x - z‖ ^ alpha))) := by
      refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
      exact hnum.div hden (Real.rpow_pos_of_pos hnormpos alpha).ne'
    have heventne : ∀ᶠ k in atTop, p k ≠ q k := by
      have hposden : ∀ᶠ k in atTop, (0 : ℝ) < ‖p k - q k‖ :=
        (tendsto_order.1 hnormlim).1 0 hnormpos
      refine hposden.mono fun k hk hcon => ?_
      rw [hcon, sub_self, norm_zero] at hk
      exact lt_irrefl 0 hk
    refine le_of_tendsto hquot ?_
    filter_upwards [heventne] with k hk
    exact le_iSup_of_le (p k) (le_iSup_of_le (hp k) (le_iSup_of_le (q k)
      (le_iSup_of_le (hq k) (le_iSup_of_le hk le_rfl))))
  · refine iSup_le fun x => iSup_le fun hx => iSup_le fun z => iSup_le fun hz =>
      iSup_le fun hne => ?_
    exact le_holderSeminormOn hx.1 hz.1 hne

end

end Algsuperdiff.Section5.Support
