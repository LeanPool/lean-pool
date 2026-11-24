/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscGrow
import Mathlib.Topology.Order.IntermediateValue

/-!
# Initial sublines contain the line near its end

The small corner caps in XII (7.2) contain initial sublines of the two
circle branches. Any nontrivial subline with the same end contains its
ambient line near that end. In interval coordinates this is the
intermediate value theorem, and the rest of the interval is compact.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- An initial subline contains its ambient line in a neighbourhood of the
common end, as needed for the vertex diversion in XII (7.2), page 260. -/
theorem exists_nhds_line_subset_initial {L A : Set S} {v a b : S}
    (hL : IsLineWithEnds L v a) (hA : IsLineWithEnds A v b)
    (hb : b ≠ v) (hAL : A ⊆ L) :
    ∃ O : Set S, IsOpen O ∧ v ∈ O ∧ L ∩ O ⊆ A := by
  obtain ⟨e, he0, _⟩ := hL
  obtain ⟨f, hf0, hf1⟩ := hA
  let q : unitInterval → unitInterval := fun t => e.symm ⟨(f t).1, hAL (f t).2⟩
  have hqc : Continuous q := e.symm.continuous.comp
    ((continuous_subtype_val.comp f.continuous).subtype_mk _)
  have hq0 : q 0 = 0 := by
    apply e.injective
    apply Subtype.ext
    change (e (e.symm ⟨(f 0).1, hAL (f 0).2⟩)).1 = (e 0).1
    rw [e.apply_symm_apply, hf0, he0]
  have hqpos : 0 < q 1 := by
    apply unitInterval.pos_iff_ne_zero.mpr
    intro h
    have heq := congrArg (fun t => (e t).1) h
    change (e (e.symm ⟨(f 1).1, hAL (f 1).2⟩)).1 = (e 0).1 at heq
    rw [e.apply_symm_apply, hf1, he0] at heq
    exact hb heq
  have hprefix : ∀ t : unitInterval, t ≤ q 1 → (e t).1 ∈ A := by
    intro t ht
    obtain ⟨s, _, hqs⟩ := intermediate_value_Icc (show (0 : unitInterval) ≤ 1 from bot_le)
      hqc.continuousOn (show t ∈ Icc (q 0) (q 1) from ⟨hq0.symm ▸ bot_le, ht⟩)
    have heq : (f s).1 = (e t).1 := by
      have h := congrArg (fun t => (e t).1) hqs
      change (e (e.symm ⟨(f s).1, hAL (f s).2⟩)).1 = (e t).1 at h
      simpa only [e.apply_symm_apply] using h
    exact heq ▸ (f s).2
  let K := (fun t : unitInterval => (e t).1) '' Icc (q 1) 1
  have hK : IsClosed K := (isCompact_Icc.image (continuous_subtype_val.comp e.continuous)).isClosed
  have hvK : v ∉ K := by
    rintro ⟨t, ht, htv⟩
    have ht0 : t = 0 := e.injective (Subtype.ext (htv.trans he0.symm))
    exact hqpos.not_ge (ht0 ▸ ht.1)
  refine ⟨Kᶜ, hK.isOpen_compl, hvK, ?_⟩
  rintro x ⟨hxL, hxK⟩
  let t := e.symm ⟨x, hxL⟩
  have heq : (e t).1 = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hxL⟩)
  have ht : t ≤ q 1 := by
    by_contra hn
    exact hxK ⟨t, ⟨(not_le.mp hn).le, le_top⟩, heq⟩
  exact heq ▸ hprefix t ht

end GraphMinor.GM12
