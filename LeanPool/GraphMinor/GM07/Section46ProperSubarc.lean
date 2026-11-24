/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section5b
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Choosing a proper boundary-to-boundary subarc

In VII (4.6), page 226, an `I`-arc in `U(L)` can be chosen to meet the
boundary only at its ends. Since `L` is proper, its boundary contacts
are vertices and hence finite. Starting at one end, choose the first
later contact in the line parameter and keep that initial segment.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

/-- The choice of a proper `I`-arc in `U(L)` in VII (4.6), page 226. -/
theorem exists_proper_IArc_subset {S : Type*} [TopologicalSpace S] [T2Space S]
    {L : Drawing S} (hL : L.IsProper) {F : Set S} (hF : IsIArc F) (hFL : F ⊆ L.U) :
    ∃ P : Set S, P ⊆ F ∧ IsProperIArc P := by
  obtain ⟨a, b, habd, hbbd, f, hf0, hf1⟩ := hF
  let γ : unitInterval → S := fun u => (f u).1
  have hγc : Continuous γ := continuous_subtype_val.comp f.continuous
  have hγi : Function.Injective γ := Subtype.val_injective.comp f.injective
  let T := γ ⁻¹' bd S
  have hT : T.Finite := (L.finite_V.preimage hγi.injOn).subset fun u hu =>
    hL ⟨hu, hFL (f u).2⟩
  have h0 : γ 0 ∈ bd S := by change (f 0).1 ∈ bd S; rw [hf0]; exact habd
  have h1 : (1 : unitInterval) ∈ T := by change (f 1).1 ∈ bd S; rw [hf1]; exact hbbd
  have hne : (T \ {0}).Nonempty := ⟨1, h1, one_ne_zero⟩
  obtain ⟨t, ht, hmin⟩ := Set.exists_min_image (T \ {0}) id hT.sdiff hne
  have ht0 : (0 : unitInterval) < t := unitInterval.pos_iff_ne_zero.mpr ht.2
  let P := γ '' Icc 0 t
  have hline : IsLineWithEnds P (γ 0) (γ t) :=
    isLineWithEnds_image_Icc_of_injOn hγc ht0 hγi.injOn
  have hends : P ∩ bd S = {γ 0, γ t} := by
    apply Subset.antisymm
    · rintro x ⟨⟨u, hu, rfl⟩, hubd⟩
      by_cases hu0 : u = 0
      · exact .inl (congrArg γ hu0)
      · have htu : t ≤ u := hmin u ⟨hubd, hu0⟩
        have hut : u = t := le_antisymm hu.2 htu
        exact .inr (congrArg γ hut)
    · rintro x (rfl | rfl)
      · exact ⟨⟨0, ⟨le_rfl, ht0.le⟩, rfl⟩, h0⟩
      · exact ⟨⟨t, ⟨ht0.le, le_rfl⟩, rfl⟩, ht.1⟩
  refine ⟨P, ?_, γ 0, γ t, (fun h => ht0.ne (hγi h)), hends, hline⟩
  rintro x ⟨u, _, rfl⟩
  exact (f u).2

end GraphMinor.GM07
