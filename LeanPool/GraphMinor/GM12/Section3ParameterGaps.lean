/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import Mathlib.Topology.Order.Compact

/-!
# Gaps between contacts with a closed set

For the finite chord reduction in the extraction used by XII (3.1),
page 245, put the two ends of an injective path on the first circle.
At a parameter outside the circle, take the last contact before it
and the first contact after it. The resulting interval is a complete
chord. A retained initial or final piece with no intervening contact
lies in this same chord.
-/

public section

namespace GraphMinor.GM12

open Set

/-- A closed subset of the unit interval containing both ends has a
maximal open gap around each point of its complement. -/
theorem exists_closed_parameter_gap
    {K : Set unitInterval} (hK : IsClosed K) (h0 : 0 ∈ K) (h1 : 1 ∈ K)
    {t : unitInterval} (ht : t ∉ K) :
    ∃ a b, a < t ∧ t < b ∧ a ∈ K ∧ b ∈ K ∧ Disjoint (Ioo a b) K := by
  obtain ⟨a, ⟨ha, hat⟩, hmax⟩ :=
    (hK.inter isClosed_Iic).isCompact.exists_isGreatest
      (show (K ∩ Iic t).Nonempty from ⟨0, h0, unitInterval.nonneg t⟩)
  obtain ⟨b, ⟨hb, htb⟩, hmin⟩ :=
    (hK.inter isClosed_Ici).isCompact.exists_isLeast
      (show (K ∩ Ici t).Nonempty from ⟨1, h1, unitInterval.le_one t⟩)
  have hat' : a < t := lt_of_le_of_ne hat (fun he => ht (he ▸ ha))
  have htb' : t < b := lt_of_le_of_ne htb (fun he => ht (he.symm ▸ hb))
  refine ⟨a, b, hat', htb', ha, hb, disjoint_left.mpr ?_⟩
  intro z hz hzK
  rcases le_total z t with hzt | htz
  · exact hz.1.not_ge (hmax ⟨hzK, hzt⟩)
  · exact hz.2.not_ge (hmin ⟨hzK, htz⟩)

/-- An interval starting inside a gap and meeting the closed set only
possibly at its final point cannot run past the end of that gap. -/
theorem parameter_segment_subset_gap_of_final_contact
    {K : Set unitInterval} {a b t v : unitInterval}
    (hat : a ≤ t) (htb : t < b) (hb : b ∈ K)
    (hcontact : ∀ z ∈ Icc t v, z ∈ K → z = v) : Icc t v ⊆ Icc a b := by
  have hvb : v ≤ b := by
    by_contra hn
    have hbv : b < v := lt_of_not_ge hn
    exact hbv.ne (hcontact b ⟨htb.le, hbv.le⟩ hb)
  exact Icc_subset_Icc hat hvb

/-- The reversed interval version: a retained final piece meeting the
closed set only possibly at its initial point stays in the same gap. -/
theorem parameter_segment_subset_gap_of_initial_contact
    {K : Set unitInterval} {a b t v : unitInterval}
    (hat : a < t) (htb : t ≤ b) (ha : a ∈ K)
    (hcontact : ∀ z ∈ Icc v t, z ∈ K → z = v) : Icc v t ⊆ Icc a b := by
  have hav : a ≤ v := by
    by_contra hn
    have hva : v < a := lt_of_not_ge hn
    exact hva.ne' (hcontact a ⟨hva.le, hat.le⟩ ha)
  exact Icc_subset_Icc hav htb

/-- A contact is represented by a degenerate interval; every other
parameter is represented by the complete gap containing it. -/
theorem exists_parameter_gap_or_contact
    {K : Set unitInterval} (hK : IsClosed K) (h0 : 0 ∈ K) (h1 : 1 ∈ K)
    (t : unitInterval) :
    ∃ a b, a ≤ t ∧ t ≤ b ∧ a ∈ K ∧ b ∈ K ∧ Disjoint (Ioo a b) K ∧
      (t ∈ K → a = t ∧ b = t) := by
  by_cases ht : t ∈ K
  · exact ⟨t, t, le_rfl, le_rfl, ht, ht, by simp, fun _ => ⟨rfl, rfl⟩⟩
  · obtain ⟨a, b, hat, htb, ha, hb, hgap⟩ := exists_closed_parameter_gap hK h0 h1 ht
    exact ⟨a, b, hat.le, htb.le, ha, hb, hgap, fun h => (ht h).elim⟩

/-- A retained initial segment belongs to the contact set or to the
complete gap at its initial parameter. -/
theorem parameter_segment_subset_contacts_union_gap_left
    {K : Set unitInterval} {a b t v : unitInterval}
    (hat : a ≤ t) (htb : t ≤ b) (hb : b ∈ K)
    (hcontact : ∀ z ∈ Icc t v, z ∈ K → z = v) :
    Icc t v ⊆ K ∪ Icc a b := by
  by_cases ht : t ∈ K
  · intro z hz
    have htv : t = v := hcontact t ⟨le_rfl, hz.1.trans hz.2⟩ ht
    have hzt : z = t := le_antisymm (hz.2.trans_eq htv.symm) hz.1
    exact Or.inl (hzt.symm ▸ ht)
  · have htb' : t < b := lt_of_le_of_ne htb (fun he => ht (he.symm ▸ hb))
    exact (parameter_segment_subset_gap_of_final_contact hat htb' hb hcontact).trans
      subset_union_right

/-- A retained final segment belongs to the contact set or to the
complete gap at its final parameter. -/
theorem parameter_segment_subset_contacts_union_gap_right
    {K : Set unitInterval} {a b t v : unitInterval}
    (hat : a ≤ t) (htb : t ≤ b) (ha : a ∈ K)
    (hcontact : ∀ z ∈ Icc v t, z ∈ K → z = v) :
    Icc v t ⊆ K ∪ Icc a b := by
  by_cases ht : t ∈ K
  · intro z hz
    have htv : t = v := hcontact t ⟨hz.1.trans hz.2, le_rfl⟩ ht
    have hzt : z = t := le_antisymm hz.2 (htv.trans_le hz.1)
    exact Or.inl (hzt.symm ▸ ht)
  · have hat' : a < t := lt_of_le_of_ne hat (fun he => ht (he ▸ ha))
    exact (parameter_segment_subset_gap_of_initial_contact hat' htb ha hcontact).trans
      subset_union_right

/-- Distinct complete gaps meet only at contacts. Non-contact points
in two closed gap intervals force both endpoint pairs to coincide. -/
theorem parameter_gaps_intersection_subset_contacts
    {K : Set unitInterval} {a b c d : unitInterval}
    (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) (hd : d ∈ K)
    (hgap : Disjoint (Ioo a b) K) (hgap' : Disjoint (Ioo c d) K)
    (hne : (a, b) ≠ (c, d)) : Icc a b ∩ Icc c d ⊆ K := by
  rintro x ⟨hx, hx'⟩
  by_contra hxK
  have hax : a < x := lt_of_le_of_ne hx.1 (fun he => hxK (he ▸ ha))
  have hxb : x < b := lt_of_le_of_ne hx.2 (fun he => hxK (he.symm ▸ hb))
  have hcx : c < x := lt_of_le_of_ne hx'.1 (fun he => hxK (he ▸ hc))
  have hxd : x < d := lt_of_le_of_ne hx'.2 (fun he => hxK (he.symm ▸ hd))
  have hac : a = c := by
    rcases lt_trichotomy a c with hac | hac | hca
    · exact (disjoint_left.mp hgap ⟨hac, hcx.trans hxb⟩ hc).elim
    · exact hac
    · exact (disjoint_left.mp hgap' ⟨hca, hax.trans hxd⟩ ha).elim
  have hbd : b = d := by
    rcases lt_trichotomy b d with hbd | hbd | hdb
    · exact (disjoint_left.mp hgap' ⟨hcx.trans hxb, hbd⟩ hb).elim
    · exact hbd
    · exact (disjoint_left.mp hgap ⟨hax.trans hxd, hdb⟩ hd).elim
  exact hne (Prod.ext hac hbd)

end GraphMinor.GM12
