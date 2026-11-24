/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ThirdDisc
import LeanPool.GraphMinor.GM12.Section3MeetingDiscs

/-!
# Enclosing discs for circles meeting once

For XII (3.1)(iii), page 245, two circles surrounding distinct cuffs
meet at one point. Their enclosing discs cannot be nested. On the
sphere, a third deleted disc supplies an outside point. The disc
intersection lemma then identifies their intersection exactly.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Surrounding circles meeting once have enclosing discs meeting
at that same point, under the surface assumption of XII (3.1). -/
theorem exists_meeting_surrounding_discs
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι)
    {i j : ι} (hij : i ≠ j) {F₁ F₂ : Set (discComplement Δ)} {u : discComplement Δ}
    (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂) (hcap : F₁ ∩ F₂ = {u})
    (hs₁ : GM07.SurroundsCuff F₁ (Subtype.val ⁻¹' discBd (Δ i)))
    (hs₂ : GM07.SurroundsCuff F₂ (Subtype.val ⁻¹' discBd (Δ j))) :
    ∃ D E : Set S, IsClosedDisc D ∧ IsClosedDisc E ∧
      discBd D = (Subtype.val : discComplement Δ → S) '' F₁ ∧
      discBd E = (Subtype.val : discComplement Δ → S) '' F₂ ∧
      (∀ l, Δ l ⊆ D ↔ l = i) ∧ (∀ l, Δ l ⊆ E ↔ l = j) ∧ D ∩ E = {u.val} := by
  classical
  obtain ⟨D, hD, hbD, hiD, hDT⟩ :=
    surrounding_bounds_disc_including_deleted_disc hS Δ hΔ hdisj i hF₁ hs₁
  obtain ⟨E, hE, hbE, hjE, hET⟩ :=
    surrounding_bounds_disc_including_deleted_disc hS Δ hΔ hdisj j hF₂ hs₂
  have honeD := included_disc_iff_of_subset_partial_fill hS Δ hΔ hiD hDT
  have honeE := included_disc_iff_of_subset_partial_fill hS Δ hΔ hjE hET
  have hcase' : ¬ IsSphere S ∨ D ∪ E ≠ univ := by
    rcases hcase with hns | hthree
    · exact Or.inl hns
    · right
      let := Fintype.ofFinite ι
      have hthree' : 3 ≤ Fintype.card ι := by
        simpa only [Nat.card_eq_fintype_card] using hthree
      obtain ⟨k, hki, hkj⟩ := ENat.exists_ne_ne_of_three_le
        (by rw [ENat.card_eq_coe_fintype_card]; exact_mod_cast hthree') i j
      exact union_ne_univ_of_subset_partial_fills hS Δ hΔ hki hkj hDT hET
  refine ⟨D, E, hD, hE, hbD, hbE, honeD, honeE, ?_⟩
  apply discs_inter_eq_singleton_of_boundaries_meet_once hS hD hE
  · rw [hbD, hbE, ← image_inter Subtype.val_injective, hcap, image_singleton]
  · intro hDE
    exact hij ((honeE i).mp (hiD.trans hDE))
  · intro hED
    exact hij (((honeD j).mp (hjE.trans hED)).symm)
  · exact hcase'

end GraphMinor.GM12
