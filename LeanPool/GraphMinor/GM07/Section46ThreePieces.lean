/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section46EdgeSegments
import LeanPool.GraphMinor.GM07.Section46EdgeContacts
import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM11.RadialBasics

/-!
# The three-edge drawing on a long seam edge

In VII (4.6), page 225, two interior contacts divide a long edge into
three edges. Glue the line drawings on its three closed parameter
intervals. The old edge may be a loop, so the first and last parameter
ends can coincide. All intersections are still at the marked vertices.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

universe u

/-- The three actual edges obtained by the two cuts on a long seam edge,
in VII (4.6), page 225. -/
theorem exists_three_piece_drawing {S : Type u} [TopologicalSpace S] [T2Space S]
    {J : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {e : Set S} (he : e ∈ J.E) {s t : unitInterval}
    (hs : s ∈ Ioo 0 1) (ht : t ∈ Ioo 0 1) (hst : s < t) :
    ∃ D : Drawing S, D.U = closure e ∧
      D.V = ({γ e 0, γ e s} ∪ {γ e s, γ e t}) ∪ {γ e t, γ e 1} ∧
      D.E = {γ e '' Ioo 0 s, γ e '' Ioo s t, γ e '' Ioo t 1} := by
  have hi₁ := edge_parameter_injOn_Icc hγ he (a := 0) (b := s) (.inr hs.2)
  have hi₂ := edge_parameter_injOn_Icc hγ he (a := s) (b := t) (.inl hs.1)
  have hi₃ := edge_parameter_injOn_Icc hγ he (a := t) (b := 1) (.inl ht.1)
  have hL₁ := edge_parameter_line_Icc hγ he hs.1 (.inr hs.2)
  have hL₂ := edge_parameter_line_Icc hγ he hst (.inl hs.1)
  have hL₃ := edge_parameter_line_Icc hγ he ht.2 (.inl ht.1)
  have hn₁ : γ e 0 ≠ γ e s := fun h => hs.1.ne (hi₁ ⟨le_rfl, hs.1.le⟩ ⟨hs.1.le, le_rfl⟩ h)
  have hn₂ : γ e s ≠ γ e t := fun h => hst.ne (hi₂ ⟨le_rfl, hst.le⟩ ⟨hst.le, le_rfl⟩ h)
  have hn₃ : γ e t ≠ γ e 1 := fun h => ht.2.ne (hi₃ ⟨le_rfl, ht.2.le⟩ ⟨ht.2.le, le_rfl⟩ h)
  let D₁ := lineDrawing hL₁ hn₁
  let D₂ := lineDrawing hL₂ hn₂
  let D₃ := lineDrawing hL₃ hn₃
  have hmeet₁₂ : D₁.U ∩ D₂.U ⊆ D₁.V ∩ D₂.V := by
    change (γ e '' Icc 0 s) ∩ (γ e '' Icc s t) ⊆ {γ e 0, γ e s} ∩ {γ e s, γ e t}
    rintro x ⟨⟨u, hu, rfl⟩, ⟨v, hv, hvu⟩⟩
    rcases edge_parameter_eq_or_ends hγ he hvu.symm with huv | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hus : u = s := le_antisymm hu.2 (huv ▸ hv.1)
      rw [hus]
      exact ⟨.inr rfl, .inl rfl⟩
    · exact (not_le_of_gt ht.2 hv.2).elim
    · exact (not_le_of_gt hs.2 hu.2).elim
  let D₁₂ := D₁.glue D₂ hmeet₁₂
  have hmeet₃ : D₁₂.U ∩ D₃.U ⊆ D₁₂.V ∩ D₃.V := by
    change ((γ e '' Icc 0 s) ∪ (γ e '' Icc s t)) ∩ (γ e '' Icc t 1) ⊆
      ({γ e 0, γ e s} ∪ {γ e s, γ e t}) ∩ {γ e t, γ e 1}
    rintro x ⟨hx, ⟨v, hv, hvx⟩⟩
    rcases hx with ⟨u, hu, hux⟩ | ⟨u, hu, hux⟩
    · have huv' : γ e u = γ e v := hux.trans hvx.symm
      rcases edge_parameter_eq_or_ends hγ he huv' with huv | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have htu : t ≤ u := huv ▸ hv.1
        exact (not_le_of_gt hst (htu.trans hu.2)).elim
      · exact ⟨.inl (.inl hux.symm), .inr hvx.symm⟩
      · exact (not_le_of_gt hs.2 hu.2).elim
    · have huv' : γ e u = γ e v := hux.trans hvx.symm
      rcases edge_parameter_eq_or_ends hγ he huv' with huv | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hut : u = t := le_antisymm hu.2 (huv ▸ hv.1)
        have hxt : x = γ e t := hux.symm.trans (congrArg (γ e) hut)
        exact ⟨.inr (.inr hxt), .inl hxt⟩
      · exact (not_le_of_gt hs.1 hu.1).elim
      · exact (not_le_of_gt ht.2 hu.2).elim
  refine ⟨D₁₂.glue D₃ hmeet₃, ?_, rfl, ?_⟩
  · change ((γ e '' Icc 0 s) ∪ (γ e '' Icc s t)) ∪ (γ e '' Icc t 1) = closure e
    rw [← image_union, ← image_union]
    have hcover : (Icc (0 : unitInterval) s ∪ Icc s t) ∪ Icc t 1 = univ := by
      ext x
      simp only [mem_union, mem_Icc, mem_univ, iff_true]
      by_cases hxs : x ≤ s
      · exact .inl (.inl ⟨bot_le, hxs⟩)
      by_cases hxt : x ≤ t
      · exact .inl (.inr ⟨(lt_of_not_ge hxs).le, hxt⟩)
      · exact .inr ⟨(lt_of_not_ge hxt).le, le_top⟩
    rw [hcover, image_univ, edge_parameter_range hγ he]
  · rw [Drawing.glue_E, Drawing.glue_E, lineDrawing_E, lineDrawing_E, lineDrawing_E]
    rw [image_Icc_diff_endpoints hs.1 hi₁, image_Icc_diff_endpoints hst hi₂,
      image_Icc_diff_endpoints ht.2 hi₃]
    ext x
    simp only [mem_union, mem_singleton_iff, mem_insert_iff]
    exact or_assoc

end GraphMinor.GM07
