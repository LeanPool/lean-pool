/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72MixedCaps
public import LeanPool.GraphMinor.GM12.Section72MixedCorners
public import LeanPool.GraphMinor.GM12.Section72InitialLine
public import LeanPool.GraphMinor.GM12.Section72PushCaps

/-!
# The local diversion at the boundary vertex in XII (7.2)

Add the two local circle branches to the old drawing. Each branch
has an adjacent old half-edge in the cyclic order. The two mixed
corner caps cover the branches near the vertex and meet each other
only on the old drawing. Push the boundary circle off these caps,
fixing the old drawing. This separates the two circles near the vertex.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
private theorem restrict_sectors {H : Drawing S} {γ : Set S → I → S} {v : S}
    {next : halfEdges H γ v → halfEdges H γ v}
    {ρ P Q : halfEdges H γ v → Set S} {W O : Set S}
    {τ : halfEdges H γ v → I} (h : IsSectors H γ v next ρ P W Q τ)
    (hO : IsOpen O) (hvO : v ∈ O) : IsSectors H γ v next ρ P (W ∩ O) Q τ := by
  refine { h with
    isOpen := h.isOpen.inter hO
    mem := ⟨h.mem, hvO⟩
    cover := fun x hx => h.cover ⟨hx.1.1, hx.2⟩
    inside := fun k x hx => h.inside k ⟨⟨hx.1.1.1, hx.1.2⟩, hx.2⟩
    off := fun k i h₁ h₂ t ht hx => h.off k i h₁ h₂ t ht hx.1
    bdU := fun k x hx => h.bdU k ⟨hx.1.1, hx.2⟩ }

/-- The local part of the diversion in XII (7.2), page 260. At a
non-isolated vertex, a normal circle has two local branches. A
homeomorphism fixing the drawing moves another closed set meeting
the drawing only at that vertex away from these branches near the vertex. -/
theorem exists_local_circle_diversion (hS : IsClosedSurface S)
    {Γ : Drawing S} {C F : Set S} {v : S}
    (hC : IsOArc C) (hn : (PaintingOrDrawing.drawing Γ).IsNormal C)
    (hv : v ∈ Γ.V) (hvC : v ∈ C)
    (hincident : ∃ e ∈ Γ.E, v ∈ closure e)
    (hF : IsClosed F) (hFG : F ∩ Γ.U ⊆ {v}) :
    ∃ (h : S ≃ₜ S) (O : Set S), IsOpen O ∧ v ∈ O ∧
      (∀ x ∈ Γ.U, h x = x) ∧ ((h '' F) ∩ C) ∩ O ⊆ {v} := by
  have : Nonempty S := ⟨v⟩
  obtain ⟨H, L₀, L₁, O₀, a, b, hO₀, hvO₀, hCO₀, hLC, hmeet, hL₀, hL₁, ha, hb, hcap, hU, hV, hE⟩ :=
    exists_normal_circle_patch hC hn hvC hv
  have hsub : Γ.IsSubdrawing H :=
    ⟨fun x hx => hV.symm ▸ Or.inl hx, fun e he => hE.symm ▸ Or.inl he⟩
  have hnew : ∀ e ∈ H.E, e ∉ Γ.E → e ⊆ C := by
    intro e he hen
    have he' : e ∈ Γ.E ∪ {L₀ \ {v, a}, L₁ \ {v, b}} := hE ▸ he
    rcases he' with heΓ | he₀ | he₁
    · exact (hen heΓ).elim
    · exact he₀.symm ▸ sdiff_subset.trans (subset_union_left.trans hLC)
    · exact he₁.symm ▸ sdiff_subset.trans (subset_union_right.trans hLC)
  obtain ⟨γ, hγ⟩ := exists_edgePar H
  obtain ⟨j₀, j₁, hne, hj₀, hj₁, hn₀, hn₁, hall⟩ :=
    circle_patch_halfEdges hL₀ hL₁ ha hb hv hmeet hcap hV hE hγ
  have : Finite (halfEdges H γ v) := (finite_halfEdges H γ v).to_subtype
  have : Nontrivial (halfEdges H γ v) := ⟨⟨j₀, j₁, hne⟩⟩
  have htwo : 2 ≤ Nat.card (halfEdges H γ v) := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hvH := hsub.1 hv
  obtain ⟨next, ρ, P, W, Q, τ, hsec⟩ := exists_sectors hS H hγ hvH htwo
  have hsec' := restrict_sectors hsec hO₀ hvO₀
  let old : Set (halfEdges H γ v) := {k | k.1.1 ∈ Γ.E}
  have hold : old.Nonempty := by
    obtain ⟨e, he, hve⟩ := hincident
    obtain ⟨d, hd⟩ := exists_end_eq hγ (hsub.2 he) hvH hve
    exact ⟨⟨(e, d), hsub.2 he, hd⟩, he⟩
  obtain ⟨k₀, k₁, hkk, hk₀, hk₁⟩ := exists_two_mixed_corners next hsec.corners.inj
    hsec.corners.reach
    hsec.next_ne hold hne hn₀ hn₁ hall
  have choose_old : ∀ (j k : halfEdges H γ v),
      ((k = j ∧ next k ∈ old) ∨ (k ∈ old ∧ next k = j)) →
      ∃ g : halfEdges H γ v, g.1.1 ∈ Γ.E ∧
        ((g = k ∧ j = next k) ∨ (j = k ∧ g = next k)) := by
    intro j k hk
    rcases hk with ⟨hkj, hko⟩ | ⟨hko, hkj⟩
    · exact ⟨next k, hko, Or.inr ⟨hkj.symm, rfl⟩⟩
    · exact ⟨k, hko, Or.inl ⟨rfl, hkj.symm⟩⟩
  obtain ⟨g₀, hg₀, hc₀⟩ := choose_old j₀ k₀ hk₀
  obtain ⟨g₁, hg₁, hc₁⟩ := choose_old j₁ k₁ hk₁
  have hlocal : C ∩ (W ∩ O₀) ⊆ H.U := by
    intro x hx
    have hxL := hCO₀ ⟨hx.1, hx.2.2⟩
    rw [hU]
    exact Or.inr hxL
  obtain ⟨tG₀, tC₀, D₀, htG₀, htG₀1, htC₀, htC₀1, hD₀, hDW₀, hDQ₀, hDb₀, hDH₀, hDG₀, _⟩ :=
    exists_mixed_corner_cap hS hsub hn hnew hγ hv hvC hsec' hlocal k₀ g₀ j₀ hg₀ hn₀ hc₀
  obtain ⟨tG₁, tC₁, D₁, htG₁, htG₁1, htC₁, htC₁1, hD₁, hDW₁, hDQ₁, hDb₁, hDH₁, hDG₁, _⟩ :=
    exists_mixed_corner_cap hS hsub hn hnew hγ hv hvC hsec' hlocal k₁ g₁ j₁ hg₁ hn₁ hc₁
  have hzero : ∀ i : halfEdges H γ v, spoke γ i.1 0 = v :=
    fun i => (spoke_zero γ i.1).trans i.2.2
  have old_spoke : ∀ i : halfEdges H γ v, i.1.1 ∈ Γ.E → ∀ t : I, spoke γ i.1 t ∈ Γ.U := by
    intro i hi t
    by_cases ht : t = 0
    · rw [ht, hzero]
      exact Γ.V_subset_U hv
    · exact (hi.2.1 (spoke_mem_edge hγ i.2.1 (unitInterval.pos_iff_ne_zero.mpr ht))).1
  have hDD : D₀ ∩ D₁ ⊆ Γ.U := by
    rintro x ⟨hx₀, hx₁⟩
    have hxH := hsec.inter k₀ k₁ hkk ⟨hDQ₀ hx₀, hDQ₁ hx₁⟩
    rcases hDH₀ ⟨hx₀, hxH⟩ with ⟨s, _, hsx⟩ | ⟨s, hs, hsx⟩
    · exact hsx ▸ old_spoke g₀ hg₀ s
    · rcases hDH₁ ⟨hx₁, hxH⟩ with ⟨t, _, htx⟩ | ⟨t, ht, htx⟩
      · exact htx ▸ old_spoke g₁ hg₁ t
      · by_cases hs0 : s = 0
        · exact hsx ▸ (hs0 ▸ (hzero j₀).symm ▸ Γ.V_subset_U hv)
        · by_cases ht0 : t = 0
          · exact htx ▸ (ht0 ▸ (hzero j₁).symm ▸ Γ.V_subset_U hv)
          · have hpairne : j₀.1 ≠ j₁.1 := fun h => hne (Subtype.ext h)
            have hs1 := (spoke_eq_of_ne hγ j₀.2.1 j₁.2.1 hpairne
              (unitInterval.pos_iff_ne_zero.mpr hs0) (unitInterval.pos_iff_ne_zero.mpr ht0)
              (hsx.trans htx.symm)).1
            exact ((hs.2.trans_lt htC₀1).ne hs1).elim
  have hline : ∀ (i : halfEdges H γ v) (t : I), 0 < t →
      IsLineWithEnds (spoke γ i.1 '' Icc 0 t) v (spoke γ i.1 t) := by
    intro i t ht
    have h := isLine_spoke_piece hγ i.2.1 ht
    rwa [hzero] at h
  have hend : ∀ (i : halfEdges H γ v) (t : I), 0 < t → spoke γ i.1 t ≠ v := by
    intro i t ht he
    exact ht.ne' (spoke_injective hγ i.2.1 (he.trans (hzero i).symm))
  have hvL₀ : v ∈ L₀ := by obtain ⟨e, h0, _⟩ := hL₀; exact h0 ▸ (e 0).2
  have hvL₁ : v ∈ L₁ := by obtain ⟨e, h0, _⟩ := hL₁; exact h0 ▸ (e 0).2
  have hCL₀ : spoke γ j₀.1 '' Icc 0 tC₀ ⊆ L₀ := by
    rintro x ⟨t, _, rfl⟩
    by_cases ht : t = 0
    · rwa [ht, hzero]
    · have h := spoke_mem_edge hγ j₀.2.1 (unitInterval.pos_iff_ne_zero.mpr ht)
      rw [hj₀] at h
      exact h.1
  have hCL₁ : spoke γ j₁.1 '' Icc 0 tC₁ ⊆ L₁ := by
    rintro x ⟨t, _, rfl⟩
    by_cases ht : t = 0
    · rwa [ht, hzero]
    · have h := spoke_mem_edge hγ j₁.2.1 (unitInterval.pos_iff_ne_zero.mpr ht)
      rw [hj₁] at h
      exact h.1
  obtain ⟨O₁, hO₁, hvO₁, hL₀O⟩ := exists_nhds_line_subset_initial hL₀ (hline j₀ tC₀ htC₀)
    (hend j₀ tC₀ htC₀) hCL₀
  obtain ⟨O₂, hO₂, hvO₂, hL₁O⟩ := exists_nhds_line_subset_initial hL₁ (hline j₁ tC₁ htC₁)
    (hend j₁ tC₁ htC₁) hCL₁
  let O := (O₀ ∩ O₁) ∩ O₂
  have hcover : C ∩ O ⊆ D₀ ∪ D₁ := by
    rintro x ⟨hxC, hxO⟩
    rcases hCO₀ ⟨hxC, hxO.1.1⟩ with hxL₀ | hxL₁
    · exact Or.inl (Surface.discBd_subset D₀ (hDb₀ (Or.inr (hL₀O ⟨hxL₀, hxO.1.2⟩))))
    · exact Or.inr (Surface.discBd_subset D₁ (hDb₁ (Or.inr (hL₁O ⟨hxL₁, hxO.2⟩))))
  obtain ⟨h, hfix, hdivert⟩ := push_two_caps_fixing hS hD₀ hD₁ (hline g₀ tG₀ htG₀)
    (hline g₁ tG₁ htG₁)
    (hend g₀ tG₀ htG₀) (hend g₁ tG₁ htG₁)
    (fun x hx => hDb₀ (Or.inl hx)) (fun x hx => hDb₁ (Or.inl hx))
    Γ.isClosed_U (Γ.V_subset_U hv)
    (by rintro x ⟨t, _, rfl⟩; exact old_spoke g₀ hg₀ t)
    (by rintro x ⟨t, _, rfl⟩; exact old_spoke g₁ hg₁ t)
    (fun x hx => hDG₀ ⟨hx.2, hx.1⟩) (fun x hx => hDG₁ ⟨hx.2, hx.1⟩) hDD hF hFG hcover
  exact ⟨h, O, (hO₀.inter hO₁).inter hO₂, ⟨⟨hvO₀, hvO₁⟩, hvO₂⟩, hfix, hdivert⟩

end GraphMinor.GM12
