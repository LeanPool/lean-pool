/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.BorderCells

/-!
# Sectors of a region

Two sides of a region at a node lie on the boundary of a closed disc that meets the paint only in
these two sides (`sector`). We push both sides into the region as strips and join the
strips by a line in the region. This gives a loop through one node, which bounds a disc by the
hypothesis on normal `O`-arcs of `RegionBoundaryOArcCriterionStatement`. If the two sides
also share their far end, a second loop at that end fills the rest of the region. These discs join
the two cells at a node in (8.7) of Graph Minors XVII (page 183), and the two border
cells at a node in (8.4) (page 182).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

/-- A disc that has a point off a second disc and misses the boundary of the second disc away from a
part `P` of its own boundary meets the second disc only in `P`. -/
theorem disc_off [T2Space S] (hman : ∀ x : S, IsManifoldPoint x) {St Δ P : Set S}
  (hSt : IsClosedDisc St) (hP : P ⊆ discBd St) (hΔ : IsClosedDisc Δ)
    (hd : ∀ z ∈ St, z ∉ P → z ∉ discBd Δ)
    {w : S} (hw : w ∈ St) (hwP : w ∉ P) (hwΔ : w ∉ Δ) :
    St ∩ Δ ⊆ P := by
  have hY := Painting.isPreconnected_disc_diff hSt hP
  have hdis : Disjoint (St \ P) (discBd Δ) := disjoint_left.mpr fun z hz => hd z hz.1 hz.2
  rcases hΔ.side hman hY hdis with h | h
  · exact absurd (h ⟨hw, hwP⟩).1 hwΔ
  · rintro z ⟨hz, hz'⟩
    by_contra hn
    exact disjoint_left.mp h ⟨hz, hn⟩ hz'

namespace Painting

variable {Γ : Painting S} [T2Space S]

omit [TopologicalSpace S] [T2Space S] in
omit [TopologicalSpace S] [T2Space S] in
private theorem subset_union_sdiff_of_inter_subset {A B C P Q : Set S}
    (hA : A ⊆ B ∪ C) (hAQ : A ∩ Q ⊆ P) : A ⊆ (B ∪ C) \ (Q \ P) :=
  fun _ hx => ⟨hA hx, fun h => h.2 (hAQ ⟨hx, h.1⟩)⟩

private theorem filled_sector_meets_disc_in_joining_arc
    {S : Type}
    [TopologicalSpace S]
    {Γ : Painting S}
    [T2Space S]
    {a : S}
    {b₁ : S}
    (hman : ∀ (x : S), IsManifoldPoint x)
    (haN : a ∈ Γ.N)
    (St₁ : Set S)
    (γ₁ : Set S)
    (hγ₁ : IsLineWithEnds γ₁ a b₁)
    (St₂ : Set S)
    (γ₂ : Set S)
    (A₁ : Set S)
    (x : S)
    (y : S)
    (β : Set S)
    (hβ : IsLineWithEnds β y x)
    (A' : Set S)
    (R₁ : Set S)
    (R₂ : Set S)
    (hi'₁ : A₁ ∩ R₁ = {x})
    (hi'₂ : A' ∩ R₂ = {y})
    (hγ₁St : γ₁ ⊆ St₁)
    (hγ₂St : γ₂ ⊆ St₂)
    (Δ : Set S)
    (hΔ : IsClosedDisc Δ)
    (hA₁Δ : A₁ ⊆ discBd Δ)
    (hβΔ : β ⊆ discBd Δ)
    (haA₁ : a ∈ A₁)
    (hS₁Δ : St₁ ∩ Δ ⊆ A₁)
    (hS₂Δ : St₂ ∩ Δ ⊆ A')
    (hR₁γ : R₁ ⊆ γ₁)
    (hR₂γ : R₂ ⊆ γ₂)
    (Δ₂ : Set S)
    (hΔ₂ : IsClosedDisc Δ₂)
    (hbΔ₂ : discBd Δ₂ = R₁ ∪ (R₂ ∪ β))
    (hΔ₂U : ∀ x ∈ Γ.U, x ≠ b₁ → x ∉ Δ₂)
    (hβΔ₂ : β ⊆ discBd Δ₂)
    (hhaβ : a ∉ β) :
    Δ ∩ Δ₂ = β := by
  apply subset_antisymm
  · refine disc_off hman hΔ hβΔ hΔ₂ ?_ (discBd_subset Δ (hA₁Δ haA₁)) hhaβ
        (hΔ₂U _ (Γ.N_subset haN) hγ₁.ne')
    intro z hz hzβ h
    rcases (hbΔ₂ ▸ h : z ∈ R₁ ∪ (R₂ ∪ β)) with h | h | h
    · have h3 : z ∈ St₁ ∩ Δ := ⟨hγ₁St (hR₁γ h), hz⟩
      exact hzβ ((hi'₁.le ⟨hS₁Δ h3, h⟩ : z = x) ▸ hβ.right_mem)
    · have h3 : z ∈ St₂ ∩ Δ := ⟨hγ₂St (hR₂γ h), hz⟩
      exact hzβ ((hi'₂.le ⟨hS₂Δ h3, h⟩ : z = y) ▸ hβ.left_mem)
    · exact hzβ h
  · exact fun z hz => ⟨discBd_subset Δ (hβΔ hz), discBd_subset Δ₂ (hβΔ₂ hz)⟩

/-- Two sides of a region at a node lie on the boundary of a closed disc that meets the paint only
in these sides. -/
theorem sector [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {c₁ c₂ L₁ L₂ r : Set S} {a b₁ b₂
  : S} (hr : r ∈ Γ.regions) (h₁ : Γ.IsSide c₁ L₁ a b₁) (h₂ : Γ.IsSide c₂ L₂ a b₂)
    (hcl₁ : L₁ ⊆ closure r)
    (hcl₂ : L₂ ⊆ closure r)
    (hi : L₁ ∩ L₂ ⊆ {a, b₂}) : ∃ Y, IsClosedDisc Y ∧ L₁ ⊆ discBd Y ∧ L₂ ⊆ discBd Y
      ∧ Y ∩ Γ.U ⊆ L₁ ∪ L₂ := by
  have hcS : CompactSpace S := hS.1
  have hman := hS.2.2
  have hU₁ := h₁.1.subset_U
  have hU₂ := h₂.1.subset_U
  have hNr : ∀ {z}, z ∈ Γ.N → z ∉ r := fun {z} hz h => region_subset hr h (Γ.N_subset hz)
  have hdr : ∀ {L : Set S}, L ⊆ Γ.U → Disjoint L r := fun {L} hL => disjoint_left.mpr fun x hx hx'
    => region_subset hr hx' (hL hx)
  have haN := h₁.1.left_mem_N
  have hb₁N := h₁.1.right_mem_N
  have hb₂N := h₂.1.right_mem_N
  obtain ⟨St₁, γ₁, hSt₁, hγ₁, hb₁, hi₁, -, -, hU'₁, hr₁, -⟩ := side_strip' hS hΓ hr h₁ hcl₁
    (isClosed_empty (X := S)) (by simp)
  have hAL₂ : St₁ ∩ L₂ ⊆ {a, b₂} := fun z hz => hi ⟨hU'₁ ⟨hz.1, hU₂ hz.2⟩, hz.2⟩
  obtain ⟨St₂, γ₂, hSt₂, hγ₂, hb₂, hi₂, -, hin, hU'₂, hr₂, -⟩ := side_strip' hS hΓ hr h₂ hcl₂
    hSt₁.isClosed hAL₂
  obtain ⟨A₁, A₂, x, y, β, hA₁, hA₂, hiA, hxr, hA₁s, hβ, hβr, hβA, hyγ, hβ₂, hβ₁, ⟨A', R₁, R₂, hA',
    hA's, rfl, hR₁, hR₂, hu₁, hi'₁, hu₂, hi'₂⟩, hA₁r, hA₂r⟩ :=
    exists_loop hS hΓ hr haN hb₁N hb₂N hSt₁ hSt₂ hγ₁ hγ₂ hb₁ hb₂ hr₁ hr₂
      (hdr hU₁) (hdr hU₂) hi₁ hi₂ hin
  have hγ₁St : γ₁ ⊆ St₁ := (hb₁ ▸ subset_union_right).trans (discBd_subset St₁)
  have hγ₂St : γ₂ ⊆ St₂ := (hb₂ ▸ subset_union_right).trans (discBd_subset St₂)
  have hF : IsOArc (A₁ ∪ (A' ∪ β)) := oArc_of_lines hA₁ hA₂ hiA
  obtain ⟨Δ, hΔ, hbΔ, hΔU⟩ := curve_disc hΓ hr haN hF (fun z hz hne => hz.elim (fun h
    => hA₁r z h hne) (fun h => hA₂r z h hne))
  have hA₁Δ : A₁ ⊆ discBd Δ := hbΔ ▸ subset_union_left
  have hA'Δ : A' ⊆ discBd Δ := by rw [hbΔ]; exact fun z hz => .inr (.inl hz)
  have hβΔ : β ⊆ discBd Δ := by rw [hbΔ]; exact fun z hz => .inr (.inr hz)
  obtain ⟨w₁, hw₁, hw₁a, hw₁b, -⟩ := exists_inner h₁.1.2.1 (finite_empty (α := S))
  obtain ⟨w₂, hw₂, hw₂a, hw₂b, -⟩ := exists_inner h₂.1.2.1 (finite_empty (α := S))
  have hL₁St : L₁ ⊆ St₁ := (hb₁ ▸ subset_union_left).trans (discBd_subset St₁)
  have hL₂St : L₂ ⊆ St₂ := (hb₂ ▸ subset_union_left).trans (discBd_subset St₂)
  have hw₁γ : w₁ ∉ γ₁ := fun h => (hi₁.le ⟨hw₁, h⟩).elim hw₁a hw₁b
  have hw₂γ : w₂ ∉ γ₂ := fun h => (hi₂.le ⟨hw₂, h⟩).elim hw₂a hw₂b
  have hb₂A₁ : b₂ ∉ A₁ := fun h => hNr hb₂N (hA₁r _ h hγ₂.ne'.symm)
  have hb₂A' : b₂ ∉ A' := fun h => hNr hb₂N (hA₂r _ (.inl h) hγ₂.ne'.symm)
  have haA' : a ∈ A' := hA'.left_mem
  have haA₁ : a ∈ A₁ := hA₁.left_mem
  have hxA₁ : x ∈ A₁ := hA₁.right_mem
  have hyA' : y ∈ A' := hA'.right_mem
  have hS₁Δ : St₁ ∩ Δ ⊆ A₁ := by
    refine disc_off hman hSt₁ (hA₁s.trans (hb₁ ▸ subset_union_right)) hΔ (fun z hz hzA h => ?_)
      (hL₁St hw₁) (fun h => hw₁γ (hA₁s h)) (hΔU _ (hU₁ hw₁) hw₁a)
    rcases (hbΔ ▸ h : z ∈ A₁ ∪ (A' ∪ β)) with h | h | h
    · exact hzA h
    · rcases hin ⟨hγ₂St (hA's h), hz⟩ with rfl | rfl
      · exact hzA haA₁
      · exact hb₂A' h
    · exact hzA ((hβ₁.le ⟨h, hz⟩ : z = x) ▸ hxA₁)
  have hS₂Δ : St₂ ∩ Δ ⊆ A' := by
    refine disc_off hman hSt₂ (hA's.trans (hb₂ ▸ subset_union_right)) hΔ (fun z hz hzA h => ?_)
      (hL₂St hw₂) (fun h => hw₂γ (hA's h)) (hΔU _ (hU₂ hw₂) hw₂a)
    rcases (hbΔ ▸ h : z ∈ A₁ ∪ (A' ∪ β)) with h | h | h
    · rcases hin ⟨hz, hγ₁St (hA₁s h)⟩ with rfl | rfl
      · exact hzA haA'
      · exact hb₂A₁ h
    · exact hzA h
    · exact hzA ((hβ₂.le ⟨h, hz⟩ : z = y) ▸ hyA')
  by_cases hbb : b₁ = b₂
  · subst hbb
    have hR₁γ : R₁ ⊆ γ₁ := fun z hz => hu₁ ▸ Or.inr hz
    have hR₂γ : R₂ ⊆ γ₂ := fun z hz => hu₂ ▸ Or.inr hz
    have haR₁ : a ∉ R₁ := fun h => hNr haN ((hi'₁.le ⟨haA₁, h⟩ : a = x) ▸ hxr)
    have haR₂ : a ∉ R₂ := fun h => hNr haN ((hi'₂.le ⟨haA', h⟩ : a = y) ▸ hβr hβ.left_mem)
    have hRβ : R₂ ∩ β = {y} := by
      apply subset_antisymm
      · rintro z ⟨h1, h2⟩
        exact hβ₂.le ⟨h2, hγ₂St (hR₂γ h1)⟩
      · rintro _ rfl
        exact ⟨hR₂.left_mem, hβ.left_mem⟩
    have hB := hR₂.symm.union hβ hRβ
    have hF₂ : IsOArc (R₁ ∪ (R₂ ∪ β)) := by
      refine oArc_of_lines hR₁.symm hB ?_
      apply subset_antisymm
      · rintro z ⟨h1, h2 | h2⟩
        · rcases hin ⟨hγ₂St (hR₂γ h2), hγ₁St (hR₁γ h1)⟩ with rfl | rfl
          · exact absurd h1 haR₁
          · exact .inl rfl
        · exact .inr (hβ₁.le ⟨h2, hγ₁St (hR₁γ h1)⟩)
      · rintro z (rfl | rfl)
        · exact ⟨hR₁.right_mem, .inl hR₂.right_mem⟩
        · exact ⟨hR₁.left_mem, .inr hβ.right_mem⟩
    obtain ⟨Δ₂, hΔ₂, hbΔ₂, hΔ₂U⟩ := curve_disc hΓ hr hb₁N hF₂ (fun z hz hne => by
      rcases hz with h | h | h
      · refine hr₁ ⟨hγ₁St (hR₁γ h), fun hL => ?_⟩
        rcases hi₁.le ⟨hL, hR₁γ h⟩ with e | e
        · exact haR₁ (e ▸ h)
        · exact hne e
      · refine hr₂ ⟨hγ₂St (hR₂γ h), fun hL => ?_⟩
        rcases hi₂.le ⟨hL, hR₂γ h⟩ with e | e
        · exact haR₂ (e ▸ h)
        · exact hne e
      · exact hβr h)
    have hβΔ₂ : β ⊆ discBd Δ₂ := hbΔ₂ ▸ subset_union_right.trans subset_union_right
    have hm := filled_sector_meets_disc_in_joining_arc hman haN St₁ γ₁ hγ₁ St₂ γ₂ A₁ x y β hβ A'
      R₁ R₂ hi'₁ hi'₂ hγ₁St hγ₂St Δ hΔ hA₁Δ hβΔ haA₁ hS₁Δ hS₂Δ hR₁γ hR₂γ Δ₂ hΔ₂ hbΔ₂ hΔ₂U
      hβΔ₂ (fun h => hNr haN (hβr h))
    obtain ⟨hD, hbD⟩ := disc_union _ _ _ _ _ hΔ hΔ₂ hβ hm hβΔ hβΔ₂
    have hγ₁D : γ₁ ⊆ discBd (Δ ∪ Δ₂) := by
      rw [hbD]
      exact subset_union_sdiff_of_inter_subset
        (hu₁ ▸ union_subset_union hA₁Δ (hbΔ₂ ▸ subset_union_left))
        (fun z hz => Or.inr (hβ₁.le ⟨hz.2, hγ₁St hz.1⟩))
    have hγ₂D : γ₂ ⊆ discBd (Δ ∪ Δ₂) := by
      rw [hbD]
      exact subset_union_sdiff_of_inter_subset (hu₂ ▸ union_subset_union hA'Δ
          (hbΔ₂ ▸ subset_union_left.trans subset_union_right))
        (fun z hz => Or.inl (hβ₂.le ⟨hz.2, hγ₂St hz.1⟩))
    have hS₁Δ₂ : St₁ ∩ Δ₂ ⊆ R₁ := by
      have hsub : R₁ ⊆ discBd St₁ := by rw [hb₁, ← hu₁]; exact fun z hz => .inr (.inr hz)
      refine disc_off hman hSt₁ hsub hΔ₂ (fun z hz hzR h => ?_) (hL₁St hw₁) (fun h => hw₁γ
        (hR₁γ h)) (hΔ₂U _ (hU₁ hw₁) hw₁b)
      rcases (hbΔ₂ ▸ h : z ∈ R₁ ∪ (R₂ ∪ β)) with h | h | h
      · exact hzR h
      · rcases hin ⟨hγ₂St (hR₂γ h), hz⟩ with rfl | rfl
        · exact haR₂ h
        · exact hzR hR₁.right_mem
      · exact hzR ((hβ₁.le ⟨h, hz⟩ : z = x) ▸ hR₁.left_mem)
    have hS₂Δ₂ : St₂ ∩ Δ₂ ⊆ R₂ := by
      have hsub : R₂ ⊆ discBd St₂ := by rw [hb₂, ← hu₂]; exact fun z hz => .inr (.inr hz)
      refine disc_off hman hSt₂ hsub hΔ₂ (fun z hz hzR h => ?_) (hL₂St hw₂) (fun h => hw₂γ
        (hR₂γ h)) (hΔ₂U _ (hU₂ hw₂) hw₂b)
      rcases (hbΔ₂ ▸ h : z ∈ R₁ ∪ (R₂ ∪ β)) with h | h | h
      · rcases hin ⟨hz, hγ₁St (hR₁γ h)⟩ with rfl | rfl
        · exact haR₁ h
        · exact hzR hR₂.right_mem
      · exact hzR h
      · exact hzR ((hβ₂.le ⟨h, hz⟩ : z = y) ▸ hR₂.left_mem)
    have hm₁ : St₁ ∩ (Δ ∪ Δ₂) = γ₁ := by
      apply subset_antisymm
      · rintro z ⟨hz, h | h⟩
        · exact hA₁s (hS₁Δ ⟨hz, h⟩)
        · exact hR₁γ (hS₁Δ₂ ⟨hz, h⟩)
      · exact fun z hz => ⟨hγ₁St hz, discBd_subset _ (hγ₁D hz)⟩
    obtain ⟨hY₁, hbY₁⟩ := disc_union _ _ _ _ _ hSt₁ hD hγ₁ hm₁ (hb₁ ▸ subset_union_right) hγ₁D
    have hm₂ : (St₁ ∪ (Δ ∪ Δ₂)) ∩ St₂ = γ₂ := by
      apply subset_antisymm
      · rintro z ⟨h | h | h, hz⟩
        · rcases hin ⟨hz, h⟩ with rfl | rfl
          · exact hγ₂.left_mem
          · exact hγ₂.right_mem
        · exact hA's (hS₂Δ ⟨hz, h⟩)
        · exact hR₂γ (hS₂Δ₂ ⟨hz, h⟩)
      · exact fun z hz => ⟨.inr (discBd_subset _ (hγ₂D hz)), hγ₂St hz⟩
    have hγ₂Y : γ₂ ⊆ discBd (St₁ ∪ (Δ ∪ Δ₂)) := hbY₁ ▸
      subset_union_sdiff_of_inter_subset (hγ₂D.trans subset_union_right)
        (fun _ hz => hin ⟨hγ₂St hz.1, hγ₁St hz.2⟩)
    obtain ⟨hY, hbY⟩ := disc_union _ _ _ _ _ hY₁ hSt₂ hγ₂ hm₂ hγ₂Y (hb₂ ▸ subset_union_right)
    refine ⟨_, hY, fun z hz => ?_, fun z hz => ?_, ?_⟩
    · rw [hbY, hbY₁]
      exact ⟨.inl ⟨.inl (hb₁ ▸ .inl hz), fun h => h.2 (hi₁.le ⟨hz, h.1⟩)⟩,
        fun h => h.2 (hin ⟨hγ₂St h.1, hL₁St hz⟩)⟩
    · rw [hbY]
      exact ⟨.inr (hb₂ ▸ .inl hz), fun h => h.2 (hi₂.le ⟨hz, h.1⟩)⟩
    · rintro z ⟨(h | h | h) | h, hzU⟩
      · exact .inl (hU'₁ ⟨h, hzU⟩)
      · by_contra hn
        refine hΔU z hzU (fun e => hn (.inl (e ▸ h₁.1.2.1.left_mem))) h
      · by_contra hn
        refine hΔ₂U z hzU (fun e => hn (.inl (e ▸ h₁.1.2.1.right_mem))) h
      · exact .inr (hU'₂ ⟨h, hzU⟩)
  · have hb₂St : b₂ ∉ St₁ := fun h => by
      have h3 := hU'₁ ⟨h, Γ.N_subset hb₂N⟩
      rcases h₁.1.2.2.2.le ⟨h3, hb₂N⟩ with e | e
      · exact hγ₂.ne'.symm e
      · exact hbb e.symm
    have hin' : ∀ {z}, z ∈ St₂ → z ∈ St₁ → z = a := fun {z} h h' => by
      rcases hin ⟨h, h'⟩ with e | e
      · exact e
      · exact absurd (e ▸ h') hb₂St
    have hm₁ : St₁ ∩ Δ = A₁ := subset_antisymm hS₁Δ fun z hz => ⟨hγ₁St (hA₁s hz), discBd_subset _
      (hA₁Δ hz)⟩
    obtain ⟨hY₁, hbY₁⟩ := disc_union _ _ _ _ _ hSt₁ hΔ hA₁ hm₁ (hA₁s.trans
      (hb₁ ▸ subset_union_right)) hA₁Δ
    have hm₂ : (St₁ ∪ Δ) ∩ St₂ = A' := by
      apply subset_antisymm
      · rintro z ⟨h | h, hz⟩
        · exact hin' hz h ▸ haA'
        · exact hS₂Δ ⟨hz, h⟩
      · exact fun z hz => ⟨.inr (discBd_subset _ (hA'Δ hz)), hγ₂St (hA's hz)⟩
    have hA'Y : A' ⊆ discBd (St₁ ∪ Δ) := fun z hz => by
      rw [hbY₁]
      exact ⟨.inr (hA'Δ hz), fun h => h.2 (hiA.le ⟨h.1, .inl hz⟩)⟩
    obtain ⟨hY, hbY⟩ := disc_union _ _ _ _ _ hY₁ hSt₂ hA' hm₂ hA'Y (hA's.trans
      (hb₂ ▸ subset_union_right))
    have hoff : ∀ {L z}, L ⊆ Γ.U → z ∈ L → z ∈ A₁ ∪ A' → z = a := fun {L z} hLU hz h => by
      by_contra hn
      refine disjoint_left.mp (hdr hLU) hz ?_
      exact h.elim (fun h => hA₁r z h hn) (fun h => hA₂r z (.inl h) hn)
    refine ⟨_, hY, fun z hz => ?_, fun z hz => ?_, ?_⟩
    · rw [hbY, hbY₁]
      exact ⟨.inl ⟨.inl (hb₁ ▸ .inl hz), fun h => h.2 (.inl (hoff hU₁ hz (.inl h.1)))⟩,
        fun h => h.2 (.inl (hoff hU₁ hz (.inr h.1)))⟩
    · rw [hbY]
      exact ⟨.inr (hb₂ ▸ .inl hz), fun h => h.2 (.inl (hoff hU₂ hz (.inr h.1)))⟩
    · rintro z ⟨(h | h) | h, hzU⟩
      · exact .inl (hU'₁ ⟨h, hzU⟩)
      · by_contra hn
        exact hΔU z hzU (fun e => hn (.inl (e ▸ h₁.1.2.1.left_mem))) h
      · exact .inr (hU'₂ ⟨h, hzU⟩)

end Painting

end GraphMinor.GM17
