/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section10i

import LeanPool.GraphMinor.GM17.Bridge

/-!
# Graph Minors XX: deductions from Section10i

The deductions apply the proved results after their geometric prerequisites.
-/

public section
namespace GraphMinor.GM17.Portrayal
open Set Topology GraphMinor.Surface GraphMinor.GM18 GraphMinor.GM20 GraphMinor.GM10
  GraphMinor.GM20.GM17
universe u v
variable {α : Type u} {β : Type v} {P : UnlabeledPatchwork α β} {π : Portrayal P.G.toHypergraph}
  {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}

/-- A consequence of (8.7) of Graph Minors XVII: two cells at each node. -/
theorem two_cells_of_87 {G : Hypergraph α β} {π : Portrayal G}
    (h₈₇ : ∀ n ∈ π.Γ.N, 2 ≤ {c ∈ starCells π.Γ | n ∈ tilde c}.ncard) :
    ∀ n ∈ π.Γ.N, ∃ c₁ ∈ π.Γ.C, ∃ c₂ ∈ π.Γ.C, c₁ ≠ c₂ ∧ n ∈ tilde c₁ ∧ n ∈ tilde c₂ := by
  intro n hn
  have hfinite : {c ∈ starCells π.Γ | n ∈ tilde c}.Finite :=
    π.Γ.finite_cells.subset fun _ hc ↦ hc.1.1
  obtain ⟨c₁, c₂, h₁, h₂, hne⟩ := (Set.one_lt_ncard_iff hfinite).mp (h₈₇ n hn)
  exact ⟨c₁, h₁.1.1, c₂, h₂.1.1, hne, h₁.2, h₂.2⟩

variable {r t : ℕ}

theorem isThreeConnected_of_standing
    (hs : Standing 𝒯 θ p (2 * p + 3) (4 * p + 5) π) (h₂ : ∀ c ∈ π.Γ.C, 2 ≤ (tilde c).ncard) :
    (π.paintingOf' h₂).IsThreeConnected := by
  refine ⟨fun F hF hU hN ↦ ?_, fun F hF hU hN hbd ↦ ?_⟩
  · have hcount : (F ∩ π.Γ.N).ncard ≤ 2 := hN
    obtain ⟨Δ, h₁, h₃, -, h₄⟩ :=
      GraphMinor.GM17.gm17Theorem85.{u, v} 𝒯 θ p π hs F hF hU (by omega)
    rcases h₄ with ⟨h₅, h₆⟩ | ⟨h₅, -⟩
    · exact ⟨Δ, h₁, h₃, h₆, h₅⟩
    · have : (F ∩ π.Γ.N).ncard ≤ 2 := hN
      omega
  · obtain ⟨f⟩ := hF
    have hend : ∀ {x : F}, (∃ t, IsLineWithEnds F x.1 t) → x.1 ∈ F ∩ π.Γ.N := by
      intro x hx
      have h₁ : x.1 ∈ F ∩ bd π.S := by
        rw [hbd]
        exact hx
      exact ⟨x.2, hU ⟨x.2, π.Γ.bd_subset h₁.2⟩⟩
    have h₀ := hend (x := f 0) ⟨(f 1).1, f, rfl, rfl⟩
    have h₁ := hend (x := f 1) ⟨(f 0).1, unitInterval.symmHomeomorph.trans f,
      by simp, by simp⟩
    have hne : (f 0).1 ≠ (f 1).1 := fun h ↦ zero_ne_one (f.injective (Subtype.ext h))
    have hfin : (F ∩ π.Γ.N).Finite := π.Γ.finite_N.subset inter_subset_right
    have h₂' : 1 < (F ∩ π.Γ.N).ncard := (Set.one_lt_ncard_iff hfin).mpr ⟨_, _, h₀, h₁, hne⟩
    have hle : (F ∩ π.Γ.N).ncard ≤ 2 := hN
    obtain ⟨Δ, h₃, h₄, h₅, h₆, h₇⟩ := GraphMinor.GM17.gm17Theorem83.{u, v} 𝒯 θ p π hs F ⟨f⟩ hU hbd
      (by omega)
    exact ⟨Δ, h₃, h₄, h₅, h₇.le, h₆⟩

/-- `(P, ℒ)` is shelled, by (8.2)-(8.5), (8.7), (8.8), (9.1) and (9.8) of Graph Minors XVII. -/
theorem isShelled_of_standing [Infinite β]
     (hr : P.G.rootSet = ∅)
    (hs : Standing 𝒯 θ p (2 * p + 3) (4 * p + 5) π) :
    IsShelled π.gradedOf P π.cellLocation := by
  have hdom := GraphMinor.GM17.gm17Theorem84.{u, v} 𝒯 θ p π hs
  have h₂ := (GraphMinor.GM17.gm17Theorem82.{u, v} 𝒯 θ p π hs).2
  have h₈₇ := two_cells_of_87 fun n hn ↦ (GraphMinor.GM17.gm17Theorem87.{u, v} 𝒯 θ p π hs n hn).1
  have h₉₈ := GraphMinor.GM17.gm17Theorem98.{u, v} 𝒯 θ p π hs
  have hsize : ∀ c ∈ π.Γ.C, (c ∩ bd π.S).Nonempty → (tilde c).ncard = 2 := fun c hc hb ↦
    (π.Γ.border_cell c hc hb).1
  have hbd : ∀ c ∈ π.Γ.C, (c ∩ bd π.S).Nonempty → ∀ n ∈ tilde c,
      Disjoint (π.borderSet n) (π.nodeVertex '' π.Γ.N) := by
    rintro c hc ⟨x, hxc, hxb⟩ n hn
    obtain ⟨Θ, hΘ, hxΘ⟩ := exists_cuff_of_bd hxb
    obtain ⟨m, hm, hne⟩ := exists_other_end h₂ hc n
    exact (h₉₈ Θ hΘ c hc ⟨x, hxc, hxΘ⟩ n hn m hm hne.symm).2.2.1
  have hρ : ∀ Θ ∈ cuffs π.S, ∀ c ∈ π.Γ.C, (c ∩ Θ).Nonempty → ∀ n ∈ tilde c,
      (π.borderSet n).ncard = π.warpAt Θ := by
    intro Θ hΘ c hc hcΘ n hn
    obtain ⟨m, hm, hne⟩ := exists_other_end h₂ hc n
    exact (h₉₈ Θ hΘ c hc hcΘ n hn m hm hne.symm).1
  have hinj := injOn_cellRooted hdom hbd hsize (GraphMinor.GM17.gm17Theorem88.{u, v} 𝒯 θ p π hs)
  have hloc := isRootedLocation (π := π) hdom hr
  have hfine : IsFine P.G π.cellLocation := isFine_cellLocation
  have hne : Nonempty β := inferInstance
  obtain ⟨e, he⟩ := exists_injOn_of_finite (δ := β) (cellLocation_finite (π := π))
  obtain ⟨Q, hQ⟩ := exists_heart hloc hfine cellLocation_finite he
  have hE : Q.G.edgeSet = e '' π.cellLocation := by
    rw [hQ.edgeSet_eq, core_edgeSet_eq_empty hfine, empty_union]
  have hA : ∀ {c : Set π.S} {A}, c ∈ π.Γ.C → A ∈ π.cellLocation → e (π.cellRooted c) = e A →
      π.cellRooted c = A := fun {c} {_} hc hA h ↦ he ⟨c, hc, rfl⟩ hA h
  refine ⟨hfine, e, Q, π.paintingOf' h₂, hullOf hdom hr h₂ h₈₇ hbd hρ he hinj hQ hE, hQ, hE,
    isThreeConnected_of_standing hs h₂, ?_, ?_⟩
  · intro c hc A hAmem hcell hb
    obtain rfl := hA hc hAmem hcell
    refine ⟨roots_cellRooted_internal hdom hc hb, fun K hK hverts ↦ ?_⟩
    have hfin : (π.nodeVertex '' tilde c).Finite := (tilde_finite hc).image _
    have h₃ : (π.nodeVertex '' tilde c).ncard ≤ 3 :=
      (Set.ncard_image_le (tilde_finite hc)).trans (π.Γ.cell_disc c hc).2.2.2
    rw [hverts]
    refine exists_realizing_subgraph hfin h₃ ?_ hK hverts
    rintro _ ⟨n₁, h₁, rfl⟩ _ ⟨n₂, h₂', rfl⟩ hne
    exact GraphMinor.GM17.gm17Theorem91.{u, v} 𝒯 θ p π hs c hc hb n₁ h₁ n₂ h₂' fun h ↦ hne
      (by rw [h])
  · intro c hc A hAmem hcell Θ hΘ hcΘ n₁ h₁ n₂ h₂' hne
    obtain rfl := hA hc hAmem hcell
    obtain ⟨-, -, -, -, L, h₃, h₄, h₅⟩ := h₉₈ Θ hΘ c hc hcΘ n₁ h₁ n₂ h₂' hne
    refine ⟨L, h₃, h₄, ?_⟩
    rcases h₅ with h₅ | ⟨c', hc', hb', -, hsub⟩
    · exact Or.inl h₅
    · exact Or.inr ⟨c', hc', hb', hsub h₁, hsub h₂'⟩

/-- A cell has at most `2p + 3` roots: at most three nodes for an internal cell, and two nodes with
their
sets `β(n)` of size at most `p` for a border cell. -/
theorem ncard_rootsOf_le
     (hs : Standing 𝒯 θ p (2 * p + 3) (4 * p + 5) π)
    {c : Set π.S} (hc : c ∈ π.Γ.C) : (π.rootsOf c).ncard ≤ 2 * p + 3 := by
  have hdom := GraphMinor.GM17.gm17Theorem84.{u, v} 𝒯 θ p π hs
  have hfinr := rootsOf_finite hdom hc
  by_cases hb : (c ∩ bd π.S).Nonempty
  · obtain ⟨n₁, n₂, hne, hti⟩ := Set.ncard_eq_two.mp (π.Γ.border_cell c hc hb).1
    obtain ⟨x, hxc, hxb⟩ := hb
    obtain ⟨Θ, hΘ, hxΘ⟩ := exists_cuff_of_bd hxb
    have h₁ : n₁ ∈ tilde c := hti ▸ Or.inl rfl
    have h₂ : n₂ ∈ tilde c := hti ▸ Or.inr rfl
    obtain ⟨hq₁, hq₂, -⟩ := GraphMinor.GM17.gm17Theorem98.{u, v} 𝒯 θ p π hs Θ hΘ c hc ⟨x, hxc, hxΘ⟩
      n₁ h₁ n₂ h₂ hne
    have hq : π.warpAt Θ ≤ p := (warpAt_le_warp_of_mem π hΘ).trans hs.warp_le
    have hf₁ : (π.borderSet n₁).Finite := hfinr.subset fun v hv ↦ Or.inr ⟨⟨x, hxc, hxb⟩, n₁, h₁, hv⟩
    have hf₂ : (π.borderSet n₂).Finite := hfinr.subset fun v hv ↦ Or.inr ⟨⟨x, hxc, hxb⟩, n₂, h₂, hv⟩
    have hsub : π.rootsOf c ⊆ ({π.nodeVertex n₁, π.nodeVertex n₂} ∪ π.borderSet n₁) ∪
        π.borderSet n₂ := by
      rintro v (⟨n, hn, rfl⟩ | ⟨-, n, hn, hv⟩)
      · rw [hti] at hn
        rcases hn with rfl | rfl
        · exact Or.inl (Or.inl (Or.inl rfl))
        · exact Or.inl (Or.inl (Or.inr rfl))
      · rw [hti] at hn
        rcases hn with rfl | rfl
        · exact Or.inl (Or.inr hv)
        · exact Or.inr hv
    have hfp : ({π.nodeVertex n₁, π.nodeVertex n₂} : Set α).Finite := by simp
    have h₃ := Set.ncard_le_ncard hsub ((hfp.union hf₁).union hf₂)
    have h₄ := Set.ncard_union_le ({π.nodeVertex n₁, π.nodeVertex n₂} ∪ π.borderSet n₁)
      (π.borderSet n₂)
    have h₅ := Set.ncard_union_le ({π.nodeVertex n₁, π.nodeVertex n₂} : Set α) (π.borderSet n₁)
    have h₆ : ({π.nodeVertex n₁, π.nodeVertex n₂} : Set α).ncard ≤ 2 := by
      have := Set.ncard_insert_le (π.nodeVertex n₁) ({π.nodeVertex n₂} : Set α)
      rwa [Set.ncard_singleton] at this
    omega
  · have hsub : π.rootsOf c ⊆ π.nodeVertex '' tilde c := by
      rintro v (h | ⟨h, -⟩)
      · exact h
      · exact (hb h).elim
    have h₁ := Set.ncard_le_ncard hsub ((tilde_finite hc).image _)
    have h₂ := Set.ncard_image_le (f := π.nodeVertex) (tilde_finite hc)
    have h₃ := (π.Γ.cell_disc c hc).2.2.2
    omega

/-- Each root of `A_c` lies in another cell. For `γ(n)` this is (8.7) of Graph Minors XVII. For
`v ∈ β(n)` with `n` on a cuff, take the other cell of the cuff at `n`. -/
theorem rootsOf_subset_other
    (hs : Standing 𝒯 θ p (2 * p + 3) (4 * p + 5) π) {c : Set π.S} (hc : c ∈ π.Γ.C) :
    π.rootsOf c ⊆ (π.cellGraph c).vertexSet ∩ π.otherVertices c := by
  have hdom := GraphMinor.GM17.gm17Theorem84.{u, v} 𝒯 θ p π hs
  have h₂ := (GraphMinor.GM17.gm17Theorem82.{u, v} 𝒯 θ p π hs).2
  have h₈₇ := two_cells_of_87 fun n hn ↦ (GraphMinor.GM17.gm17Theorem87.{u, v} 𝒯 θ p π hs n hn).1
  intro v hv
  refine ⟨rootsOf_subset hdom hc hv, ?_⟩
  rcases hv with ⟨n, hn, rfl⟩ | ⟨hb, n, hn, hv⟩
  · have hnN := tilde_subset_nodes π.Γ hc hn
    obtain ⟨c₁, hc₁, c₂, hc₂, hne, h₁, h₃⟩ := h₈₇ n hnN
    by_cases h : c₁ = c
    · exact ⟨c₂, hc₂, fun h' ↦ hne (h.trans h'.symm), π.p2 c₂ hc₂ n ⟨h₃, hdom ▸ hnN⟩⟩
    · exact ⟨c₁, hc₁, h, π.p2 c₁ hc₁ n ⟨h₁, hdom ▸ hnN⟩⟩
  · have hnN := tilde_subset_nodes π.Γ hc hn
    obtain ⟨Θ, hΘ, hnΘ⟩ := exists_cuff_of_bd (tilde_subset_bd hc hb hn)
    obtain ⟨c₁, hc₁, c₂, hc₂, hne, h₁, h₃, ⟨x₁, h₄, h₅⟩, ⟨x₂, h₆, h₇⟩⟩ :=
      exists_two_cells π.isSurface (π.paintingOf' h₂) hΘ ⟨hnN, hnΘ⟩
    by_cases h : c₁ = c
    · exact ⟨c₂, hc₂, fun h' ↦ hne (h.trans h'.symm),
        π.p3_subset c₂ hc₂ ⟨x₂, h₆, cuff_subset_bd hΘ h₇⟩ n h₃ hv⟩
    · exact ⟨c₁, hc₁, h, π.p3_subset c₁ hc₁ ⟨x₁, h₄, cuff_subset_bd hΘ h₅⟩ n h₁ hv⟩

/-- `ℒ` is linked to `𝒯`. Since `π` is `𝒯`-central, `α(c)` is the small side of a member of `𝒯`, and
so
`(A_c⁻, (G \ A_c)⁻)` is in `𝒯`, by the first two tangle axioms. The second part is (11.7) of Graph
Minors XVII, since every root of `A_c` lies in `α(c) ∩ α(-c)`. -/
theorem isLinkedTo_of_standing
    (hr : P.G.rootSet = ∅) (hs : Standing 𝒯 θ p (2 * p + 4) (6 * p + 8) π) :
    IsLinkedTo P.G 𝒯 π.cellLocation := by
  have hs₈ : Standing 𝒯 θ p (2 * p + 3) (4 * p + 5) π := hs.mono (by omega) (by omega)
  have hdom := GraphMinor.GM17.gm17Theorem84.{u, v} 𝒯 θ p π hs₈
  have h𝒯 := hs.isTangle
  constructor
  · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    have hcomp := isComplemented_cellRooted hdom hr hc
    have hsep := isSeparation_complement hcomp
    have hord : Hypergraph.separationOrder (π.cellRooted c).toHypergraph
        (complementHypergraph P.G (π.cellRooted c)) < θ := by
      have h₁ := separationOrder_complement_le (G := P.G) (A := π.cellRooted c)
      rw [rootSet_cellRooted hdom hc] at h₁
      have h₂ := ncard_rootsOf_le hs₈ hc
      have h₃ := hs.lt
      omega
    rcases h𝒯.axiom1 hsep hord with h | h
    · exact h
    · exfalso
      obtain ⟨B, hB⟩ := hs.isTrue.1 c hc
      have heq := hsep.union_eq
      refine h𝒯.axiom2 hB h h ?_
      have hu : (π.cellGraph c ∪ complementHypergraph P.G (π.cellRooted c)) ∪
          complementHypergraph P.G (π.cellRooted c) =
          π.cellGraph c ∪ complementHypergraph P.G (π.cellRooted c) := by
        refine Hypergraph.ext ?_ ?_ ?_
        · exact Set.union_eq_left.mpr subset_union_right
        · exact Set.union_eq_left.mpr subset_union_right
        · funext e v
          exact propext ⟨fun h ↦ h.elim id Or.inr, Or.inl⟩
      rw [hu]
      exact heq
  · rintro _ ⟨c, hc, rfl⟩ A' B' hmem hle -
    have hsub := rootsOf_subset_other hs₈ hc
    have hfin : ((π.cellGraph c).vertexSet ∩ π.otherVertices c).Finite :=
      (π.cellGraph c).vertexSet_finite.subset inter_subset_left
    have hk := Set.ncard_le_ncard hsub hfin
    rw [rootSet_cellRooted hdom hc]
    by_contra hlt
    have hlt' := not_le.mp hlt
    have hle' : Hypergraph.separationOrder A' B' ≤ ((π.cellGraph c).vertexSet ∩ π.otherVertices
      c).ncard := by
      omega
    have heq := GraphMinor.GM17.gm17Theorem117.{u, v} 𝒯 θ p π hs c hc hmem hle hle'
    omega

end GraphMinor.GM17.Portrayal
