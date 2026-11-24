/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section8a
public import LeanPool.GraphMinor.GM20.Section9h
public import LeanPool.GraphMinor.GM20.Section10j

import LeanPool.GraphMinor.GM19.Main

import LeanPool.GraphMinor.Surface.PushOff

/-!
# Graph Minors XX, (8.1)

We deduce (8.1) from (2.1) of Graph Minors XIX. Each painting is made narrow as in `Section8a`. The
new
paintings are internally 3-connected, since by `PushOffStatement` an `O`-arc that misses the new set
`U` moves to an `O`-arc that misses the old one. A linear inflation between the new paintings gives
one between the old paintings, with the same map on the nodes. A painting with no cell is not
internally
3-connected, so we treat paintings with no cells apart, by counting nodes.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface

universe w

variable {S : Type} [TopologicalSpace S] [T2Space S]

open Thin

/-- The narrow painting of a 3-connected painting with a cell is internally 3-connected. -/
theorem isInternallyThreeConnected (hS : IsSurface S) {Γ : Painting S}
    {L : Set S → Set S} (hL : IsChordData Γ L) (h3 : Γ.IsThreeConnected) (hne : Γ.C.Nonempty) :
    (Thin.painting Γ L hL).IsInternallyThreeConnected := by
  refine ⟨by rw [painting_E]; exact hne.image _, ?_⟩
  intro F hF hFU _ hcard
  change F ∩ U' Γ L ⊆ Γ.N at hFU
  change (F ∩ Γ.N).ncard + _ ≤ 2 at hcard
  let ι : Set (Set S) := {c | c ∈ Γ.C ∧ (tilde c).ncard = 2}
  have hι : ι.Finite := Γ.finite_cells.subset fun _ h ↦ h.1
  have := hι.to_subtype
  let T : Set (Set S) := {c | c ∈ Γ.C ∧ (tilde c).ncard ≠ 2}
  have hT : T.Finite := Γ.finite_cells.subset fun _ h ↦ h.1
  let Z : Set S := Γ.N ∪ ⋃ c ∈ T, closure c
  have hZ : IsClosed Z :=
    Γ.finite_N.isClosed.union (hT.isClosed_biUnion fun _ _ ↦ isClosed_closure)
  have hZU : Z ⊆ U' Γ L := by
    rintro x (hx | hx)
    · exact Or.inl hx
    · simp only [mem_iUnion, exists_prop] at hx
      obtain ⟨c, hc, hx⟩ := hx
      refine Or.inr (mem_biUnion hc.1 ?_)
      simp only [W, ite_eq_right hc.2]
      exact hx
  have hmeet : ∀ {c c' : Set S}, c ∈ Γ.C → c' ∈ Γ.C → c ≠ c' → closure c ∩ closure c' ⊆ Γ.N := by
    intro c c' hc hc' hne x hx
    by_contra hn
    have h₁ : x ∈ c := by
      rw [← closure_diff hc]
      exact ⟨hx.1, hn⟩
    have h₂ : x ∈ c' := by
      rw [← closure_diff hc']
      exact ⟨hx.2, hn⟩
    exact hne (arcComponent_eq hc hc' h₁ h₂)
  obtain ⟨h, hfix, hZ', hD'⟩ := GraphMinor.Surface.push_off S hS ι Γ.N Z (fun i ↦ closure i.1)
    (fun i ↦ L i.1) Γ.finite_N
    hZ (fun i ↦ Γ.cell_disc _ i.2.1)
    (fun i ↦ by
      obtain ⟨a, b, h₁, h₂, h₃, h₄⟩ := hL i.1 i.2.1 i.2.2
      have ha : a ∈ tilde i.1 := by rw [h₂]; exact Or.inl rfl
      have hb : b ∈ tilde i.1 := by rw [h₂]; exact Or.inr rfl
      refine ⟨a, b, h₁, ?_, Γ.tilde_subset _ i.2.1 ha, Γ.tilde_subset _ i.2.1 hb, h₃, ?_⟩
      · rw [Γ.closure_inter _ i.2.1, h₂]
      · rcases h₄ with ⟨h₅, h₆⟩ | ⟨-, h₅⟩
        · refine Or.inl ⟨h₆, ?_⟩
          rintro x ⟨hx, hxb⟩
          by_contra hn
          have : x ∈ i.1 := by
            rw [← closure_diff i.2.1]
            exact ⟨hx, hn⟩
          exact h₅ ⟨x, this, hxb⟩
        · exact Or.inr h₅)
    (fun i j hij ↦ hmeet i.2.1 j.2.1 fun he ↦ hij (Subtype.ext he))
    (fun i ↦ by
      rintro x ⟨hx, hx' | hx'⟩
      · exact hx'
      · simp only [mem_iUnion, exists_prop] at hx'
        obtain ⟨c, hc, hx'⟩ := hx'
        exact hmeet i.2.1 hc.1 (fun he ↦ hc.2 (he ▸ i.2.2)) ⟨hx, hx'⟩)
    F hF (fun x hx ↦ hFU ⟨hx.1, hZU hx.2⟩)
    (fun i x hx ↦ by
      refine hFU ⟨hx.1, Or.inr (mem_biUnion i.2.1 ?_)⟩
      simp only [W, ite_eq_left i.2.2]
      exact hx.2)
  have hnorm : (h '' F) ∩ Γ.U ⊆ Γ.N := by
    rintro x ⟨hxF, hxU⟩
    by_contra hn
    have hc : pathComponentIn (Γ.U \ Γ.N) x ∈ Γ.C :=
      mem_arcComponentsIn_pathComponentIn ⟨hxU, hn⟩
    have hxc : x ∈ closure (pathComponentIn (Γ.U \ Γ.N) x) :=
      subset_closure (mem_pathComponentIn_self ⟨hxU, hn⟩)
    by_cases h₂ : (tilde (pathComponentIn (Γ.U \ Γ.N) x)).ncard = 2
    · exact hn (hD' ⟨_, hc, h₂⟩ ⟨hxF, hxc⟩)
    · exact hn (hZ' ⟨hxF, Or.inr (mem_biUnion (show _ ∈ T from ⟨hc, h₂⟩) hxc)⟩)
  have hsymm : ∀ n ∈ Γ.N, h.symm n = n := fun n hn ↦ by
    rw [Homeomorph.symm_apply_eq, hfix n hn]
  have hF' : (h '' F) ∩ Γ.N ⊆ F ∩ Γ.N := by
    rintro _ ⟨⟨y, hy, rfl⟩, hn⟩
    have h₁ := hsymm _ hn
    rw [h.symm_apply_apply] at h₁
    rw [← h₁] at hn ⊢
    exact ⟨hy, hn⟩
  have hle : ((h '' F) ∩ Γ.N).ncard ≤ 2 :=
    (Set.ncard_le_ncard hF' (Γ.finite_N.inter_of_right _)).trans (by omega)
  obtain ⟨Δ, h₁, h₂, -, h₄⟩ := h3.1 _ (image_isOArc h hF) hnorm hle
  refine ⟨h.symm '' Δ, image_isClosedDisc h.symm h₁, ?_, ?_⟩
  · rw [image_discBd, h₂, symm_image_image]
  · rintro _ ⟨⟨y, hy, rfl⟩, hn⟩
    have hyN : y = h (h.symm y) := by simp
    have h₅ : h.symm y ∈ Γ.N := hn
    rw [hfix _ h₅] at hyN
    have h₆ : y ∈ Γ.N := by rw [hyN]; exact h₅
    have h₇ := hF' ⟨h₄ ⟨hy, h₆⟩, h₆⟩
    rw [hsymm y h₆]
    exact h₇.1

/-- In a cell that borders a cuff, the part of the cell in the cuff is the part kept. -/
theorem inter_cuff {Γ : Painting S} {L : Set S → Set S} (hL : IsChordData Γ L) {c Θ : Set S}
    (hc : c ∈ Γ.C) (hΘ : Θ ∈ cuffs S) (hne : (c ∩ Θ).Nonempty) : c ∩ Θ = τ L c := by
  obtain ⟨x, hxb, rfl⟩ := hΘ
  have hΘb : connectedComponentIn (bd S) x ⊆ bd S := connectedComponentIn_subset _ _
  have h₁ := inter_bd hL hc
  have hsub : ∀ y ∈ c ∩ connectedComponentIn (bd S) x, y ∈ τ L c := fun y hy ↦ by
    have h₂ : y ∈ c ∩ bd S := ⟨hy.1, hΘb hy.2⟩
    rw [h₁] at h₂
    exact h₂.1
  obtain ⟨y, hy⟩ := hne
  have hyτ := hsub y hy
  have hbd := (τ_subset_bd hL hc ⟨y, hyτ, hΘb hy.2⟩).1
  have hτ : τ L c ⊆ connectedComponentIn (bd S) x := by
    have h₂ := (isPathConnected_τ hL hc).isConnected.isPreconnected
    rw [connectedComponentIn_eq hy.2]
    exact h₂.subset_connectedComponentIn hyτ hbd
  exact subset_antisymm hsub fun z hz ↦ ⟨τ_subset hL hc hz, hτ hz⟩

/-- A linear inflation of the narrow paintings is a linear inflation of the paintings. -/
theorem isLinearInflation_of_narrow {Γ Γ' : Painting S} {L L' : Set S → Set S}
    (hL : IsChordData Γ L) (hL' : IsChordData Γ' L') {σv : S → Set S} {σe : Set S → Set S}
    (hσ : GM19.IsLinearInflation (Thin.painting Γ L hL) (Thin.painting Γ' L' hL') σv σe) :
    IsLinearInflation Γ Γ' σv (fun c ↦ back Γ' L' (σe (τ L c))) := by
  have hmem : ∀ c ∈ Γ.C, τ L c ∈ (Thin.painting Γ L hL).E := fun c hc ↦ by
    rw [painting_E]
    exact ⟨c, hc, rfl⟩
  have key : ∀ c ∈ Γ.C, ∃ c' ∈ Γ'.C, σe (τ L c) = τ L' c' ∧ back Γ' L' (σe (τ L c)) = c' := by
    intro c hc
    have h₁ := hσ.edge_mem _ (hmem c hc)
    rw [painting_E] at h₁
    obtain ⟨c', hc', h₂⟩ := h₁
    exact ⟨c', hc', h₂.symm, by rw [← h₂, back_τ hL' hc']⟩
  have hγ : ∀ c ∈ Γ.C, (Thin.painting Γ L hL).γ (τ L c) = Γ.γ c := fun c hc ↦ by
    change Γ.γ (back Γ L (τ L c)) = _
    rw [back_τ hL hc]
  have hγ' : ∀ e, (Thin.painting Γ' L' hL').γ e = Γ'.γ (back Γ' L' e) := fun _ ↦ rfl
  have hnode : ∀ c ∈ Γ.C, ∀ (i : ℕ) (hi : i < (Γ.γ c).length), (Γ.γ c)[i] ∈ Γ.N := by
    intro c hc i hi
    have h₁ : (Γ.γ c)[i] ∈ {n | n ∈ Γ.γ c} := List.getElem_mem hi
    rw [Γ.γ_set c hc] at h₁
    exact tilde_subset_N Γ hc h₁
  have hends : ∀ c ∈ Γ.C, ∀ (i : ℕ) (hi : i < (Γ.γ c).length)
      (hi' : i < (Γ'.γ (back Γ' L' (σe (τ L c)))).length),
      (Γ'.γ (back Γ' L' (σe (τ L c))))[i] ∈ σv (Γ.γ c)[i] := by
    intro c hc i hi hi'
    have h₁ := hσ.ends _ (hmem c hc) i (by rw [hγ c hc]; exact hi) hi'
    rwa [List.getElem_of_eq (hγ c hc)] at h₁
  refine
    { cell_mem := ?_, cell_size := ?_, borders_iff := ?_, cell_injOn := ?_, orientation := ?_,
      node_nonempty := hσ.vertex_nonempty, node_subset := hσ.vertex_subset, node_connected := ?_,
      node_disjoint := hσ.vertex_disjoint, nodes := ?_, border_cell := ?_ }
  · intro c hc
    obtain ⟨c', hc', -, h₂⟩ := key c hc
    simpa only [h₂] using hc'
  · intro c hc
    obtain ⟨c', hc', h₁, h₂⟩ := key c hc
    have h₃ := hσ.edge_size _ (hmem c hc)
    rw [h₁, tilde_τ hL' hc', tilde_τ hL hc] at h₃
    simpa only [h₂] using h₃
  · intro c hc Θ hΘ
    obtain ⟨c', hc', h₁, h₂⟩ := key c hc
    have h₃ := hσ.borders_iff _ (hmem c hc) Θ hΘ
    rw [h₁] at h₃
    simp only [h₂]
    have hb : ∀ {Γ₀ : Painting S} {L₀ : Set S → Set S} (_ : IsChordData Γ₀ L₀) {c₀ : Set S},
        c₀ ∈ Γ₀.C → ((c₀ ∩ Θ).Nonempty ↔ (τ L₀ c₀ ∩ Θ).Nonempty) := by
      intro Γ₀ L₀ h₀ c₀ hc₀
      constructor
      · intro h₄
        have h₅ := inter_cuff h₀ hc₀ hΘ h₄
        obtain ⟨y, hy⟩ := h₄
        exact ⟨y, h₅ ▸ hy, hy.2⟩
      · rintro ⟨y, hy, hy'⟩
        exact ⟨y, τ_subset h₀ hc₀ hy, hy'⟩
    rw [hb hL hc, h₃, ← hb hL' hc']
  · intro c₁ h₁ c₂ h₂ he
    obtain ⟨c₁', -, h₃, h₄⟩ := key c₁ h₁
    obtain ⟨c₂', -, h₅, h₆⟩ := key c₂ h₂
    have h₇ : c₁' = c₂' := by rw [← h₄, ← h₆]; exact he
    have h₈ : σe (τ L c₁) = σe (τ L c₂) := by rw [h₃, h₅, h₇]
    exact τ_injOn hL h₁ h₂ (hσ.edge_injOn (hmem _ h₁) (hmem _ h₂) h₈)
  · intro c hc Θ hΘ hne f n n' hn hn' hpre
    obtain ⟨c', hc', h₁, h₂⟩ := key c hc
    simp only [h₂] at hn' ⊢
    have hne' : (τ L c ∩ Θ).Nonempty := by
      have h₃ := inter_cuff hL hc hΘ hne
      obtain ⟨y, hy⟩ := hne
      exact ⟨y, h₃ ▸ hy, hy.2⟩
    have h₃ := hσ.orientation _ (hmem c hc) Θ hΘ hne' f n n' (by rw [hγ c hc]; exact hn)
      (by rw [hγ', h₁, back_τ hL' hc']; exact hn') (by rw [← inter_cuff hL hc hΘ hne]; exact hpre)
    have hb := (hσ.borders_iff _ (hmem c hc) Θ hΘ).mp hne'
    rw [h₁] at hb h₃
    have hne'' : (c' ∩ Θ).Nonempty := by
      obtain ⟨y, hy, hy'⟩ := hb
      exact ⟨y, τ_subset hL' hc' hy, hy'⟩
    rw [inter_cuff hL' hc' hΘ hne'']
    exact h₃
  · intro n hn
    have h₁ := hσ.vertex_connected n hn
    rw [painting_skAdj] at h₁
    exact h₁
  · intro n hn c hc i hi hi'
    have h₁ := hends c hc i hi hi'
    constructor
    · rintro rfl
      exact h₁
    · intro h₂
      by_contra hne
      exact Set.disjoint_left.mp (hσ.vertex_disjoint _ (hnode c hc i hi) n hn hne) h₁ h₂
  · intro c' hc' hb hni
    have hb' : GM19.Painting.IsBorder (τ L' c') := by
      obtain ⟨x, hx, hx'⟩ := hb
      have h₁ : x ∈ c' ∩ bd S := ⟨hx, hx'⟩
      rw [inter_bd hL' hc'] at h₁
      exact ⟨x, h₁⟩
    have hni' : τ L' c' ∉ σe '' (Thin.painting Γ L hL).E := by
      rintro ⟨_, he, h₁⟩
      rw [painting_E] at he
      obtain ⟨c, hc, rfl⟩ := he
      refine hni ⟨c, hc, ?_⟩
      change back Γ' L' (σe (τ L c)) = c'
      rw [h₁, back_τ hL' hc']
    obtain ⟨v, hv, h₁⟩ := hσ.border_edge _ (by rw [painting_E]; exact ⟨c', hc', rfl⟩) hb' hni'
    rw [tilde_τ hL' hc'] at h₁
    exact ⟨v, hv, h₁⟩

omit [T2Space S] in
/-- Paintings with no cells, with `|N(Γ)| ≤ |N(Γ')|`: a linear inflation is an injection of the
nodes. -/
theorem isLinearInflation_of_empty [Nonempty S] {Γ Γ' : Painting S} (hC : Γ.C = ∅) (hC' : Γ'.C = ∅)
    (hle : Γ.N.ncard ≤ Γ'.N.ncard) :
    ∃ ζn : S → Set S, IsLinearInflation Γ Γ' ζn id := by
  have hle' : Γ.N.encard ≤ Γ'.N.encard := by
    rw [← Γ.finite_N.cast_ncard_eq, ← Γ'.finite_N.cast_ncard_eq]
    exact_mod_cast hle
  obtain ⟨g, hg, hinj⟩ := Γ.finite_N.exists_injOn_of_encard_le hle'
  refine ⟨fun n ↦ {g n}, ?_⟩
  refine
    { cell_mem := ?_, cell_size := ?_, borders_iff := ?_, cell_injOn := ?_, orientation := ?_,
      node_nonempty := fun n _ ↦ singleton_nonempty _, node_subset := ?_, node_connected := ?_,
      node_disjoint := ?_, nodes := ?_, border_cell := ?_ }
  · simp [hC]
  · simp [hC]
  · simp [hC]
  · simp [hC]
  · simp [hC]
  · intro n hn _ hx
    obtain rfl := mem_singleton_iff.mp hx
    exact hg hn
  · intro n _ x y
    have : x = y := Subtype.ext (by rw [mem_singleton_iff.mp x.2, mem_singleton_iff.mp y.2])
    rw [this]
  · intro n₁ h₁ n₂ h₂ hne
    exact Set.disjoint_singleton.mpr fun he ↦ hne (hinj h₁ h₂ he)
  · simp [hC]
  · simp [hC']

/-- Graph Minors XX, (8.1) (page 348), from (2.1) of Graph Minors XIX and `PushOffStatement`. -/
theorem theorem_8_1_proof : Theorem81Statement.{w} := by
  classical
  intro S _ Ω _ hS hc hΩ Γ φ h3
  have : T2Space S := hS.2.1
  choose L hL using fun i ↦ exists_chordData (Γ i)
  by_cases hinf : {i | (Γ i).C.Nonempty}.Infinite
  · let g : ℕ → ℕ := Nat.nth fun i ↦ (Γ i).C.Nonempty
    have hg : StrictMono g := Nat.nth_strictMono hinf
    have hgm : ∀ k, (Γ (g k)).C.Nonempty := fun k ↦ Nat.nth_mem_of_infinite hinf k
    obtain ⟨k, l, hkl, σv, σe, hσ, hφ⟩ := GraphMinor.GM19.gm19_main.{w} S hS hc hΩ
      (fun k ↦ Thin.painting (Γ (g k)) (L (g k)) (hL (g k)))
      (fun k e ↦ φ (g k) (back (Γ (g k)) (L (g k)) e))
      (fun k ↦ isInternallyThreeConnected hS (hL _) (h3 _) (hgm k))
    refine ⟨g k, g l, hg hkl, σv, _, isLinearInflation_of_narrow (hL _) (hL _) hσ, fun c hc ↦ ?_⟩
    have h₁ := hφ (τ (L (g k)) c) (by rw [painting_E]; exact ⟨c, hc, rfl⟩)
    simp only [back_τ (hL _) hc] at h₁
    exact h₁
  · obtain ⟨B, hB⟩ := (Set.not_infinite.mp hinf).bddAbove
    have hemp : ∀ n, (Γ (B + 1 + n)).C = ∅ := fun n ↦ by
      by_contra hne
      have := hB (nonempty_iff_ne_empty.mpr hne)
      omega
    obtain ⟨k, l, hkl, hle⟩ := (wellQuasiOrdered_le (α := ℕ))
      (fun n ↦ (Γ (B + 1 + n)).N.ncard)
    have : Nonempty S := hc.toNonempty
    obtain ⟨ζn, hζ⟩ := isLinearInflation_of_empty (hemp k) (hemp l) hle
    refine ⟨B + 1 + k, B + 1 + l, by omega, ζn, id, hζ, fun c hc' ↦ ?_⟩
    rw [hemp k] at hc'
    exact hc'.elim

end GraphMinor.GM20
