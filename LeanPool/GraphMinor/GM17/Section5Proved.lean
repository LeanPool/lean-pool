/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section5

public import LeanPool.GraphMinor.GM17.Section4
import LeanPool.GraphMinor.Surface.DiscUnion
import LeanPool.GraphMinor.Surface.DiscsInSurface
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

import LeanPool.GraphMinor.Surface.Cuffs

import LeanPool.GraphMinor.GM17.CutArcPaint

import LeanPool.GraphMinor.GM17.PasteCuff

import LeanPool.GraphMinor.GM17.PushNode

/-!
# Graph Minors XVII: proved deductions of Section5

The portrayal deductions use the existing painting proofs. The definitions and
independent geometric lemmas are imported from `Section5`.
-/

public section

namespace GraphMinor.GM17

open Set Topology Metric GraphMinor.Surface GraphMinor.GM10 GraphMinor.Hypergraph

local notation "𝕀" => unitInterval

universe u v

/-! ## 1. Shrinking a Cell from a Node (Page 171) -/

open Classical in
private noncomputable abbrev capped_zero_warp_portrayal
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    (hp5_Θ : ∀ c ∈ π.Γ.C, (c ∩ Θ).Nonempty → ∀ v ∈ (π.cellGraph c).vertexSet, (∃ c' ∈ π.Γ.C, c' ≠
      c ∧ v ∈ (π.cellGraph c').vertexSet) → v ∈ π.nodeVertex '' (tilde c ∩ π.domγ))
    (S' : Type)
    [tS' : TopologicalSpace S']
    [connS' : ConnectedSpace S']
    (hsS' : IsSurface S')
    (ι : π.S → S')
    (Γ' : Painting S')
    (hι_inj : Function.Injective ι)
    (hΓ'N : Γ'.N = ι '' π.Γ.N)
    (hΓ'C : Γ'.C = (fun c => ι '' c) '' π.Γ.C)
    (hbdS' : bd S' = ι '' (bd π.S \ Θ))
    (hcuffsS' : cuffs S' = (fun Θ' => ι '' Θ') '' (cuffs π.S \ {Θ}))
    (htilde_ι : ∀ c ∈ π.Γ.C, tilde (ι '' c) = ι '' tilde c)
    (horder_ι : ∀ Θ' ∈ cuffs π.S, Θ' ≠ Θ → ∀ n₁ ∈ π.Γ.N ∩ Θ', ∀ n₂ ∈ π.Γ.N ∩ Θ', ∀ n₃ ∈ π.Γ.N ∩
      Θ', ∀ n₄ ∈ π.Γ.N ∩ Θ', GM19.InOrderOn (ι '' Θ') (ι n₁) (ι n₂) (ι n₃) (ι n₄) → GM19.InOrderOn
      Θ' n₁ n₂ n₃ n₄)
    (α' : Set S' → Hypergraph α β)
    (hα'_eq : ∀ c ∈ π.Γ.C, α' (ι '' c) = π.cellGraph c)
    (β' : S' → Set α)
    (hβ'_eq : ∀ (n : π.S), β' (ι n) = π.borderSet n)
    (γ' : S' → α)
    (hγ'_eq : ∀ (n : π.S), γ' (ι n) = π.nodeVertex n)
    (hbd_iff : ∀ c ∈ π.Γ.C, (ι '' c ∩ bd S').Nonempty ↔
      (c ∩ bd π.S).Nonempty ∧ ¬(c ∩ Θ).Nonempty) : Portrayal G :=
  { S := S'
    top := tS'
    isSurface := hsS'
    connected := connS'
    Γ := Γ'
    cellGraph := α'
    borderSet := β'
    domγ := ι '' π.domγ
    nodeVertex := γ'
    cellGraph_le := by
      intro d hd
      rw [hΓ'C] at hd
      obtain ⟨c, hc, rfl⟩ := hd
      rw [hα'_eq c hc]
      exact π.cellGraph_le c hc
    borderSet_subset := by
      intro x ⟨hxN, hxbd⟩
      rw [hΓ'N] at hxN
      rw [hbdS'] at hxbd
      rcases hxN with ⟨n, hnN, rfl⟩
      rcases hxbd with ⟨m, hmbd, hmn⟩
      obtain rfl := hι_inj hmn
      rw [hβ'_eq m]
      exact π.borderSet_subset m ⟨hnN, hmbd.1⟩
    domγ_subset := by
      rw [hΓ'N]
      exact image_mono π.domγ_subset
    nodeVertex_mem := by
      rintro _ ⟨n, hn, rfl⟩
      rw [hγ'_eq n]
      exact π.nodeVertex_mem n hn
    nodeVertex_injOn := by
      rintro _ ⟨n₁, hn₁, rfl⟩ _ ⟨n₂, hn₂, rfl⟩ hEq
      rw [hγ'_eq n₁, hγ'_eq n₂] at hEq
      rw [π.nodeVertex_injOn hn₁ hn₂ hEq]
    p1_vertex := by
      intro v hv
      obtain ⟨c, hc, hvc⟩ := π.p1_vertex v hv
      exact ⟨ι '' c, hΓ'C ▸ mem_image_of_mem _ hc, by rwa [hα'_eq c hc]⟩
    p1_edge := by
      intro e he
      obtain ⟨c, hc, hec⟩ := π.p1_edge e he
      exact ⟨ι '' c, hΓ'C ▸ mem_image_of_mem _ hc, by rwa [hα'_eq c hc]⟩
    p1_disjoint := by
      intro d₁ hd₁ d₂ hd₂ hne
      rw [hΓ'C] at hd₁ hd₂
      obtain ⟨c₁, hc₁, rfl⟩ := hd₁
      obtain ⟨c₂, hc₂, rfl⟩ := hd₂
      rw [hα'_eq c₁ hc₁, hα'_eq c₂ hc₂]
      exact π.p1_disjoint c₁ hc₁ c₂ hc₂ (fun h => hne (congrArg _ h))
    p2 := by
      intro d hd x hx
      rw [hΓ'C] at hd
      obtain ⟨c, hc, rfl⟩ := hd
      rw [htilde_ι c hc, ← image_inter hι_inj] at hx
      obtain ⟨n, hn, rfl⟩ := hx
      rw [hγ'_eq n, hα'_eq c hc]
      exact π.p2 c hc n hn
    p3_notMem := by
      intro x ⟨hxγ, hxbd⟩
      rw [hbdS'] at hxbd
      rcases hxγ with ⟨n, hnγ, rfl⟩
      rcases hxbd with ⟨m, hmbd, hmn⟩
      obtain rfl := hι_inj hmn
      rw [hγ'_eq m, hβ'_eq m]
      exact π.p3_notMem m ⟨hnγ, hmbd.1⟩
    p3_subset := by
      intro d hd hdbd x hx
      rw [hΓ'C] at hd
      obtain ⟨c, hc, rfl⟩ := hd
      rw [htilde_ι c hc] at hx
      obtain ⟨n, hn, rfl⟩ := hx
      rw [hβ'_eq n, hα'_eq c hc]
      exact π.p3_subset c hc ((hbd_iff c hc).mp hdbd).1 n hn
    p4_disjoint := by
      intro Φ₁ hΦ₁ Φ₂ hΦ₂ hne x₁ hx₁ x₂ hx₂
      rw [hcuffsS'] at hΦ₁ hΦ₂
      obtain ⟨Θ₁, ⟨hΘ₁, _⟩, rfl⟩ := hΦ₁
      obtain ⟨Θ₂, ⟨hΘ₂, _⟩, rfl⟩ := hΦ₂
      rw [hΓ'N, ← image_inter hι_inj] at hx₁ hx₂
      obtain ⟨n₁, hn₁, rfl⟩ := hx₁
      obtain ⟨n₂, hn₂, rfl⟩ := hx₂
      rw [hβ'_eq n₁, hβ'_eq n₂]
      exact π.p4_disjoint Θ₁ hΘ₁ Θ₂ hΘ₂ (fun h => hne (congrArg _ h)) n₁ hn₁ n₂ hn₂
    p4_notMem := by
      intro Φ hΦ x₁ hx₁ x₂ hx₂ hx₂Φ
      rw [hcuffsS'] at hΦ
      obtain ⟨Θ₁, ⟨hΘ₁, _⟩, rfl⟩ := hΦ
      rw [hΓ'N, ← image_inter hι_inj] at hx₁
      obtain ⟨n₁, hn₁, rfl⟩ := hx₁
      obtain ⟨n₂, hn₂, rfl⟩ := hx₂
      rw [hγ'_eq n₂, hβ'_eq n₁]
      exact π.p4_notMem Θ₁ hΘ₁ n₁ hn₁ n₂ hn₂ (fun h => hx₂Φ (mem_image_of_mem ι h))
    p5 := by
      intro d hd hdbd v hv ⟨d₂, hd₂, hd₂_ne, hv₂⟩
      rw [hΓ'C] at hd hd₂
      obtain ⟨c, hc, rfl⟩ := hd
      obtain ⟨c₂, hc₂, rfl⟩ := hd₂
      rw [hα'_eq c hc] at hv
      rw [hα'_eq c₂ hc₂] at hv₂
      have hc₂_ne : c₂ ≠ c := fun h => hd₂_ne (congrArg _ h)
      rw [htilde_ι c hc, ← image_inter hι_inj]
      by_cases hcΘ : (c ∩ Θ).Nonempty
      · obtain ⟨n, hn, rfl⟩ := hp5_Θ c hc hcΘ v hv ⟨c₂, hc₂, hc₂_ne, hv₂⟩
        exact ⟨ι n, mem_image_of_mem ι hn, hγ'_eq n⟩
      · have hcbd : ¬ (c ∩ bd π.S).Nonempty :=
          fun h => hdbd ((hbd_iff c hc).mpr ⟨h, hcΘ⟩)
        obtain ⟨n, hn, rfl⟩ := π.p5 c hc hcbd v hv ⟨c₂, hc₂, hc₂_ne, hv₂⟩
        exact ⟨ι n, mem_image_of_mem ι hn, hγ'_eq n⟩
    p6 := by
      intro d hd hdbd v hv ⟨d₂, hd₂, hd₂_ne, hv₂⟩
      rw [hΓ'C] at hd hd₂
      obtain ⟨c, hc, rfl⟩ := hd
      obtain ⟨c₂, hc₂, rfl⟩ := hd₂
      rw [hα'_eq c hc] at hv
      rw [hα'_eq c₂ hc₂] at hv₂
      have hc₂_ne : c₂ ≠ c := fun h => hd₂_ne (congrArg _ h)
      obtain ⟨n, hn, hvn⟩ :=
        π.p6 c hc ((hbd_iff c hc).mp hdbd).1 v hv ⟨c₂, hc₂, hc₂_ne, hv₂⟩
      rw [htilde_ι c hc]
      refine ⟨ι n, mem_image_of_mem ι hn, ?_⟩
      rw [hβ'_eq n, hγ'_eq n]
      rcases hvn with hvn | ⟨hnγ, rfl⟩
      · exact Or.inl hvn
      · exact Or.inr ⟨mem_image_of_mem ι hnγ, rfl⟩
    p7 := by
      intro Φ hΦ x₁ hx₁ x₂ hx₂ x₃ hx₃ x₄ hx₄ hord v hv₁ hv₃
      rw [hcuffsS'] at hΦ
      obtain ⟨Θ', ⟨hΘ', hΘ'ne⟩, rfl⟩ := hΦ
      rw [hΓ'N, ← image_inter hι_inj] at hx₁ hx₂ hx₃ hx₄
      obtain ⟨n₁, hn₁, rfl⟩ := hx₁
      obtain ⟨n₂, hn₂, rfl⟩ := hx₂
      obtain ⟨n₃, hn₃, rfl⟩ := hx₃
      obtain ⟨n₄, hn₄, rfl⟩ := hx₄
      rw [hβ'_eq, hγ'_eq, hι_inj.mem_set_image] at hv₁ hv₃ ⊢
      rw [hβ'_eq, hγ'_eq, hι_inj.mem_set_image]
      exact π.p7 Θ' hΘ' n₁ hn₁ n₂ hn₂ n₃ hn₃ n₄ hn₄
        (horder_ι Θ' hΘ' hΘ'ne n₁ hn₁ n₂ hn₂ n₃ hn₃ n₄ hn₄ hord) v hv₁ hv₃ }

/-- **Graph Minors XVII, (5.1)** (page 171):
"If $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ is a 0-redundant $\mathscr{T}$-central
portrayal of a hypergraph $G$, then for each cuff $\Theta$ of $\Sigma$, $\pi$ has warp $\ge
1$ at $\Theta$." -/
theorem theorem_5_1_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (π : Portrayal G) [CompactSpace π.S] [T2Space π.S]
    (hT : π.IsCentral 𝒯) (hred : π.IsZeroRedundant 𝒯)
    {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) :
    1 ≤ π.warpAt Θ := by
  classical
  by_contra hlt
  have hw0 : π.warpAt Θ = 0 := by omega
  obtain ⟨hβ0, hp5_Θ⟩ := π.borderSet_eq_empty_of_warpAt_eq_zero hΘ hw0
  have : ConnectedSpace π.S := π.connected
  obtain ⟨S', tS', cS', h2S', connS', hsS', hsimpS', ι, Γ', hι_inj, hΓ'N, hΓ'C, hbdS', hcuffsS',
    htilde_ι, horder_ι⟩ := GraphMinor.GM17.pasteCuffPainting π.S π.isSurface π.Γ Θ hΘ
  have hcell_eq : ∀ {c₁ c₂ : Set π.S}, ι '' c₁ = ι '' c₂ → c₁ = c₂ :=
    fun h => hι_inj.image_injective h
  let α' : Set S' → Hypergraph α β := fun d =>
    if h : ∃ c ∈ π.Γ.C, d = ι '' c then π.cellGraph h.choose else ⊥
  have hα'_eq : ∀ c ∈ π.Γ.C, α' (ι '' c) = π.cellGraph c := by
    intro c hc
    have hex : ∃ c₀ ∈ π.Γ.C, ι '' c = ι '' c₀ := ⟨c, hc, rfl⟩
    dsimp [α']
    rw [dite_eq_left hex]
    exact congrArg π.cellGraph (hcell_eq hex.choose_spec.2).symm
  let β' : S' → Set α := fun x =>
    if h : ∃ n, x = ι n then π.borderSet h.choose else ∅
  have hβ'_eq : ∀ n : π.S, β' (ι n) = π.borderSet n := by
    intro n
    have hex : ∃ m, ι n = ι m := ⟨n, rfl⟩
    dsimp [β']
    rw [dite_eq_left hex]
    exact congrArg π.borderSet (hι_inj hex.choose_spec).symm
  let γ' : S' → α := fun x =>
    if h : ∃ n, x = ι n then π.nodeVertex h.choose
    else π.nodeVertex (Classical.arbitrary π.S)
  have hγ'_eq : ∀ n : π.S, γ' (ι n) = π.nodeVertex n := by
    intro n
    have hex : ∃ m, ι n = ι m := ⟨n, rfl⟩
    dsimp [γ']
    rw [dite_eq_left hex]
    exact congrArg π.nodeVertex (hι_inj hex.choose_spec).symm
  have hbd_iff : ∀ c ∈ π.Γ.C,
      ((ι '' c) ∩ bd S').Nonempty ↔ (c ∩ bd π.S).Nonempty ∧ ¬ (c ∩ Θ).Nonempty := by
    intro c hc
    rw [hbdS', ← image_inter hι_inj, image_nonempty]
    constructor
    · rintro ⟨x, hxc, hxbd, hxΘ⟩
      refine ⟨⟨x, hxc, hxbd⟩, fun hcΘ => ?_⟩
      have hsub := (π.Γ.border_cell_subset_cuff hc hΘ hcΘ).1
      exact hxΘ (hsub ⟨subset_closure hxc, hxbd⟩)
    · rintro ⟨⟨x, hxc, hxbd⟩, hcΘ⟩
      exact ⟨x, hxc, hxbd, fun hxΘ => hcΘ ⟨x, hxc, hxΘ⟩⟩
  let π' : Portrayal G :=
    capped_zero_warp_portrayal (α := α) (β := β) (G := G) π (Θ := Θ) hp5_Θ S' hsS' ι Γ' hι_inj
      hΓ'N hΓ'C hbdS' hcuffsS' htilde_ι horder_ι α' hα'_eq β' hβ'_eq γ' hγ'_eq hbd_iff
  have hπ'_central : π'.IsCentral 𝒯 := by
    intro d hd
    change ∃ B, (α' d, B) ∈ 𝒯
    rw [hΓ'C] at hd
    obtain ⟨c, hc, rfl⟩ := hd
    rw [hα'_eq c hc]
    exact hT c hc
  have hcellWarp_eq : ∀ c ∈ π.Γ.C, π'.cellWarp (ι '' c) = π.cellWarp c := by
    intro c hc
    have hbp : ∀ n : π.S, π'.borderPlus (ι n) = π.borderPlus n := by
      intro n
      ext v
      simp only [Portrayal.borderPlus, mem_ofPred_eq]
      change (v ∈ β' (ι n) ∨ (ι n ∈ ι '' π.domγ ∧ v = γ' (ι n))) ↔ _
      rw [hβ'_eq n, hγ'_eq n, hι_inj.mem_set_image]
    unfold Portrayal.cellWarp Portrayal.CellWarpLE
    congr 1
    ext p
    change (∀ x₁ ∈ tilde (ι '' c), ∀ x₂ ∈ tilde (ι '' c), x₁ ≠ x₂ →
        (β' x₁).ncard ≤ p ∧ (β' x₂).ncard ≤ p ∧
        ((π'.borderPlus x₁).ncard = p + 1 → (π'.borderPlus x₂).ncard = p + 1 →
          Portrayal.LinkagePairs (α' (ι '' c)).skeleton (π'.borderPlus x₁) (π'.borderPlus x₂)
            (p + 1)
            (γ' x₁) (γ' x₂))) ↔ _
    rw [htilde_ι c hc, hα'_eq c hc]
    constructor
    · intro h n₁ hn₁ n₂ hn₂ hne
      have := h (ι n₁) (mem_image_of_mem ι hn₁) (ι n₂) (mem_image_of_mem ι hn₂)
        (fun hEq => hne (hι_inj hEq))
      rwa [hβ'_eq n₁, hβ'_eq n₂, hbp n₁, hbp n₂, hγ'_eq n₁, hγ'_eq n₂] at this
    · rintro h _ ⟨n₁, hn₁, rfl⟩ _ ⟨n₂, hn₂, rfl⟩ hne
      rw [hβ'_eq n₁, hβ'_eq n₂, hbp n₁, hbp n₂, hγ'_eq n₁, hγ'_eq n₂]
      exact h n₁ hn₁ n₂ hn₂ (fun hEq => hne (congrArg ι hEq))
  have hwarpAt_eq : ∀ Θ' ∈ cuffs π.S, Θ' ≠ Θ → π'.warpAt (ι '' Θ') = π.warpAt Θ' := by
    intro Θ' hΘ' _
    unfold Portrayal.warpAt
    congr 1
    ext p
    change (∃ d ∈ Γ'.C, (d ∩ (ι '' Θ')).Nonempty ∧ p = π'.cellWarp d) ↔ _
    rw [hΓ'C]
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, hinter, rfl⟩
      rw [← image_inter hι_inj, image_nonempty] at hinter
      exact ⟨c, hc, hinter, hcellWarp_eq c hc⟩
    · rintro ⟨c, hc, hinter, rfl⟩
      refine ⟨ι '' c, mem_image_of_mem _ hc, ?_, (hcellWarp_eq c hc).symm⟩
      rw [← image_inter hι_inj, image_nonempty]
      exact hinter
  have hwarp_le : π'.warp ≤ π.warp := by
    by_cases hne' : (cuffs S').Nonempty
    · have hSup_bdd : ∀ p ∈ {p | ∃ Φ ∈ cuffs S', p = π'.warpAt Φ}, p ≤ π.warp := by
        rintro p ⟨Φ, hΦ, rfl⟩
        rw [hcuffsS'] at hΦ
        obtain ⟨Θ', ⟨hΘ', hΘ'ne⟩, rfl⟩ := hΦ
        rw [hwarpAt_eq Θ' hΘ' hΘ'ne]
        exact π.warpAt_le_warp hΘ'
      unfold Portrayal.warp
      rw [ite_eq_left hne']
      obtain ⟨Φ₀, hΦ₀⟩ := hne'
      exact max_le π.one_le_warp (csSup_le ⟨π'.warpAt Φ₀, Φ₀, hΦ₀, rfl⟩ hSup_bdd)
    · have h1 : π'.warp = 1 := by
        unfold Portrayal.warp
        exact ite_eq_right hne'
      rw [h1]
      exact π.one_le_warp
  exact hred π' hπ'_central (Or.inl ⟨hsimpS', hwarp_le⟩)

private lemma areaGraph_eq_cellsUnion {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) {Δ : Set π.S} {I : Set (Set π.S)}
    (hcells : {c ∈ π.Γ.C | c ⊆ Δ} = I) :
    π.areaGraph Δ = π.cellsUnion I := by
  unfold Portrayal.areaGraph
  rw [hcells]

/-- **Graph Minors XVII, (5.3)** (page 172):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a 0-redundant $\mathscr{T}$-central
portrayal of a hypergraph $G$. Let $F$ be a $\Gamma$-normal I-arc with ends $n_1, n_2$ such
that $\beta(n_1) = \beta(n_2) = F \cap \operatorname{dom}(\gamma) = \emptyset$. Then there
is a disc $\Delta \subseteq \Sigma$ with $F \subseteq \operatorname{bd}(\Delta) \subseteq F
\cup \operatorname{bd}(\Sigma)$ such that $\alpha(\Delta)$ is small." -/
theorem theorem_5_3_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (hTangle : IsTangle G θ 𝒯) (hθ : 1 ≤ θ)
    (π : Portrayal G) [CompactSpace π.S] [T2Space π.S]
    (hT : π.IsCentral 𝒯) (hred : π.IsZeroRedundant 𝒯)
    {F : Set π.S} {n₁ n₂ : π.S}
    (hnorm : π.Γ.IsNormal F) (hF : IsLineWithEnds F n₁ n₂)
    (hFbd : F ∩ bd π.S = {n₁, n₂})
    (hβ₁ : π.borderSet n₁ = ∅) (hβ₂ : π.borderSet n₂ = ∅)
    (hFγ : F ∩ π.domγ = ∅) :
    ∃ Δ : Set π.S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd π.S ∧
      IsSmallWrt 𝒯 (π.areaGraph Δ) := by
  let P : ∀ (π₁ : Portrayal G), Set π₁.S → Prop := fun π₁ F₁ =>
    ∀ (m₁ m₂ : π₁.S), IsLineWithEnds F₁ m₁ m₂ → F₁ ∩ bd π₁.S = {m₁, m₂} →
      π₁.borderSet m₁ = ∅ → π₁.borderSet m₂ = ∅ →
      ∃ Δ : Set π₁.S, IsClosedDisc Δ ∧ F₁ ⊆ discBd Δ ∧ discBd Δ ⊆ F₁ ∪ bd π₁.S ∧
        IsSmallWrt 𝒯 (π₁.areaGraph Δ)
  suffices hP : P π F from hP n₁ n₂ hF hFbd hβ₁ hβ₂
  refine Portrayal.induction_shrink_internal_cells ?_ ?_ π hT hred hnorm hFγ
  · intro π₁ _ _ hT₁ hred₁ F₁ hnorm₁ hF₁γ hdisj m₁ m₂ hF₁ hF₁bd hm₁ hm₂
    have : ConnectedSpace π₁.S := π₁.connected
    have hβF₁ : ∀ n ∈ F₁ ∩ (π₁.Γ.N ∩ bd π₁.S), π₁.borderSet n = ∅ := by
      rintro n ⟨hnF, _, hnbd⟩
      have hn : n ∈ ({m₁, m₂} : Set π₁.S) := hF₁bd ▸ ⟨hnF, hnbd⟩
      rcases hn with rfl | rfl
      · exact hm₁
      · exact hm₂
    rcases GraphMinor.GM17.cutNormalIArc π₁.S π₁.isSurface π₁.Γ F₁ m₁ m₂ hnorm₁ hF₁ hF₁bd hdisj with
      ⟨S₀, tS₀, cS₀, h2S₀, connS₀, ι₀, Γ₀, hsS₀, hsimpS₀, _, hcut₀⟩ |
      ⟨I₁, I₂, hI₁, hI₂, hsep, hside₁, hside₂⟩
    · have hsmall_empty : IsSmallWrt 𝒯 (π₁.cellsUnion (π₁.Γ.C \ π₁.Γ.C)) := by
        rw [sdiff_self]
        exact π₁.isSmallWrt_cellsUnion_empty hTangle hθ
      obtain ⟨π', hπ'T, hπ'S⟩ :=
        π₁.exists_simpler_of_isCutSidePainting hTangle hθ hT₁ hF₁γ hβF₁
          subset_rfl rfl (fun _ _ _ h => (sdiff_self ▸ h).elim)
          hsmall_empty hsS₀ hsimpS₀ hcut₀
      exact (hred₁ π' hπ'T hπ'S).elim
    · obtain ⟨hIsSep, hinter_empty⟩ :=
        π₁.isSeparation_order_zero_of_normal_cut hF₁γ hβF₁ hI₁ hI₂ hsep
      have hord_lt : separationOrder (π₁.cellsUnion I₁) (π₁.cellsUnion I₂) < θ := by
        unfold separationOrder
        rw [inter_vertexSet, hinter_empty, ncard_empty]
        exact hθ
      rcases hTangle.axiom1 hIsSep hord_lt with h1 | h2
      · have hsmall₁ : IsSmallWrt 𝒯 (π₁.cellsUnion I₁) := ⟨π₁.cellsUnion I₂, h1⟩
        rcases hside₁ with ⟨Δ, hΔ, hFΔ, hΔbd, hcells⟩ |
          ⟨S', tS', cS', h2S', connS', ι, Γ', hsS', hsimpS', _, hcut'⟩
        · refine ⟨Δ, hΔ, hFΔ, hΔbd, ?_⟩
          rwa [areaGraph_eq_cellsUnion π₁ hcells]
        · have hI₂_sub : I₂ ⊆ π₁.Γ.C := hI₂ ▸ sdiff_subset
          have hI₁_eq : I₁ = π₁.Γ.C \ I₂ := by
            ext c
            simp only [hI₂, mem_sdiff]
            exact ⟨fun hc => ⟨hI₁ hc, fun h => h.2 hc⟩,
              fun hc => by_contra fun h => hc.2 ⟨hc.1, h⟩⟩
          have hsep' : ∀ c₂ ∈ I₂, ∀ c₁ ∈ I₁, tilde c₂ ∩ tilde c₁ ⊆ F₁ :=
            fun c₂ hc₂ c₁ hc₁ => Set.inter_comm (tilde c₂) (tilde c₁) ▸ hsep c₁ hc₁ c₂ hc₂
          obtain ⟨π', hπ'T, hπ'S⟩ :=
            π₁.exists_simpler_of_isCutSidePainting hTangle hθ hT₁ hF₁γ hβF₁
              hI₂_sub hI₁_eq hsep' hsmall₁ hsS' hsimpS' hcut'
          exact (hred₁ π' hπ'T hπ'S).elim
      · have hsmall₂ : IsSmallWrt 𝒯 (π₁.cellsUnion I₂) := ⟨π₁.cellsUnion I₁, h2⟩
        rcases hside₂ with ⟨Δ, hΔ, hFΔ, hΔbd, hcells⟩ |
          ⟨S', tS', cS', h2S', connS', ι, Γ', hsS', hsimpS', _, hcut'⟩
        · refine ⟨Δ, hΔ, hFΔ, hΔbd, ?_⟩
          rwa [areaGraph_eq_cellsUnion π₁ hcells]
        · obtain ⟨π', hπ'T, hπ'S⟩ :=
            π₁.exists_simpler_of_isCutSidePainting hTangle hθ hT₁ hF₁γ hβF₁
              hI₁ hI₂ hsep hsmall₂ hsS' hsimpS' hcut'
          exact (hred₁ π' hπ'T hπ'S).elim
  · intro π₁ _ _ Γ' c₀ n Δ₀ hsh hn_γ F₁ hnorm₁ ih m₁ m₂ hF₁ hF₁bd hm₁ hm₂
    obtain ⟨Δ, hΔ, hFΔ, hΔbd, hsmall⟩ := ih m₁ m₂ hF₁ hF₁bd hm₁ hm₂
    rw [π₁.shrinkCell_areaGraph_eq Γ' c₀ n Δ₀ hsh hn_γ hnorm₁ hΔ hΔbd] at hsmall
    exact ⟨Δ, hΔ, hFΔ, hΔbd, hsmall⟩

/-- **Graph Minors XVII, (5.4)** (page 173):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a 0-redundant $\mathscr{T}$-central
portrayal of a hypergraph $G$. Let $F \subseteq \Sigma$ be a $\Gamma$-normal O-arc with $F
\cap \operatorname{dom}(\gamma) = \emptyset$. Then there is a disc $\Delta \subseteq \Sigma$
with $\operatorname{bd}(\Delta) = F$ such that $\alpha(\Delta)$ is small." -/
theorem theorem_5_4_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (hTangle : IsTangle G θ 𝒯) (hθ : 1 ≤ θ)
    (π : Portrayal G) [CompactSpace π.S] [T2Space π.S]
    (hT : π.IsCentral 𝒯) (hred : π.IsZeroRedundant 𝒯)
    {F : Set π.S} (hnorm : π.Γ.IsNormal F) (hF : IsOArc F)
    (hFγ : F ∩ π.domγ = ∅) :
    ∃ Δ : Set π.S, IsClosedDisc Δ ∧ discBd Δ = F ∧
      IsSmallWrt 𝒯 (π.areaGraph Δ) := by
  let P : ∀ (π₁ : Portrayal G), Set π₁.S → Prop := fun π₁ F₁ =>
    IsOArc F₁ →
      ∃ Δ : Set π₁.S, IsClosedDisc Δ ∧ discBd Δ = F₁ ∧
        IsSmallWrt 𝒯 (π₁.areaGraph Δ)
  suffices hP : P π F from hP hF
  refine Portrayal.induction_shrink_internal_cells ?_ ?_ π hT hred hnorm hFγ
  · intro π₁ _ _ hT₁ hred₁ F₁ hnorm₁ _ hdisj hF₁
    have : ConnectedSpace π₁.S := π₁.connected
    have hF₀γ : (∅ : Set π₁.S) ∩ π₁.domγ = ∅ := empty_inter _
    have hβF₀ : ∀ n ∈ (∅ : Set π₁.S) ∩ (π₁.Γ.N ∩ bd π₁.S), π₁.borderSet n = ∅ :=
      fun _ h => h.1.elim
    have hkeep_ne : ∀ {I_keep I_absorb : Set (Set π₁.S)},
        I_keep ⊆ π₁.Γ.C → I_absorb = π₁.Γ.C \ I_keep →
        IsSmallWrt 𝒯 (π₁.cellsUnion I_absorb) → I_keep.Nonempty := by
      intro I_keep I_absorb _ hI_abs hsmall
      by_contra hnot
      have h_empty : I_keep = ∅ := not_nonempty_iff_eq_empty.mp hnot
      have h_all : I_absorb = π₁.Γ.C := by rw [hI_abs, h_empty, sdiff_empty]
      rw [h_all, π₁.cellsUnion_C] at hsmall
      exact hsmall.ne_G hTangle rfl
    rcases GraphMinor.GM17.cutNormalOArc π₁.S π₁.isSurface π₁.Γ F₁ hnorm₁ hF₁ hdisj with
      ⟨_, S₀, tS₀, cS₀, h2S₀, connS₀, ι₀, Γ₀, hsS₀, hsimpS₀, hcut₀⟩ |
      ⟨I₁, I₂, hI₁, hI₂, hsep, hside₁, hside₂⟩
    · have hsmall_empty : IsSmallWrt 𝒯 (π₁.cellsUnion (π₁.Γ.C \ π₁.Γ.C)) := by
        rw [sdiff_self]
        exact π₁.isSmallWrt_cellsUnion_empty hTangle hθ
      obtain ⟨π', hπ'T, hπ'S⟩ :=
        π₁.exists_simpler_of_isCutSidePainting hTangle hθ hT₁ hF₀γ hβF₀
          subset_rfl rfl (fun _ _ _ h => (sdiff_self ▸ h).elim)
          hsmall_empty hsS₀ hsimpS₀ hcut₀
      exact (hred₁ π' hπ'T hπ'S).elim
    · have hsep₀ : ∀ c₁ ∈ I₁, ∀ c₂ ∈ I₂, tilde c₁ ∩ tilde c₂ ⊆ (∅ : Set π₁.S) :=
        fun c₁ hc₁ c₂ hc₂ => (hsep c₁ hc₁ c₂ hc₂).subset
      obtain ⟨hIsSep, hinter_empty⟩ :=
        π₁.isSeparation_order_zero_of_normal_cut hF₀γ hβF₀ hI₁ hI₂ hsep₀
      have hord_lt : separationOrder (π₁.cellsUnion I₁) (π₁.cellsUnion I₂) < θ := by
        unfold separationOrder
        rw [inter_vertexSet, hinter_empty, ncard_empty]
        exact hθ
      rcases hTangle.axiom1 hIsSep hord_lt with h1 | h2
      · have hsmall₁ : IsSmallWrt 𝒯 (π₁.cellsUnion I₁) := ⟨π₁.cellsUnion I₂, h1⟩
        rcases hside₁ with ⟨Δ, hΔ, hΔbd, hcells⟩ | hsimpler₁
        · refine ⟨Δ, hΔ, hΔbd, ?_⟩
          rwa [areaGraph_eq_cellsUnion π₁ hcells]
        · have hI₂_sub : I₂ ⊆ π₁.Γ.C := hI₂ ▸ sdiff_subset
          have hI₁_eq : I₁ = π₁.Γ.C \ I₂ := by
            ext c
            simp only [hI₂, mem_sdiff]
            exact ⟨fun hc => ⟨hI₁ hc, fun h => h.2 hc⟩,
              fun hc => by_contra fun h => hc.2 ⟨hc.1, h⟩⟩
          have hI₂_ne : I₂.Nonempty := hkeep_ne hI₂_sub hI₁_eq hsmall₁
          obtain ⟨S', tS', cS', h2S', connS', ι, Γ', hsS', hsimpS', hcut'⟩ := hsimpler₁ hI₂_ne
          have hsep' : ∀ c₂ ∈ I₂, ∀ c₁ ∈ I₁, tilde c₂ ∩ tilde c₁ ⊆ (∅ : Set π₁.S) :=
            fun c₂ hc₂ c₁ hc₁ => Set.inter_comm (tilde c₂) (tilde c₁) ▸ hsep₀ c₁ hc₁ c₂ hc₂
          obtain ⟨π', hπ'T, hπ'S⟩ :=
            π₁.exists_simpler_of_isCutSidePainting hTangle hθ hT₁ hF₀γ hβF₀
              hI₂_sub hI₁_eq hsep' hsmall₁ hsS' hsimpS' hcut'
          exact (hred₁ π' hπ'T hπ'S).elim
      · have hsmall₂ : IsSmallWrt 𝒯 (π₁.cellsUnion I₂) := ⟨π₁.cellsUnion I₁, h2⟩
        rcases hside₂ with ⟨Δ, hΔ, hΔbd, hcells⟩ | hsimpler₂
        · refine ⟨Δ, hΔ, hΔbd, ?_⟩
          rwa [areaGraph_eq_cellsUnion π₁ hcells]
        · have hI₁_ne : I₁.Nonempty := hkeep_ne hI₁ hI₂ hsmall₂
          obtain ⟨S', tS', cS', h2S', connS', ι, Γ', hsS', hsimpS', hcut'⟩ := hsimpler₂ hI₁_ne
          obtain ⟨π', hπ'T, hπ'S⟩ :=
            π₁.exists_simpler_of_isCutSidePainting hTangle hθ hT₁ hF₀γ hβF₀
              hI₁ hI₂ hsep₀ hsmall₂ hsS' hsimpS' hcut'
          exact (hred₁ π' hπ'T hπ'S).elim
  · intro π₁ _ _ Γ' c₀ n Δ₀ hsh hn_γ F₁ hnorm₁ ih hF₁
    obtain ⟨Δ, hΔ, hΔbd, hsmall⟩ := ih hF₁
    have hΔbd_sub : discBd Δ ⊆ F₁ ∪ bd π₁.S := hΔbd ▸ subset_union_left
    rw [π₁.shrinkCell_areaGraph_eq Γ' c₀ n Δ₀ hsh hn_γ hnorm₁ hΔ hΔbd_sub] at hsmall
    exact ⟨Δ, hΔ, hΔbd, hsmall⟩

end GraphMinor.GM17

end
