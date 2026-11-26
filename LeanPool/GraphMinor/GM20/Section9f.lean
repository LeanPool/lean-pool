/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section9e

/-!
# Graph Minors XX, Section 9: the expansion

This file proves claims (5), (6) and (7) of the proof of (9.1): the sets `η(v)` of `Section9e` and
the map
`η(c) = ζ(c)` form an expansion of `P` in `P'`.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface GraphMinor.GM04 GraphMinor.GM18 GraphMinor.GM10 Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-- The bijection between two marches maps a free patch to a free patch, since it maps a grouping to
a
grouping. -/
theorem marchMap_mem_of_isFree {α' : Type*} {μ : List α} {μ' : List α'} {Δ : Patch α} {Δ' : Patch
  α'}
    (hnd : μ.Nodup) (hnd' : μ'.Nodup) (hlen : μ.length = μ'.length) (hV : Δ.verts = {x | x ∈ μ})
    (hV' : Δ'.verts = {x | x ∈ μ'}) (hfree : Δ'.IsFree) {δ : (⊤ : SimpleGraph α).Subgraph}
    (hδ : δ ∈ Δ) : marchMapSubgraph μ μ' δ ∈ Δ' := by
  have hverts := Δ.verts_eq δ hδ
  have huniq₁ : ∀ {x y y'}, MarchCorresponds μ μ' x y → MarchCorresponds μ μ' x y' → y = y' :=
    fun h₁ h₂ ↦ marchCorresponds_unique_right hnd h₁ h₂
  have huniq₂ : ∀ {x x' y}, MarchCorresponds μ μ' x y → MarchCorresponds μ μ' x' y → x = x' :=
    fun h₁ h₂ ↦ marchCorresponds_unique_left hnd' h₁ h₂
  have hset : (marchMapSubgraph μ μ' δ).verts = Δ'.verts := by
    rw [hV']
    ext y
    constructor
    · rintro ⟨x, -, p, -, h₂, -, rfl⟩
      exact List.getElem_mem h₂
    · intro hy
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
      have hi' : i < μ.length := hlen ▸ hi
      refine ⟨μ[i], ?_, i, hi', hi, rfl, rfl⟩
      rw [hverts, hV]
      exact List.getElem_mem hi'
  refine hfree _ ?_ hset
  have hg := isGrouping_iff.mp (Δ.isGrouping δ hδ)
  refine isGrouping_iff.mpr ⟨hset.le, ?_⟩
  rintro a b c hac ⟨-, x₁, x₂, h₁, h₂, h₃⟩ ⟨-, x₃, x₄, h₄, h₅, h₆⟩
  obtain rfl := huniq₂ h₂ h₄
  have hne : x₁ ≠ x₄ := fun heq ↦ hac (huniq₁ h₁ (heq ▸ h₅))
  exact ⟨hac, x₁, x₄, h₁, h₅, hg.2 _ _ _ hne h₃ h₆⟩

section Main

variable {Ω : Type*} [Preorder Ω] {X : GradedSurface} {F : CuffParam X.S} {Q Q' : Patchwork Ω α β}
  {A : Side X F Q} {A' : Side X F Q'} {ζn : X.S → Set X.S} {ζc : Set X.S → Set X.S} {K : ℕ}
  (H : InflationHyp A A' ζn ζc K)

open Classical in
/-- The map `η` on edges. -/
noncomputable def etaEdge (A : Side X F Q) (A' : Side X F Q') (ζc : Set X.S → Set X.S) (e : β) : β
  :=
  A'.h.cell (ζc (Function.invFunOn A.h.cell A.Γ.C e))

omit [Preorder Ω] in
theorem etaEdge_cell {c : Set X.S} (hc : c ∈ A.Γ.C) :
    etaEdge A A' ζc (A.h.cell c) = A'.h.cell (ζc c) := by
  have h₁ : Function.invFunOn A.h.cell A.Γ.C (A.h.cell c) = c :=
    A.h.cell_bijOn.injOn (Function.invFunOn_mem ⟨c, hc, rfl⟩) hc
      (Function.invFunOn_eq ⟨c, hc, rfl⟩)
  simp only [etaEdge, h₁]

theorem Side.length_γ {Γ : Painting X.S} {c : Set X.S} (hc : c ∈ Γ.C) :
    (Γ.γ c).length = (tilde c).ncard := by
  classical
  rw [← Γ.γ_set c hc]
  have h₁ : {n | n ∈ Γ.γ c} = ↑(Γ.γ c).toFinset := by
    ext x
    simp
  rw [h₁, Set.ncard_coe_finset, List.toFinset_card_of_nodup (Γ.γ_nodup c hc)]

namespace InflationHyp

include H

theorem length_γ_image {c : Set X.S} (hc : c ∈ A.Γ.C) :
    (A.Γ.γ c).length = (A'.Γ.γ (ζc c)).length := by
  rw [Side.length_γ hc, Side.length_γ (H.infl.cell_mem c hc), H.infl.cell_size c hc]

theorem isBorder_image {c : Set X.S} (hc : c ∈ A.Γ.C) :
    Painting.IsBorder (ζc c) ↔ Painting.IsBorder c := Painting.isBorder_image H.infl hc

/-- Claims (5) and the case of a border cell in (6). -/
theorem border_cell_facts {Θ : Set X.S} (hΘ : Θ ∈ cuffs X.S) (m : ℕ) :
    ∃ m', ζc ((A.C Θ hΘ).cell m) = (A'.C Θ hΘ).cell m' ∧
      (A'.C Θ hΘ).pos m' ∈ ζn ((A.C Θ hΘ).pos m) ∧
      (A'.C Θ hΘ).pos (m' + 1) ∈ ζn ((A.C Θ hΘ).pos (m + 1)) := by
  have hc := (A.C Θ hΘ).cell_mem m
  obtain ⟨m', -, hm'⟩ := (A'.C Θ hΘ).exists_cell _ (H.infl.cell_mem _ hc)
    ((H.infl.borders_iff _ hc Θ hΘ).mp ((A.C Θ hΘ).meets m))
  obtain ⟨h₁, h₂⟩ := image_cell H.infl hΘ _ _ hm'.symm
  exact ⟨m', hm'.symm, h₁, h₂⟩

/-- Claim (5) of the proof of (9.1), for an internal cell. -/
theorem μ_mem_internal {c : Set X.S} (hc : c ∈ A.Γ.C) (hb : ¬ Painting.IsBorder c) (i : ℕ)
    (hi : i < (Q.μ (A.h.cell c)).length) (hi' : i < (Q'.μ (A'.h.cell (ζc c))).length) :
    (Q'.μ (A'.h.cell (ζc c)))[i] ∈ etaVert A A' ζn (Q.μ (A.h.cell c))[i] := by
  have hc' := H.infl.cell_mem c hc
  have hb' : ¬ Painting.IsBorder (ζc c) := fun h₁ ↦ hb ((H.isBorder_image hc).mp h₁)
  have hμ := A.μ_internal c hc hb
  have hμ' := A'.μ_internal _ hc' hb'
  have hlen : i < (A.Γ.γ c).length := by
    rw [hμ] at hi
    simpa using hi
  have hlen' : i < (A'.Γ.γ (ζc c)).length := by
    rw [hμ'] at hi'
    simpa using hi'
  have hn : (A.Γ.γ c)[i] ∈ A.Γ.N := by
    have h₁ : (A.Γ.γ c)[i] ∈ {n | n ∈ A.Γ.γ c} := List.getElem_mem hlen
    rw [A.Γ.γ_set c hc] at h₁
    exact tilde_subset_N A.Γ hc h₁
  refine Or.inl ⟨_, hn, ?_, _, (H.infl.nodes _ hn c hc i hlen hlen').mp rfl, ?_⟩
  · simp only [hμ, List.getElem_map]
  · simp only [hμ', List.getElem_map]

/-- Claim (5) of the proof of (9.1), for a border cell. -/
theorem μ_mem_border {c : Set X.S} (hc : c ∈ A.Γ.C) (hb : Painting.IsBorder c) (i : ℕ)
    (hi : i < (Q.μ (A.h.cell c)).length) (hi' : i < (Q'.μ (A'.h.cell (ζc c))).length) :
    (Q'.μ (A'.h.cell (ζc c)))[i] ∈ etaVert A A' ζn (Q.μ (A.h.cell c))[i] := by
  obtain ⟨Θ, hΘ, hcΘ⟩ := exists_cuff_of_isBorder hb
  obtain ⟨m, -, rfl⟩ := (A.C Θ hΘ).exists_cell c hc hcΘ
  obtain ⟨m', hm', h₁, h₂⟩ := H.border_cell_facts hΘ m
  have ha := aligned_cell A A' H.infl H.ψ_le H.two_le H.bounded H.bounded' hΘ hm'
  revert hi'
  rw [hm']
  intro hi'
  set r := Q.μ (A.h.cell ((A.C Θ hΘ).cell m))
  set r' := Q'.μ (A'.h.cell ((A'.C Θ hΘ).cell m'))
  have hbk := H.bounded _ hc hb
  have hq : i < K := hi.trans_le hbk
  have hri : r[(⟨i, hq⟩ : Fin K).1]? = some r[i] := List.getElem?_eq_getElem hi
  have hri' : r'[(⟨i, hq⟩ : Fin K).1]? = some r'[i] := List.getElem?_eq_getElem hi'
  have hd : A.h.cell ((A.C Θ hΘ).cell m) ∈ Q.dom := by
    rw [A.dom_eq]
    exact A.h.cell_bijOn.mapsTo hc
  have hvs : r[i] ∈ Q.G.ends (A.h.cell ((A.C Θ hΘ).cell m)) := by
    rw [← Q.μ_set _ hd]
    exact List.getElem_mem hi
  rw [show Q.G.ends (A.h.cell ((A.C Θ hΘ).cell m)) = _ from A.h.ends_border _ hc hb,
    (A.C Θ hΘ).tilde_eq] at hvs
  have hN₁ := (A.C Θ hΘ).mem_N m
  have hN₂ := (A.C Θ hΘ).mem_N (m + 1)
  have hΘ₁ := (A.C Θ hΘ).mem_cuff m
  have hΘ₂ := (A.C Θ hΘ).mem_cuff (m + 1)
  have hlab : ∀ {n n' : X.S} {code : Prop} (_ : n ∈ A.Γ.N ∩ Θ) (_ : n' ∈ ζn n ∩ Θ)
      (_ : marchCode K r (A.π n) = marchCode K r' (A'.π n')) (_ : (A.π n).length ≤ K)
      (_ : r[i] ∈ A.h.border n) (_ : code), r'[i] ∈ etaVert A A' ζn r[i] := by
    intro n n' code hn hn' hcd hlen hmem _
    obtain ⟨a, -, rfl⟩ := (A.C Θ hΘ).exists_pos n hn
    change r[i] ∈ A.h.border ((A.C Θ hΘ).pos a) at hmem
    obtain ⟨j, hj⟩ := A.exists_getElem? hΘ hmem
    obtain ⟨y, hy, hy'⟩ := marchCode_forward hcd hlen hj hri
    have : r'[i] = y := by
      rw [hri'] at hy'
      exact Option.some.inj hy'
    rw [this]
    exact Or.inr ⟨Θ, hΘ, _, hn, n', hn', j, hj, hy⟩
  rcases hvs with ⟨n, hn, hnv⟩ | hvs
  · rcases hn with rfl | rfl
    · have heq : r[i] = A.h.node ((A.C Θ hΘ).pos m) := hnv.symm
      have h₃ := ha.node₁ ⟨i, hq⟩ (by rw [hri, heq])
      rw [hri'] at h₃
      exact Or.inl ⟨_, hN₁, hnv, _, h₁, (Option.some.inj h₃).symm⟩
    · have heq : r[i] = A.h.node ((A.C Θ hΘ).pos (m + 1)) := hnv.symm
      have h₃ := ha.node₂ ⟨i, hq⟩ (by rw [hri, heq])
      rw [hri'] at h₃
      exact Or.inl ⟨_, hN₂, hnv, _, h₂, (Option.some.inj h₃).symm⟩
  · simp only [mem_iUnion, exists_prop] at hvs
    obtain ⟨n, hn, hvn⟩ := hvs
    rcases hn with rfl | rfl
    · exact hlab (code := True) ⟨hN₁, hΘ₁⟩ ⟨h₁, (A'.C Θ hΘ).mem_cuff m'⟩ ha.code₁
        (A.length_π_le hΘ H.bounded m) hvn trivial
    · exact hlab (code := True) ⟨hN₂, hΘ₂⟩ ⟨h₂, (A'.C Θ hΘ).mem_cuff (m' + 1)⟩ ha.code₂
        (A.length_π_le hΘ H.bounded (m + 1)) hvn trivial

/-- Claim (7) of the proof of (9.1): `η` is an expansion of `P` in `P'`. -/
theorem isExpansion : IsExpansion Q Q' (etaVert A A' ζn) (etaEdge A A' ζc) := by
  have hdom : ∀ {c}, c ∈ A.Γ.C → A.h.cell c ∈ Q.dom := fun hc ↦ by
    rw [A.dom_eq]
    exact A.h.cell_bijOn.mapsTo hc
  have hdom' : ∀ {c}, c ∈ A'.Γ.C → A'.h.cell c ∈ Q'.dom := fun hc ↦ by
    rw [A'.dom_eq]
    exact A'.h.cell_bijOn.mapsTo hc
  have hsurj : ∀ {e}, e ∈ Q.G.edgeSet → ∃ c ∈ A.Γ.C, A.h.cell c = e := fun he ↦
    A.h.cell_bijOn.surjOn he
  have hsurjd : ∀ {e}, e ∈ Q.dom → ∃ c ∈ A.Γ.C, A.h.cell c = e := fun he ↦ by
    rw [A.dom_eq] at he
    exact hsurj he
  have hlength : ∀ c ∈ A.Γ.C, (Q.μ (A.h.cell c)).length = (Q'.μ (A'.h.cell (ζc c))).length := by
    intro c hc
    have hc' := H.infl.cell_mem c hc
    by_cases hb : Painting.IsBorder c
    · obtain ⟨Θ, hΘ, hcΘ⟩ := exists_cuff_of_isBorder hb
      obtain ⟨m, -, rfl⟩ := (A.C Θ hΘ).exists_cell c hc hcΘ
      obtain ⟨m', hm', -, -⟩ := H.border_cell_facts hΘ m
      rw [hm']
      exact (aligned_cell A A' H.infl H.ψ_le H.two_le H.bounded H.bounded' hΘ hm').length_eq
    · have hb' : ¬ Painting.IsBorder (ζc c) := fun h₁ ↦ hb ((H.isBorder_image hc).mp h₁)
      rw [A.μ_internal c hc hb, A'.μ_internal _ hc' hb', List.length_map, List.length_map]
      exact H.length_γ_image hc
  refine ⟨fun v hv ↦ H.claim_2 hv, fun v _ ↦ H.eta_subset v, fun e he ↦ ?_,
    fun v₁ _ v₂ _ hne ↦ H.claim_4 hne, ?_, fun e he ↦ ?_, fun e he hnd ↦ ?_, fun e he ↦ ?_,
    fun e he i hi hi' ↦ ?_, ?_, ?_, fun e he ↦ ?_, fun e he ↦ ?_⟩
  · obtain ⟨c, hc, rfl⟩ := hsurj he
    rw [etaEdge_cell hc]
    exact A'.h.cell_bijOn.mapsTo (H.infl.cell_mem c hc)
  · intro e₁ he₁ e₂ he₂ heq
    obtain ⟨c₁, hc₁, rfl⟩ := hsurj he₁
    obtain ⟨c₂, hc₂, rfl⟩ := hsurj he₂
    rw [etaEdge_cell hc₁, etaEdge_cell hc₂] at heq
    exact congrArg _ (H.infl.cell_injOn hc₁ hc₂ (A'.h.cell_bijOn.injOn (H.infl.cell_mem _ hc₁)
      (H.infl.cell_mem _ hc₂) heq))
  · obtain ⟨c, hc, rfl⟩ := hsurj he
    rw [etaEdge_cell hc]
    exact ⟨fun _ ↦ hdom' (H.infl.cell_mem c hc), fun _ ↦ hdom hc⟩
  · exact absurd (by rw [A.dom_eq]; exact he) hnd
  · obtain ⟨c, hc, rfl⟩ := hsurjd he
    rw [etaEdge_cell hc]
    exact hlength c hc
  · obtain ⟨c, hc, rfl⟩ := hsurjd he
    revert hi'
    rw [etaEdge_cell hc]
    intro hi'
    by_cases hb : Painting.IsBorder c
    · exact H.μ_mem_border hc hb i hi hi'
    · exact H.μ_mem_internal hc hb i hi hi'
  · rw [A.roots_nil, A'.roots_nil]
  · intro i hi
    rw [A.roots_nil] at hi
    exact absurd hi (Nat.not_lt_zero i)
  · obtain ⟨c, hc, rfl⟩ := hsurjd he
    rw [etaEdge_cell hc]
    have hc' := H.infl.cell_mem c hc
    have hE := A.h.cell_bijOn.mapsTo hc
    have hE' := A'.h.cell_bijOn.mapsTo hc'
    have hV : (Q.Δ (A.h.cell c)).verts = {x | x ∈ Q.μ (A.h.cell c)} := by
      rw [Q.Δ_verts _ hE, Q.μ_set _ (hdom hc)]
    have hV' : (Q'.Δ (A'.h.cell (ζc c))).verts = {x | x ∈ Q'.μ (A'.h.cell (ζc c))} := by
      rw [Q'.Δ_verts _ hE', Q'.μ_set _ (hdom' hc')]
    by_cases hb : Painting.IsBorder c
    · have hb' := (H.isBorder_image hc).mpr hb
      have hcode := code_eq_of_ψ A A' hc hb H.infl (H.ψ_le c hc)
      simp only [Side.code, Prod.mk.injEq] at hcode
      obtain ⟨-, h₀, -, -, -, hp⟩ := hcode
      exact mapsTo_of_code (H.bounded _ hc hb) (H.bounded' _ hc' hb') (A.μ_nodup hc)
        (A'.μ_nodup hc') (fun _ h ↦ h) (fun _ h ↦ h) hV hV' h₀ hp
    · have hb' : ¬ Painting.IsBorder (ζc c) := fun h₁ ↦ hb ((H.isBorder_image hc).mp h₁)
      intro δ hδ
      exact marchMap_mem_of_isFree (A.μ_nodup hc) (A'.μ_nodup hc') (hlength c hc) hV hV'
        (A'.free_internal _ hc' hb') hδ
  · obtain ⟨c, hc, rfl⟩ := hsurj he
    rw [etaEdge_cell hc]
    exact φ_le_of_ψ A A' hc H.infl (H.ψ_le c hc)

end InflationHyp

end Main

end GraphMinor.GM20
