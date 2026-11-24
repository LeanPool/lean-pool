/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section13c
public import LeanPool.GraphMinor.GM17.Section14

import LeanPool.GraphMinor.GM17.Section13Proved

import LeanPool.GraphMinor.GM17.Section13d

import LeanPool.GraphMinor.GM17.Section8Proved

/-!
# Graph Minors XVII, Section 14: the hypergraph form of the excluded minor theorem

This file proves (14.2) of Robertson and Seymour, *Graph Minors. XVII. Taming a Vortex*, J. Combin.
Theory Ser. B 77 (1999), 162-210 (`theorem_14_2`, page 209), from (13.1).

We pass to the tangle `𝒯*` of (14.1) in the 1-skeleton `G*`, apply (13.4) there, and use (12.6) to
go back to `G / Z`. Each cell stays small, since a separation of `G* \ Z` that is small comes from a
separation of `G` in `𝒯`. The same reason carries redundancy over, by
`Portrayal.IsRedundant.of_moved`, which the paper leaves to the reader.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface GraphMinor.GM10 GraphMinor.Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-- An edge of the skeleton of `G / Z` is an edge of the skeleton of `G` with no end in `Z`. -/
theorem mem_skeleton_quotient {G : Hypergraph α β} {Z : Set α} {s : Sym2 α} :
    s ∈ (quotientVertices G Z).skeleton.edgeSet ↔ s ∈ G.skeleton.edgeSet ∧ ∀ v ∈ Z, v ∉ s := by
  induction s using Sym2.ind with
  | _ x y =>
    constructor
    · intro hs
      rw [SimpleGraph.mem_edgeSet] at hs
      obtain ⟨hne, e, hx, hy⟩ := hs
      refine ⟨(SimpleGraph.mem_edgeSet _).2 ⟨hne, e, hx.1, hy.1⟩, fun v hv hm => ?_⟩
      rcases Sym2.mem_iff.mp hm with rfl | rfl
      · exact hx.2 hv
      · exact hy.2 hv
    · rintro ⟨hs, hZ⟩
      rw [SimpleGraph.mem_edgeSet] at hs
      obtain ⟨hne, e, hx, hy⟩ := hs
      exact (SimpleGraph.mem_edgeSet _).2 ⟨hne, e, ⟨hx, fun h => hZ x h (Sym2.mem_mk_left _ _)⟩,
        ⟨hy, fun h => hZ y h (Sym2.mem_mk_right _ _)⟩⟩

/-- "`G* \ Z = (G/Z)*`" (page 210). -/
theorem oneSkeleton_quotient (G : Hypergraph α β) (Z : Set α) :
    oneSkeletonHypergraph (quotientVertices G Z) = (oneSkeletonHypergraph G).deleteVertices Z := by
  have hI : ∀ (s : Sym2 α), (∀ v ∈ Z, ¬ (s ∈ G.skeleton.edgeSet ∧ v ∈ s)) ↔ (s ∈ G.skeleton.edgeSet
    → ∀ v ∈ Z, v ∉ s) := fun s => by
    constructor
    · exact fun h hs v hv hm => h v hv ⟨hs, hm⟩
    · exact fun h v hv hm => h hm.1 v hv hm.2
  refine Hypergraph.ext rfl ?_ ?_
  · ext s
    change s ∈ (quotientVertices G Z).skeleton.edgeSet ↔ s ∈ G.skeleton.edgeSet ∧ ∀ v ∈ Z, ¬
      (s ∈ G.skeleton.edgeSet ∧ v ∈ s)
    rw [mem_skeleton_quotient, hI]
    exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
  · funext s v
    apply propext
    change (s ∈ (quotientVertices G Z).skeleton.edgeSet ∧ v ∈ s) ↔ ((s ∈ G.skeleton.edgeSet
      ∧ v ∈ s) ∧ ∀ w ∈ Z, ¬ (s ∈ G.skeleton.edgeSet ∧ w ∈ s))
    rw [mem_skeleton_quotient, hI]
    exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, fun _ => h.1.2⟩, fun h => ⟨⟨h.1.1, h.2 h.1.1⟩, h.1.2⟩⟩

theorem oneSkeleton_isGraph (G : Hypergraph α β) : (oneSkeletonHypergraph G).IsGraph := by
  intro s hs
  induction s using Sym2.ind with
  | _ x y =>
    have hend : (oneSkeletonHypergraph G).ends s(x, y) ⊆ {x, y} := fun w hw => by
      have hw' : w ∈ s(x, y) := hw.2
      rcases Sym2.mem_iff.mp hw' with rfl | rfl
      · exact .inl rfl
      · exact .inr rfl
    refine ⟨⟨x, hs, Sym2.mem_mk_left _ _⟩, ?_⟩
    calc ((oneSkeletonHypergraph G).ends s(x, y)).ncard ≤ ({x, y} : Set α).ncard
      := ncard_le_ncard hend (by simp)
      _ ≤ 2 := ncard_insert_le _ _ |>.trans (by simp)

/-- The 1-skeleton has the same simple graph. -/
theorem skeleton_oneSkeleton (G : Hypergraph α β) : (oneSkeletonHypergraph G).skeleton = G.skeleton
  := by
  ext x y
  constructor
  · rintro ⟨hne, s, hx, hy⟩
    induction s using Sym2.ind with
    | _ u v =>
      have hadj : G.skeleton.Adj u v := hx.1
      rcases Sym2.mem_iff.mp hx.2 with rfl | rfl <;> rcases Sym2.mem_iff.mp hy.2 with rfl | rfl
      · exact absurd rfl hne
      · exact hadj
      · exact hadj.symm
      · exact absurd rfl hne
  · intro h
    exact ⟨h.1, s(x, y), ⟨h, Sym2.mem_mk_left _ _⟩, ⟨h, Sym2.mem_mk_right _ _⟩⟩

/-- A separation of `G` in `𝒯`, of order below `θ*`, gives a separation of `G*` in `𝒯*` with the
same vertex sets. -/
theorem oneSkeleton_mem {G : Hypergraph α β} {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ θs : ℕ}
  (h𝒯 : IsTangle G θ 𝒯) {A B : Hypergraph α β} (h : (A, B) ∈ 𝒯)
    (ho : separationOrder A B < θs) :
    (oneSkeletonHypergraph A, (oneSkeletonHypergraph B).deleteEdges (oneSkeletonHypergraph
      A).edgeSet) ∈ oneSkeletonTangle G 𝒯 θs :=
  ⟨isSeparation_oneSkeleton (h𝒯.isSeparation h), ho, (A, B), h, rfl, rfl⟩

/-- The tangle `𝒯*` controls no more than `𝒯` does: step (1) of the proof of (14.2) (page 209). -/
theorem controlsMinor_of_oneSkeleton {α' β' : Type} {G : Hypergraph α β} {H : Hypergraph α' β'} {𝒯
  : Set (Hypergraph α β × Hypergraph α β)} {θ θs : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (hle : H.vertexSet.ncard ≤ θs) (hc : ControlsMinor
      (oneSkeletonHypergraph G) (oneSkeletonTangle G 𝒯 θs) H) : ControlsMinor G 𝒯 H := by
  obtain ⟨hH, av, ae', ae, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hc
  rw [skeleton_oneSkeleton] at h₁ h₃
  refine ⟨hH, av, ae', ae, h₁, h₂, h₃, h₄, h₅, h₆, fun A B hm ho v hv => ?_⟩
  exact h₇ (oneSkeleton_mem h𝒯 hm (lt_of_lt_of_le ho hle)) ho v hv

theorem separationOrder_quotient {A B : Hypergraph α β} {Z : Set α} (hZ : Z ⊆ (A ∩ B).vertexSet) :
    separationOrder (quotientVertices A Z) (quotientVertices B Z) + Z.ncard = separationOrder A B
      := by
  change ((A.vertexSet \ Z) ∩ (B.vertexSet \ Z)).ncard + Z.ncard = (A.vertexSet ∩ B.vertexSet).ncard
  have e : (A.vertexSet \ Z) ∩ (B.vertexSet \ Z) = (A.vertexSet ∩ B.vertexSet) \ Z := by
    ext v; simp only [mem_inter_iff, mem_sdiff]; tauto
  rw [e]
  exact Set.ncard_sdiff_add_ncard_of_subset hZ (A.vertexSet_finite.inter_of_left _)

/-- A separation in `𝒯 / Z / Y` of small order is below a separation in `𝒯* \ Z / Y`. The paper
leaves this step of (14.2) to the reader. -/
theorem quotient_dom {G : Hypergraph α β} {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ θs : ℕ}
  (h𝒯 : IsTangle G θ 𝒯) {Z Y : Set α}
    {A B : Hypergraph α β} (hm : (A, B) ∈ quotientTangle (quotientVertices G Z)
      (quotientTangle G 𝒯 Z) Y)
    (hord : separationOrder A B + Y.ncard + Z.ncard < θs) :
    ∃ A' B', (A', B') ∈ quotientTangle ((oneSkeletonHypergraph G).deleteVertices Z)
      (deleteVerticesTangle (oneSkeletonHypergraph G) Z (oneSkeletonTangle G 𝒯 θs) θs) Y ∧
      A.vertexSet ⊆ A'.vertexSet := by
  obtain ⟨-, ⟨A₀, B₀⟩, ⟨-, ⟨A₃, B₃⟩, hm₃, hZ₃, h₁, h₂⟩, hY₀, h₃, h₄⟩ := hm
  dsimp only at h₁ h₂ h₃ h₄ hZ₃ hY₀
  subst h₁ h₂ h₃ h₄
  have hsep₃ := h𝒯.isSeparation hm₃
  have e₁ := separationOrder_quotient hZ₃
  have e₂ := separationOrder_quotient hY₀
  have ho : separationOrder A₃ B₃ < θs := by omega
  have hm₅ := oneSkeleton_mem h𝒯 hm₃ ho
  set A₅ := oneSkeletonHypergraph A₃
  set B₅ := (oneSkeletonHypergraph B₃).deleteEdges (oneSkeletonHypergraph A₃).edgeSet
  have hsepd := isSeparation_deleteVertices (isSeparation_oneSkeleton hsep₃) Z
  have hZ₅ : Z ⊆ (A₅ ∩ B₅).vertexSet := hZ₃
  have e₃ := separationOrder_deleteVertices hZ₅
  have e₄ : separationOrder A₅ B₅ = separationOrder A₃ B₃ := rfl
  refine ⟨quotientVertices (A₅.deleteVertices Z) Y, quotientVertices (B₅.deleteVertices Z) Y,
    ⟨GM10.IsSeparation.quotientVertices hsepd Y, (A₅.deleteVertices Z, B₅.deleteVertices Z),
      ⟨hsepd, ?_, (A₅, B₅), hm₅, hZ₅, rfl, rfl⟩, hY₀, rfl, rfl⟩, subset_rfl⟩
  dsimp only
  omega

/-- A cell small for the embodiment of `𝒯* \ Z` lies in a separation of `𝒯 / Z`: step (2) of the
proof of (14.2) (page 210). -/
theorem embodiment_dom {G : Hypergraph α β} {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ θs θ₂ :
  ℕ} (h𝒯 : IsTangle G θ 𝒯) {Z : Set α}
    {A B : Hypergraph α β}
    (hm : (A, B) ∈ embodimentTangle (quotientVertices G Z) (deleteVerticesTangle
      (oneSkeletonHypergraph G) Z (oneSkeletonTangle G 𝒯 θs) θs) θ₂) :
    ∃ A' B', (A', B') ∈ quotientTangle G 𝒯 Z ∧ A.vertexSet ⊆ A'.vertexSet := by
  obtain ⟨-, -, B₁, -, -, ⟨A₂, B₂⟩, hm₂, hZ₂, h₁, -⟩ := hm
  obtain ⟨-, -, ⟨A₃, B₃⟩, hm₃, hv₁, hv₂⟩ := hm₂
  dsimp only at h₁ hZ₂ hv₁ hv₂
  have hZ₃ : Z ⊆ (A₃ ∩ B₃).vertexSet := fun v hv => ⟨hv₁ ▸ (hZ₂ hv).1, hv₂ ▸ (hZ₂ hv).2⟩
  refine ⟨quotientVertices A₃ Z, quotientVertices B₃ Z, ⟨GM10.IsSeparation.quotientVertices
    (h𝒯.isSeparation hm₃) Z, (A₃, B₃), hm₃, hZ₃, rfl, rfl⟩, ?_⟩
  have h₂ : A.vertexSet = A₂.vertexSet \ Z := by
    have := congrArg Hypergraph.vertexSet h₁
    exact this.symm
  rw [h₂, ← hv₁]
  exact subset_rfl

theorem encard_cuffs_congr {G₁ : Hypergraph α β} {G₂ : Hypergraph α (Sym2 α)} {π₁ : Portrayal G₁}
  {π₂ : Portrayal G₂} (e : π₁.S ≃ₜ π₂.S) :
    (cuffs π₁.S).encard = (cuffs π₂.S).encard := by
  obtain ⟨a, b, c, ⟨e₂⟩⟩ := classification π₂.S π₂.isSurface π₂.connected
  rw [← π₁.finite_cuffs.cast_ncard_eq, ← π₂.finite_cuffs.cast_ncard_eq, ncard_cuffs_of_homeo e₂,
    ncard_cuffs_of_homeo (e.trans e₂)]

/-- **Graph Minors XVII, (14.2)** (page 209): "For any graph $H$ there are numbers $p, q, z$ and
$\theta > z$, such that for every hypergraph $G$ and every tangle $\mathscr{T}$ in $G$ of order $\ge
\theta$, either (i) $\mathscr{T}$ controls an $H$-minor of $G^*$, or (ii) there exists $Z \subseteq
V(G)$ with $|Z| \le z$ and a $\mathscr{T}/Z$-central portrayal $\pi = (\Sigma, \Gamma, \alpha,
\beta, \gamma)$ of $G/Z$ with warp $\le p$, such that $\Sigma$ has $\le q$ cuffs and $H$ cannot be
drawn in $\Sigma$, and $\pi$ is true and $(2p + 7)$-redundant." -/
theorem theorem_14_2_proof {α' β' : Type} (H : Hypergraph α' β') (hH : H.IsGraph) :
    ∃ p q z θ : ℕ, z < θ ∧ ∀ {α : Type u} {β : Type v} (G : Hypergraph α β) (θ' : ℕ)
      (𝒯 : Set (Hypergraph α β × Hypergraph α β)), IsTangle G θ' 𝒯 → θ ≤ θ' →
      ControlsMinor G 𝒯 H ∨ ∃ Z ⊆ G.vertexSet, Z.ncard ≤ z ∧
        ∃ π : Portrayal (quotientVertices G Z), π.warp ≤ p ∧ (cuffs π.S).encard ≤ q ∧
          ¬ CanBeDrawn π.S H ∧ π.IsTrue (quotientTangle G 𝒯 Z) ∧
          π.IsRedundant (quotientTangle G 𝒯 Z) (θ' - Z.ncard) (2 * p + 7) := by
  obtain ⟨p, q, z, θ₀, hz, h4⟩ := theorem_13_4_proof H hH (fun _ _ p _ => 2 * p + 7)
    (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)
  set θs := H.vertexSet.ncard + θ₀ + 4 * p + z + 10 with hθs
  refine ⟨p, q, z, 3 * θs, by omega, ?_⟩
  intro α β G θ' 𝒯 h𝒯 hθ
  by_cases hctrl : ControlsMinor G 𝒯 H
  · exact .inl hctrl
  refine .inr ?_
  have hts : IsTangle (oneSkeletonHypergraph G) θs (oneSkeletonTangle G 𝒯 θs) := theorem_14_1_proof
    (by omega) (by omega) h𝒯
  rcases h4 (oneSkeletonHypergraph G) (oneSkeleton_isGraph G) θs _ hts
    (by omega) with hc | ⟨Z, hZ, hcZ, π₁, hw, hcu, hdr, htrue, hred⟩
  · exact absurd (controlsMinor_of_oneSkeleton h𝒯 (by omega) hc) hctrl
  have hp : 1 ≤ p := π₁.one_le_warp.trans hw
  have hmax : max 3 (2 * p + 2) = 2 * p + 2 := by omega
  have hZG : Z ⊆ G.vertexSet := hZ
  have hts₁ := GM10.theorem_8_5_proof (oneSkeleton_isGraph G) hts hZ (by omega)
  set T' := deleteVerticesTangle (oneSkeletonHypergraph G) Z (oneSkeletonTangle G 𝒯 θs) θs with hT'
  obtain ⟨π₁', e₁, hts', hcen', hw', hred'⟩ : ∃ π₁' : Portrayal (oneSkeletonHypergraph
    (quotientVertices G Z)), Nonempty (π₁'.S ≃ₜ π₁.S) ∧
      IsTangle (oneSkeletonHypergraph (quotientVertices G Z)) (θs - Z.ncard) T' ∧ π₁'.IsCentral T'
        ∧ π₁'.warp ≤ p ∧ π₁'.IsRedundant T' (θs - Z.ncard) (2 * p + 7) := by
    rw [oneSkeleton_quotient]
    exact ⟨π₁, ⟨Homeomorph.refl _⟩, hts₁, htrue.1, hw, hred⟩
  obtain ⟨e₁⟩ := e₁
  obtain ⟨π₂, hc₂, hres₂⟩ := theorem_12_6_proof hts' (by omega) π₁' hcen' hred' hw'
  have hw₂ : π₂.warp ≤ p := by rw [hres₂.warp_eq]; exact hw'
  have ht := GM10.theorem_6_2_proof h𝒯 hZG (by omega)
  have hred₂ : π₂.IsRedundant (quotientTangle G 𝒯 Z) (θ' - Z.ncard) (2 * p + 7) := by
    refine Portrayal.IsRedundant.of_moved ht hts' (by omega) rfl (edgesCovered_oneSkeleton _)
      (by omega) hred' hw' hres₂.warpLE ?_
    intro Y _ hY A B hm ho
    rw [oneSkeleton_quotient]
    exact quotient_dom h𝒯 hm (by omega)
  have hc₃ : π₂.IsCentral (quotientTangle G 𝒯 Z) := by
    intro c hc
    obtain ⟨B, hB⟩ := hc₂ c hc
    obtain ⟨A', B', hm, hsub⟩ := embodiment_dom h𝒯 hB
    have hle := π₂.cellGraph_le c hc
    have hsmall := π₂.ncard_cell_inter_other_le hw₂ hc
    have ho₀ : separationOrder (π₂.cellGraph c) (complSubhypergraph (quotientVertices G Z)
      (π₂.cellGraph c)) ≤ max 3 (2 * p + 2) := by
      rw [separationOrder_complSubhypergraph]
      exact (ncard_le_ncard (π₂.attachments_cellGraph_subset_otherVertices hc)
        ((π₂.cellGraph c).vertexSet_finite.inter_of_left _)).trans hsmall
    exact ⟨_, GM10.theorem_2_9_proof ht hm (isSeparation_complSubhypergraph hle) (by omega) (.inr
      (.inl hsub))⟩
  obtain ⟨π, htrue', hres, hred₃⟩ := exists_true_resembling ht hc₃ hred₂
  obtain ⟨ψ, -⟩ := id hres
  obtain ⟨ψ₂, -⟩ := id hres₂
  have hS : π.S ≃ₜ π₁.S := ψ.trans (ψ₂.trans e₁)
  refine ⟨Z, hZG, hcZ, π, by rwa [hres.warp_eq], ?_,
    fun hd => hdr (GM20.Draw.CanBeDrawn.map hS hd), htrue', hred₃⟩
  rw [encard_cuffs_congr hS]
  exact hcu

end GraphMinor.GM17
