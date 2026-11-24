/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section8i

/-!
# Poles and the edges of `Γ*`

An edge of the radial drawing either lies in `Σ`, or runs from a pole to a vertex on the cuff of the
pole. We also show that two vertices on a cuff are joined through the pole, and that a pole on a
circuit of `Γ*` has two different neighbours in the circuit.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S} {rad : RadialDrawing cap Γ}

omit [T2Space S] [T2Space Shat] in
theorem RadialDrawing.edge_ends (rad : RadialDrawing cap Γ) {e : Set Shat} (he : e ∈ rad.G.E) :
    ∃ v ∈ Γ.V, ∃ w ∈ rad.Rstar, closure e ∩ rad.G.V = {cap.emb v, w} := by
  obtain ⟨_, ⟨v, hv, rfl⟩, w, hw, h⟩ := rad.isPreRadial.2.2.2.2.1 e he
  exact ⟨v, hv, w, hw, h⟩

omit [T2Space S] [T2Space Shat] in
theorem RadialDrawing.not_mem_hatV (rad : RadialDrawing cap Γ) {w : Shat} (hw : w ∈ rad.Rstar) :
    w ∉ Γ.hatV cap := hw.2

omit [T2Space Shat] in
omit [T2Space S] in
/-- An edge of `Γ*` with end `w ∈ R*` lies in the region of `w`. -/
theorem RadialDrawing.edge_subset_region (rad : RadialDrawing cap Γ) {e : Set Shat} {x w : Shat}
    (he : e ∈ rad.G.E) (hw : w ∈ rad.Rstar) (hset : closure e ∩ rad.G.V = {x, w}) :
    e ⊆ rad.regionOf w := by
  have hdis : e ⊆ (Γ.hatU cap)ᶜ := fun y hy hyU ↦ by
    have hm : y ∈ Γ.hatU cap ∩ rad.G.U := ⟨hyU, rad.G.closure_subset_U he (subset_closure hy)⟩
    rw [rad.isPreRadial.1] at hm
    exact (he.2.1 hy).2 (rad.isPreRadial.2.1 hm)
  have hwcl : w ∈ closure e := by
    have : w ∈ closure e ∩ rad.G.V := by rw [hset]; exact Or.inr rfl
    exact this.1
  have hwU := (rad.regionOf_mem hw).2
  have hwn : w ∈ (Γ.hatU cap)ᶜ := connectedComponentIn_subset _ _ hwU
  have hconn : IsPreconnected (insert w e) := by
    have : insert w e = e ∪ {w} := by rw [union_singleton]
    rw [this]
    exact he.2.2.1.isConnected.isPreconnected.subset_closure subset_union_left
      (union_subset subset_closure (singleton_subset_iff.mpr hwcl))
  have hsub := hconn.subset_connectedComponentIn (mem_insert w e)
    (insert_subset hwn hdis)
  exact (subset_insert w e).trans hsub

variable (hS : IsSurface S)
include hS

omit [T2Space Shat] in
omit [T2Space S] in
/-- A cuff has a pole, and the region of this pole is the pasted open disc. -/
theorem RadialDrawing.exists_pole (rad : RadialDrawing cap Γ) {Θ : Set S} (hΘ : Θ ∈ cuffs S) :
    ∃ p ∈ rad.poles, p ∈ cap.cuffDisc Θ ∧ rad.regionOf p = cap.cuffDisc Θ := by
  have hman : ∀ x : Shat, IsManifoldPoint x := cap.isSurface.2.2
  obtain ⟨x, hx⟩ : (cap.cuffDisc Θ).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have h₁ := cap.closure_cuffDisc hS hΘ
    rw [hne, closure_empty, empty_union] at h₁
    obtain ⟨y, hy, rfl⟩ := hΘ
    exact (h₁.symm ▸ mem_image_of_mem cap.emb (mem_connectedComponentIn hy) : cap.emb y ∈
      (∅ : Set Shat))
  have hxU : x ∈ (Γ.hatU cap)ᶜ := fun ⟨y, _, hy⟩ ↦ cap.notMem_range hΘ hx ⟨y, hy⟩
  have hr : connectedComponentIn (Γ.hatU cap)ᶜ x ∈ Γ.hatRegions cap := ⟨x, hxU, rfl⟩
  have hxr := mem_connectedComponentIn hxU
  have hreg : connectedComponentIn (Γ.hatU cap)ᶜ x = cap.cuffDisc Θ := by
    rcases hatRegion_cases hS cap Γ hr with h | ⟨Θ', hΘ', h⟩
    · exact absurd (h hxr) (cap.notMem_range hΘ hx)
    · have : Θ' = Θ := by
        by_contra hne
        have hd := cap.cuffDisc_disjoint Θ' hΘ' Θ hΘ hne
        exact disjoint_left.mp hd (subset_closure (h ▸ hxr)) (subset_closure hx)
      rw [h, this]
  obtain ⟨p, ⟨hpr, hpG⟩, -⟩ := rad.isPreRadial.2.2.1 _ hr
  have hpU : p ∉ Γ.hatV cap := fun ⟨y, hy, h⟩ ↦
    (connectedComponentIn_subset _ _ hpr) ⟨y, Γ.V_subset hy, h⟩
  have hpΘ : p ∈ cap.cuffDisc Θ := hreg ▸ hpr
  have hreg' : rad.regionOf p = cap.cuffDisc Θ := by
    simp only [RadialDrawing.regionOf]
    rw [← connectedComponentIn_eq hpr, hreg]
  exact ⟨p, ⟨⟨hpG, hpU⟩, fun h ↦ cap.notMem_range hΘ hpΘ
    (h (hreg'.symm ▸ hpΘ : p ∈ rad.regionOf p))⟩, hpΘ, hreg'⟩

omit [T2Space Shat] in
omit [T2Space S] in
/-- The region of a pole is a pasted open disc. -/
theorem RadialDrawing.pole_cases (rad : RadialDrawing cap Γ) {p : Shat} (hp : p ∈ rad.poles) :
    ∃ Θ ∈ cuffs S, rad.regionOf p = cap.cuffDisc Θ ∧ p ∈ cap.cuffDisc Θ := by
  obtain ⟨hr, hpr⟩ := rad.regionOf_mem hp.1
  rcases hatRegion_cases hS cap Γ hr with h | ⟨Θ, hΘ, h⟩
  · exact absurd h hp.2
  · exact ⟨Θ, hΘ, h, h ▸ hpr⟩

omit [T2Space S] [T2Space Shat] hS in
/-- A vertex in `R*` that is not a pole has its region in `Σ`. -/
theorem RadialDrawing.region_subset_range (rad : RadialDrawing cap Γ) {w : Shat}
    (hw : w ∈ rad.Rstar) (hn : w ∉ rad.poles) : rad.regionOf w ⊆ range cap.emb := by
  by_contra h
  exact hn ⟨hw, h⟩

omit [T2Space Shat] in
omit [T2Space S] in
/-- An edge of `Γ*` at a pole misses `Σ`, and its other end lies on the cuff of the pole. -/
theorem RadialDrawing.pole_edge (rad : RadialDrawing cap Γ) {e : Set Shat} {p : Shat} {v : S}
    (he : e ∈ rad.G.E) (hp : p ∈ rad.poles) {Θ : Set S} (hΘ : Θ ∈ cuffs S)
    (hreg : rad.regionOf p = cap.cuffDisc Θ) (hset : closure e ∩ rad.G.V = {cap.emb v, p}) :
    Disjoint e (range cap.emb) ∧ v ∈ Θ := by
  have hsub := rad.edge_subset_region he hp.1 hset
  rw [hreg] at hsub
  refine ⟨disjoint_left.mpr fun x hx hr ↦ cap.notMem_range hΘ (hsub hx) hr, ?_⟩
  have hvcl : cap.emb v ∈ closure e := by
    have : cap.emb v ∈ closure e ∩ rad.G.V := by rw [hset]; exact Or.inl rfl
    exact this.1
  have h₁ := closure_mono hsub hvcl
  rw [cap.closure_cuffDisc hS hΘ] at h₁
  rcases h₁ with h | ⟨y, hy, hyv⟩
  · exact absurd ⟨v, rfl⟩ (cap.notMem_range hΘ h)
  · rwa [← cap.isEmbedding.injective hyv]

omit [T2Space Shat] hS in
omit [T2Space S] in
/-- An edge of `Γ*` with no end a pole lies in `Σ`. -/
theorem RadialDrawing.edge_subset_range (rad : RadialDrawing cap Γ) {e : Set Shat} {x w : Shat}
    (he : e ∈ rad.G.E) (hw : w ∈ rad.Rstar) (hn : w ∉ rad.poles)
    (hset : closure e ∩ rad.G.V = {x, w}) : e ⊆ range cap.emb :=
  (rad.edge_subset_region he hw hset).trans (rad.region_subset_range hw hn)

variable (h3 : Γ.IsInternallyThreeConnected)
include h3

omit [T2Space Shat] in
/-- Each vertex on a cuff is joined to the pole of the cuff. -/
theorem RadialDrawing.exists_pole_edge (rad : RadialDrawing cap Γ) {p : Shat} (hp : p ∈ rad.poles)
    {Θ : Set S} (hΘ : Θ ∈ cuffs S) (hreg : rad.regionOf p = cap.cuffDisc Θ) {v : S}
    (hv : v ∈ Γ.V) (hvΘ : v ∈ Θ) : ∃ e ∈ rad.G.E, closure e ∩ rad.G.V = {cap.emb v, p} := by
  refine rad.exists_spoke hS (h3.hatRegions_isOpenDisc hS cap) h3.1 hp.1 hv ?_
  rw [hreg, cap.closure_cuffDisc hS hΘ]
  exact Or.inr (mem_image_of_mem _ hvΘ)

/-- There is at most one edge of `Γ*` between two given vertices. -/
theorem RadialDrawing.edge_unique (rad : RadialDrawing cap Γ) {e₁ e₂ : Set Shat} {v : S} {w : Shat}
    (he₁ : e₁ ∈ rad.G.E) (he₂ : e₂ ∈ rad.G.E) (hv : v ∈ Γ.V) (hw : w ∈ rad.Rstar)
    (h₁ : closure e₁ ∩ rad.G.V = {cap.emb v, w}) (h₂ : closure e₂ ∩ rad.G.V = {cap.emb v, w}) :
    e₁ = e₂ := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨D, G₃, hD, hrad, hmax, hsub, hhat⟩ :=
    rad.exists_full hS (h3.hatRegions_isOpenDisc hS cap) h3.1
  obtain ⟨hr, hwr⟩ := rad.regionOf_mem hw
  have key : ∀ {e}, e ∈ rad.G.E → closure e ∩ rad.G.V = {cap.emb v, w} →
      closure e ∩ G₃.V = {cap.emb v, w} := by
    intro e he h
    have hl : rad.G.toGraph.IsLink e (cap.emb v) w :=
      ⟨he, rad.isPreRadial.2.1 (mem_image_of_mem _ hv), hw.1, h⟩
    exact ((hsub.isLink_iff hl.1).mp hl).2.2.2
  exact spoke_unique hS hD h3 hrad (hsub.2 he₁) (hsub.2 he₂) hr
    (rad.edge_subset_region he₁ hw h₁) (rad.edge_subset_region he₂ hw h₂) hv hwr
    (hsub.1 hw.1) (key he₁ h₁) (key he₂ h₂)

end GraphMinor.GM19
