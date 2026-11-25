/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13y

/-!
# Graph Minors XIX, Section 13: `sk(Γ)` in a closed disc

Let `Δ` be a closed disc whose boundary lies in `Γ*`. The part of `sk(Γ)` in `Δ` is a proper drawing
on `Δ`, and this is the drawing to which we apply VI (3.6) in the proof of (13.7). A region of
this drawing lies in a region of `Γ` or in a cell. So two vertices on its closure are joined by a
walk of `Γ*` with at most two edges.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

/-- The part of `sk(Γ)` in `Δ`, as a drawing on `Δ`. -/
structure IsSkPart (D : TangleDatum cap χ) (Δ : Set Shat) (Sk : Drawing Shat)
  (G : Drawing Δ) : Prop where
  sk : IsSkHat cap D.P.Γ Sk
  mem_U : ∀ z : Δ, z ∈ G.U ↔ z.1 ∈ Sk.U
  mem_V : ∀ z : Δ, z ∈ G.V ↔ z.1 ∈ D.P.Γ.hatV cap
  proper : G.IsProper
  link : ∀ e (x y : Δ), G.toGraph.IsLink e x y → x = y ∨ ∃ a b, cap.emb a = x.1 ∧ cap.emb b = y.1
    ∧ D.P.Γ.skAdj.Adj a b

variable {D : TangleDatum cap χ} {Δ : Set Shat} {Sk : Drawing Shat} {G : Drawing Δ}

theorem exists_isSkPart (D : TangleDatum cap χ) (hΔ : IsClosedDisc Δ)
  (hbd : discBd Δ ⊆ D.rad.G.U) : ∃ Sk G, D.IsSkPart Δ Sk G := by
  classical
  have hS := χ.isSurface
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨Sk, hSk⟩ := exists_isSkHat hS cap D.P.Γ
  have hcl : IsClosed Δ := hΔ.isClosed
  have hsub : Sk.U ⊆ D.P.Γ.hatU cap := by
    rw [hSk.hU]
    exact image_mono D.P.Γ.skU_subset
  have hrad : ∀ x ∈ Sk.U, x ∈ D.rad.G.U → x ∈ D.P.Γ.hatV cap := fun x h₁ h₂ ↦ by
    rw [← D.rad.isPreRadial.1]
    exact ⟨hsub h₁, h₂⟩
  obtain ⟨D', hU', hV', hE'⟩ := exists_restrict Sk hcl (fun x hx ↦ by
    have hx₂ := hx.2
    rw [IsClosedDisc.frontier_eq_discBd hT hΔ] at hx₂
    rw [hSk.hV]
    exact hrad x hx.1 (hbd hx₂))
  have hj : IsClosedEmbedding (Subtype.val : Δ → Shat) := hcl.isClosedEmbedding_subtypeVal
  have : Nonempty Δ := (hΔ.nonempty_discInt.mono (discInt_subset _)).to_subtype
  have hP : D'.U ⊆ range (Subtype.val : Δ → Shat) := fun x hx ↦ by
    rw [hU'] at hx
    exact ⟨⟨x, hx.2⟩, rfl⟩
  refine ⟨Sk, D'.comap hj hP, hSk, fun z ↦ ?_, fun z ↦ ?_, ?_, ?_⟩
  · change z.1 ∈ D'.U ↔ _
    rw [hU']
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, z.2⟩⟩
  · change z.1 ∈ D'.V ↔ _
    rw [hV', hSk.hV]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, z.2⟩⟩
  · rintro z ⟨hz₁, hz₂⟩
    have hb : z.1 ∈ discBd Δ := ⟨z, hz₁, rfl⟩
    change z.1 ∈ D'.U at hz₂
    rw [hU'] at hz₂
    change z.1 ∈ D'.V
    rw [hV', hSk.hV]
    exact ⟨hrad _ hz₂.1 (hbd hb), z.2⟩
  · intro e x y hl
    by_cases hxy : x = y
    · exact .inl hxy
    right
    obtain ⟨he, hx, hy, hc⟩ := hl
    have heE : Subtype.val '' e ∈ arcComponentsIn (D'.U \ D'.V) := by
      rw [arcs_comap hj hP]
      exact mem_image_of_mem _ he
    obtain ⟨heS, -⟩ := (hE' _).mp heE
    obtain ⟨f, hf, hfe⟩ := hSk.edge_iff.mp heS
    obtain ⟨c, hc'⟩ := D.P.Γ.exists_isSkEdgeIn hf
    have hmem : ∀ z : Δ, z ∈ closure e → z ∈ (D'.comap hj hP).V → ∃ a, cap.emb a = z.1
      ∧ a ∈ D.P.Γ.V ∧ a ∈ tilde c := fun z hz hzV ↦ by
      have hz₁ : z.1 ∈ D'.V := hzV
      rw [hV', hSk.hV] at hz₁
      obtain ⟨a, ha, haz⟩ := hz₁.1
      have hzcl : z.1 ∈ closure (Subtype.val '' e) := by
        rw [hj.closure_image_eq]
        exact mem_image_of_mem _ hz
      rw [← hfe, (cap.isClosedEmbedding hS).closure_image_eq] at hzcl
      obtain ⟨a', ha', haz'⟩ := hzcl
      have haa : a' = a := (cap.isClosedEmbedding hS).injective (haz'.trans haz.symm)
      subst haa
      exact ⟨a', haz, ha, closure_mono hc'.subset ha', fun hn ↦ D.P.Γ.disjoint_V hc'.1 hn ha⟩
    have hxm : x ∈ closure e ∩ (D'.comap hj hP).V := by rw [hc]; exact .inl rfl
    have hym : y ∈ closure e ∩ (D'.comap hj hP).V := by rw [hc]; exact .inr rfl
    obtain ⟨a, ha₁, ha₂, ha₃⟩ := hmem x hxm.1 hxm.2
    obtain ⟨b, hb₁, hb₂, hb₃⟩ := hmem y hym.1 hym.2
    refine ⟨a, b, ha₁, hb₁, fun hab ↦ hxy (Subtype.ext ?_), ha₂, hb₂, c, hc'.1, ha₃, hb₃⟩
    rw [← ha₁, ← hb₁, hab]

omit [T2Space S] [T2Space Shat] in
/-- A region of the part of `sk(Γ)` in `Δ` lies in a region of `sk(Γ)`. -/
theorem IsSkPart.exists_region (h : D.IsSkPart Δ Sk G) {R : Set Δ} (hR : R ∈ G.R) : ∃ q ∈ Sk.R,
  Subtype.val '' R ⊆ q := by
  obtain ⟨y, hy, rfl⟩ := (mem_R_iff G).mp hR
  have hyR : y ∈ connectedComponentIn (univ \ G.U) y := mem_connectedComponentIn ⟨mem_univ _, hy⟩
  have hoff : y.1 ∉ Sk.U := fun hn ↦ hy ((h.mem_U y).mpr hn)
  obtain ⟨q, hq, hyq⟩ := exists_region_of_notMem hoff
  refine ⟨q, hq, subset_region hq (isPreconnected_connectedComponentIn.image _
    continuous_subtype_val.continuousOn) ?_ (mem_image_of_mem _ hyR) hyq⟩
  refine disjoint_left.mpr ?_
  rintro _ ⟨z, hz, rfl⟩ hzU
  exact (connectedComponentIn_subset _ _ hz).2 ((h.mem_U z).mpr hzU)

omit [T2Space Shat] in
/-- A vertex of `Γ` on the closure of a region of `Γ` is a neighbour of the vertex of `Γ*` in that
region. -/
theorem exists_link_of_closure (D : TangleDatum cap χ) {w : Shat} (hw : w ∈ D.rad.Rstar) {v : S}
  (hv : v ∈ D.P.Γ.V) (hcl : cap.emb v ∈ closure (D.rad.regionOf w)) :
    ∃ e, D.rad.G.toGraph.IsLink e w (cap.emb v) := by
  have hS := χ.isSurface
  have h3 := D.P.fits.internally_three_connected
  obtain ⟨e, he, hc⟩ := D.rad.exists_spoke hS (h3.hatRegions_isOpenDisc hS cap) h3.1 hw hv hcl
  exact ⟨e, he, hw.1, D.rad.isPreRadial.2.1 (mem_image_of_mem _ hv), by rw [hc, Set.pair_comm]⟩

omit [T2Space Shat] in
/-- Two vertices of `Γ` on the closure of a region of `Γ` are at most two steps apart in `Γ*`. -/
theorem exists_walk_of_hatRegion (D : TangleDatum cap χ) {q : Set Shat}
  (hq : q ∈ D.P.Γ.hatRegions cap) {a b : S} (ha : a ∈ D.P.Γ.V) (hb : b ∈ D.P.Γ.V)
    (hca : cap.emb a ∈ closure q)
    (hcb : cap.emb b ∈ closure q) : ∃ K : GraphWalk D.rad.G.toGraph (cap.emb a)
      (cap.emb b), K.length ≤ 2 := by
  obtain ⟨w, ⟨hw, hwG⟩, -⟩ := D.rad.isPreRadial.2.2.1 q hq
  have hwU : w ∉ D.P.Γ.hatU cap := by
    obtain ⟨y, hy, rfl⟩ := hq
    exact connectedComponentIn_subset _ _ hw
  have hwR : w ∈ D.rad.Rstar := ⟨hwG, fun hn ↦ hwU (image_mono D.P.Γ.V_subset hn)⟩
  have hreg : D.rad.regionOf w = q := by
    obtain ⟨y, hy, rfl⟩ := id hq
    exact (connectedComponentIn_eq hw).symm
  obtain ⟨e₁, h₁⟩ := D.exists_link_of_closure hwR ha (hreg ▸ hca)
  obtain ⟨e₂, h₂⟩ := D.exists_link_of_closure hwR hb (hreg ▸ hcb)
  have hnil : cap.emb b ∈ D.rad.G.toGraph.vertexSet := h₂.2.2.1
  exact ⟨.cons h₁.symm (.cons h₂ (.nil hnil)), by simp [GraphWalk.length]⟩

end TangleDatum

end GraphMinor.GM19
